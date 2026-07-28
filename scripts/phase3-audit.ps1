param(
  [switch] $VerifyExpected,
  [switch] $SkipReachability
)

$ErrorActionPreference = 'Stop'
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path

$TransportPattern =
  '(?<![A-Za-z0-9_])(cast|HEq|change)(?![A-Za-z0-9_])|Eq\.(ndrec|mpr|rec)(?![A-Za-z0-9_])|▸'

function Remove-LeanCommentsAndStrings([string] $Source) {
  $result = [Text.StringBuilder]::new()
  $depth = 0
  $inString = $false
  $escaped = $false
  for ($i = 0; $i -lt $Source.Length; $i++) {
    $c = $Source[$i]
    $next = if ($i + 1 -lt $Source.Length) { $Source[$i + 1] } else { [char] 0 }
    if ($depth -gt 0) {
      if ($c -eq '/' -and $next -eq '-') { $depth++; $i++ }
      elseif ($c -eq '-' -and $next -eq '/') { $depth--; $i++ }
      elseif ($c -eq "`n") { [void] $result.Append("`n") }
      continue
    }
    if ($inString) {
      if ($escaped) { $escaped = $false }
      elseif ($c -eq '\') { $escaped = $true }
      elseif ($c -eq '"') { $inString = $false }
      elseif ($c -eq "`n") { $inString = $false; [void] $result.Append("`n") }
      continue
    }
    if ($c -eq '/' -and $next -eq '-') { $depth = 1; $i++ }
    elseif ($c -eq '-' -and $next -eq '-') {
      while ($i -lt $Source.Length -and $Source[$i] -ne "`n") { $i++ }
      [void] $result.Append("`n")
    }
    elseif ($c -eq '"') { $inString = $true }
    else { [void] $result.Append($c) }
  }
  return $result.ToString()
}

function Select-Files([string] $Prefix) {
  $path = Join-Path $RepoRoot $Prefix
  if (-not (Test-Path $path)) { return @() }
  return @(Get-ChildItem -Path $path -Filter '*.lean' -Recurse |
    ForEach-Object { $_.FullName.Substring($RepoRoot.Length + 1).Replace('\', '/') })
}

function Get-Code([string] $Relative) {
  return Remove-LeanCommentsAndStrings (
    [IO.File]::ReadAllText((Join-Path $RepoRoot $Relative)).Replace("`r", ''))
}

function Get-Imports([string] $Relative) {
  return @([IO.File]::ReadAllLines((Join-Path $RepoRoot $Relative)) |
    Where-Object { $_ -match '^\s*import\s+(\S+)' } |
    ForEach-Object { ($_ -replace '^\s*import\s+', '').Trim() })
}

function Count-Pattern([string[]] $Files, [string] $Pattern) {
  $total = 0
  foreach ($f in $Files) { $total += [regex]::Matches((Get-Code $f), $Pattern).Count }
  return $total
}

function Measure-Nonblank([string[]] $Files) {
  $total = 0
  foreach ($f in $Files) {
    $total += ([IO.File]::ReadAllLines((Join-Path $RepoRoot $f)) |
      Where-Object { $_.Trim().Length -gt 0 }).Count
  }
  return $total
}

$Results = [ordered]@{}
function Report([string] $Key, $Value) {
  $script:Results[$Key] = $Value
  Write-Output "$Key=$Value"
}

$ProtocolFiles = Select-Files 'GameTheory/Protocol'
$LanguageFiles = Select-Files 'GameTheory/Languages'

# --------------------------------------------------------------------------
# 1. Layering. Protocol sits above Core and below the languages; nothing in
#    either may reach into the executable frontend, the examples, or the tests.
# --------------------------------------------------------------------------

$ProtocolForbidden = 'GameTheory\.Languages|GameTheory\.Finite|GameTheory\.Examples|' +
  'GameTheory\.Tests|GameTheory\.Experimental'
$protocolBad = 0
foreach ($f in $ProtocolFiles) {
  foreach ($imp in Get-Imports $f) { if ($imp -match $ProtocolForbidden) { $protocolBad++ } }
}
Report 'PROTOCOL_FORBIDDEN_IMPORTS' $protocolBad

$LanguageForbidden = 'GameTheory\.Examples|GameTheory\.Tests|GameTheory\.Experimental'
$languageBad = 0
foreach ($f in $LanguageFiles) {
  foreach ($imp in Get-Imports $f) { if ($imp -match $LanguageForbidden) { $languageBad++ } }
}
Report 'LANGUAGE_FORBIDDEN_IMPORTS' $languageBad

# --------------------------------------------------------------------------
# 2. Forbidden patterns
# --------------------------------------------------------------------------

$SequentialFiles = $ProtocolFiles + $LanguageFiles
Report 'TRANSPORT_PROTOCOL' (Count-Pattern $ProtocolFiles $TransportPattern)
Report 'TRANSPORT_LANGUAGES' (Count-Pattern $LanguageFiles $TransportPattern)
Report 'FUNCTION_UPDATE_SEQUENTIAL' `
  (Count-Pattern $SequentialFiles '(?<![A-Za-z0-9_.])Function\.update(?![A-Za-z0-9_])')
Report 'SORRY_OR_ADMIT_SEQUENTIAL' `
  (Count-Pattern $SequentialFiles '(?<![A-Za-z0-9_])(sorry|admit|native_decide)(?![A-Za-z0-9_])')
Report 'CUSTOM_AXIOM_SEQUENTIAL' (Count-Pattern $SequentialFiles '(?m)^\s*axiom\s')

# The execution and information layers stay independent: the information model
# may consume an execution protocol, but execution must not mention information.
$executionBad = 0
foreach ($imp in Get-Imports 'GameTheory/Protocol/Execution.lean') {
  if ($imp -match 'GameTheory\.Protocol\.Information') { $executionBad++ }
}
Report 'EXECUTION_IMPORTS_INFORMATION' $executionBad

# --------------------------------------------------------------------------
# 3. Sizes
# --------------------------------------------------------------------------

# Line width is a style guide, not a gate, so these are reported rather than
# verified. They carry their threshold in the name: an unqualified "long lines"
# count is ambiguous, because the answer moves with where the limit is drawn.
$LibraryFiles = @(Get-ChildItem -Path (Join-Path $RepoRoot 'GameTheory') -Filter '*.lean' -Recurse |
  ForEach-Object { $_.FullName.Substring($RepoRoot.Length + 1).Replace('\', '/') } |
  Where-Object { -not $_.StartsWith('GameTheory/Experimental') })
$widest = 0
$over90 = 0
$over100 = 0
foreach ($f in $LibraryFiles) {
  foreach ($line in [IO.File]::ReadAllLines((Join-Path $RepoRoot $f))) {
    if ($line.Length -gt $widest) { $widest = $line.Length }
    if ($line.Length -gt 90) { $over90++ }
    if ($line.Length -gt 100) { $over100++ }
  }
}
Report 'LIBRARY_MAX_LINE_LENGTH' $widest
Report 'LIBRARY_LINES_OVER_90' $over90
Report 'LIBRARY_LINES_OVER_100' $over100

Report 'NONBLANK_PROTOCOL' (Measure-Nonblank $ProtocolFiles)
Report 'NONBLANK_LANGUAGES' (Measure-Nonblank $LanguageFiles)
Report 'PROTOCOL_MODULES' $ProtocolFiles.Count
Report 'LANGUAGE_MODULES' $LanguageFiles.Count

# --------------------------------------------------------------------------
# 4. Symbol reachability. The sequential layer inherits the core's dependency
#    budget: convexity and polynomial theory must stay out.
# --------------------------------------------------------------------------

if (-not $SkipReachability) {
  $probeFile = Join-Path ([IO.Path]::GetTempPath()) 'gametheory-phase3-probe.lean'
  function Test-Unreachable([string] $Root, [string] $Constant) {
    Set-Content -Path $probeFile -Value "import $Root`n#check @$Constant" -Encoding utf8
    $output = & lake env lean $probeFile 2>&1 | Out-String
    return ($output -match 'Unknown identifier|unknown identifier|unknown constant')
  }
  $unreachable = 0
  $reachable = @()
  foreach ($probe in @(
      @('GameTheory.Protocol.Execution', 'stdSimplex'),
      @('GameTheory.Protocol.Execution', 'Polynomial'),
      @('GameTheory.Protocol.Information', 'stdSimplex'))) {
    if (Test-Unreachable $probe[0] $probe[1]) { $unreachable++ }
    else { $reachable += "$($probe[0]) reaches $($probe[1])" }
  }
  Remove-Item $probeFile -ErrorAction SilentlyContinue
  Report 'UNREACHABLE_PROBES_PASSED' $unreachable
  foreach ($r in $reachable) { Write-Output "REACHABLE_UNEXPECTED=$r" }
}

# --------------------------------------------------------------------------
# 5. Expected values
# --------------------------------------------------------------------------

if ($VerifyExpected) {
  $Expected = [ordered]@{
    PROTOCOL_FORBIDDEN_IMPORTS = 0
    LANGUAGE_FORBIDDEN_IMPORTS = 0
    TRANSPORT_PROTOCOL = 0
    TRANSPORT_LANGUAGES = 0
    FUNCTION_UPDATE_SEQUENTIAL = 0
    SORRY_OR_ADMIT_SEQUENTIAL = 0
    CUSTOM_AXIOM_SEQUENTIAL = 0
    EXECUTION_IMPORTS_INFORMATION = 0
    # The 90-column guide is soft and 52 lines exceed it, but nothing in the
    # library exceeds 100. That ceiling holds today, so it is locked here to
    # stop it drifting.
    LIBRARY_LINES_OVER_100 = 0
  }
  if (-not $SkipReachability) { $Expected['UNREACHABLE_PROBES_PASSED'] = 3 }
  foreach ($entry in $Expected.GetEnumerator()) {
    if ($Results[$entry.Key] -ne $entry.Value) {
      throw "$($entry.Key): expected $($entry.Value), got $($Results[$entry.Key])"
    }
  }
  Write-Output 'VERIFIED=1'
}
