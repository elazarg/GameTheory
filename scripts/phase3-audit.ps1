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

$ProtocolFiles = @(Select-Files 'GameTheory/Protocol') + @('GameTheory/Protocol.lean')
$LanguageFiles = @(Select-Files 'GameTheory/Languages')

# --------------------------------------------------------------------------
# 1. Layering. Protocol sits above Core and below the languages; nothing in
#    either may reach into the executable frontend, the examples, or the tests.
# --------------------------------------------------------------------------

$ProtocolForbidden = 'GameTheory\.Languages|GameTheory\.Finite|GameTheory\.Examples|' +
  'GameTheory\.Tests|GameTheory\.Experimental|GameTheory\.Analysis|FixedPointTheorems'
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

# The public root carries the sequential layer and nothing that is evidence
# rather than library: encodings with recorded scope limits, and spikes.
$rootImports = Get-Imports 'GameTheory.lean'
Report 'ROOT_REEXPORTS_PROTOCOL' `
  (@($rootImports | Where-Object { $_ -eq 'GameTheory.Protocol' }).Count)
Report 'ROOT_FORBIDDEN_IMPORTS' `
  (@($rootImports | Where-Object {
    $_ -match 'GameTheory\.Languages|GameTheory\.Tests|GameTheory\.Experimental' }).Count)

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
  function Run-Probe([string] $Root, [string[]] $Constants) {
    $checks = $Constants | ForEach-Object { "#check @$_" }
    Set-Content -Path $probeFile -Value (@("import $Root") + $checks) -Encoding utf8
    return (& lake env lean $probeFile 2>&1 | Out-String)
  }
  function Is-Unreachable([string] $Output, [string] $Constant) {
    $escaped = [regex]::Escape($Constant)
    return ($Output -match
      "(?im)unknown (identifier|constant)[^\r\n]*$escaped")
  }
  $unreachable = 0
  $reachable = @()
  foreach ($group in @(
      @('GameTheory.Protocol.Execution', @('stdSimplex', 'Polynomial')),
      @('GameTheory.Protocol.Information', @('stdSimplex')))) {
    $output = Run-Probe $group[0] $group[1]
    foreach ($constant in $group[1]) {
      if (Is-Unreachable $output $constant) { $unreachable++ }
      else { $reachable += "$($group[0]) reaches $constant" }
    }
  }
  Report 'UNREACHABLE_PROBES_PASSED' $unreachable
  foreach ($r in $reachable) { Write-Output "REACHABLE_UNEXPECTED=$r" }

  # The Bayesian compiler deliberately imports the static data and information
  # interfaces, but not solution concepts. Test both directions: absence alone
  # would also pass if the compiler had quietly stopped using either input.
  $bayesianSolutionRejected = 0
  $bayesianConstants = @(
    'GameTheory.IsNash',
    'GameTheory.euPreference',
    'GameTheory.BayesianGame',
    'GameTheory.Languages.Bayesian.informationModel')
  $bayesianOutput = Run-Probe 'GameTheory.Languages.Bayesian' $bayesianConstants
  foreach ($constant in @('GameTheory.IsNash', 'GameTheory.euPreference')) {
    if (Is-Unreachable $bayesianOutput $constant) {
      $bayesianSolutionRejected++
    }
  }
  Report 'BAYESIAN_SOLUTION_PROBES_REJECTED' $bayesianSolutionRejected

  $bayesianInputsReached = 0
  foreach ($constant in @(
      'GameTheory.BayesianGame',
      'GameTheory.Languages.Bayesian.informationModel')) {
    if (-not (Is-Unreachable $bayesianOutput $constant)) {
      $bayesianInputsReached++
    }
  }
  Report 'BAYESIAN_INPUT_PROBES_REACHED' $bayesianInputsReached

  # Repeated play has one native deterministic-path layer and one deliberately
  # finite Protocol bridge. Check both the separation and the positive joins:
  # absence alone would pass if the compiler stopped consuming either side.
  $repeatedBoundaryRejected = 0
  foreach ($root in @(
      'GameTheory.Repeated.Basic',
      'GameTheory.Repeated.Discounted')) {
    $output = Run-Probe $root @('GameTheory.Protocol.ExecutionProtocol')
    if (Is-Unreachable $output 'GameTheory.Protocol.ExecutionProtocol') {
      $repeatedBoundaryRejected++
    }
  }
  $repeatedProtocolConstants = @(
    'GameTheory.UtilityGame.discountedPayoff',
    'GameTheory.UtilityGame.repeatedPlay',
    'GameTheory.Repeated.informationModel')
  $repeatedProtocolOutput =
    Run-Probe 'GameTheory.Repeated.Protocol' $repeatedProtocolConstants
  $discountedRejected = Is-Unreachable $repeatedProtocolOutput `
    'GameTheory.UtilityGame.discountedPayoff'
  if ($discountedRejected) {
    $repeatedBoundaryRejected++
  }
  Report 'REPEATED_BOUNDARY_PROBES_REJECTED' $repeatedBoundaryRejected

  $repeatedInputsReached = 0
  foreach ($constant in @(
      'GameTheory.UtilityGame.repeatedPlay',
      'GameTheory.Repeated.informationModel')) {
    if (-not (Is-Unreachable $repeatedProtocolOutput $constant)) {
      $repeatedInputsReached++
    }
  }
  Report 'REPEATED_INPUT_PROBES_REACHED' $repeatedInputsReached

  # Sequential equilibrium is a one-way analytic bridge over Protocol.
  # Protocol must not see the convergence specialization, while the bridge
  # must positively consume both stable halves and its analytic definition.
  $protocolAnalysisRejected = 0
  $protocolAnalysisConstants = @(
      'GameTheory.Analysis.Protocol.FinDistConvergesPointwise',
      'GameTheory.Protocol.InformationModel.BehavioralAssessment.IsSequentiallyConsistent')
  $protocolOutput = Run-Probe 'GameTheory.Protocol' $protocolAnalysisConstants
  foreach ($constant in $protocolAnalysisConstants) {
    if (Is-Unreachable $protocolOutput $constant) {
      $protocolAnalysisRejected++
    }
  }
  Report 'PROTOCOL_ANALYSIS_PROBES_REJECTED' $protocolAnalysisRejected

  $sequentialBridgeInputsReached = 0
  $sequentialBridgeConstants = @(
      'GameTheory.Protocol.InformationModel.BehavioralAssessment.IsSequentiallyRational',
      'GameTheory.Protocol.InformationModel.BehavioralAssessment.IsBayesConsistent',
      'GameTheory.Analysis.Protocol.FinDistConvergesPointwise')
  $sequentialOutput = Run-Probe 'GameTheory.Analysis.Protocol' `
    ($sequentialBridgeConstants + @('stdSimplex', 'Polynomial'))
  foreach ($constant in $sequentialBridgeConstants) {
    if (-not (Is-Unreachable $sequentialOutput $constant)) {
      $sequentialBridgeInputsReached++
    }
  }
  Report 'SEQUENTIAL_BRIDGE_INPUTS_REACHED' $sequentialBridgeInputsReached

  $sequentialGeometryRejected = 0
  foreach ($constant in @('stdSimplex', 'Polynomial')) {
    if (Is-Unreachable $sequentialOutput $constant) {
      $sequentialGeometryRejected++
    }
  }
  Report 'SEQUENTIAL_BRIDGE_GEOMETRY_REJECTED' $sequentialGeometryRejected
  Remove-Item $probeFile -ErrorAction SilentlyContinue
}

# --------------------------------------------------------------------------
# 5. Expected values
# --------------------------------------------------------------------------

if ($VerifyExpected) {
  $Expected = [ordered]@{
    PROTOCOL_FORBIDDEN_IMPORTS = 0
    LANGUAGE_FORBIDDEN_IMPORTS = 0
    ROOT_REEXPORTS_PROTOCOL = 1
    ROOT_FORBIDDEN_IMPORTS = 0
    TRANSPORT_PROTOCOL = 0
    TRANSPORT_LANGUAGES = 0
    FUNCTION_UPDATE_SEQUENTIAL = 0
    SORRY_OR_ADMIT_SEQUENTIAL = 0
    CUSTOM_AXIOM_SEQUENTIAL = 0
    EXECUTION_IMPORTS_INFORMATION = 0
    # The 90-column guide is soft and some lines exceed it; the count is
    # reported above rather than pinned here, because it moves with ordinary
    # edits. Nothing in the library exceeds 100, and that ceiling is locked to
    # stop it drifting.
    LIBRARY_LINES_OVER_100 = 0
  }
  if (-not $SkipReachability) {
    $Expected['UNREACHABLE_PROBES_PASSED'] = 3
    $Expected['BAYESIAN_SOLUTION_PROBES_REJECTED'] = 2
    $Expected['BAYESIAN_INPUT_PROBES_REACHED'] = 2
    $Expected['REPEATED_BOUNDARY_PROBES_REJECTED'] = 3
    $Expected['REPEATED_INPUT_PROBES_REACHED'] = 2
    $Expected['PROTOCOL_ANALYSIS_PROBES_REJECTED'] = 2
    $Expected['SEQUENTIAL_BRIDGE_INPUTS_REACHED'] = 3
    $Expected['SEQUENTIAL_BRIDGE_GEOMETRY_REJECTED'] = 2
  }
  foreach ($entry in $Expected.GetEnumerator()) {
    if ($Results[$entry.Key] -ne $entry.Value) {
      throw "$($entry.Key): expected $($entry.Value), got $($Results[$entry.Key])"
    }
  }
  Write-Output 'VERIFIED=1'
}
