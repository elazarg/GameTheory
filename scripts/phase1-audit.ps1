param(
  [switch] $Time,
  [switch] $VerifyExpected
)

$ErrorActionPreference = 'Stop'
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path

$Groups = [ordered]@{
  D1_INDEXED = @('GameTheory/Experimental/Phase1/D1/Indexed.lean')
  D1_BUNDLED = @('GameTheory/Experimental/Phase1/D1/Bundled.lean')
  D1_STRESS = @('GameTheory/Experimental/Phase1/D1/Stress.lean')
  D2_PMF = @('GameTheory/Experimental/Phase1/D2/FiniteSupportPMF.lean')
  D2_FINSUPP = @('GameTheory/Experimental/Phase1/D2/NormalizedFinsupp.lean')
  D2_INTEROP = @('GameTheory/Experimental/Phase1/D2/Interop.lean')
}

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

function Measure-Group([string[]] $RelativePaths) {
  $source = ''
  $nonblank = 0
  foreach ($relative in $RelativePaths) {
    $path = Join-Path $RepoRoot $relative
    $text = [IO.File]::ReadAllText($path).Replace("`r", '')
    $source += "`n" + (Remove-LeanCommentsAndStrings $text)
    $nonblank += ([IO.File]::ReadAllLines($path) |
      Where-Object { $_.Trim().Length -gt 0 }).Count
  }
  return [ordered]@{
    NONBLANK = $nonblank
    TRANSPORT = [regex]::Matches($source,
      '(?<![A-Za-z0-9_])(cast|HEq|change)(?![A-Za-z0-9_])|Eq\.(ndrec|mpr)').Count
    TOREAL = [regex]::Matches($source, '(?<![A-Za-z0-9_])toReal(?![A-Za-z0-9_])').Count
    ENNREAL = [regex]::Matches($source, '(?<![A-Za-z0-9_])ENNReal(?![A-Za-z0-9_])').Count
    CLASSICAL = [regex]::Matches($source,
      '(?<![A-Za-z0-9_])(classical|noncomputable)(?![A-Za-z0-9_])').Count
  }
}

function Measure-Declaration([string] $RelativePath, [string] $Name) {
  $lines = [IO.File]::ReadAllLines((Join-Path $RepoRoot $RelativePath))
  $start = -1
  $pattern = '^\s*(?:@\[[^]]+\]\s*)?(?:(?:private|noncomputable)\s+)*' +
    '(?:theorem|def|structure|abbrev)\s+' + [regex]::Escape($Name) + '\b'
  for ($i = 0; $i -lt $lines.Count; $i++) {
    if ($lines[$i] -match $pattern) { $start = $i; break }
  }
  if ($start -lt 0) { throw "Declaration $Name not found in $RelativePath" }
  $end = $lines.Count
  for ($i = $start + 1; $i -lt $lines.Count; $i++) {
    if ($lines[$i] -match '^\s*(?:@\[[^]]+\]\s*)?(?:(?:private|noncomputable)\s+)*(?:theorem|def|structure|abbrev)\s+') {
      $end = $i
      break
    }
  }
  return ($lines[$start..($end - 1)] | Where-Object { $_.Trim().Length -gt 0 }).Count
}

$Results = [ordered]@{}
foreach ($entry in $Groups.GetEnumerator()) {
  $measurement = Measure-Group $entry.Value
  foreach ($metric in $measurement.GetEnumerator()) {
    $key = "$($entry.Key)_$($metric.Key)"
    $Results[$key] = $metric.Value
    Write-Output "$key=$($metric.Value)"
  }
}

$declarations = @(
  @('D1_INDEXED_COMP_ASSOC_LINES', 'GameTheory/Experimental/Phase1/D1/Indexed.lean', 'Hom.comp_assoc'),
  @('D1_BUNDLED_COMP_ASSOC_LINES', 'GameTheory/Experimental/Phase1/D1/Bundled.lean', 'Hom.comp_assoc'),
  @('D2_PMF_EXPECT_BIND_LINES', 'GameTheory/Experimental/Phase1/D2/FiniteSupportPMF.lean', 'expect_bind'),
  @('D2_FINSUPP_EXPECT_BIND_LINES', 'GameTheory/Experimental/Phase1/D2/NormalizedFinsupp.lean', 'expect_bind'),
  @('D2_PMF_SIMPLEX_LINES', 'GameTheory/Experimental/Phase1/D2/FiniteSupportPMF.lean', 'simplexEquiv'),
  @('D2_FINSUPP_SIMPLEX_LINES', 'GameTheory/Experimental/Phase1/D2/NormalizedFinsupp.lean', 'simplexEquiv')
)
foreach ($item in $declarations) {
  $value = Measure-Declaration $item[1] $item[2]
  $Results[$item[0]] = $value
  Write-Output "$($item[0])=$value"
}

if ($Time) {
  foreach ($relative in @(
      'GameTheory/Experimental/Phase1/D1/Indexed.lean',
      'GameTheory/Experimental/Phase1/D1/Bundled.lean',
      'GameTheory/Experimental/Phase1/D1/Stress.lean',
      'GameTheory/Experimental/Phase1/D2/FiniteSupportPMF.lean',
      'GameTheory/Experimental/Phase1/D2/NormalizedFinsupp.lean',
      'GameTheory/Experimental/Phase1/D2/Interop.lean')) {
    $elapsed = Measure-Command {
      & lake env lean $relative *> $null
      if ($LASTEXITCODE -ne 0) { throw "Lean failed for $relative" }
    }
    Write-Output ("TIME_MS_{0}={1}" -f ([IO.Path]::GetFileNameWithoutExtension($relative)),
      [math]::Round($elapsed.TotalMilliseconds))
  }
}

if ($VerifyExpected) {
  $Expected = [ordered]@{
    D1_INDEXED_TRANSPORT = 1
    D1_BUNDLED_TRANSPORT = 1
    D1_STRESS_TRANSPORT = 0
    D2_PMF_TOREAL = 15
    D2_FINSUPP_TOREAL = 0
  }
  foreach ($entry in $Expected.GetEnumerator()) {
    if ($Results[$entry.Key] -ne $entry.Value) {
      throw "$($entry.Key): expected $($entry.Value), got $($Results[$entry.Key])"
    }
  }
  Write-Output 'VERIFIED=1'
}
