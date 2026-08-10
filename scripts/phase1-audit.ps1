param(
  [switch] $Time,
  [switch] $VerifyExpected
)

$ErrorActionPreference = 'Stop'
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$TransportPattern =
  '(?<![A-Za-z0-9_])(cast|HEq|change)(?![A-Za-z0-9_])|Eq\.(ndrec|mpr|rec)(?![A-Za-z0-9_])|▸'

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
    TRANSPORT = [regex]::Matches($source, $TransportPattern).Count
    TOREAL = [regex]::Matches($source, '(?<![A-Za-z0-9_])toReal(?![A-Za-z0-9_])').Count
    ENNREAL = [regex]::Matches($source, '(?<![A-Za-z0-9_])ENNReal(?![A-Za-z0-9_])').Count
    CLASSICAL = [regex]::Matches($source,
      '(?<![A-Za-z0-9_])(classical|noncomputable)(?![A-Za-z0-9_])').Count
  }
}

function Measure-NamespaceTransport([string] $RelativePath, [string] $Namespace) {
  $source = Remove-LeanCommentsAndStrings (
    [IO.File]::ReadAllText((Join-Path $RepoRoot $RelativePath)).Replace("`r", ''))
  $name = [regex]::Escape($Namespace)
  $match = [regex]::Match($source,
    "(?ms)^[ \t]*namespace[ \t]+$name[ \t]*$\n(.*?)^[ \t]*end[ \t]+$name[ \t]*$")
  if (-not $match.Success) { throw "Namespace $Namespace not found in $RelativePath" }
  return [regex]::Matches($match.Groups[1].Value, $TransportPattern).Count
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

# The RFC permits dependent transport inside the profile implementation. Keep
# that allowance explicit, then report each candidate's comparable path after
# subtracting only that region and adding its own downstream stress namespace.
$indexedProfile = Measure-NamespaceTransport `
  'GameTheory/Experimental/Phase1/D1/Indexed.lean' 'Profile'
$bundledProfile = Measure-NamespaceTransport `
  'GameTheory/Experimental/Phase1/D1/Bundled.lean' 'Profile'
$indexedStress = Measure-NamespaceTransport `
  'GameTheory/Experimental/Phase1/D1/Stress.lean' 'I'
$bundledStress = Measure-NamespaceTransport `
  'GameTheory/Experimental/Phase1/D1/Stress.lean' 'B'
$derived = [ordered]@{
  D1_INDEXED_PROFILE_ALLOWANCE = $indexedProfile
  D1_BUNDLED_PROFILE_ALLOWANCE = $bundledProfile
  D1_INDEXED_STRESS_TRANSPORT = $indexedStress
  D1_BUNDLED_STRESS_TRANSPORT = $bundledStress
  D1_INDEXED_PATH_TRANSPORT =
    $Results.D1_INDEXED_TRANSPORT - $indexedProfile + $indexedStress
  D1_BUNDLED_PATH_TRANSPORT =
    $Results.D1_BUNDLED_TRANSPORT - $bundledProfile + $bundledStress
}
foreach ($entry in $derived.GetEnumerator()) {
  $Results[$entry.Key] = $entry.Value
  Write-Output "$($entry.Key)=$($entry.Value)"
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
    D1_INDEXED_NONBLANK = 95
    D1_INDEXED_TRANSPORT = 2
    D1_INDEXED_TOREAL = 0
    D1_INDEXED_ENNREAL = 0
    D1_INDEXED_CLASSICAL = 1
    D1_BUNDLED_NONBLANK = 99
    D1_BUNDLED_TRANSPORT = 2
    D1_BUNDLED_TOREAL = 0
    D1_BUNDLED_ENNREAL = 0
    D1_BUNDLED_CLASSICAL = 1
    D1_STRESS_NONBLANK = 57
    D1_STRESS_TRANSPORT = 2
    D1_STRESS_TOREAL = 0
    D1_STRESS_ENNREAL = 0
    D1_STRESS_CLASSICAL = 1
    D2_PMF_NONBLANK = 344
    D2_PMF_TRANSPORT = 3
    D2_PMF_TOREAL = 24
    D2_PMF_ENNREAL = 41
    D2_PMF_CLASSICAL = 5
    D2_FINSUPP_NONBLANK = 221
    D2_FINSUPP_TRANSPORT = 4
    D2_FINSUPP_TOREAL = 0
    D2_FINSUPP_ENNREAL = 1
    D2_FINSUPP_CLASSICAL = 8
    D2_INTEROP_NONBLANK = 101
    D2_INTEROP_TRANSPORT = 3
    D2_INTEROP_TOREAL = 3
    D2_INTEROP_ENNREAL = 3
    D2_INTEROP_CLASSICAL = 4
    D1_INDEXED_PROFILE_ALLOWANCE = 1
    D1_BUNDLED_PROFILE_ALLOWANCE = 1
    D1_INDEXED_STRESS_TRANSPORT = 0
    D1_BUNDLED_STRESS_TRANSPORT = 2
    D1_INDEXED_PATH_TRANSPORT = 1
    D1_BUNDLED_PATH_TRANSPORT = 3
    D1_INDEXED_COMP_ASSOC_LINES = 6
    D1_BUNDLED_COMP_ASSOC_LINES = 5
    D2_PMF_EXPECT_BIND_LINES = 52
    D2_FINSUPP_EXPECT_BIND_LINES = 19
    D2_PMF_SIMPLEX_LINES = 14
    D2_FINSUPP_SIMPLEX_LINES = 12
  }
  foreach ($entry in $Expected.GetEnumerator()) {
    if ($Results[$entry.Key] -ne $entry.Value) {
      throw "$($entry.Key): expected $($entry.Value), got $($Results[$entry.Key])"
    }
  }
  Write-Output 'VERIFIED=1'
}
