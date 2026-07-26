param(
  [switch] $VerifyExpected,
  [switch] $SkipReachability
)

$ErrorActionPreference = 'Stop'
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path

# RFC 7.1 counts transport at source level over authored declarations, not in
# elaborated proof terms.
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

$AllFiles = Get-ChildItem -Path (Join-Path $RepoRoot 'GameTheory') -Filter '*.lean' -Recurse |
  ForEach-Object { $_.FullName.Substring($RepoRoot.Length + 1).Replace('\', '/') }
$AllFiles += 'GameTheory.lean'

function Get-Code([string] $Relative) {
  $text = [IO.File]::ReadAllText((Join-Path $RepoRoot $Relative)).Replace("`r", '')
  return Remove-LeanCommentsAndStrings $text
}

function Get-Imports([string] $Relative) {
  $lines = [IO.File]::ReadAllLines((Join-Path $RepoRoot $Relative))
  return $lines | Where-Object { $_ -match '^\s*import\s+(\S+)' } |
    ForEach-Object { ($_ -replace '^\s*import\s+', '').Trim() }
}

function Count-Pattern([string[]] $Files, [string] $Pattern) {
  $total = 0
  foreach ($f in $Files) { $total += [regex]::Matches((Get-Code $f), $Pattern).Count }
  return $total
}

function Select-Files([string] $Prefix) {
  return @($AllFiles | Where-Object { $_.StartsWith($Prefix) })
}

$Results = [ordered]@{}
function Report([string] $Key, $Value) {
  $script:Results[$Key] = $Value
  Write-Output "$Key=$Value"
}

# --------------------------------------------------------------------------
# 1. Forbidden patterns (RFC 7.1)
# --------------------------------------------------------------------------

$ProfileModule = 'GameTheory/Core/Signature.lean'
$OutsideProfile = @($AllFiles | Where-Object { $_ -ne $ProfileModule })

Report 'FUNCTION_UPDATE_OUTSIDE_PROFILE' `
  (Count-Pattern $OutsideProfile '(?<![A-Za-z0-9_.])Function\.update(?![A-Za-z0-9_])')
Report 'TRANSPORT_IN_PROFILE_MODULE' (Count-Pattern @($ProfileModule) $TransportPattern)

# Phase 1's experimental candidates are frozen evidence; they are reported
# separately so that the Phase 2 source budget is a like-for-like number.
$Phase1Files = @(Select-Files 'GameTheory/Experimental/Phase1')
$Phase2ProbeFiles = @(Select-Files 'GameTheory/Experimental/Phase2')
$Phase2Files = @($OutsideProfile | Where-Object {
  ($Phase1Files -notcontains $_) -and ($Phase2ProbeFiles -notcontains $_) })
Report 'TRANSPORT_PHASE2_SOURCE' (Count-Pattern $Phase2Files $TransportPattern)
Report 'TRANSPORT_PHASE2_PROBE' (Count-Pattern $Phase2ProbeFiles $TransportPattern)
Report 'TRANSPORT_PHASE1_EVIDENCE' (Count-Pattern $Phase1Files $TransportPattern)
# D2 requires the finite-law representation to stay hidden. `ENNReal`, `toReal`,
# `PMF`, and `toPMF` must not appear outside the representation module; the
# frozen Phase 1 candidates are evidence and are excluded.
$RepresentationModule = 'GameTheory/Probability/FinDist.lean'
$Phase1Prefix = 'GameTheory/Experimental/Phase1'
$NonRepresentation = @($AllFiles | Where-Object {
  ($_ -ne $RepresentationModule) -and (-not $_.StartsWith($Phase1Prefix)) })
Report 'REPRESENTATION_TOKENS_OUTSIDE_FINDIST' `
  (Count-Pattern $NonRepresentation `
    '(?<![A-Za-z0-9_])(ENNReal|toReal|toPMF|PMF)(?![A-Za-z0-9_])')

Report 'FINTYPE_OF_FINITE' (Count-Pattern $AllFiles 'Fintype\.ofFinite')
Report 'ALGORITHM_OPEN_CLASSICAL' `
  (Count-Pattern @('GameTheory/Finite/Algorithm.lean') '(?<![A-Za-z0-9_])(open\s+Classical|classical|noncomputable)(?![A-Za-z0-9_])')
Report 'SORRY_OR_ADMIT' `
  (Count-Pattern $AllFiles '(?<![A-Za-z0-9_])(sorry|admit|native_decide)(?![A-Za-z0-9_])')
Report 'CUSTOM_AXIOM' (Count-Pattern $AllFiles '(?m)^\s*axiom\s')

# --------------------------------------------------------------------------
# 2. Authored-import audit (RFC 7.1, D12)
# --------------------------------------------------------------------------

$CoreFiles = @(Select-Files 'GameTheory/Core') + @('GameTheory/Core.lean') +
  @(Select-Files 'GameTheory/Probability')
$CoreForbidden = 'GameTheory\.Finite|GameTheory\.Languages|GameTheory\.Frontier|' +
  'GameTheory\.Challenges|GameTheory\.Experimental|Mathlib\.Analysis|Mathlib\.Topology|' +
  'Mathlib\.Dynamics|Mathlib\.Geometry'
$coreBad = 0
foreach ($f in $CoreFiles) {
  foreach ($imp in Get-Imports $f) { if ($imp -match $CoreForbidden) { $coreBad++ } }
}
Report 'CORE_FORBIDDEN_IMPORTS' $coreBad

$AlgorithmForbidden = 'GameTheory\.Probability|GameTheory\.Core\.Form|GameTheory\.Core\.' +
  'Deviation|Mathlib\.Probability|Mathlib\.Analysis|Mathlib\.Topology|Mathlib\.MeasureTheory|' +
  'Mathlib\.Data\.Real'
$algBad = 0
foreach ($imp in Get-Imports 'GameTheory/Finite/Algorithm.lean') {
  if ($imp -match $AlgorithmForbidden) { $algBad++ }
}
Report 'ALGORITHM_FORBIDDEN_IMPORTS' $algBad

$sigBad = 0
foreach ($imp in Get-Imports 'GameTheory/Core/Signature.lean') {
  if ($imp -match 'GameTheory\.Probability|Mathlib\.Probability') { $sigBad++ }
}
Report 'SIGNATURE_PROBABILITY_IMPORTS' $sigBad

# --------------------------------------------------------------------------
# 3. One public definition per concept (RFC 7.1, 9.1.1)
# --------------------------------------------------------------------------

$Concepts = @('IsEquilibrium', 'IsNash', 'IsCoarseCorrelatedEq', 'IsCorrelatedEq',
  'IsStrongNash', 'IsBestResponse', 'WeaklyDominates', 'StrictlyDominatesOn',
  'IsDominant', 'IsRationalizable', 'IsParetoEfficient')
$duplicates = 0
foreach ($concept in $Concepts) {
  $pattern = '(?m)^\s*(?:@\[[^]]*\]\s*)?(?:noncomputable\s+)?def\s+' +
    [regex]::Escape($concept) + '(?![A-Za-z0-9_])'
  $count = Count-Pattern $AllFiles $pattern
  Report ("DEF_COUNT_" + $concept.ToUpper()) $count
  if ($count -ne 1) { $duplicates++ }
}
Report 'CONCEPTS_NOT_DEFINED_EXACTLY_ONCE' $duplicates

# --------------------------------------------------------------------------
# 4. Size measurements
# --------------------------------------------------------------------------

function Measure-Nonblank([string[]] $Files) {
  $total = 0
  foreach ($f in $Files) {
    $total += ([IO.File]::ReadAllLines((Join-Path $RepoRoot $f)) |
      Where-Object { $_.Trim().Length -gt 0 }).Count
  }
  return $total
}

Report 'NONBLANK_PROBABILITY' (Measure-Nonblank (Select-Files 'GameTheory/Probability'))
Report 'NONBLANK_CORE' `
  (Measure-Nonblank (@(Select-Files 'GameTheory/Core') + @('GameTheory/Core.lean')))
Report 'NONBLANK_FINITE' (Measure-Nonblank (Select-Files 'GameTheory/Finite'))
Report 'NONBLANK_EXAMPLES' (Measure-Nonblank (Select-Files 'GameTheory/Examples'))
Report 'NONBLANK_TESTS' (Measure-Nonblank (Select-Files 'GameTheory/Tests'))
Report 'NONBLANK_PHASE2_PROBE' `
  (Measure-Nonblank (Select-Files 'GameTheory/Experimental/Phase2'))

# RFC 7.3 budgets the Prisoner's Dilemma definition at under 25 nonblank
# authored lines. The span is delimited by its first and last declaration.
function Measure-Span([string] $Relative, [string] $StartPattern, [string] $EndPattern) {
  $lines = [IO.File]::ReadAllLines((Join-Path $RepoRoot $Relative))
  $start = -1
  $end = -1
  for ($i = 0; $i -lt $lines.Count; $i++) {
    if ($start -lt 0 -and $lines[$i] -match $StartPattern) { $start = $i }
    if ($lines[$i] -match $EndPattern) { $end = $i }
  }
  if ($start -lt 0 -or $end -lt $start) {
    throw "Span $StartPattern .. $EndPattern not found in $Relative"
  }
  return ($lines[$start..$end] | Where-Object { $_.Trim().Length -gt 0 }).Count
}

Report 'PRISONERS_DILEMMA_DEF_LINES' `
  (Measure-Span 'GameTheory/Examples/Classic.lean' '^inductive Choice\b' '^def bothDefect\b')

# --------------------------------------------------------------------------
# 5. Symbol-reachability probes
#
# Authored-import checks cannot see Mathlib's transitive closure. These probes
# elaborate a one-line file against a public root and require the named
# constant to be *unknown*.
# --------------------------------------------------------------------------

if (-not $SkipReachability) {
  $probeFile = Join-Path ([IO.Path]::GetTempPath()) 'gametheory-phase2-probe.lean'
  function Test-Unreachable([string] $Root, [string] $Constant) {
    Set-Content -Path $probeFile -Value "import $Root`n#check @$Constant" -Encoding utf8
    $output = & lake env lean $probeFile 2>&1 | Out-String
    return ($output -match 'Unknown identifier|unknown identifier|unknown constant')
  }
  $unreachable = 0
  $reachable = @()
  foreach ($probe in @(
      @('GameTheory.Finite.Algorithm', 'Real.instAdd'),
      @('GameTheory.Finite.Algorithm', 'PMF'),
      @('GameTheory.Finite.Algorithm', 'MeasureTheory.Measure'),
      @('GameTheory.Finite.Algorithm', 'stdSimplex'),
      @('GameTheory.Core', 'stdSimplex'),
      @('GameTheory.Core', 'Polynomial'))) {
    if (Test-Unreachable $probe[0] $probe[1]) { $unreachable++ }
    else { $reachable += "$($probe[0]) reaches $($probe[1])" }
  }
  Remove-Item $probeFile -ErrorAction SilentlyContinue
  Report 'UNREACHABLE_PROBES_PASSED' $unreachable
  foreach ($r in $reachable) { Write-Output "REACHABLE_UNEXPECTED=$r" }
}

# --------------------------------------------------------------------------
# 6. Expected values
# --------------------------------------------------------------------------

if ($VerifyExpected) {
  $Expected = [ordered]@{
    FUNCTION_UPDATE_OUTSIDE_PROFILE = 0
    TRANSPORT_IN_PROFILE_MODULE = 1
    TRANSPORT_PHASE2_SOURCE = 1
    TRANSPORT_PHASE2_PROBE = 0
    FINTYPE_OF_FINITE = 0
    ALGORITHM_OPEN_CLASSICAL = 0
    SORRY_OR_ADMIT = 0
    CUSTOM_AXIOM = 0
    CORE_FORBIDDEN_IMPORTS = 0
    ALGORITHM_FORBIDDEN_IMPORTS = 0
    SIGNATURE_PROBABILITY_IMPORTS = 0
    CONCEPTS_NOT_DEFINED_EXACTLY_ONCE = 0
    REPRESENTATION_TOKENS_OUTSIDE_FINDIST = 0
  }
  # RFC 7.3 states a budget, not a target, so this one is a bound.
  if ($Results['PRISONERS_DILEMMA_DEF_LINES'] -ge 25) {
    throw ("PRISONERS_DILEMMA_DEF_LINES: RFC 7.3 budgets under 25, got " +
      $Results['PRISONERS_DILEMMA_DEF_LINES'])
  }
  if (-not $SkipReachability) { $Expected['UNREACHABLE_PROBES_PASSED'] = 6 }
  foreach ($entry in $Expected.GetEnumerator()) {
    if ($Results[$entry.Key] -ne $entry.Value) {
      throw "$($entry.Key): expected $($entry.Value), got $($Results[$entry.Key])"
    }
  }
  Write-Output 'VERIFIED=1'
}
