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

# Each phase gets its own transport budget. Without this split a later phase's
# files are silently charged to an earlier phase's gate number, which would make
# the earlier measurement drift as the repository grows.
$Phase1Files = @(Select-Files 'GameTheory/Experimental/Phase1')
$Phase2ProbeFiles = @(Select-Files 'GameTheory/Experimental/Phase2')
$Phase4Files = @(Select-Files 'GameTheory/Experimental/Phase4')
$Phase2Owned = @('GameTheory/Probability', 'GameTheory/Core', 'GameTheory/Finite',
  'GameTheory/Examples', 'GameTheory/Tests/Locality.lean', 'GameTheory.lean')
$Phase2Files = @($OutsideProfile | Where-Object {
  $candidate = $_
  ($Phase2Owned | Where-Object { $candidate.StartsWith($_) }).Count -gt 0 })
$Phase3Files = @($OutsideProfile | Where-Object {
  $_.StartsWith('GameTheory/Protocol') -or
    ($_.StartsWith('GameTheory/Tests') -and $_ -ne 'GameTheory/Tests/Locality.lean') })
$AnalysisFiles = @(Select-Files 'GameTheory/Analysis')
Report 'TRANSPORT_ANALYSIS_SOURCE' (Count-Pattern $AnalysisFiles $TransportPattern)
Report 'TRANSPORT_PHASE2_SOURCE' (Count-Pattern $Phase2Files $TransportPattern)
Report 'TRANSPORT_PHASE3_SOURCE' (Count-Pattern $Phase3Files $TransportPattern)
Report 'TRANSPORT_PHASE2_PROBE' (Count-Pattern $Phase2ProbeFiles $TransportPattern)
Report 'TRANSPORT_PHASE1_EVIDENCE' (Count-Pattern $Phase1Files $TransportPattern)
# D1 keeps the carriers as fields, and the price is that every instance of a
# carrier-bearing structure must be reducible or elaboration fails at some
# distant use site. That failure is far from its cause, so it is checked here
# instead of being left to whoever trips over it.
$CarrierStructures = 'ExecutionProtocol|InfoSignals|InformationModel|GameForm|Tree|Mechanism'
$unannotated = 0
foreach ($f in $AllFiles) {
  if ($f.StartsWith('GameTheory/Experimental')) { continue }
  $lines = [IO.File]::ReadAllLines((Join-Path $RepoRoot $f))
  for ($i = 0; $i -lt $lines.Count; $i++) {
    # Only literal instances — a structure built field by field. A definition
    # that merely takes or returns one by application needs no annotation.
    if ($lines[$i] -notmatch "^\s*def\s+\S+.*:\s*($CarrierStructures)\b[^:]*\bwhere\s*$") { continue }
    $j = $i - 1
    while ($j -ge 0 -and ($lines[$j].Trim() -eq '' -or $lines[$j] -match '^\s*(/--|--|\S.*-/$)' -or
        $lines[$j] -match '^\s*[a-z]' -and $lines[$j] -notmatch '^\s*(def|theorem|end)\b')) { $j-- }
    if ($j -lt 0 -or $lines[$j].Trim() -ne '@[reducible]') {
      $unannotated++
      Write-Output "CARRIER_INSTANCE_UNANNOTATED=${f}:$($i + 1)"
    }
  }
}
Report 'CARRIER_INSTANCES_NOT_REDUCIBLE' $unannotated
Report 'TRANSPORT_PHASE4_EVIDENCE' (Count-Pattern $Phase4Files $TransportPattern)
# Every library file belongs to exactly one transport budget. An unbucketed file
# is worse than a mis-bucketed one: nothing measures it, so it drifts unseen.
$Bucketed = @($Phase1Files + $Phase2ProbeFiles + $Phase4Files + $Phase2Files + $Phase3Files +
  $AnalysisFiles + @($ProfileModule) + @(Select-Files 'GameTheory/Languages'))
Report 'UNBUCKETED_FILES' (@($AllFiles | Where-Object { $Bucketed -notcontains $_ }).Count)
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

# The fixed-point dependency is not part of Mathlib and reaches the whole of
# convexity and topology when imported. Both facts are tolerable only while it
# stays behind one root, so the containment is measured rather than intended.
$analysisLeak = 0
foreach ($f in @($AllFiles | Where-Object { -not $_.StartsWith('GameTheory/Analysis') })) {
  foreach ($imp in Get-Imports $f) {
    if ($imp -match '^(GameTheory\.Analysis|FixedPointTheorems)') { $analysisLeak++ }
  }
}
Report 'ANALYSIS_IMPORTED_OUTSIDE_ROOT' $analysisLeak
# Inside the root only the module that applies the theorem may name the package.
$fixedPointNamers = 0
foreach ($f in $AnalysisFiles) {
  foreach ($imp in Get-Imports $f) { if ($imp -match '^FixedPointTheorems') { $fixedPointNamers++ } }
}
Report 'FIXED_POINT_IMPORTERS' $fixedPointNamers

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
Report 'NONBLANK_ANALYSIS' (Measure-Nonblank $AnalysisFiles)
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
  Report 'UNREACHABLE_PROBES_PASSED' $unreachable
  foreach ($r in $reachable) { Write-Output "REACHABLE_UNEXPECTED=$r" }
  # The analytic root is the one place the budget is spent, and a probe that
  # only ever asserts absence would not notice if it stopped being spent there.
  $reached = 0
  foreach ($constant in @('stdSimplex', 'Polynomial')) {
    if (-not (Test-Unreachable 'GameTheory.Analysis.Nash' $constant)) { $reached++ }
  }
  Report 'ANALYSIS_PROBES_REACHED' $reached
  Remove-Item $probeFile -ErrorAction SilentlyContinue
}

# --------------------------------------------------------------------------
# 6. Expected values
# --------------------------------------------------------------------------

if ($VerifyExpected) {
  $Expected = [ordered]@{
    FUNCTION_UPDATE_OUTSIDE_PROFILE = 0
    TRANSPORT_IN_PROFILE_MODULE = 1
    TRANSPORT_PHASE2_SOURCE = 1
    TRANSPORT_PHASE3_SOURCE = 0
    TRANSPORT_PHASE2_PROBE = 0
    # One, and it is the measurement rather than a defect: the indexed
    # round-trip statement cannot be written without a signature equality to
    # transport along, which is the evidence the recheck exists to produce.
    TRANSPORT_PHASE4_EVIDENCE = 1
    TRANSPORT_ANALYSIS_SOURCE = 0
    ANALYSIS_IMPORTED_OUTSIDE_ROOT = 0
    # One: the module that applies the fixed-point theorem, and nothing else.
    FIXED_POINT_IMPORTERS = 1
    UNBUCKETED_FILES = 0
    CARRIER_INSTANCES_NOT_REDUCIBLE = 0
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
  if (-not $SkipReachability) {
    $Expected['UNREACHABLE_PROBES_PASSED'] = 6
    $Expected['ANALYSIS_PROBES_REACHED'] = 2
  }
  foreach ($entry in $Expected.GetEnumerator()) {
    if ($Results[$entry.Key] -ne $entry.Value) {
      throw "$($entry.Key): expected $($entry.Value), got $($Results[$entry.Key])"
    }
  }
  Write-Output 'VERIFIED=1'
}
