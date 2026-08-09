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
$MathFiles = @(Get-ChildItem -Path (Join-Path $RepoRoot 'GameTheoryMath') -Filter '*.lean' -Recurse |
  ForEach-Object { $_.FullName.Substring($RepoRoot.Length + 1).Replace('\', '/') })
$MathFiles += 'GameTheoryMath.lean'
$TrustedFiles = @($AllFiles + $MathFiles)

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
$PostArchitectureFiles = @(Select-Files 'GameTheory/Experimental/PostArchitecture')
$Phase2Owned = @('GameTheory/Probability', 'GameTheory/Core', 'GameTheory/Finite',
  'GameTheory/Examples', 'GameTheory/Tests/Locality.lean', 'GameTheory.lean')
$Phase2Files = @($OutsideProfile | Where-Object {
  $candidate = $_
  ($Phase2Owned | Where-Object { $candidate.StartsWith($_) }).Count -gt 0 })
$Phase3Files = @($OutsideProfile | Where-Object {
  $_.StartsWith('GameTheory/Protocol') -or
    ($_.StartsWith('GameTheory/Tests') -and $_ -ne 'GameTheory/Tests/Locality.lean') })
$AnalysisFiles = @(Select-Files 'GameTheory/Analysis')
$RepeatedFiles = @(@(Select-Files 'GameTheory/Repeated') +
  @('GameTheory/Repeated.lean') | Sort-Object -Unique)
$EpistemicFiles = @(@(Select-Files 'GameTheory/Epistemic') +
  @('GameTheory/Epistemic.lean') | Sort-Object -Unique)
$EvolutionaryFiles = @(@(Select-Files 'GameTheory/Evolutionary') +
  @('GameTheory/Evolutionary.lean') | Sort-Object -Unique)
$CongestionFiles = @(Select-Files 'GameTheory/Congestion')
$MechanismFiles = @(Select-Files 'GameTheory/Mechanism')
$CooperativeFiles = @(@(Select-Files 'GameTheory/Cooperative') +
  @('GameTheory/Cooperative.lean') | Sort-Object -Unique)
$StochasticFiles = @(@(Select-Files 'GameTheory/Stochastic') +
  @('GameTheory/Stochastic.lean') | Sort-Object -Unique)
Report 'TRANSPORT_GAMETHEORYMATH_SOURCE' (Count-Pattern $MathFiles $TransportPattern)
Report 'TRANSPORT_ANALYSIS_SOURCE' (Count-Pattern $AnalysisFiles $TransportPattern)
Report 'TRANSPORT_REPEATED_SOURCE' (Count-Pattern $RepeatedFiles $TransportPattern)
Report 'TRANSPORT_EPISTEMIC_SOURCE' (Count-Pattern $EpistemicFiles $TransportPattern)
Report 'TRANSPORT_EVOLUTIONARY_SOURCE' `
  (Count-Pattern $EvolutionaryFiles $TransportPattern)
Report 'TRANSPORT_CONGESTION_SOURCE' `
  (Count-Pattern $CongestionFiles $TransportPattern)
Report 'TRANSPORT_MECHANISM_SOURCE' `
  (Count-Pattern $MechanismFiles $TransportPattern)
Report 'TRANSPORT_COOPERATIVE_SOURCE' `
  (Count-Pattern $CooperativeFiles $TransportPattern)
Report 'TRANSPORT_STOCHASTIC_SOURCE' `
  (Count-Pattern $StochasticFiles $TransportPattern)
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
Report 'TRANSPORT_POST_ARCHITECTURE' `
  (Count-Pattern $PostArchitectureFiles $TransportPattern)
# Every library file belongs to exactly one transport budget. An unbucketed file
# is worse than a mis-bucketed one: nothing measures it, so it drifts unseen.
$Bucketed = @($Phase1Files + $Phase2ProbeFiles + $Phase4Files + $PostArchitectureFiles +
  $Phase2Files + $Phase3Files + $AnalysisFiles + $RepeatedFiles + $EpistemicFiles +
  $EvolutionaryFiles + $CongestionFiles + $MechanismFiles + $StochasticFiles +
  $CooperativeFiles +
  @($ProfileModule) + @(Select-Files 'GameTheory/Languages'))
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
# Keep the representation escape hatch independently visible: a future
# broadening of the aggregate token check must not silently permit it.
Report 'TOPMF_OUTSIDE_FINDIST' `
  (Count-Pattern $NonRepresentation '(?<![A-Za-z0-9_])toPMF(?![A-Za-z0-9_])')

Report 'FINTYPE_OF_FINITE' (Count-Pattern $TrustedFiles 'Fintype\.ofFinite')
$AlgorithmFiles = @(
  'GameTheory/Finite/Algorithm.lean',
  'GameTheory/Mechanism/Knapsack/Aggregate.lean',
  'GameTheory/Mechanism/Knapsack/Algorithm.lean',
  'GameTheory/Mechanism/Knapsack/ApproximationAlgorithm.lean')
Report 'ALGORITHM_OPEN_CLASSICAL' `
  (Count-Pattern $AlgorithmFiles '(?<![A-Za-z0-9_])(open\s+Classical|classical|noncomputable)(?![A-Za-z0-9_])')
Report 'SORRY_OR_ADMIT' `
  (Count-Pattern $TrustedFiles '(?<![A-Za-z0-9_])(sorry|admit|native_decide)(?![A-Za-z0-9_])')
Report 'CUSTOM_AXIOM' (Count-Pattern $TrustedFiles '(?m)^\s*axiom\s')

# --------------------------------------------------------------------------
# 2. Authored-import audit (RFC 7.1, D12)
# --------------------------------------------------------------------------

$CoreFiles = @(Select-Files 'GameTheory/Core') + @('GameTheory/Core.lean') +
  @(Select-Files 'GameTheory/Probability')
$CoreForbidden = 'GameTheory\.Finite|GameTheory\.Languages|GameTheory\.Protocol|' +
  'GameTheory\.Frontier|' +
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
foreach ($algorithmFile in $AlgorithmFiles) {
  foreach ($imp in Get-Imports $algorithmFile) {
    if ($imp -match $AlgorithmForbidden) { $algBad++ }
  }
}
# EXP-055/D25 and EXP-056 permit precisely one authored GameTheory import into
# each executable knapsack solver: scalar-generic aggregation.  The
# aggregation leaf itself remains wholly game-free, so neither solver can
# acquire profile, real, or VCG semantics through a convenience import.
foreach ($algorithmFile in @(
    'GameTheory/Mechanism/Knapsack/Algorithm.lean',
    'GameTheory/Mechanism/Knapsack/ApproximationAlgorithm.lean')) {
  foreach ($imp in Get-Imports $algorithmFile) {
    if ($imp -match '^GameTheory\.' -and
        $imp -ne 'GameTheory.Mechanism.Knapsack.Aggregate') { $algBad++ }
  }
}
Report 'ALGORITHM_FORBIDDEN_IMPORTS' $algBad

$knapsackAggregateBad = 0
foreach ($imp in Get-Imports 'GameTheory/Mechanism/Knapsack/Aggregate.lean') {
  if ($imp -match '^GameTheory\.') { $knapsackAggregateBad++ }
}
Report 'KNAPSACK_AGGREGATE_GAMETHEORY_IMPORTS' $knapsackAggregateBad

# The real semantic layer consumes only scalar aggregation.  Execution,
# canonical mechanism/equilibrium, protocol, and analytic roots must remain
# outside its authored and transitive closure.
$knapsackBasicForbidden = 'GameTheory\.Mechanism\.Knapsack\.Algorithm|' +
  'GameTheory\.Mechanism\.VCG|GameTheory\.Core|GameTheory\.Protocol|' +
  'GameTheory\.Analysis|FixedPointTheorems'
$knapsackBasicBad = 0
foreach ($imp in Get-Imports 'GameTheory/Mechanism/Knapsack/Basic.lean') {
  if ($imp -match $knapsackBasicForbidden) { $knapsackBasicBad++ }
}
Report 'KNAPSACK_BASIC_FORBIDDEN_IMPORTS' $knapsackBasicBad

$sigBad = 0
foreach ($imp in Get-Imports 'GameTheory/Core/Signature.lean') {
  if ($imp -match 'GameTheory\.Probability|Mathlib\.Probability') { $sigBad++ }
}
Report 'SIGNATURE_PROBABILITY_IMPORTS' $sigBad

$RepeatedForbidden = 'GameTheory\.Languages|GameTheory\.Finite|GameTheory\.Examples|' +
  'GameTheory\.Tests|GameTheory\.Experimental|GameTheory\.Frontier|' +
  'GameTheory\.Challenges|GameTheory\.Analysis|FixedPointTheorems'
$repeatedBad = 0
foreach ($f in $RepeatedFiles) {
  foreach ($imp in Get-Imports $f) {
    if ($imp -match $RepeatedForbidden) { $repeatedBad++ }
  }
}
Report 'REPEATED_FORBIDDEN_IMPORTS' $repeatedBad

$EpistemicForbidden = 'GameTheory\.Core|GameTheory\.Protocol|GameTheory\.Finite|' +
  'GameTheory\.Languages|GameTheory\.Repeated|GameTheory\.Examples|' +
  'GameTheory\.Tests|GameTheory\.Experimental|GameTheory\.Analysis|' +
  'FixedPointTheorems'
$epistemicBad = 0
foreach ($f in $EpistemicFiles) {
  foreach ($imp in Get-Imports $f) {
    if ($imp -match $EpistemicForbidden) { $epistemicBad++ }
  }
}
Report 'EPISTEMIC_FORBIDDEN_IMPORTS' $epistemicBad

$EvolutionaryForbidden = 'GameTheory\.Protocol|GameTheory\.Finite|' +
  'GameTheory\.Languages|GameTheory\.Repeated|GameTheory\.Epistemic|' +
  'GameTheory\.Examples|GameTheory\.Tests|GameTheory\.Experimental|' +
  'GameTheory\.Analysis|FixedPointTheorems'
$evolutionaryBad = 0
foreach ($f in $EvolutionaryFiles) {
  foreach ($imp in Get-Imports $f) {
    if ($imp -match $EvolutionaryForbidden) { $evolutionaryBad++ }
  }
}
Report 'EVOLUTIONARY_FORBIDDEN_IMPORTS' $evolutionaryBad

$StochasticForbidden = 'GameTheory\.Languages|GameTheory\.Finite|' +
  'GameTheory\.Repeated|GameTheory\.Epistemic|GameTheory\.Evolutionary|' +
  'GameTheory\.Congestion|GameTheory\.Mechanism|GameTheory\.Examples|' +
  'GameTheory\.Tests|GameTheory\.Experimental|GameTheory\.Frontier|' +
  'GameTheory\.Challenges|GameTheory\.Analysis|FixedPointTheorems'
$stochasticBad = 0
foreach ($f in $StochasticFiles) {
  foreach ($imp in Get-Imports $f) {
    if ($imp -match $StochasticForbidden) { $stochasticBad++ }
  }
}
Report 'STOCHASTIC_FORBIDDEN_IMPORTS' $stochasticBad

$mathBad = 0
foreach ($f in $MathFiles) {
  foreach ($imp in Get-Imports $f) {
    if ($imp -match '^(GameTheory(\.|$)|FixedPointTheorems)') { $mathBad++ }
  }
}
Report 'GAMETHEORYMATH_FORBIDDEN_IMPORTS' $mathBad

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
Report 'NONBLANK_REPEATED' (Measure-Nonblank $RepeatedFiles)
Report 'NONBLANK_EPISTEMIC' (Measure-Nonblank $EpistemicFiles)
Report 'NONBLANK_EVOLUTIONARY' (Measure-Nonblank $EvolutionaryFiles)
Report 'NONBLANK_GAMETHEORYMATH' (Measure-Nonblank $MathFiles)
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
  # Delivery audits run in parallel during breadth recovery. A fixed filename
  # lets one process overwrite another process's import root between writing
  # and elaboration, producing spurious reachability failures.
  $probeFile = Join-Path ([IO.Path]::GetTempPath()) `
    ("gametheory-phase2-probe-$PID.lean")
  function Run-Probe([string] $Root, [string[]] $Constants) {
    $checks = $Constants | ForEach-Object { "#check @$_" }
    Set-Content -Path $probeFile -Value (@("import $Root") + $checks) -Encoding utf8
    return (& lake env lean $probeFile 2>&1 | Out-String)
  }
  function Is-Unreachable([string] $Output, [string] $Constant) {
    $escaped = [regex]::Escape($Constant)
    return ($Output -match
      "(?im)unknown (identifier|constant)[^\r\n]*$escaped(?![A-Za-z0-9_.])")
  }
  $unreachable = 0
  $reachable = @()
  foreach ($group in @(
      @('GameTheory.Finite.Algorithm',
        @('Real.instAdd', 'PMF', 'MeasureTheory.Measure', 'stdSimplex')),
      @('GameTheory.Core', @('stdSimplex', 'Polynomial')))) {
    $output = Run-Probe $group[0] $group[1]
    foreach ($constant in $group[1]) {
      if (Is-Unreachable $output $constant) { $unreachable++ }
      else { $reachable += "$($group[0]) reaches $constant" }
    }
  }
  Report 'UNREACHABLE_PROBES_PASSED' $unreachable
  foreach ($r in $reachable) { Write-Output "REACHABLE_UNEXPECTED=$r" }

  # EXP-054/D25 admits a second exact executable leaf for knapsack.  Its
  # explicit item order must not buy computability by importing either the
  # semantic game layer or real/analytic machinery.
  $knapsackAlgorithmBoundary = @(
    'Real.instAdd',
    'PMF',
    'MeasureTheory.Measure',
    'stdSimplex',
    'Polynomial',
    'GameTheory.GameForm',
    'GameTheory.Mechanism.Auction.auctionGame')
  $knapsackAlgorithmOutput =
    Run-Probe 'GameTheory.Mechanism.Knapsack.Algorithm' `
      $knapsackAlgorithmBoundary
  $knapsackAlgorithmRejected = 0
  foreach ($constant in $knapsackAlgorithmBoundary) {
    if (Is-Unreachable $knapsackAlgorithmOutput $constant) {
      $knapsackAlgorithmRejected++
    }
  }
  Report 'KNAPSACK_ALGORITHM_BOUNDARY_PROBES_REJECTED' `
    $knapsackAlgorithmRejected

  # EXP-056 adds a second executable knapsack leaf.  Its internally checked
  # density ordering may use list sorting, but cannot bring semantic game,
  # real, probability, or analytic machinery into the executable closure.
  $knapsackApproximationAlgorithmBoundary = @(
    'Real.instAdd',
    'PMF',
    'MeasureTheory.Measure',
    'stdSimplex',
    'Polynomial',
    'GameTheory.GameForm',
    'GameTheory.Mechanism.Auction.auctionGame')
  $knapsackApproximationAlgorithmOutput =
    Run-Probe 'GameTheory.Mechanism.Knapsack.ApproximationAlgorithm' `
      $knapsackApproximationAlgorithmBoundary
  $knapsackApproximationAlgorithmRejected = 0
  foreach ($constant in $knapsackApproximationAlgorithmBoundary) {
    if (Is-Unreachable $knapsackApproximationAlgorithmOutput $constant) {
      $knapsackApproximationAlgorithmRejected++
    }
  }
  Report 'KNAPSACK_APPROXIMATION_ALGORITHM_BOUNDARY_PROBES_REJECTED' `
    $knapsackApproximationAlgorithmRejected

  # The shared aggregation leaf may be scalar-generic, but it may not turn
  # into a back door from the executable solver to real-valued, game, VCG, or
  # analytic machinery.  The negative probe measures that transitive closure.
  $knapsackAggregateBoundary = @(
    'Real.instAdd',
    'PMF',
    'MeasureTheory.Measure',
    'stdSimplex',
    'Polynomial',
    'GameTheory.GameForm',
    'GameTheory.IsNash',
    'GameTheory.Mechanism.Auction.VCGSetup')
  $knapsackAggregateOutput =
    Run-Probe 'GameTheory.Mechanism.Knapsack.Aggregate' `
      $knapsackAggregateBoundary
  $knapsackAggregateRejected = 0
  foreach ($constant in $knapsackAggregateBoundary) {
    if (Is-Unreachable $knapsackAggregateOutput $constant) {
      $knapsackAggregateRejected++
    }
  }
  Report 'KNAPSACK_AGGREGATE_BOUNDARY_PROBES_REJECTED' `
    $knapsackAggregateRejected

  # Real finite-allocation semantics deliberately share scalar aggregation but
  # stop before execution, canonical VCG/Nash, Protocol, and Analysis.
  $knapsackBasicBoundary = @(
    'GameTheory.Mechanism.Knapsack.solveList',
    'GameTheory.Mechanism.Auction.VCGSetup',
    'GameTheory.IsNash',
    'GameTheory.Protocol.ExecutionProtocol',
    'GameTheory.Analysis.nash_exists',
    'stdSimplex',
    'Polynomial')
  $knapsackBasicOutput =
    Run-Probe 'GameTheory.Mechanism.Knapsack.Basic' $knapsackBasicBoundary
  $knapsackBasicRejected = 0
  foreach ($constant in $knapsackBasicBoundary) {
    if (Is-Unreachable $knapsackBasicOutput $constant) {
      $knapsackBasicRejected++
    }
  }
  Report 'KNAPSACK_BASIC_BOUNDARY_PROBES_REJECTED' $knapsackBasicRejected

  # The opt-in domain root must positively expose the executable and semantic
  # paths; otherwise negative containment could be passing because a leaf
  # quietly fell out of use.
  $knapsackInputs = @(
    'GameTheory.Mechanism.Knapsack.solveList',
    'GameTheory.Mechanism.Knapsack.solveList_feasible',
    'GameTheory.Mechanism.Knapsack.solveList_optimal',
    'GameTheory.Mechanism.Knapsack.approximate?_supported_feasible',
    'GameTheory.Mechanism.Knapsack.solveList_welfare_le_two_mul_approximate?')
  $knapsackOutput =
    Run-Probe 'GameTheory.Mechanism.Knapsack' $knapsackInputs
  $knapsackInputsReached = 0
  foreach ($constant in $knapsackInputs) {
    if (-not (Is-Unreachable $knapsackOutput $constant)) {
      $knapsackInputsReached++
    }
  }
  Report 'KNAPSACK_ROOT_INPUT_PROBES_REACHED' $knapsackInputsReached

  # The public mechanism root must make the canonical update, VCG
  # certificates, payment normalization, monotonicity, and ex-post Nash
  # theorem jointly reachable.  This is a positive integration probe, not an
  # import-surrogate: it fails if any layer stops being public.
  $knapsackMechanismInputs = @(
    'GameTheory.Mechanism.Knapsack.vcgSetup_efficient',
    'GameTheory.Mechanism.Knapsack.vcgSetup_offset_independent',
    'GameTheory.Mechanism.Knapsack.vcgPayment_update_zero',
    'GameTheory.Mechanism.Knapsack.allocationRule_monotone',
    'GameTheory.Mechanism.Knapsack.vcgSetup_truthful_isExPostNash',
    'GameTheory.Profile.update')
  $knapsackMechanismOutput =
    Run-Probe 'GameTheory.Mechanism.Knapsack' $knapsackMechanismInputs
  $knapsackMechanismInputsReached = 0
  foreach ($constant in $knapsackMechanismInputs) {
    if (-not (Is-Unreachable $knapsackMechanismOutput $constant)) {
      $knapsackMechanismInputsReached++
    }
  }
  Report 'KNAPSACK_MECHANISM_INPUT_PROBES_REACHED' `
    $knapsackMechanismInputsReached

  # Finite fair division consumes the sole combinatorial allocation and stays
  # independent of games, probability, Protocol, and measurable theory.
  $fairDivisionInputs = @(
    'GameTheory.Mechanism.Combinatorial.Allocation',
    'GameTheory.Mechanism.FairDivision.IsComplete',
    'GameTheory.Mechanism.FairDivision.roundRobinAllocation',
    'GameTheory.Mechanism.FairDivision.roundRobinAllocation_isEF1')
  $fairDivisionBoundary = @(
    'GameTheory.Probability.FinDist',
    'GameTheory.IsNash',
    'GameTheory.Protocol.ExecutionProtocol',
    'MeasureTheory.Measure')
  $fairDivisionOutput = Run-Probe 'GameTheory.Mechanism.FairDivision' `
    ($fairDivisionInputs + $fairDivisionBoundary)
  $fairDivisionInputsReached = 0
  foreach ($constant in $fairDivisionInputs) {
    if (-not (Is-Unreachable $fairDivisionOutput $constant)) {
      $fairDivisionInputsReached++
    }
  }
  Report 'FAIR_DIVISION_INPUT_PROBES_REACHED' $fairDivisionInputsReached
  $fairDivisionBoundaryRejected = 0
  foreach ($constant in $fairDivisionBoundary) {
    if (Is-Unreachable $fairDivisionOutput $constant) {
      $fairDivisionBoundaryRejected++
    }
  }
  Report 'FAIR_DIVISION_BOUNDARY_PROBES_REJECTED' `
    $fairDivisionBoundaryRejected

  # Stable matching is a native ordinal branch.  Its opt-in root must expose
  # the semantic market, deferred-acceptance stability, and perfectness while
  # remaining independent of games, probability, Protocol, and Analysis.
  $matchingInputs = @(
    'GameTheory.MatchingMarket',
    'GameTheory.MatchingMarket.deferredAcceptance_isStable',
    'GameTheory.MatchingMarket.exists_stable',
    'GameTheory.MatchingMarket.stable_matching_perfect',
    'GameTheory.MatchingMarket.exists_perfect_stable')
  $matchingBoundary = @(
    'GameTheory.IsNash',
    'GameTheory.Probability.FinDist',
    'GameTheory.Protocol.ExecutionProtocol',
    'MeasureTheory.Measure')
  $matchingOutput = Run-Probe 'GameTheory.Cooperative' `
    ($matchingInputs + $matchingBoundary)
  $matchingInputsReached = 0
  foreach ($constant in $matchingInputs) {
    if (-not (Is-Unreachable $matchingOutput $constant)) {
      $matchingInputsReached++
    }
  }
  Report 'MATCHING_INPUT_PROBES_REACHED' $matchingInputsReached
  $matchingBoundaryRejected = 0
  foreach ($constant in $matchingBoundary) {
    if (Is-Unreachable $matchingOutput $constant) {
      $matchingBoundaryRejected++
    }
  }
  Report 'MATCHING_BOUNDARY_PROBES_REJECTED' $matchingBoundaryRejected

  # The analytic root is the one place the budget is spent, and a probe that
  # only ever asserts absence would not notice if it stopped being spent there.
  $reached = 0
  $analysisOutput = Run-Probe 'GameTheory.Analysis.Nash' @('stdSimplex', 'Polynomial')
  foreach ($constant in @('stdSimplex', 'Polynomial')) {
    if (-not (Is-Unreachable $analysisOutput $constant)) { $reached++ }
  }
  Report 'ANALYSIS_PROBES_REACHED' $reached

  $repeatedAnalysisRejected = 0
  foreach ($root in @(
      'GameTheory.Repeated.Basic',
      'GameTheory.Repeated.Discounted',
      'GameTheory.Repeated')) {
    $output = Run-Probe $root @('stdSimplex', 'Polynomial')
    foreach ($constant in @('stdSimplex', 'Polynomial')) {
      if (Is-Unreachable $output $constant) {
        $repeatedAnalysisRejected++
      }
    }
  }
  Report 'REPEATED_ANALYSIS_PROBES_REJECTED' $repeatedAnalysisRejected

  $repeatedBridgeReached = 0
  $bridgeConstants = @(
      'GameTheory.UtilityGame.triggerRepeatedProfile',
      'GameTheory.UtilityGame.opponentMinmaxVector',
      'GameTheoryMath.SimplexApproximation.residualFloorCounts')
  $bridgeOutput = Run-Probe 'GameTheory.Analysis.Repeated' `
    ($bridgeConstants + @('GameTheory.Protocol.ExecutionProtocol'))
  foreach ($constant in $bridgeConstants) {
    if (-not (Is-Unreachable $bridgeOutput $constant)) {
      $repeatedBridgeReached++
    }
  }
  Report 'REPEATED_BRIDGE_PROBES_REACHED' $repeatedBridgeReached
  $bridgeProtocolRejected = Is-Unreachable $bridgeOutput `
    'GameTheory.Protocol.ExecutionProtocol'
  Report 'REPEATED_BRIDGE_PROTOCOL_REJECTED' ([int] $bridgeProtocolRejected)
  $mathOutput = Run-Probe 'GameTheoryMath' `
    @('GameTheory.UtilityGame')
  $mathGameRejected = Is-Unreachable $mathOutput 'GameTheory.UtilityGame'
  Report 'GAMETHEORYMATH_GAME_REJECTED' ([int] $mathGameRejected)

  # EXP-049/D21 keeps the exponential-potential proof independent of both
  # game semantics and the canonical law representation. Core owns only the
  # finite averaging bridge; the opt-in analytic bridge is the first root
  # allowed to reach all three inputs at once.
  $mathLearningBoundary = @(
    'GameTheory.UtilityGame',
    'GameTheory.Probability.FinDist')
  $mathLearningOutput =
    Run-Probe 'GameTheoryMath.OnlineLearning' $mathLearningBoundary
  $mathLearningBoundaryRejected = 0
  foreach ($constant in $mathLearningBoundary) {
    if (Is-Unreachable $mathLearningOutput $constant) {
      $mathLearningBoundaryRejected++
    }
  }
  Report 'MATH_LEARNING_BOUNDARY_PROBES_REJECTED' `
    $mathLearningBoundaryRejected

  $coreLearningBoundary = @(
    'GameTheoryMath.OnlineLearning.externalRegret_le',
    'GameTheory.Probability.OnlineLearning.multiplicativeWeights')
  $coreLearningOutput =
    Run-Probe 'GameTheory.Core.Learning' $coreLearningBoundary
  $coreLearningBoundaryRejected = 0
  foreach ($constant in $coreLearningBoundary) {
    if (Is-Unreachable $coreLearningOutput $constant) {
      $coreLearningBoundaryRejected++
    }
  }
  Report 'CORE_LEARNING_MW_PROBES_REJECTED' `
    $coreLearningBoundaryRejected

  # The fictitious-play trajectory remains a topology-free Core leaf.  Its
  # successor law and canonical best-response recurrence must be positively
  # reachable there, while the shared convergence vocabulary and Protocol
  # stay above or beside it.
  $coreFictitiousInputs = @(
    'GameTheory.UtilityGame.empiricalMarginal_succ_expect',
    'GameTheory.UtilityGame.IsFictitiousPlay.isBestResponse')
  $coreFictitiousBoundary = @(
    'GameTheory.Analysis.FinDistConvergesPointwise',
    'GameTheory.Protocol.ExecutionProtocol')
  $coreFictitiousOutput = Run-Probe 'GameTheory.Core.FictitiousPlay' `
    ($coreFictitiousInputs + $coreFictitiousBoundary)
  $coreFictitiousInputsReached = 0
  foreach ($constant in $coreFictitiousInputs) {
    if (-not (Is-Unreachable $coreFictitiousOutput $constant)) {
      $coreFictitiousInputsReached++
    }
  }
  Report 'CORE_FICTITIOUS_INPUT_PROBES_REACHED' `
    $coreFictitiousInputsReached
  $coreFictitiousBoundaryRejected = 0
  foreach ($constant in $coreFictitiousBoundary) {
    if (Is-Unreachable $coreFictitiousOutput $constant) {
      $coreFictitiousBoundaryRejected++
    }
  }
  Report 'CORE_FICTITIOUS_BOUNDARY_PROBES_REJECTED' `
    $coreFictitiousBoundaryRejected

  $coreMixedPotentialInputs = @(
    'GameTheory.UtilityGame.mixedPotential_update',
    'GameTheory.UtilityGame.IsExactPotential.mixed')
  $coreMixedPotentialBoundary = @(
    'GameTheory.Analysis.FinDistConvergesPointwise',
    'GameTheory.Protocol.ExecutionProtocol')
  $coreMixedPotentialOutput = Run-Probe 'GameTheory.Core.MixedPotential' `
    ($coreMixedPotentialInputs + $coreMixedPotentialBoundary)
  $coreMixedPotentialInputsReached = 0
  foreach ($constant in $coreMixedPotentialInputs) {
    if (-not (Is-Unreachable $coreMixedPotentialOutput $constant)) {
      $coreMixedPotentialInputsReached++
    }
  }
  Report 'CORE_MIXED_POTENTIAL_INPUT_PROBES_REACHED' `
    $coreMixedPotentialInputsReached
  $coreMixedPotentialBoundaryRejected = 0
  foreach ($constant in $coreMixedPotentialBoundary) {
    if (Is-Unreachable $coreMixedPotentialOutput $constant) {
      $coreMixedPotentialBoundaryRejected++
    }
  }
  Report 'CORE_MIXED_POTENTIAL_BOUNDARY_PROBES_REJECTED' `
    $coreMixedPotentialBoundaryRejected

  $coreMixedImprovementInputs = @(
    'GameTheory.UtilityGame.mixedImprovement',
    'GameTheory.UtilityGame.isεNash_of_mixedImprovement_le')
  $coreMixedImprovementBoundary = @(
    'GameTheory.UtilityGame.eventually_isεNash_of_mixedImprovement_tendsto_zero',
    'GameTheory.Protocol.ExecutionProtocol')
  $coreMixedImprovementOutput = Run-Probe 'GameTheory.Core.MixedImprovement' `
    ($coreMixedImprovementInputs + $coreMixedImprovementBoundary)
  $coreMixedImprovementInputsReached = 0
  foreach ($constant in $coreMixedImprovementInputs) {
    if (-not (Is-Unreachable $coreMixedImprovementOutput $constant)) {
      $coreMixedImprovementInputsReached++
    }
  }
  Report 'CORE_MIXED_IMPROVEMENT_INPUT_PROBES_REACHED' `
    $coreMixedImprovementInputsReached
  $coreMixedImprovementBoundaryRejected = 0
  foreach ($constant in $coreMixedImprovementBoundary) {
    if (Is-Unreachable $coreMixedImprovementOutput $constant) {
      $coreMixedImprovementBoundaryRejected++
    }
  }
  Report 'CORE_MIXED_IMPROVEMENT_BOUNDARY_PROBES_REJECTED' `
    $coreMixedImprovementBoundaryRejected

  $coreFictitiousPotentialInputs = @(
    'GameTheory.UtilityGame.expectedUtility_belief_update_empiricalMarginal_succ_sub',
    'GameTheory.UtilityGame.IsFictitiousPlay.mixedImprovement_le_weightedPlayedGain',
    'GameTheory.UtilityGame.IsExactPotential.mixedPotential_belief_update_empiricalMarginal_succ_sub',
    'GameTheory.UtilityGame.mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le',
    'GameTheory.UtilityGame.IsExactPotential.mixedPotential_empiricalBelief_succ_sub_ge')
  $coreFictitiousPotentialBoundary = @(
    'GameTheory.UtilityGame.eventually_isεNash_of_mixedImprovement_tendsto_zero',
    'GameTheory.Protocol.ExecutionProtocol')
  $coreFictitiousPotentialOutput =
    Run-Probe 'GameTheory.Core.FictitiousPlayPotential' `
      ($coreFictitiousPotentialInputs + $coreFictitiousPotentialBoundary)
  $coreFictitiousPotentialInputsReached = 0
  foreach ($constant in $coreFictitiousPotentialInputs) {
    if (-not (Is-Unreachable $coreFictitiousPotentialOutput $constant)) {
      $coreFictitiousPotentialInputsReached++
    }
  }
  Report 'CORE_FICTITIOUS_POTENTIAL_INPUT_PROBES_REACHED' `
    $coreFictitiousPotentialInputsReached
  $coreFictitiousPotentialBoundaryRejected = 0
  foreach ($constant in $coreFictitiousPotentialBoundary) {
    if (Is-Unreachable $coreFictitiousPotentialOutput $constant) {
      $coreFictitiousPotentialBoundaryRejected++
    }
  }
  Report 'CORE_FICTITIOUS_POTENTIAL_BOUNDARY_PROBES_REJECTED' `
    $coreFictitiousPotentialBoundaryRejected

  $harmonicSequenceInputs = @(
    'GameTheoryMath.frequently_lt_of_summable_one_div_mul',
    'GameTheoryMath.tendsto_zero_of_summable_one_div_mul_of_succ_abs_sub_le')
  $harmonicSequenceBoundary = @(
    'GameTheory.UtilityGame',
    'GameTheory.Probability.FinDist')
  $harmonicSequenceOutput = Run-Probe 'GameTheoryMath.HarmonicSequence' `
    ($harmonicSequenceInputs + $harmonicSequenceBoundary)
  $harmonicSequenceInputsReached = 0
  foreach ($constant in $harmonicSequenceInputs) {
    if (-not (Is-Unreachable $harmonicSequenceOutput $constant)) {
      $harmonicSequenceInputsReached++
    }
  }
  Report 'HARMONIC_SEQUENCE_INPUT_PROBES_REACHED' `
    $harmonicSequenceInputsReached
  $harmonicSequenceBoundaryRejected = 0
  foreach ($constant in $harmonicSequenceBoundary) {
    if (Is-Unreachable $harmonicSequenceOutput $constant) {
      $harmonicSequenceBoundaryRejected++
    }
  }
  Report 'HARMONIC_SEQUENCE_BOUNDARY_PROBES_REJECTED' `
    $harmonicSequenceBoundaryRejected

  # Approachability's reusable B-set and orthant geometry must remain
  # independent of both game semantics and the canonical law adapter.
  $mathApproachabilityInputs = @(
    'GameTheoryMath.Approachability.sq_infDist_avg_le',
    'GameTheoryMath.Approachability.orthantProj',
    'GameTheoryMath.Approachability.infDist_eq_norm_sub_orthantProj')
  $mathApproachabilityBoundary = @(
    'GameTheory.UtilityGame',
    'GameTheory.Probability.FinDist')
  $mathApproachabilityOutput =
    Run-Probe 'GameTheoryMath.ApproachabilityRegret' `
      ($mathApproachabilityInputs + $mathApproachabilityBoundary)
  $mathApproachabilityInputsReached = 0
  foreach ($constant in $mathApproachabilityInputs) {
    if (-not (Is-Unreachable $mathApproachabilityOutput $constant)) {
      $mathApproachabilityInputsReached++
    }
  }
  Report 'MATH_APPROACHABILITY_INPUT_PROBES_REACHED' `
    $mathApproachabilityInputsReached
  $mathApproachabilityBoundaryRejected = 0
  foreach ($constant in $mathApproachabilityBoundary) {
    if (Is-Unreachable $mathApproachabilityOutput $constant) {
      $mathApproachabilityBoundaryRejected++
    }
  }
  Report 'MATH_APPROACHABILITY_BOUNDARY_PROBES_REJECTED' `
    $mathApproachabilityBoundaryRejected

  # The opt-in analytic leaf is the first layer allowed to combine the
  # canonical finite law with the geometric steering theorem.
  $approachabilityAnalysisInputs = @(
    'GameTheory.Analysis.Approachability.regretPayoff',
    'GameTheory.Analysis.Approachability.regretMatch',
    'GameTheory.Analysis.Approachability.regretMatch_steering',
    'GameTheory.Analysis.Approachability.regretMatch_approaches')
  $approachabilityAnalysisBoundary = @(
    'GameTheory.Protocol.ExecutionProtocol',
    'kakutani_fixed_point')
  $approachabilityAnalysisOutput =
    Run-Probe 'GameTheory.Analysis.Approachability' `
      ($approachabilityAnalysisInputs + $approachabilityAnalysisBoundary)
  $approachabilityAnalysisInputsReached = 0
  foreach ($constant in $approachabilityAnalysisInputs) {
    if (-not (Is-Unreachable $approachabilityAnalysisOutput $constant)) {
      $approachabilityAnalysisInputsReached++
    }
  }
  Report 'APPROACHABILITY_ANALYSIS_INPUT_PROBES_REACHED' `
    $approachabilityAnalysisInputsReached
  $approachabilityAnalysisBoundaryRejected = 0
  foreach ($constant in $approachabilityAnalysisBoundary) {
    if (Is-Unreachable $approachabilityAnalysisOutput $constant) {
      $approachabilityAnalysisBoundaryRejected++
    }
  }
  Report 'APPROACHABILITY_ANALYSIS_BOUNDARY_PROBES_REJECTED' `
    $approachabilityAnalysisBoundaryRejected

  $fictitiousPotentialAnalysisInputs = @(
    'GameTheoryMath.tendsto_zero_of_summable_one_div_mul_of_succ_abs_sub_le',
    'GameTheory.UtilityGame.IsExactPotential.summable_harmonic_aggregatePlayedGain',
    'GameTheory.UtilityGame.IsExactPotential.mixedImprovement_empiricalBelief_tendsto_zero',
    'GameTheory.UtilityGame.IsExactPotential.eventually_isεNash_of_isFictitiousPlay')
  $fictitiousPotentialAnalysisBoundary = @(
    'GameTheory.Protocol.ExecutionProtocol',
    'kakutani_fixed_point')
  $fictitiousPotentialAnalysisOutput =
    Run-Probe 'GameTheory.Analysis.FictitiousPlayPotential' `
      ($fictitiousPotentialAnalysisInputs + $fictitiousPotentialAnalysisBoundary)
  $fictitiousPotentialAnalysisInputsReached = 0
  foreach ($constant in $fictitiousPotentialAnalysisInputs) {
    if (-not (Is-Unreachable $fictitiousPotentialAnalysisOutput $constant)) {
      $fictitiousPotentialAnalysisInputsReached++
    }
  }
  Report 'FICTITIOUS_POTENTIAL_ANALYSIS_INPUT_PROBES_REACHED' `
    $fictitiousPotentialAnalysisInputsReached
  $fictitiousPotentialAnalysisBoundaryRejected = 0
  foreach ($constant in $fictitiousPotentialAnalysisBoundary) {
    if (Is-Unreachable $fictitiousPotentialAnalysisOutput $constant) {
      $fictitiousPotentialAnalysisBoundaryRejected++
    }
  }
  Report 'FICTITIOUS_POTENTIAL_ANALYSIS_BOUNDARY_PROBES_REJECTED' `
    $fictitiousPotentialAnalysisBoundaryRejected

  $learningBridgeInputs = @(
    'GameTheory.UtilityGame.selfPlay_timeAverage_isεCoarseCorrelatedEq',
    'GameTheoryMath.OnlineLearning.externalRegret_le',
    'GameTheory.Probability.OnlineLearning.multiplicativeWeights',
    'GameTheory.UtilityGame.mwSelfPlay_timeAverage_isεCoarseCorrelatedEq',
    'GameTheory.Analysis.FinDistConvergesPointwise.expect',
    'GameTheory.UtilityGame.IsFictitiousPlay.limit_isNash',
    'GameTheory.UtilityGame.eventually_isεNash_of_mixedImprovement_tendsto_zero',
    'GameTheory.UtilityGame.IsExactPotential.eventually_isεNash_of_isFictitiousPlay',
    'GameTheory.Analysis.Approachability.regretMatch_approaches')
  $learningBridgeBoundary = @(
    'GameTheory.Protocol.ExecutionProtocol',
    'kakutani_fixed_point')
  $learningBridgeOutput = Run-Probe 'GameTheory.Analysis.Learning' `
    ($learningBridgeInputs + $learningBridgeBoundary)
  $learningBridgeInputsReached = 0
  foreach ($constant in $learningBridgeInputs) {
    if (-not (Is-Unreachable $learningBridgeOutput $constant)) {
      $learningBridgeInputsReached++
    }
  }
  Report 'LEARNING_BRIDGE_INPUT_PROBES_REACHED' `
    $learningBridgeInputsReached
  $learningBridgeBoundaryRejected = 0
  foreach ($constant in $learningBridgeBoundary) {
    if (Is-Unreachable $learningBridgeOutput $constant) {
      $learningBridgeBoundaryRejected++
    }
  }
  Report 'LEARNING_BRIDGE_BOUNDARY_PROBES_REJECTED' `
    $learningBridgeBoundaryRejected

  # Protocol's analytic consumer must use the same generic finite-law
  # convergence leaf without acquiring the learning theorem family.
  $protocolFiniteLawInputs = @(
    'GameTheory.Analysis.FinDistConvergesPointwise',
    'GameTheory.Protocol.InformationModel.BehavioralAssessmentConvergesPointwise')
  $protocolFiniteLawBoundary = @(
    'GameTheory.UtilityGame.IsFictitiousPlay.limit_isNash')
  $protocolFiniteLawOutput =
    Run-Probe 'GameTheory.Analysis.Protocol.Sequential' `
      ($protocolFiniteLawInputs + $protocolFiniteLawBoundary)
  $protocolFiniteLawInputsReached = 0
  foreach ($constant in $protocolFiniteLawInputs) {
    if (-not (Is-Unreachable $protocolFiniteLawOutput $constant)) {
      $protocolFiniteLawInputsReached++
    }
  }
  Report 'PROTOCOL_FINITE_LAW_INPUT_PROBES_REACHED' `
    $protocolFiniteLawInputsReached
  $protocolFiniteLawBoundaryRejected = 0
  foreach ($constant in $protocolFiniteLawBoundary) {
    if (Is-Unreachable $protocolFiniteLawOutput $constant) {
      $protocolFiniteLawBoundaryRejected++
    }
  }
  Report 'PROTOCOL_FINITE_LAW_BOUNDARY_PROBES_REJECTED' `
    $protocolFiniteLawBoundaryRejected

  # D16's epistemic branch consumes the canonical finite law but remains
  # independent of static, sequential, and analytic game semantics.
  $epistemicInputs = @(
    'GameTheory.Probability.FinDist',
    'GameTheory.Epistemic.InfoPartition',
    'GameTheory.Epistemic.aumann_full_agreement',
    'GameTheory.Epistemic.CommonKnowledgeAt.idem',
    'GameTheory.Epistemic.CommonKnowledgeAt.commonPBeliefAt',
    'GameTheory.Epistemic.commonPBelief_posterior_reports_close')
  $epistemicBoundary = @(
    'GameTheory.IsNash',
    'GameTheory.Protocol.InformationModel',
    'GameTheory.Analysis.FinDistConvergesPointwise',
    'stdSimplex',
    'Polynomial')
  $epistemicOutput =
    Run-Probe 'GameTheory.Epistemic' ($epistemicInputs + $epistemicBoundary)
  $epistemicInputsReached = 0
  foreach ($constant in $epistemicInputs) {
    if (-not (Is-Unreachable $epistemicOutput $constant)) {
      $epistemicInputsReached++
    }
  }
  Report 'EPISTEMIC_INPUT_PROBES_REACHED' $epistemicInputsReached
  $epistemicBoundaryRejected = 0
  foreach ($constant in $epistemicBoundary) {
    if (Is-Unreachable $epistemicOutput $constant) {
      $epistemicBoundaryRejected++
    }
  }
  Report 'EPISTEMIC_BOUNDARY_PROBES_REJECTED' $epistemicBoundaryRejected

  # D20 integrates Bayesian and epistemic semantics only in a concrete
  # Examples bridge. Each input root must remain blind to the other.
  $electronicMailInputs = @(
    'GameTheory.BayesianGame',
    'GameTheory.Epistemic.InfoPartition',
    'GameTheory.Examples.ElectronicMail.game',
    'GameTheory.Examples.ElectronicMail.not_commonPBeliefAt_attackStateEvent_bothConfirmed_of_half_lt')
  $electronicMailBoundary = @(
    'GameTheory.Protocol.ExecutionProtocol',
    'GameTheory.Analysis.nash_exists',
    'stdSimplex',
    'Polynomial')
  $electronicMailOutput = Run-Probe 'GameTheory.Examples.ElectronicMail' `
    ($electronicMailInputs + $electronicMailBoundary)
  $electronicMailInputsReached = 0
  foreach ($constant in $electronicMailInputs) {
    if (-not (Is-Unreachable $electronicMailOutput $constant)) {
      $electronicMailInputsReached++
    }
  }
  Report 'ELECTRONIC_MAIL_INPUT_PROBES_REACHED' $electronicMailInputsReached
  $electronicMailBoundaryRejected = 0
  foreach ($constant in $electronicMailBoundary) {
    if (Is-Unreachable $electronicMailOutput $constant) {
      $electronicMailBoundaryRejected++
    }
  }
  Report 'ELECTRONIC_MAIL_BOUNDARY_PROBES_REJECTED' `
    $electronicMailBoundaryRejected
  $bayesianEpistemicOutput = Run-Probe 'GameTheory.Core.BayesianEquilibrium' `
    @('GameTheory.Epistemic.InfoPartition')
  Report 'BAYESIAN_EPISTEMIC_PROBE_REJECTED' `
    ([int] (Is-Unreachable $bayesianEpistemicOutput `
      'GameTheory.Epistemic.InfoPartition'))
  $epistemicBayesianOutput = Run-Probe 'GameTheory.Epistemic' `
    @('GameTheory.BayesianGame')
  Report 'EPISTEMIC_BAYESIAN_PROBE_REJECTED' `
    ([int] (Is-Unreachable $epistemicBayesianOutput `
      'GameTheory.BayesianGame'))

  # D17 keeps the payoff-kernel definitions independent of game semantics,
  # then exposes one deliberate bridge into the canonical static concepts.
  $evolutionaryBasicInputs = @(
    'GameTheory.Evolutionary.IsESS',
    'GameTheory.Evolutionary.IsNSS')
  $evolutionaryBasicBoundary = @(
    'GameTheory.GameForm',
    'GameTheory.IsNash',
    'GameTheory.Protocol.ExecutionProtocol',
    'GameTheory.Analysis.nash_exists',
    'stdSimplex',
    'Polynomial')
  $evolutionaryBasicOutput = Run-Probe 'GameTheory.Evolutionary.Basic' `
    ($evolutionaryBasicInputs + $evolutionaryBasicBoundary)
  $evolutionaryBasicInputsReached = 0
  foreach ($constant in $evolutionaryBasicInputs) {
    if (-not (Is-Unreachable $evolutionaryBasicOutput $constant)) {
      $evolutionaryBasicInputsReached++
    }
  }
  Report 'EVOLUTIONARY_BASIC_INPUT_PROBES_REACHED' `
    $evolutionaryBasicInputsReached
  $evolutionaryBasicBoundaryRejected = 0
  foreach ($constant in $evolutionaryBasicBoundary) {
    if (Is-Unreachable $evolutionaryBasicOutput $constant) {
      $evolutionaryBasicBoundaryRejected++
    }
  }
  Report 'EVOLUTIONARY_BASIC_BOUNDARY_PROBES_REJECTED' `
    $evolutionaryBasicBoundaryRejected

  $evolutionaryBridgeInputs = @(
    'GameTheory.Evolutionary.IsESS',
    'GameTheory.IsNash',
    'GameTheory.Evolutionary.IsESS.isNash_symmetric')
  $evolutionaryBridgeBoundary = @(
    'GameTheory.Protocol.ExecutionProtocol',
    'GameTheory.Analysis.nash_exists',
    'stdSimplex',
    'Polynomial')
  $evolutionaryBridgeOutput = Run-Probe 'GameTheory.Evolutionary' `
    ($evolutionaryBridgeInputs + $evolutionaryBridgeBoundary)
  $evolutionaryBridgeInputsReached = 0
  foreach ($constant in $evolutionaryBridgeInputs) {
    if (-not (Is-Unreachable $evolutionaryBridgeOutput $constant)) {
      $evolutionaryBridgeInputsReached++
    }
  }
  Report 'EVOLUTIONARY_BRIDGE_INPUT_PROBES_REACHED' `
    $evolutionaryBridgeInputsReached
  $evolutionaryBridgeBoundaryRejected = 0
  foreach ($constant in $evolutionaryBridgeBoundary) {
    if (Is-Unreachable $evolutionaryBridgeOutput $constant) {
      $evolutionaryBridgeBoundaryRejected++
    }
  }
  Report 'EVOLUTIONARY_BRIDGE_BOUNDARY_PROBES_REJECTED' `
    $evolutionaryBridgeBoundaryRejected

  $coreEvolutionaryRejected = 0
  $coreEvolutionaryConstants = @(
    'GameTheory.Evolutionary.IsESS',
    'GameTheory.Evolutionary.IsESS.isNash_symmetric')
  $coreEvolutionaryOutput =
    Run-Probe 'GameTheory.Core' $coreEvolutionaryConstants
  foreach ($constant in $coreEvolutionaryConstants) {
    if (Is-Unreachable $coreEvolutionaryOutput $constant) {
      $coreEvolutionaryRejected++
    }
  }
  Report 'CORE_EVOLUTIONARY_PROBES_REJECTED' $coreEvolutionaryRejected

  # D18 makes observable one-stage cheap talk a static Core construction.
  # The public root must expose the extension and its ordinary Nash theorem
  # without also acquiring Protocol timing or analytic existence machinery.
  $cheapTalkInputs = @(
    'GameTheory.GameForm.CheapTalkExtension',
    'GameTheory.GameForm.CheapTalkExtension.babbling_isNash')
  $cheapTalkBoundary = @(
    'GameTheory.Protocol.ExecutionProtocol',
    'GameTheory.Analysis.nash_exists',
    'stdSimplex',
    'Polynomial')
  $cheapTalkOutput =
    Run-Probe 'GameTheory.Core' ($cheapTalkInputs + $cheapTalkBoundary)
  $cheapTalkInputsReached = 0
  foreach ($constant in $cheapTalkInputs) {
    if (-not (Is-Unreachable $cheapTalkOutput $constant)) {
      $cheapTalkInputsReached++
    }
  }
  Report 'CHEAP_TALK_INPUT_PROBES_REACHED' $cheapTalkInputsReached
  $cheapTalkBoundaryRejected = 0
  foreach ($constant in $cheapTalkBoundary) {
    if (Is-Unreachable $cheapTalkOutput $constant) {
      $cheapTalkBoundaryRejected++
    }
  }
  Report 'CHEAP_TALK_BOUNDARY_PROBES_REJECTED' $cheapTalkBoundaryRejected

  # D19 adds a separate static bridge from mixed cheap talk to correlation.
  # It must be publicly reachable without changing the D18 boundary.
  $cheapTalkRandomizationInputs = @(
    'GameTheory.GameForm.CheapTalkExtension.mixedActionLaw',
    'GameTheory.GameForm.CheapTalkExtension.mixedNash_mixedActionLaw_isCorrelatedEq')
  $cheapTalkRandomizationBoundary = @(
    'GameTheory.Protocol.ExecutionProtocol',
    'GameTheory.Analysis.nash_exists',
    'stdSimplex',
    'Polynomial')
  $cheapTalkRandomizationOutput =
    Run-Probe 'GameTheory.Core' `
      ($cheapTalkRandomizationInputs + $cheapTalkRandomizationBoundary)
  $cheapTalkRandomizationInputsReached = 0
  foreach ($constant in $cheapTalkRandomizationInputs) {
    if (-not (Is-Unreachable $cheapTalkRandomizationOutput $constant)) {
      $cheapTalkRandomizationInputsReached++
    }
  }
  Report 'CHEAP_TALK_RANDOMIZATION_INPUT_PROBES_REACHED' `
    $cheapTalkRandomizationInputsReached
  $cheapTalkRandomizationBoundaryRejected = 0
  foreach ($constant in $cheapTalkRandomizationBoundary) {
    if (Is-Unreachable $cheapTalkRandomizationOutput $constant) {
      $cheapTalkRandomizationBoundaryRejected++
    }
  }
  Report 'CHEAP_TALK_RANDOMIZATION_BOUNDARY_PROBES_REJECTED' `
    $cheapTalkRandomizationBoundaryRejected

  # D8 exposes only concrete equivalences. The probability laws remain
  # game-free, while the Core root deliberately reaches the preservation
  # theorems that consume them.
  $transformInputs = @(
    'GameTheory.GameSignature.reindexPlayers',
    'GameTheory.Profile.relabelStrategies',
    'GameTheory.isNash_reindexPlayers',
    'GameTheory.isNash_relabelStrategies',
    'GameTheory.isCorrelatedEq_relabelStrategies',
    'GameTheory.mixed_reindexPlayers_play')
  $transformOutput = Run-Probe 'GameTheory.Core' $transformInputs
  $transformInputsReached = 0
  foreach ($constant in $transformInputs) {
    if (-not (Is-Unreachable $transformOutput $constant)) {
      $transformInputsReached++
    }
  }
  Report 'TRANSFORM_INPUT_PROBES_REACHED' $transformInputsReached

  $probabilityReindexInputs = @(
    'GameTheory.Probability.FinDist.pi_reindex',
    'GameTheory.Probability.FinDist.pi_unreindex')
  $probabilityReindexBoundary = @(
    'GameTheory.GameForm',
    'GameTheory.IsNash')
  $probabilityReindexOutput = Run-Probe 'GameTheory.Probability.FinDist' `
    ($probabilityReindexInputs + $probabilityReindexBoundary)
  $probabilityReindexInputsReached = 0
  foreach ($constant in $probabilityReindexInputs) {
    if (-not (Is-Unreachable $probabilityReindexOutput $constant)) {
      $probabilityReindexInputsReached++
    }
  }
  Report 'PROBABILITY_REINDEX_INPUT_PROBES_REACHED' `
    $probabilityReindexInputsReached
  $probabilityReindexBoundaryRejected = 0
  foreach ($constant in $probabilityReindexBoundary) {
    if (Is-Unreachable $probabilityReindexOutput $constant) {
      $probabilityReindexBoundaryRejected++
    }
  }
  Report 'PROBABILITY_REINDEX_BOUNDARY_PROBES_REJECTED' `
    $probabilityReindexBoundaryRejected

  # EXP-050/D22 and EXP-051/D23 keep the stable stochastic root
  # analysis-light. It must positively reach the four semantic layers,
  # canonical approximate Nash, and the structural zero-sum surface, while
  # rejecting Repeated and both analytic fixed-point routes.
  $stochasticInputs = @(
    'GameTheory.Stochastic.Game',
    'GameTheory.Stochastic.Game.IsZeroSum',
    'GameTheory.Stochastic.Game.pairAction',
    'GameTheory.Stochastic.Game.perfectMonitoring',
    'GameTheory.Stochastic.Game.horizonGame_expectedUtility',
    'GameTheory.Stochastic.Game.IsUniformEquilibriumPayoff',
    'GameTheory.IsεNash')
  $stochasticBoundary = @(
    'GameTheory.UtilityGame.repeatedForm',
    'GameTheory.Stochastic.Game.shapleyOperator',
    'kakutani_fixed_point')
  $stochasticOutput = Run-Probe 'GameTheory.Stochastic' `
    ($stochasticInputs + $stochasticBoundary)
  $stochasticInputsReached = 0
  foreach ($constant in $stochasticInputs) {
    if (-not (Is-Unreachable $stochasticOutput $constant)) {
      $stochasticInputsReached++
    }
  }
  Report 'STOCHASTIC_INPUT_PROBES_REACHED' $stochasticInputsReached
  $stochasticBoundaryRejected = 0
  foreach ($constant in $stochasticBoundary) {
    if (Is-Unreachable $stochasticOutput $constant) {
      $stochasticBoundaryRejected++
    }
  }
  Report 'STOCHASTIC_BOUNDARY_PROBES_REJECTED' $stochasticBoundaryRejected

  # D23's one-way bridge must consume canonical matrix values, FinDist, the
  # stable zero-sum surface, and the already-admitted D12 Kakutani path behind
  # finite minimax. Protocol and Repeated remain unrelated and unreachable.
  $stochasticAnalysisInputs = @(
    'GameTheory.Stochastic.Game.shapleyOperator',
    'GameTheory.Stochastic.Game.contractingWith_shapleyOperator',
    'GameTheory.Stochastic.Game.stationarySaddleProfile_isSaddlePoint',
    'GameTheory.Stochastic.Game.auxiliaryUtility_one_eq',
    'GameTheory.MatrixGame.abs_value_sub_le_of_entrywise_abs_le',
    'GameTheory.Stochastic.Game.IsZeroSum',
    'GameTheory.Probability.FinDist',
    'kakutani_fixed_point')
  $stochasticAnalysisBoundary = @(
    'GameTheory.Protocol.ExecutionProtocol',
    'GameTheory.UtilityGame.repeatedForm')
  $stochasticAnalysisOutput = Run-Probe 'GameTheory.Analysis.Stochastic' `
    ($stochasticAnalysisInputs + $stochasticAnalysisBoundary)
  $stochasticAnalysisInputsReached = 0
  foreach ($constant in $stochasticAnalysisInputs) {
    if (-not (Is-Unreachable $stochasticAnalysisOutput $constant)) {
      $stochasticAnalysisInputsReached++
    }
  }
  Report 'STOCHASTIC_ANALYSIS_INPUT_PROBES_REACHED' `
    $stochasticAnalysisInputsReached
  $stochasticAnalysisBoundaryRejected = 0
  foreach ($constant in $stochasticAnalysisBoundary) {
    if (Is-Unreachable $stochasticAnalysisOutput $constant) {
      $stochasticAnalysisBoundaryRejected++
    }
  }
  Report 'STOCHASTIC_ANALYSIS_BOUNDARY_PROBES_REJECTED' `
    $stochasticAnalysisBoundaryRejected
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
    TRANSPORT_REPEATED_SOURCE = 0
    TRANSPORT_EPISTEMIC_SOURCE = 0
    TRANSPORT_EVOLUTIONARY_SOURCE = 0
    TRANSPORT_CONGESTION_SOURCE = 0
    TRANSPORT_MECHANISM_SOURCE = 0
    TRANSPORT_COOPERATIVE_SOURCE = 0
    TRANSPORT_STOCHASTIC_SOURCE = 0
    TRANSPORT_GAMETHEORYMATH_SOURCE = 0
    TRANSPORT_POST_ARCHITECTURE = 0
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
    KNAPSACK_AGGREGATE_GAMETHEORY_IMPORTS = 0
    KNAPSACK_BASIC_FORBIDDEN_IMPORTS = 0
    SIGNATURE_PROBABILITY_IMPORTS = 0
    REPEATED_FORBIDDEN_IMPORTS = 0
    EPISTEMIC_FORBIDDEN_IMPORTS = 0
    EVOLUTIONARY_FORBIDDEN_IMPORTS = 0
    STOCHASTIC_FORBIDDEN_IMPORTS = 0
    GAMETHEORYMATH_FORBIDDEN_IMPORTS = 0
    CONCEPTS_NOT_DEFINED_EXACTLY_ONCE = 0
    REPRESENTATION_TOKENS_OUTSIDE_FINDIST = 0
    TOPMF_OUTSIDE_FINDIST = 0
  }
  # RFC 7.3 states a budget, not a target, so this one is a bound.
  if ($Results['PRISONERS_DILEMMA_DEF_LINES'] -ge 25) {
    throw ("PRISONERS_DILEMMA_DEF_LINES: RFC 7.3 budgets under 25, got " +
      $Results['PRISONERS_DILEMMA_DEF_LINES'])
  }
  if (-not $SkipReachability) {
    $Expected['UNREACHABLE_PROBES_PASSED'] = 6
    $Expected['KNAPSACK_ALGORITHM_BOUNDARY_PROBES_REJECTED'] = 7
    $Expected['KNAPSACK_APPROXIMATION_ALGORITHM_BOUNDARY_PROBES_REJECTED'] = 7
    $Expected['KNAPSACK_AGGREGATE_BOUNDARY_PROBES_REJECTED'] = 8
    $Expected['KNAPSACK_BASIC_BOUNDARY_PROBES_REJECTED'] = 7
    $Expected['KNAPSACK_ROOT_INPUT_PROBES_REACHED'] = 5
    $Expected['KNAPSACK_MECHANISM_INPUT_PROBES_REACHED'] = 6
    $Expected['FAIR_DIVISION_INPUT_PROBES_REACHED'] = 4
    $Expected['FAIR_DIVISION_BOUNDARY_PROBES_REJECTED'] = 4
    $Expected['MATCHING_INPUT_PROBES_REACHED'] = 5
    $Expected['MATCHING_BOUNDARY_PROBES_REJECTED'] = 4
    $Expected['ANALYSIS_PROBES_REACHED'] = 2
    $Expected['REPEATED_ANALYSIS_PROBES_REJECTED'] = 6
    $Expected['REPEATED_BRIDGE_PROBES_REACHED'] = 3
    $Expected['REPEATED_BRIDGE_PROTOCOL_REJECTED'] = 1
    $Expected['GAMETHEORYMATH_GAME_REJECTED'] = 1
    $Expected['MATH_LEARNING_BOUNDARY_PROBES_REJECTED'] = 2
    $Expected['CORE_LEARNING_MW_PROBES_REJECTED'] = 2
    $Expected['CORE_FICTITIOUS_INPUT_PROBES_REACHED'] = 2
    $Expected['CORE_FICTITIOUS_BOUNDARY_PROBES_REJECTED'] = 2
    $Expected['CORE_MIXED_POTENTIAL_INPUT_PROBES_REACHED'] = 2
    $Expected['CORE_MIXED_POTENTIAL_BOUNDARY_PROBES_REJECTED'] = 2
    $Expected['CORE_MIXED_IMPROVEMENT_INPUT_PROBES_REACHED'] = 2
    $Expected['CORE_MIXED_IMPROVEMENT_BOUNDARY_PROBES_REJECTED'] = 2
    $Expected['CORE_FICTITIOUS_POTENTIAL_INPUT_PROBES_REACHED'] = 5
    $Expected['CORE_FICTITIOUS_POTENTIAL_BOUNDARY_PROBES_REJECTED'] = 2
    $Expected['HARMONIC_SEQUENCE_INPUT_PROBES_REACHED'] = 2
    $Expected['HARMONIC_SEQUENCE_BOUNDARY_PROBES_REJECTED'] = 2
    $Expected['MATH_APPROACHABILITY_INPUT_PROBES_REACHED'] = 3
    $Expected['MATH_APPROACHABILITY_BOUNDARY_PROBES_REJECTED'] = 2
    $Expected['APPROACHABILITY_ANALYSIS_INPUT_PROBES_REACHED'] = 4
    $Expected['APPROACHABILITY_ANALYSIS_BOUNDARY_PROBES_REJECTED'] = 2
    $Expected['FICTITIOUS_POTENTIAL_ANALYSIS_INPUT_PROBES_REACHED'] = 4
    $Expected['FICTITIOUS_POTENTIAL_ANALYSIS_BOUNDARY_PROBES_REJECTED'] = 2
    $Expected['LEARNING_BRIDGE_INPUT_PROBES_REACHED'] = 9
    $Expected['LEARNING_BRIDGE_BOUNDARY_PROBES_REJECTED'] = 2
    $Expected['PROTOCOL_FINITE_LAW_INPUT_PROBES_REACHED'] = 2
    $Expected['PROTOCOL_FINITE_LAW_BOUNDARY_PROBES_REJECTED'] = 1
    $Expected['EPISTEMIC_INPUT_PROBES_REACHED'] = 6
    $Expected['EPISTEMIC_BOUNDARY_PROBES_REJECTED'] = 5
    $Expected['ELECTRONIC_MAIL_INPUT_PROBES_REACHED'] = 4
    $Expected['ELECTRONIC_MAIL_BOUNDARY_PROBES_REJECTED'] = 4
    $Expected['BAYESIAN_EPISTEMIC_PROBE_REJECTED'] = 1
    $Expected['EPISTEMIC_BAYESIAN_PROBE_REJECTED'] = 1
    $Expected['EVOLUTIONARY_BASIC_INPUT_PROBES_REACHED'] = 2
    $Expected['EVOLUTIONARY_BASIC_BOUNDARY_PROBES_REJECTED'] = 6
    $Expected['EVOLUTIONARY_BRIDGE_INPUT_PROBES_REACHED'] = 3
    $Expected['EVOLUTIONARY_BRIDGE_BOUNDARY_PROBES_REJECTED'] = 4
    $Expected['CORE_EVOLUTIONARY_PROBES_REJECTED'] = 2
    $Expected['CHEAP_TALK_INPUT_PROBES_REACHED'] = 2
    $Expected['CHEAP_TALK_BOUNDARY_PROBES_REJECTED'] = 4
    $Expected['CHEAP_TALK_RANDOMIZATION_INPUT_PROBES_REACHED'] = 2
    $Expected['CHEAP_TALK_RANDOMIZATION_BOUNDARY_PROBES_REJECTED'] = 4
    $Expected['TRANSFORM_INPUT_PROBES_REACHED'] = 6
    $Expected['PROBABILITY_REINDEX_INPUT_PROBES_REACHED'] = 2
    $Expected['PROBABILITY_REINDEX_BOUNDARY_PROBES_REJECTED'] = 2
    $Expected['STOCHASTIC_INPUT_PROBES_REACHED'] = 7
    $Expected['STOCHASTIC_BOUNDARY_PROBES_REJECTED'] = 3
    $Expected['STOCHASTIC_ANALYSIS_INPUT_PROBES_REACHED'] = 8
    $Expected['STOCHASTIC_ANALYSIS_BOUNDARY_PROBES_REJECTED'] = 2
  }
  foreach ($entry in $Expected.GetEnumerator()) {
    if ($Results[$entry.Key] -ne $entry.Value) {
      throw "$($entry.Key): expected $($entry.Value), got $($Results[$entry.Key])"
    }
  }
  Write-Output 'VERIFIED=1'
}
