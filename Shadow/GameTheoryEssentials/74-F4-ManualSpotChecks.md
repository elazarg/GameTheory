# F4 Manual Spot Checks (Precise, Non-Mnemonic Mapping)

Purpose: correct/validate heuristic mapping on key high-impact theorems.

## `NashExistenceMixed.lean`

### `isNash_iff_gains_nonpos` (line ~110)

- Primary: `B9`
- Secondary: `B6`
- Status: `R`
- Structural restatement:
  - predicate defined by universal unilateral deviation inequality
    is equivalent to nonpositivity of local gain functional.

### `weighted_gain_sum_zero` (line ~140)

- Primary: `B9`
- Secondary: `B1`
- Status: `R`
- Structural restatement:
  - expectation of centered gain functional under current measure is zero.

### `nash_fp_is_nash` (line ~220)

- Primary: `B6`
- Secondary: `B9`
- Status: `R`
- Structural restatement:
  - fixed point of normalized map implies target inequality predicate.

### `continuous_nashMapOnMixedSimplex` (line ~702)

- Primary: `B8`
- Secondary: `B1`
- Status: `R`
- Structural restatement:
  - continuity of constructed self-map follows from continuity of base evaluators and compositional operators.

### `mixed_nash_exists` (line ~808)

- Primary: `B6`
- Secondary: `B8`
- Status: `A`
- Structural restatement:
  - package fixed-point existence + transfer lemma into existential theorem surface.

## `CorrelatedNashMixed.lean`

### `deviateDistribution_pmfPi` (line ~58)

- Primary: `B1`
- Secondary: `B4`
- Status: `R`
- Structural restatement:
  - deviation distribution over product law admits explicit bind/pushforward decomposition.

### `mixed_nash_isCorrelatedEq` (line ~86)

- Primary: `B9`
- Secondary: `B1`
- Status: `R`
- Structural restatement:
  - inequality predicate for one equilibrium notion implies inequality predicate for broader distributional notion.

### `correlatedEq_exists` (line ~115)

- Primary: `B6`
- Secondary: `B1`
- Status: `A`
- Structural restatement:
  - existence by reduction to previously established existence plus translation.

## `SolutionConcepts.lean`

### representative implication lemmas (multiple lines)

- Primary: `B10` (surface taxonomy)
- Secondary: `B9`
- Status: `A`
- Structural restatement:
  - concept implication lattice statements; mostly wrappers if underlying inequality lemmas are elsewhere.

## `ApproximateNash.lean`

### `isNash_iff_isεNash_zero` (line ~52)

- Primary: `B9`
- Secondary: `B10`
- Status: `R`
- Structural restatement:
  - parameterized inequality notion collapses to base notion at parameter zero.

### `IsεNash.mono` (line ~61)

- Primary: `B9`
- Secondary: `B0`
- Status: `S/R` (often standard monotonicity template)
- Structural restatement:
  - monotonicity in tolerance parameter.

## Spot-check conclusion

Heuristic map is directionally correct for high-impact files:

- `B9` dominates characterization lemmas.
- `B6+B8` dominates existence chain.
- many `B10` rows in concept-taxonomy files are adapter-level by design.

