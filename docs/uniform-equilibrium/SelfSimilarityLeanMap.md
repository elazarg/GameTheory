# Lean map: strategic self-similarity of quitting holonomy

This file is the declaration-level map for the self-similarity layer. The
mathematical derivation and open research boundary are in
[SelfSimilarity.md](SelfSimilarity.md),
[SelfSimilarityTangent.md](SelfSimilarityTangent.md), and
[SelfSimilarityExtendedObstacle.md](SelfSimilarityExtendedObstacle.md).

The status of every declaration in this file is **implemented on the PR
branch, subject to the PR's recorded focused Lean validation**. This document
does not turn coefficient compactness into strategic closedness or claim the
missing producer theorem.

## Entry point

```text
GameTheory/Concepts/Stochastic/QuittingSelfSimilarity.lean
```

imports the complete layer. `GameTheory/Theorems.lean` imports that umbrella.

---

## 1. Affine residual algebra

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityAffine.lean`.

### Definitions

- `QuittingAffineSummary.absorptionMass`: `1 - survival`.
- `QuittingAffineSummary.targetResidual`: `eval target - target`.
- `QuittingAffineSummary.normalizedTargetResidual`: residual divided by
  absorption mass.
- `QuittingAffineSummary.IsFixedAt`: exact target reproduction.

### Theorems

- `absorptionMass_mul`: chronological mass law
  `m(outer * inner) = m outer + survival outer * m inner`.
- `targetResidual_eq`: residual is `intercept - mass * target`.
- `targetResidual_mul`: exact transported residual cocycle.
- `isFixedAt_iff_targetResidual_eq_zero`.
- `isFixedAt_iff_intercept_eq`.
- `targetResidual_eq_absorptionMass_mul_fixedPoint_sub`.
- `normalizedTargetResidual_eq_fixedPoint_sub`.
- `isFixedAt_iff_fixedPoint_eq` away from survival one.

The normalized residual is not an arbitrary conditioning device: away from the
neutral face it is exactly the affine fixed-point displacement from the target.

---

## 2. Affine iteration and idempotents

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityAffineIteration.lean`.

### Finite iteration

- `identitySummary`.
- `selfCompose`.
- `geometricAmplifier`.
- `absorptionMass_mul_geometricAmplifier`.
- `geometricAmplifier_eq_div` away from the neutral face.
- `targetResidual_selfCompose`.
- `normalizedTargetResidual_mul`: absorption-mass-weighted averaging under
  chronological composition.

### Neutral pumping

- `targetResidual_selfCompose_of_survival_eq_one`: exact linear growth.
- `exists_targetResidual_selfCompose_gt_of_survival_eq_one`: every finite
  residual budget is eventually exceeded by a positive neutral residual.
- `IsFixedAt.selfCompose`: exact fixedness is stable under repetition.

### Idempotents

- `mul_self_eq_self_iff`: an affine coefficient idempotent is either a constant
  projector (`survival = 0`) or the identity
  (`survival = 1`, `intercept = 0`).
- `eval_normalForm_of_mul_self_eq_self`: functional normal form.

---

## 3. Max-affine stopping algebra

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityMaxAffine.lean`.

### Definitions

- `QuittingMaxAffineSummary.absorptionMass`.
- `tailResidual`.
- `targetExcess`.
- `tailAnchor`.
- `normalizedTailResidual`.

### Composition and target safety

- `absorptionMass_mul`: tail absorption obeys the same transported mass law.
- `tailResidual_mul`: exact chronological tail-residual cocycle.
- `normalizedTailResidual_mul`: transported absorption-mass-weighted averaging.
- `targetExcess_eq_max`: target excess is the maximum of early and tail
  residuals.
- `eval_le_target_iff`: exact two-halfspace characterization.
- `eval_mono`: monotonicity used to compose safe stopping maps.
- `tailResidual_eq_absorptionMass_mul_tailAnchor_sub`.
- `normalizedTailResidual_eq_tailAnchor_sub`.

### Idempotents

- `mul_self_eq_self_iff`: a max-affine coefficient idempotent is either
  constant (`survival = 0`, `tail ≤ early`) or a threshold closure
  (`survival = 1`, `tail = 0`).
- `eval_normalForm_of_mul_self_eq_self`.

---

## 4. Nonempty max-affine repetition

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityMaxAffineIteration.lean`.

A finite max-affine identity would require an infinite early floor, so this
module iterates one or more blocks rather than manufacturing a false monoid
unit.

- `selfComposeNonempty`.
- `tailResidual_selfComposeNonempty`.
- `tailResidual_selfComposeNonempty_of_survival_eq_one`.
- `exists_tailResidual_selfComposeNonempty_gt_of_survival_eq_one`.
- `eval_selfComposeNonempty_le_target`: target safety survives every nonempty
  finite repetition.
- `eval_selfComposeNonempty_le_target_iff_of_idempotent`.

---

## 5. Complete strategic coefficient holonomy

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityHolonomy.lean`.

### Definition

`QuittingBoundaryHolonomy.IsSelfSimilarAt holonomy target` requires:

1. every prescribed affine coordinate fixes its target coordinate; and
2. every max-affine unilateral stopping coordinate is at most that target.

### Theorems

- `isSelfSimilarAt_iff`: one affine equation and two affine inequalities per
  player.
- `IsSelfSimilarAt.mul`: closure under chronological composition.
- `IsSelfSimilarAt.gap_nonpos`: the existing boundary gap is nonpositive at
  zero relative debt.
- `IsIdempotent` and `isIdempotent_iff`: complete coefficient idempotence is
  componentwise.
- `normalForm_of_isIdempotent_of_isSelfSimilarAt`: safe projector/identity and
  constant/threshold normal forms at the target.

### Scope

This is the complete **coefficient projection** of strategic return. It does
not assert equality of source paths, controller phases, full Snell obstacles,
conditional marked packets, entry debt, or splice provenance.

---

## 6. Complete holonomy repetition

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityHolonomyIteration.lean`.

- `QuittingBoundaryHolonomy.selfComposeNonempty`.
- `prescribed_selfComposeNonempty`.
- `bestResponse_selfComposeNonempty`.
- `IsSelfSimilarAt.selfComposeNonempty`.
- `IsSelfSimilarAt.gap_selfComposeNonempty_nonpos`.
- `selfComposeNonempty_eq_of_isIdempotent`.

This lifts scalar repetition to the common playerwise holonomy without losing
cross-player synchronization at the coefficient level.

---

## 7. Affine absorbed-mass tangent coordinates

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityAffineTangent.lean`.

### Constructor

`QuittingAffineSummary.ofAbsorptionMass mass anchor` represents

```text
w ↦ mass * anchor + (1 - mass) * w.
```

### Exact identities

- `absorptionMass_ofAbsorptionMass`.
- `eval_ofAbsorptionMass`.
- `targetResidual_ofAbsorptionMass`.
- `isFixedAt_ofAbsorptionMass_iff`.
- `absorptionMass_mul_ofAbsorptionMass`.
- `intercept_mul_ofAbsorptionMass`.
- `targetResidual_mul_ofAbsorptionMass`.
- `normalizedTargetResidual_ofAbsorptionMass`.

### Generic weighted-bound consequences

- `abs_fixedPoint_le_of_abs_intercept_le_mul_absorptionMass`.
- `intercept_eq_zero_of_abs_intercept_le_mul_absorptionMass`.

The first theorem converts a weighted intercept estimate into compactness of
the conditional anchor. The second identifies the neutral face exactly.

---

## 8. Finite-scale max-plus tangent coordinates

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityMaxAffineTangent.lean`.

### Helper

- `max_add_mul_eq_add_mul_max`: a common nonnegative scale factors through
  `max` after a common translation.

### Constructor

`QuittingMaxAffineSummary.ofScaledObstacles target mass earlyDrift tailAnchor`
represents

```text
w ↦ max (target + mass * earlyDrift)
        (mass * tailAnchor + (1 - mass) * w).
```

### Exact tangent identities

- `eval_target_ofScaledObstacles`.
- `targetExcess_ofScaledObstacles`.
- `eval_target_ofScaledObstacles_le_iff` at positive mass.
- `eval_probe_ofScaledObstacles` for a probe `target + mass * x`.
- `normalized_eval_probe_ofScaledObstacles`.

### Generic weighted-bound consequences

- `abs_tailAnchor_le_of_abs_tail_le_mul_absorptionMass`.
- `tail_eq_zero_of_abs_tail_le_mul_absorptionMass`.

The probe formula retains the exact finite-scale correction `-mass * x`; the
limiting operator is max-plus, not linear.

---

## 9. Max-plus tangent dynamics

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityMaxPlusDynamics.lean`.

For

```text
F x = max early (tail + x)
```

the module defines `iterateNonempty` and proves:

- `eval_zero_le_zero_iff`: origin safety iff `early ≤ 0 ∧ tail ≤ 0`.
- `linear_tail_le_iterateNonempty`: every iterate dominates the pure translated
  tail branch.
- `iterateNonempty_eq_max_of_tail_nonpos`: exact formula
  `max early ((k : ℝ) * tail + x)` for nonpositive tail drift.
- `iterateNonempty_zero_tail`: zero tail drift is the idempotent threshold
  closure after one step.
- `exists_iterateNonempty_gt_of_tail_pos`: positive tail drift exceeds every
  finite budget.
- `exists_eventually_iterateNonempty_eq_early_of_tail_neg`: negative tail drift
  reaches the constant early projector after finitely many steps.
- `dynamics_trichotomy`: exact negative/zero/positive alternative.

This is the formal relevant/marginal/irrelevant classification at the tangent
operator level.

---

## 10. Realized finite-block first-order bounds

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityRealizedBounds.lean`.

This module combines the tangent algebra with existing weighted holonomy
estimates for actual product-root blocks.

### Conditional anchors

- `abs_quittingFiniteBoundaryHolonomy_prescribed_fixedPoint_le`.
- `abs_quittingFiniteBoundaryHolonomy_bestResponse_tailAnchor_le`.
- `abs_quittingFiniteBoundaryHolonomy_prescribed_fixedPoint_le_all`.
- `abs_quittingFiniteBoundaryHolonomy_bestResponse_tailAnchor_le_all`.

The `_all` versions use Lean's totalized division: the anchor is zero on the
neutral face and lies in the reward box elsewhere.

### First-order residual bounds

- `abs_quittingFiniteBoundaryHolonomy_prescribed_targetResidual_le`.
- `abs_quittingFiniteBoundaryHolonomy_bestResponse_tailResidual_le`.

Raw residuals are bounded by `(rewardBound + |target|)` times their own
absorption mass.

### Normalized residual bounds

- `abs_quittingFiniteBoundaryHolonomy_prescribed_normalizedTargetResidual_le`.
- `abs_quittingFiniteBoundaryHolonomy_bestResponse_normalizedTailResidual_le`.

These are the bounded first-order coordinates available along an escaping
sequence.

---

## 11. Realized neutral faces

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityRealizedNeutral.lean`.

- `quittingFiniteBoundaryHolonomy_prescribed_intercept_eq_zero_of_survival_eq_one`.
- `quittingFiniteBoundaryHolonomy_prescribed_eval_eq_of_survival_eq_one`.
- `quittingFiniteBoundaryHolonomy_bestResponse_tail_eq_zero_of_survival_eq_one`.
- `quittingFiniteBoundaryHolonomy_bestResponse_eval_eq_max_of_survival_eq_one`.
- `quittingFiniteBoundaryHolonomy_isSelfSimilarAt_iff_of_survival_eq_one`:
  when all prescribed and unilateral tail slopes are neutral, complete
  coefficient self-similarity is exactly the early floors lying below target.

No hidden nonzero prescribed or tail intercept survives at zero absorption
mass.

---

## 12. Compact bounded tangent core

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityTangentCompactness.lean`.

### Coordinates

`QuittingBoundaryTangentCoreCoordinates` retain, playerwise:

- prescribed absorption mass;
- prescribed conditional anchor;
- raw early stopping floor;
- unilateral tail absorption mass;
- unilateral conditional tail anchor.

### Theorems

- `quittingBoundaryTangentCoreBox`.
- `isCompact_quittingBoundaryTangentCoreBox`.
- `quittingFiniteBoundaryHolonomy_tangentCoreCoordinates_mem_box`.
- `exists_tendsto_subseq_quittingFiniteBoundaryTangentCoreCoordinates`.

Every sequence of actual finite blocks has a subsequence whose bounded tangent
core converges. This theorem does not include full obstacle, marked packet,
debt, path, or splice data.

---

## 13. Extended positive early-obstacle scale

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityEarlyExcess.lean`.

### Definitions

- `positiveEarlyExcess = max 0 (early - target)`.
- `scaledPositiveEarlyExcess` in `ℝ≥0∞`, divided by tail absorption mass.

### Exact classifications

- `positiveEarlyExcess_eq_zero_iff`.
- `positiveEarlyExcess_pos_iff`.
- `scaledPositiveEarlyExcess_eq_zero_iff`: zero exactly means early safety,
  including at zero mass.
- `scaledPositiveEarlyExcess_eq_top_iff`: under nonnegative mass, infinity is
  exactly an unsafe neutral face.
- `scaledPositiveEarlyExcess_ne_top_of_absorptionMass_pos`.

### Extended compactness

- `QuittingBoundaryExtendedTangentCoordinates`.
- `QuittingBoundaryHolonomy.extendedTangentCoordinates`.
- `quittingBoundaryExtendedTangentBox`.
- `isCompact_quittingBoundaryExtendedTangentBox`.
- `quittingFiniteBoundaryHolonomy_extendedTangentCoordinates_mem_box`.
- `exists_tendsto_subseq_quittingFiniteBoundaryExtendedTangentCoordinates`.

A diverging positive early-obstacle ratio converges to `⊤` rather than being
silently excluded by an unjustified real boundedness assumption.

---

## 14. Existing tools used rather than duplicated

The layer builds on:

- `QuittingBoundaryHolonomy.lean` for exact actual-block extraction and
  associative composition;
- `QuittingBoundaryHolonomyWeightedBounds.lean` for intercept bounds weighted
  by survival defect;
- `QuittingBoundaryHolonomyCompactness.lean` for fixed-cutoff resolved
  compactness and the unbounded-length fence;
- `QuittingPeriodicCompiler.lean` for quantitative cyclic contraction;
- `GraphDirectedPeriodicLift.lean` for periodic compatible lifts under strict
  contraction;
- `BigMatchSelfSimilarity.lean` for the exact physical/target live cycle;
- `BigMatchDeficitIndexNoGo.lean` for the wrong harmonic hazard scaling;
- `FinkTangentRate.lean` for rate-sensitive supported tangent equations.

No theorem in this PR upgrades those scoped results into the missing global
producer.

---

## 15. Mathematics and interfaces not claimed as Lean theorems here

The accompanying notes derive or state with explicit status:

- logarithmic absorption time and its additive composition;
- Puiseux relevant/marginal/irrelevant classification for realized germs;
- projective stratification of multiple playerwise scales;
- the conditional game-level pumping criterion for a complete returning packet;
- the compact enriched-semigroup/idempotent route under strategic closedness;
- the strategic self-similarity / escape alternative;
- the finite enriched packet and both decoder obligations;
- exact semialgebraic and tangent-chart search programs.

The central open implication remains:

```text
uniform equilibrium or positive-debt plateau
    ⇒ strategically admissible contracting return
       or admissible tangent return
       or executable positive-work escape/descent.
```

The present Lean layer settles the coefficient algebra, finite repetition,
idempotent normal forms, max-plus dynamics, realized first-order estimates, and
compact bounded/extended tangent projections needed to state that implication
without ambiguity. It does not prove semantic repeatability or the enriched
compactification and decoders.
