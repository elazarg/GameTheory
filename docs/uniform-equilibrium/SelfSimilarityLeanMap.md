# Lean map: strategic self-similarity of quitting holonomy

This file is the declaration-level map for the self-similarity layer. The
mathematical derivation and open research boundary are in
[SelfSimilarity.md](SelfSimilarity.md).

## Entry point

```text
GameTheory/Concepts/Stochastic/QuittingSelfSimilarity.lean
```

imports the complete layer.

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

The last three declarations justify dividing by `1-survival`: the quotient is
not an arbitrary condition number but the exact displacement of the affine
fixed point from the proposed target.

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
  projector (`survival=0`) or the identity (`survival=1`, `intercept=0`).
- `eval_normalForm_of_mul_self_eq_self`: functional version of the same
  classification.

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

### Target safety

- `targetExcess_eq_max`: target excess is the maximum of early and tail
  residuals.
- `eval_le_target_iff`: exact two-halfspace characterization.
- `eval_mono`: monotonicity used to compose safe stopping maps.
- `tailResidual_eq_absorptionMass_mul_tailAnchor_sub`.
- `normalizedTailResidual_eq_tailAnchor_sub`.

### Idempotents

- `mul_self_eq_self_iff`: a max-affine coefficient idempotent is either
  constant (`survival=0`, `tail≤early`) or a threshold closure
  (`survival=1`, `tail=0`).
- `eval_normalForm_of_mul_self_eq_self`.

---

## 4. Complete strategic holonomy

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

This definition is a coefficient-level strategic projection. It does not by
itself assert equality of source paths, controller phases, marked packets,
Snell obstacles, or splice provenance.

---

## 5. Affine tangent coordinates

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

The first theorem turns a weighted intercept bound into compactness of the
conditional anchor. The second identifies the neutral face exactly.

---

## 6. Max-plus tangent coordinates

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
- `eval_probe_ofScaledObstacles` for a probe `target + mass*x`.
- `normalized_eval_probe_ofScaledObstacles`.

### Generic weighted-bound consequences

- `abs_tailAnchor_le_of_abs_tail_le_mul_absorptionMass`.
- `tail_eq_zero_of_abs_tail_le_mul_absorptionMass`.

The probe formula retains the exact correction `-mass*x`; the limiting tangent
map is max-plus, not linear.

---

## 7. Realized finite-block bounds

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityRealizedBounds.lean`.

This module combines the new tangent algebra with the existing weighted
holonomy estimates for actual product-root blocks.

### Compact anchors

- `abs_quittingFiniteBoundaryHolonomy_prescribed_fixedPoint_le`.
- `abs_quittingFiniteBoundaryHolonomy_bestResponse_tailAnchor_le`.

Both conditional anchors lie in the common terminal reward box whenever their
survival defect is positive.

### First-order residual bounds

- `abs_quittingFiniteBoundaryHolonomy_prescribed_targetResidual_le`.
- `abs_quittingFiniteBoundaryHolonomy_bestResponse_tailResidual_le`.

The raw residuals are bounded by `(rewardBound + |target|)` times their own
absorption mass.

### Normalized residual bounds

- `abs_quittingFiniteBoundaryHolonomy_prescribed_normalizedTargetResidual_le`.
- `abs_quittingFiniteBoundaryHolonomy_bestResponse_normalizedTailResidual_le`.

These are the compact first-order coordinates available along an escaping
sequence.

---

## 8. Realized neutral faces

File:
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarityRealizedNeutral.lean`.

- `quittingFiniteBoundaryHolonomy_prescribed_intercept_eq_zero_of_survival_eq_one`.
- `quittingFiniteBoundaryHolonomy_prescribed_eval_eq_of_survival_eq_one`.
- `quittingFiniteBoundaryHolonomy_bestResponse_tail_eq_zero_of_survival_eq_one`.
- `quittingFiniteBoundaryHolonomy_bestResponse_eval_eq_max_of_survival_eq_one`.

An actual neutral prescribed map is the identity. An actual neutral unilateral
tail map is a threshold closure. No hidden nonzero intercept survives at zero
absorption mass.

---

## 9. Existing tools used rather than duplicated

The new layer deliberately builds on:

- `QuittingBoundaryHolonomy.lean` for exact actual-block extraction and
  associative composition;
- `QuittingBoundaryHolonomyWeightedBounds.lean` for intercept bounds weighted
  by survival defect;
- `QuittingBoundaryHolonomyCompactness.lean` for fixed-cutoff resolved
  compactness and the unbounded-length fence;
- `QuittingPeriodicCompiler.lean` for quantitative cyclic contraction;
- `BigMatchSelfSimilarity.lean` for the exact physical/target live cycle;
- `BigMatchDeficitIndexNoGo.lean` for the wrong harmonic hazard scaling;
- `FinkTangentRate.lean` for rate-sensitive supported tangent equations.

No theorem in this PR upgrades those scoped results into the missing global
producer.

---

## 10. Mathematics documented but not formalized here

[SelfSimilarity.md](SelfSimilarity.md) and
[SelfSimilarityResearchProgram.md](SelfSimilarityResearchProgram.md) derive or
state with explicit status:

- logarithmic absorption time and its additive composition;
- Puiseux relevant/marginal/irrelevant classification;
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

The present Lean layer proves the algebra and the realized first-order bounds
needed to state that implication without ambiguity.
