# Audit: `NashExistenceMixed.lean` (Structure-First)

Scope: fixed-point-to-equilibrium pipeline and continuity chain.

Reference constraints: `A1..A8` from `40-StructuralCore.md`.

## Module-level observation

- This file is mostly not in the `A1..A8` sequential-kernel track.
- It is a parallel structural track:
  - `B1`: simplex embedding/normalization,
  - `B2`: continuity of constructed self-map,
  - `B3`: fixed-point transfer to equilibrium inequalities.
- Main reusable shape is “fixed point of normalized gain map implies no-positive-deviation”.

## Theorem audit (major chain only)

## `isNash_iff_gains_nonpos` (line ~110)

- Role: algebraic characterization of equilibrium as pointwise inequality.
- Structural layer: algebraic core (non-sequential).
- Essential assumptions:
  - affine expectation linearity over finite supports,
  - deviation evaluation map defined.
- Likely accidental:
  - concrete update style in statement could be abstracted as “single-coordinate override”.
- Extraction candidate:
  - generic theorem: equilibrium predicate ↔ nonpositive local gain functional.

## `weighted_gain_sum_zero` (line ~140)

- Role: conservation identity at current profile (expected gain against own mixed law is zero).
- Structural layer: algebraic normalization.
- Essential assumptions:
  - finite support and normalization (`sum weights = 1`).
- Cross-field alias:
  - “mean-zero advantage under current sampling measure”.

## `nash_fp_is_nash` (line ~220)

- Role: fixed-point identity of map ⇒ inequality conditions ⇒ equilibrium.
- Structural layer: fixed-point transfer (`B3`).
- Essential assumptions:
  - map fixed-point equation,
  - nonnegativity of normalization terms.
- Likely accidental:
  - specific map encoding choices in statement.
- Extraction candidate:
  - `fixedPoint_of_normalized_gain_map_implies_equilibrium`.

## Continuity ladder (`continuous_*` family around 485..714)

- Role: produce continuity hypothesis required by fixed-point engine.
- Structural layer: `B2`.
- Essential assumptions:
  - continuity of base payoff evaluators,
  - continuity-preserving operations (sum, max/pospart, normalization).
- Likely accidental:
  - repeated variants with slight premise differences; can be consolidated by interface parameters.
- Extraction candidate:
  - one parametrized continuity transfer lemma.

## Approximation/fixed-point bridge
`nashMap_weightFixedPoint_of_nashMapOnMixedSimplex_approxOnly` (line ~730)

- Role: from approximate fixed points to exact weight fixed point (compactness/Brouwer pipeline).
- Structural layer: fixed-point engine wrapper.
- Essential assumptions:
  - approximation sequence property.
- Adapter quality:
  - good candidate to isolate completely from game semantics.

## Public existence theorems
`mixed_nash_exists_*` and `mixed_nash_exists` (lines ~746..808)

- Role: thin wrappers around fixed-point existence + algebraic transfer.
- Structural layer: packaging.
- Recommendation:
  - keep these thin; move reusable skeleton to generic fixed-point/equilibrium bridge module.

## Immediate reusable extractions from this module

1. Generic gain-inequality characterization lemma.
2. Generic normalized-map fixed-point ⇒ equilibrium transfer theorem.
3. Consolidated continuity transfer template for map constructors.

