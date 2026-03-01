# Brouwer Formalization Plan (Lean 4.27)

## Goal
Prove Brouwer fixed point theorem in this repository with no `axiom` / `sorry`, then use it to discharge unconditional mixed Nash existence.

Target theorem shape (core):
- `brouwer_stdSimplex`:
  for finite `ι`, every continuous `f : stdSimplex Real ι -> stdSimplex Real ι` has a fixed point.

Derived theorem shape (game-facing):
- `KernelGame.mixed_nash_exists` for finite players/strategies/outcomes.

## Strategy Choice
Use a combinatorial-topological route based on simplicial approximation / Sperner-style machinery.

Why this route:
- Compatible with finite simplices (`stdSimplex`) used by mixed strategies.
- Avoids building full fundamental-group stack.
- Aligns with existing blueprints while leveraging newer Mathlib (`stdSimplex`, compactness/convexity/continuity libraries).

## High-Level Dependency Graph
1. Geometry of simplex partitions
2. Labeling and Sperner lemma
3. Approximation-to-fixed-point extraction
4. Compactness limit argument
5. Brouwer on `stdSimplex`
6. Product-simplex version
7. Nash-map construction and fixed-point-to-Nash argument

## Module Plan

### M0: Foundation setup
File(s):
- `Fixpoint/Prelude.lean`

Deliverables:
- common notation, helper lemmas, namespace discipline.
- wrappers around `stdSimplex` coercions used repeatedly.

### M1: Finite simplex combinatorics
File(s):
- `Fixpoint/SimplexSubdivision.lean`
- `Fixpoint/Grid.lean`

Deliverables:
- finite grid/subdivision model for `stdSimplex`.
- barycentric coordinate lemmas for subdivision vertices.
- boundary-face characterization compatible with labeling constraints.

Mathlib leverage:
- `Analysis.Convex.StdSimplex`
- finset/fintype combinatorics.

### M2: Sperner labeling framework
File(s):
- `Fixpoint/SpernerLabeling.lean`

Deliverables:
- definition of admissible labeling on subdivided simplex.
- boundary admissibility lemmas.
- odd-parity / existence of fully-labeled simplex (Sperner theorem).

Mathlib leverage:
- finite sums/parity (`ZMod 2`, `Nat` parity lemmas).

### M3: Approximate fixed points from full labels
File(s):
- `Fixpoint/ApproximateFixedPoint.lean`

Deliverables:
- construct `x_n` from fully-labeled subsimplices.
- prove `||f x_n - x_n||` controlled by mesh size.

Mathlib leverage:
- normed-space inequalities, simplex coordinate bounds.

### M4: Limit extraction and exact fixed point
File(s):
- `Fixpoint/BrouwerStdSimplex.lean`

Deliverables:
- compactness subsequence extraction in `stdSimplex`.
- continuity passes approximate fixed points to exact fixed point.
- theorem `brouwer_stdSimplex`.

Mathlib leverage:
- compactness of `stdSimplex` (`isCompact_stdSimplex`).
- continuity and closed fixed-point set lemmas.

### M5: Product simplex / game domain packaging
File(s):
- `Fixpoint/ProductSimplex.lean`

Deliverables:
- package mixed-profile space as finite product of simplices.
- equivalence/homeomorphism to single `stdSimplex` representation when needed.
- Brouwer corollary on product simplex.

### M6: Nash map and mixed Nash existence
File(s):
- `Fixpoint/NashMap.lean`
- `Fixpoint/MixedNashFromBrouwer.lean`

Deliverables:
- define Nash continuous self-map (best-response style with normalization).
- prove map is continuous and self-maps mixed-profile simplex.
- fixed point implies `IsNash` in mixed extension.
- remove `KernelGame.mixed_nash_exists` axiom and replace by theorem.
- derive NFG theorem immediately.

## Integration Plan
1. Keep development isolated in `Fixpoint/` until theorem is complete.
2. After M6, replace axiom in `GameTheory/MixedNashExistence.lean` with import + theorem application.
3. Add imports to `GameTheory.lean`.
4. Add focused examples/tests showing theorem use.

## Hard Parts and Mitigations
1. Subdivision encoding complexity
- Mitigation: choose one canonical encoding early; avoid abstraction churn.

2. Parity/Sperner bookkeeping verbosity
- Mitigation: isolate parity lemmas in dedicated section; reuse aggressively.

3. Coercion friction with `stdSimplex`
- Mitigation: centralize coercion helper lemmas in `Prelude`.

4. Product-simplex vs single-simplex transport
- Mitigation: keep this as a separate module (M5) and prove small reusable equivalence lemmas.

## Definition of Done
- Brouwer theorem on finite simplex proved with no placeholders.
- Unconditional mixed Nash existence proved from Brouwer.
- No `axiom` / `sorry` in fixed-point and mixed-existence path.

## Immediate Next Execution Steps
1. Implement M0 and M1 skeletons with compilable definitions.
2. Land a first complete Sperner theorem statement and supporting finite combinatorics skeleton (M2).
3. Iterate until M4 closed theorem is achieved.
