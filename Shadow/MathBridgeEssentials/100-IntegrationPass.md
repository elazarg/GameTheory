# Integration Pass

Goal:

- turn bridge abstractions into direct, low-friction use in `GameTheory` while keeping `Math` model-free.

Process:

1. identify a local helper theorem in `GameTheory`,
2. restate it in `Math` terminology,
3. prove it in `Math` with minimal assumptions,
4. (later) replace the local helper with the `Math` lemma.

Scope rule for this phase:

- no changes to domain theorem statements are required,
- only reduce local proof boilerplate and assumption noise.

Equivalent names:

- `Integration pass` (chosen):
  - structure: systematic replacement of local proofs by reusable abstractions.
  - equivalent names: refactoring pass, abstraction uptake pass.

External-field fit:

- library engineering, proof modularization, API stabilization.

Success metrics:

1. local helper count decreases in target files,
2. no loss in theorem statement clarity,
3. abstraction lemmas remain meaningful outside domain use.

## Completion Snapshot (Model-Agnostic Scope)

Implemented in `Math`:

1. Execution/core iteration laws:
   `Math.ProbabilityMassFunction`, `Math.Promotion.Iteration`, `Math.ListSuffix`.
2. Projection/reachability congruence:
   `Math.SetReachability`.
3. Transport/refinement combinators:
   `Math.OrderTransfer`.
4. Disintegration/recombination PMF layer:
   `Math.PMFProduct`, `Math.ProbabilityMassFunction`.
5. Locality/non-interference update algebra:
   `Math.FunctionUpdate`, `Math.PMFProduct`, `Math.FinsetUpdate`.
6. Descent/well-founded wrappers:
   `Math.OrderWellFounded`.
7. Optimization shell (fixed-point/local/global/no-improvement):
   `Math.OptimizationLocalGlobal`.
8. Geometry envelope (closed/compact/convex region wrappers):
   `Math.TopologyConvexRegion`.
9. Objective decomposition (additive and nonnegative scaling transport):
   `Math.OptimizationLocalGlobal`.

Deferred (domain adapter layer, not model-agnostic):

1. any theorem that names a specific game format or equilibrium concept.
2. conversion theorems that depend on concrete game encodings rather than generic maps.
