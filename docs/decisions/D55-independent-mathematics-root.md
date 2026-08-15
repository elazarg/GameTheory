# D55: reusable mathematics lives under `GameTheory.Math`

- **Status:** adopted
- **Date:** 2026-08-16
- **Experiment IDs:** EXP-101

## Decision / question

How should mathematical infrastructure that is useful beyond game semantics be
named, packaged, and audited, including the canonical finite-support
probability law?

Use one public subtree, `GameTheory.Math.*`, with a separately buildable dotted
Lake target named `GameTheory.Math`. Probability lives at
`GameTheory.Math.Probability.*`. The main `GameTheory` target still builds the
whole repository, while the narrower target proves that this subtree can be
consumed without the rest of the library.

The directory is the ownership signal. Module comments describe their
mathematics and API rather than repeating the dependency classification.

## Competing designs

1. Keep the separate `GameTheoryMath` namespace and top-level directory, with
   probability under `GameTheory.Probability`.
2. Move the modules to `GameTheory.Math` but rely only on directory convention,
   without an independent Lake target or import audit.
3. Use `GameTheory.Math` as one subtree and one independently buildable target,
   including finite probability.
4. Publish the mathematics as a separate repository and package immediately.

Design 3 is adopted. Design 1 makes one conceptual library look like two
unrelated public namespaces and leaves probability in a game-branded semantic
root. Design 2 cannot falsify accidental imports from the rest of the library.
Design 4 adds release and dependency coordination before any external package
consumer requires it; the subtree and target preserve that option without
paying that cost now.

## Representative hostile slice

The migration moved every existing `GameTheoryMath` module and the complete
finite-probability family, then extracted the finite-law/standard-simplex
correspondence from `GameTheory.Analysis.Simplex`, finite-law pointwise
convergence from `GameTheory.Analysis`, and cyclic finite-index lemmas from
`GameTheory.Repeated`. The remaining modules own mixed-profile geometry and
periodic repeated-game payoffs respectively.

The experiment retained the D21 internal boundary:
`GameTheory.Math.OnlineLearning` works with normalized coordinate vectors,
while `GameTheory.Math.Probability.OnlineLearning` is the sole `FinDist`
adapter. A common subtree does not require every module to import every sibling.

Placement is semantic rather than a scan for files that happen not to import a
game module. General probability, finite-vector learning, DAGs, discounted
sums, and geometric lemmas belong here. A knapsack aggregate or a preference
rank can remain with its domain when its vocabulary and intended public API are
that domain's mathematics. A later consumer can justify extracting a more
general abstraction.

## Measurements

| Measure | EXP-101 result |
|---|---|
| focused target | `lake build GameTheory.Math` passed, 2,436 jobs, 66.7 seconds on a cold local build |
| full default target | final `lake build` passed all 3,611 jobs; the initial cold namespace rebuild passed 3,610 jobs in 450.1 seconds |
| authored-import boundary | `MATH_FORBIDDEN_IMPORTS=0` |
| negative semantic reachability | `MATH_GAME_REJECTED=1` |
| source transport count | `TRANSPORT_MATH_SOURCE=1`, the already accepted internal `change` in `FinDist` |
| source size | 3,261 nonblank lines in `GameTheory/Math`, of which 1,633 are finite probability |
| downstream slice | Core passed at 1,753 jobs; Protocol, analytic simplex, Epistemic, Evolutionary, and Stochastic passed together at 2,367 jobs |
| stale public roots | zero stale imports, namespace declarations, or filesystem paths using `GameTheoryMath` or `GameTheory.Probability` |
| compiled architecture gates | deep Phase 2 and Phase 3 passed with `VERIFIED=1` in 686.5 and 209.3 seconds; retained as release/CI gates rather than implementation-loop checks |
| post-extraction reachability | Math, Analysis learning, and sequential consistency reach finite-law convergence; Core and Protocol reject it |

## Kill conditions

Reject or narrow the layout if the dotted target cannot coexist with the main
target, if probability creates a dependency cycle, if the math target can
reach game semantics or the fixed-point package, if downstream APIs need a
second probability representation, or if the migration requires compatibility
aliases or public transports.

None fired. The move is intentionally source-incompatible: no aliases preserve
the former namespaces. The mathematical APIs and proofs remain the same except
for ownership-qualified names and the extracted simplex correspondence.

## Consequences

- Import `GameTheory.Math` for the umbrella, or a focused
  `GameTheory.Math.*` module for a smaller closure.
- Use `GameTheory.Math.Probability.FinDist` as the sole finite-support law.
- Keep analytic game theorems in `GameTheory.Analysis`; only their reusable
  supporting mathematics belongs here.
- Preserve module-level dependency discipline inside the subtree when it gives
  clients a meaningfully smaller interface, as in online learning.
- Run the independent target and its authored-import/reachability probes at
  architecture gates.
