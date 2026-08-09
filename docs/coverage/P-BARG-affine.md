# P-BARG: topology-free Nash bargaining and affine invariance

Title: Capability-free Nash bargaining and positive-affine invariance
Family ID: P-BARG
Pinned roots: `GameTheory/Cooperative/Bargaining.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `d2156f3`
Canonical destination: `GameTheory.Cooperative`
Domain contract / decision: D9, EXP-069, D36
Owner: Wave 4 / bargaining
Status: partial; all 30 declarations classified, with the 14-declaration Nash slice complete and 16 egalitarian/Kalai--Smorodinsky rows deferred
Last verified: 2026-08-09

The successor keeps a bargaining problem as an arbitrary feasible predicate
and explicit feasible disagreement point.  It stores no finite enumeration,
convexity, compactness, topology, probability, or existence hypothesis.
Finite-player capability appears only on the Nash product.  The bounded gate
recovers Pareto vocabulary, the Nash solution, symmetry, and positive-affine
invariance; egalitarian and Kalai--Smorodinsky characterization form the named
BFS continuation.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Cooperative/Bargaining.lean` | `BargainingProblem` | structure | adapt | `GameTheory.BargainingProblem` | EXP-069 owner comparison | Uses descriptive `disagreement`; stores no capability. |
| same | `IsIR` | def | adapt | `BargainingProblem.IsIndividuallyRational` | focused build | Public name spells out the economic predicate. |
| same | `IsPareto` | def | port | `BargainingProblem.IsPareto` | focused build | Strong Pareto predicate over the feasible set. |
| same | `IsWeaklyPareto` | def | port | `BargainingProblem.IsWeaklyPareto` | hostile specialization | Weak Pareto predicate over the feasible set. |
| same | `isWeaklyPareto_of_isPareto` | theorem | port | same name under `BargainingProblem` | focused build | Requires only a nonempty player type. |
| same | `IsNashSolution` | def | adapt | `BargainingProblem.IsNashSolution` | hostile product comparison | Finiteness occurs only on this product-valued predicate. |
| same | `nashSolution_IR` | theorem | adapt | `BargainingProblem.IsNashSolution.isIndividuallyRational` | projection theorem | Bundled as a method on the certificate. |
| same | `nashSolution_weaklyPareto` | theorem | adapt | `BargainingProblem.IsNashSolution.isWeaklyPareto` | generic theorem plus fixture | Handles zero gains without convexity. |
| same | `IsSymmetric` | def | port | `BargainingProblem.IsSymmetric` | focused build | Constant disagreement and permutation-closed feasibility. |
| same | `nashSolution_symmetric` | theorem | adapt | `BargainingProblem.IsNashSolution.equal_gain_of_symmetric` | focused build | Retains the explicit uniqueness premise. |
| same | `posAffineMap` | def | adapt | `BargainingProblem.positiveAffineMap` | unequal-scale fixture | Descriptive greenfield name; one shared componentwise transformation. |
| same | `posAffineMap_feasible_image` | theorem | adapt | `BargainingProblem.positiveAffineMap_feasible_image` | focused build | Exact feasibility reflection. |
| same | `posAffineMap_isIR_image` | theorem | adapt | `BargainingProblem.positiveAffineMap_isIndividuallyRational_image` | focused build | Exact IR reflection. |
| same | `nashSolution_affine_invariant` | theorem | adapt | `BargainingProblem.IsNashSolution.positiveAffineMap` | hostile transformed maximizer | Unequal positive scales and nonzero shifts. |
| same | `IsEgalitarian` | def | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Reuse the same disagreement and affine map. |
| same | `egalitarian_IR` | theorem | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Transparent projection after the predicate is admitted. |
| same | `egalitarian_equal_gain` | theorem | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Equal-gain characterization. |
| same | `egalitarian_maximal` | theorem | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Pareto comparison breadth. |
| same | `nashSolution_le_egalitarian` | theorem | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Cross-solution comparison. |
| same | `IsIdealPoint` | def | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Ideal-point ownership must remain native and capability-light. |
| same | `IsKalaiSmorodinskyRelativeTo` | def | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Relative characterization. |
| same | `IsKalaiSmorodinsky` | def | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Familiar specialization, not a parallel problem type. |
| same | `kalaiSmorodinskyRelativeTo_IR` | theorem | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Basic projection. |
| same | `kalaiSmorodinskyRelativeTo_pareto` | theorem | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Strong Pareto projection. |
| same | `kalaiSmorodinskyRelativeTo_proportional` | theorem | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Proportional-gain characterization. |
| same | `kalaiSmorodinskyRelativeTo_symmetric` | theorem | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Symmetry consequence. |
| same | `kalaiSmorodinskyRelativeTo_affine_invariant` | theorem | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Must reuse `positiveAffineMap`. |
| same | `kalaiSmorodinsky_le_ideal` | theorem | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Coordinatewise ideal bound. |
| same | `kalaiSmorodinsky_monotone` | theorem | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Feasible-set monotonicity. |
| same | `kalaiSmorodinsky_relativeTo_unique` | theorem | deferred | P-BARG egalitarian/KS BFS gate | D36 follow-up | Uniqueness under positive ideal gains. |

Attribution: the predecessor supplies the topology-free Nash-product proof
spine and the positive-affine factorization.  The successor retains that
mathematics while removing unused logarithm/probability imports, avoiding
stored `Fintype`, and keeping topology-dependent existence out of the native
semantic owner.

Validation:

```text
lake build GameTheory.Cooperative GameTheory.Tests.Bargaining
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```

The two-player fixture contains disagreement, balanced, and two asymmetric
feasible profiles.  The balanced product is four while each asymmetric product
is three.  Unequal scales `(2,3)` and shifts `(5,-1)` transform the solution to
`(9,5)` and disagreement to `(5,-1)`, so the invariance witness cannot collapse
to identity, uniform scaling, or a singleton feasible set.
