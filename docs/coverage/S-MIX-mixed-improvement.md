# S-MIX: mixed-improvement certificates

Title: Aggregate positive pure-deviation gain
Family ID: S-MIX
Pinned root: `GameTheory/Concepts/Mixed/MixedImprovement.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `f2dbd5c`
Canonical destinations: `GameTheory.Core.MixedImprovement`, `GameTheory.Analysis.Learning`
Domain contract / decision: D4-D5, D10, D21
Owner: Wave 2 / mixed equilibrium and learning
Status: complete; 11/11 declarations classified, no deferred rows
Last verified: 2026-08-09

The successor retains the finite aggregate positive-gain certificate while
placing only the convergence endpoint in Analysis.  The base gain is defined
once from canonical mixed expected utility; no PMF evaluator or parallel Nash
predicate is introduced.  Compared with the predecessor, neither the outcome
carrier nor pure strategy carriers need finiteness until the aggregate finite
sum is formed.

| Pinned path | Declaration | Kind | Disposition | Successor declaration | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Mixed/MixedImprovement.lean` | `max_zero_eq_zero_iff` | private theorem | adapt | private `max_zero_eq_zero_iff` | focused Core build | Local real-order helper remains private. |
| same | `mixedImprovement` | def | adapt | `GameTheory.UtilityGame.mixedImprovement` | focused Core build | Sum of positive canonical `mixedGain`s. |
| same | `mixedImprovement_nonneg` | theorem | adapt | `GameTheory.UtilityGame.mixedImprovement_nonneg` | focused Core build | Finite-sum order only. |
| same | `mixedGain_pospart_le_mixedImprovement` | theorem | adapt | `GameTheory.UtilityGame.mixedGain_pospart_le_mixedImprovement` | focused Core build | Selected term is bounded by the aggregate. |
| same | `mixedGain_le_mixedImprovement` | theorem | adapt | `GameTheory.UtilityGame.mixedGain_le_mixedImprovement` | focused Core build | Removes predecessor outcome-finiteness assumptions. |
| same | `mixedGain_le_of_mixedImprovement_le` | theorem | adapt | `GameTheory.UtilityGame.mixedGain_le_of_mixedImprovement_le` | focused Core build | Direct transitive bound. |
| same | `mixedImprovement_eq_zero_iff_gains_nonpos` | theorem | adapt | `GameTheory.UtilityGame.mixedImprovement_eq_zero_iff_gains_nonpos` | focused Core build | Exact zero certificate. |
| same | `mixedImprovement_eq_zero_iff_isNash` | theorem | adapt | `GameTheory.UtilityGame.mixedImprovement_eq_zero_iff_isNash` | focused Core build | Uses the sole canonical mixed `IsNash`. |
| same | `isNash_iff_mixedImprovement_eq_zero` | theorem | adapt | `GameTheory.UtilityGame.isNash_iff_mixedImprovement_eq_zero` | focused Core build | Symmetric public orientation. |
| same | `isεNash_of_mixedImprovement_le` | theorem | adapt | `GameTheory.UtilityGame.isεNash_of_mixedImprovement_le` | focused Core build | Uses canonical `IsεNash`; arbitrary mixed deviations are integrated. |
| same | `eventually_isεNash_of_mixedImprovement_tendsto_zero` | theorem | adapt | `GameTheory.UtilityGame.eventually_isεNash_of_mixedImprovement_tendsto_zero` | focused Analysis build | Topological endpoint is kept out of Core. |

Attribution: the pinned file supplies the aggregate-positive-gain certificate
and the vanishing-gap endpoint.  The successor reuses that proof structure over
`FinDist`, factors the expected own-gain-zero identity into the canonical mixed
utility layer, and enforces the Core/Analysis split.

Validation:

```text
lake build GameTheory.Core.MixedImprovement GameTheory.Analysis.Learning
git diff --check
```

