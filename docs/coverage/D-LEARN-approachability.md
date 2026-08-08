# D-LEARN: approachability and regret matching

Title: Blackwell approachability and the nonpositive-regret orthant
Family ID: D-LEARN
Pinned roots: `GameTheory/Concepts/Learning/Approachability.lean`, `GameTheory/Concepts/Learning/ApproachabilityRegret.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `b63bdf9`
Canonical destinations: `GameTheoryMath.Approachability`, `GameTheory.Analysis.Approachability`
Domain contract / decision: D10, D21
Owner: Wave 2 / learning dynamics
Status: complete; 23/23 declarations classified, no deferred rows
Last verified: 2026-08-09

The squared-distance, Cesàro, B-set, and orthant-projection mathematics is
independent of games and probability, so it lives in `GameTheoryMath`.  The
only representation adapter lives in the opt-in Analysis leaf and packages
regret matching with canonical `FinDist`; no predecessor PMF interface or
second regret predicate survives.  The fallback action is explicitly
noncomputable proof semantics.

| Pinned path | Declaration | Kind | Disposition | Successor declaration | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Learning/Approachability.lean` | `sq_infDist_avg_le` | theorem | adapt | `GameTheoryMath.Approachability.sq_infDist_avg_le` | focused GameTheoryMath build | Game-free squared-distance potential. |
| same | `infDist_avg_tendsto_zero` | theorem | adapt | `GameTheoryMath.Approachability.infDist_avg_tendsto_zero` | focused GameTheoryMath build | Analytic convergence endpoint. |
| same | `avgVec` | def | adapt | `GameTheoryMath.Approachability.avgVec` | alternating-environment fixture | Reactive Cesàro average without strategic semantics. |
| same | `avgVec_succ` | theorem | adapt | `GameTheoryMath.Approachability.avgVec_succ` | focused GameTheoryMath build | Exact recurrence. |
| same | `avgVec_norm_le` | theorem | adapt | `GameTheoryMath.Approachability.avgVec_norm_le` | nonconstant payoff bound | Uniform ball invariant. |
| same | `blackwell_approaches` | theorem | adapt | `GameTheoryMath.Approachability.blackwell_approaches` | focused GameTheoryMath build | Proper-space B-set theorem. |
| `GameTheory/Concepts/Learning/ApproachabilityRegret.lean` | `nonposOrthant` | def | adapt | `GameTheoryMath.Approachability.nonposOrthant` | focused geometry build | Probability-free target set. |
| same | `mem_nonposOrthant` | theorem | adapt | `GameTheoryMath.Approachability.mem_nonposOrthant` | focused geometry build | Transparent coordinate criterion. |
| same | `nonposOrthant_nonempty` | theorem | adapt | `GameTheoryMath.Approachability.nonposOrthant_nonempty` | focused geometry build | Zero witness. |
| same | `isClosed_nonposOrthant` | theorem | adapt | `GameTheoryMath.Approachability.isClosed_nonposOrthant` | focused geometry build | Coordinatewise closedness. |
| same | `orthantProj` | def | adapt | `GameTheoryMath.Approachability.orthantProj` | nonuniform score fixture | Coordinatewise clamp. |
| same | `orthantProj_ofLp` | theorem | adapt | `GameTheoryMath.Approachability.orthantProj_ofLp` | focused geometry build | Projection coordinate equation. |
| same | `orthantProj_mem` | theorem | adapt | `GameTheoryMath.Approachability.orthantProj_mem` | focused geometry build | Projection membership. |
| same | `sub_orthantProj_ofLp` | theorem | adapt | `GameTheoryMath.Approachability.sub_orthantProj_ofLp` | focused geometry build | Positive-part displacement. |
| same | `norm_sq_eq_sum` | theorem | adapt | `GameTheoryMath.Approachability.norm_sq_eq_sum` | two-coordinate norm bound | General Euclidean helper stays game-free. |
| same | `infDist_eq_norm_sub_orthantProj` | theorem | adapt | `GameTheoryMath.Approachability.infDist_eq_norm_sub_orthantProj` | focused geometry build | Clamp realizes infimum distance. |
| same | `norm_orthantProj_le` | theorem | adapt | `GameTheoryMath.Approachability.norm_orthantProj_le` | focused geometry build | Nonexpansiveness from coordinate squares. |
| same | `regretPayoff` | def | adapt | `GameTheory.Analysis.Approachability.regretPayoff` | changing-environment fixture | Canonical finite-support expectation; arbitrary action carrier until regret matching. |
| same | `regretPayoff_ofLp` | theorem | adapt | `GameTheory.Analysis.Approachability.regretPayoff_ofLp` | two distinct regret coordinates | No stored finiteness assumption. |
| same | `regretMatch` | def | adapt | `GameTheory.Analysis.Approachability.regretMatch` | probabilities `1/4` and `3/4` | `FinDist.ofWeights`, not PMF construction. |
| same | `expect_regretMatch_pos` | theorem | adapt | `GameTheory.Analysis.Approachability.expect_regretMatch_pos` | focused Analysis build | Positive-regret weighted expectation. |
| same | `regretMatch_steering` | theorem | adapt | `GameTheory.Analysis.Approachability.regretMatch_steering` | both environment states | Canonical B-set bridge. |
| same | `regretMatch_approaches` | theorem | adapt | `GameTheory.Analysis.Approachability.regretMatch_approaches` | alternating-environment capstone | No-regret convergence on a nonstationary environment sequence. |

Attribution: the pinned files supply the squared-distance telescope, reactive
average, orthant projection, and regret-matching steering calculation.  The
successor preserves that mathematics while extracting the game-free theorems,
using canonical finite-support expectations, and keeping topology out of Core
and Probability.

Validation:

```text
lake build GameTheoryMath.Approachability GameTheoryMath.ApproachabilityRegret
lake build GameTheory.Analysis.Approachability GameTheory.Analysis.ApproachabilityTest GameTheory.Analysis.Learning
git diff --check
```

The hostile fixture has two actions, a nonuniform score law with probabilities
`1/4` and `3/4`, opposite best actions across two environment states, two
nonzero regret coordinates, a uniform norm bound, and an alternating sequence
specializing the convergence theorem.
