# MATH: finite online learning

Title: Finite multiplicative weights and its external-regret bound
Family ID: MATH
Pinned roots: `Math/OnlineLearning/MultiplicativeWeights.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `d9ff55e`
Canonical destination: `GameTheoryMath.OnlineLearning` with a `GameTheory.Probability.OnlineLearning` adapter
Domain contract / decision: D0, D2, D12, EXP-049
Owner: Wave 2 / D-LEARN consumer
Status: complete; 23/23 declarations reviewed
Last verified: 2026-08-02

This is demand-driven recovery of the pinned mathematics needed by the live
finite self-play consumer.  The independent target proves the exponential-
potential argument over a normalized real vector and defines no probability
law.  A thin adapter packages the vector as the canonical `FinDist`, preserving
both the `GameTheoryMath` dependency boundary and the single-law invariant.

| Pinned path | Declaration | Kind | Disposition | Successor declaration | Evidence | Notes |
|---|---|---|---|---|---|---|
| `OnlineLearning/MultiplicativeWeights.lean` | `cumGain` | definition | adapt | `GameTheoryMath.OnlineLearning.cumGain` | focused build | Same finite cumulative-gain sum. |
| same | `cumGain_zero` | theorem | adapt | `GameTheoryMath.OnlineLearning.cumGain_zero` | focused build | Zero-horizon identity. |
| same | `cumGain_succ` | theorem | adapt | `GameTheoryMath.OnlineLearning.cumGain_succ` | focused build | Successor recurrence. |
| same | `mwWeight` | definition | adapt | `GameTheoryMath.OnlineLearning.weight` | focused build | Unnormalized exponential coordinate; shorter name inside the MW namespace. |
| same | `mwWeight_pos` | theorem | adapt | `GameTheoryMath.OnlineLearning.weight_pos` | focused build | Strict positivity of `Real.exp`. |
| same | `mwDenom` | definition | adapt | `GameTheoryMath.OnlineLearning.denominator` | focused build | Finite partition function. |
| same | `mwDenom_pos` | theorem | adapt | `GameTheoryMath.OnlineLearning.denominator_pos` | focused build | Nonempty finite action set makes the sum positive. |
| same | `mwDenom_zero` | theorem | adapt | `GameTheoryMath.OnlineLearning.denominator_zero` | focused build | Initial partition function is the action cardinality. |
| same | `mwDist` | definition | adapt | `GameTheory.Probability.OnlineLearning.multiplicativeWeights` | adapter build | The normalized vector is packaged directly as `FinDist`, not a parallel `PMF` API. |
| same | `expect_mwDist` | theorem | adapt | `GameTheory.Probability.OnlineLearning.expect_multiplicativeWeights` | adapter build | Canonical expectation agrees with the vector expectation. |
| same | `algGain` | definition | adapt | `GameTheoryMath.OnlineLearning.algorithmGain` | focused build | Sum of per-round vector expectations. |
| same | `algGain_succ` | theorem | adapt | `GameTheoryMath.OnlineLearning.algorithmGain_succ` | focused build | Successor recurrence. |
| same | `bestGain` | definition | adapt | `GameTheoryMath.OnlineLearning.bestGain` | focused build | Finite supremum over actions. |
| same | `onlineExternalRegret` | definition | adapt | `GameTheoryMath.OnlineLearning.externalRegret` | focused build | No game-specific regret concept is introduced. |
| same | `exp_mul_le_of_mem_Icc` | theorem | adapt | `GameTheoryMath.OnlineLearning.exp_mul_le_of_mem_Icc` | focused build | Convex chord bound on `[0,1]`. |
| same | `mwDenom_succ_le` | theorem | adapt | `GameTheoryMath.OnlineLearning.denominator_succ_le` | focused build | One-step potential inequality over vector expectation. |
| same | `mwDenom_le` | theorem | adapt | `GameTheoryMath.OnlineLearning.denominator_le` | focused build | Telescoped potential bound. |
| same | `exp_bestGain_le_mwDenom` | theorem | adapt | `GameTheoryMath.OnlineLearning.exp_bestGain_le_denominator` | focused build | Best action supplies one summand. |
| same | `mw_externalRegret_le` | theorem | adapt | `GameTheoryMath.OnlineLearning.externalRegret_le` | focused build; axiom audit | Fixed-positive-rate external-regret bound. |
| same | `expWeights` | definition | adapt | `GameTheory.Probability.OnlineLearning.exponentialWeights` | adapter build | Score vector is packaged as canonical `FinDist`. |
| same | `mwDist_eq_expWeights` | theorem | adapt | `GameTheory.Probability.OnlineLearning.multiplicativeWeights_eq_exponentialWeights` | adapter build | Equality follows coordinatewise through the representation adapter. |
| same | `exp_sub_one_sub_self_le_sq` | theorem | adapt | `GameTheoryMath.OnlineLearning.exp_sub_one_sub_self_le_sq` | focused build | Quadratic exponential remainder used for tuning. |
| same | `fixedActionRegret_le_onlineExternalRegret` | theorem | adapt | `GameTheoryMath.OnlineLearning.fixedActionRegret_le_externalRegret` | focused build | A fixed action is bounded by best-in-hindsight regret. |

Disposition count: 23 adapt; 0 subsumed; 0 retired; 0 deferred.

Attribution: the pinned proof supplies the finite exponential-potential spine.
The successor changes only ownership and representation: reusable algebra is
law-free, while the sole law-valued declarations use `FinDist.ofWeights`.

Validation:

```text
lake build GameTheoryMath.OnlineLearning GameTheory.Probability.OnlineLearning
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
```
