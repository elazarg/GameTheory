# D-LEARN: finite independent self-play

Title: Finite independent self-play and normalization bridge
Family ID: D-LEARN
Pinned roots: `GameTheory/Concepts/Learning/SelfPlay.lean`; `GameTheory/Concepts/Learning/MWSelfPlay.lean`; `GameTheory/Concepts/Learning/Tests.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `a829d9d`
Canonical destination: `GameTheory.Core.Learning`; `GameTheory.Analysis.Learning`; `GameTheory.Analysis.LearningTest`; `GameTheory.Tests.Learning`
Domain contract / decision: D4-D5, D10, F2; EXP-049
Owner: Wave 2 / learning
Status: complete
Last verified: 2026-08-02

The pinned self-play file separates into two layers.  Its finite mathematical
bridge—product play, affine payoff normalization, and the transfer of a
cumulative deviation bound to the canonical approximate CCE—is recovered
directly over `FinDist` and `UtilityGame`. EXP-049 then validated the missing
game-independent finite MW layer in `GameTheoryMath.OnlineLearning`, with
`Probability.OnlineLearning` as its sole `FinDist` adapter. The quantitative
capstone therefore lives in the one-way opt-in `Analysis.Learning` consumer,
while Core remains free of exponential and logarithmic machinery.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Learning/SelfPlay.lean` | `externalRegret_pmfPi` | theorem | adapt | `GameTheory.UtilityGame.externalRegret_pi` | focused Core build; self-play API test | Replaces `KernelGame`, `PMF`, and raw update with `UtilityGame`, `FinDist.pi`, and `Profile.update`. |
| same | `normGain` | def | adapt | `GameTheory.UtilityGame.normGain` | focused Core build | The normalization is now an expected-utility expression over canonical mixed play. |
| same | `expect_eu_update` | theorem | adapt | `GameTheory.UtilityGame.expect_expectedUtility_update` | focused Core build | Own-marginal linearity follows from the canonical affine mixed-play law. |
| same | `normGain_mem_Icc` | theorem | adapt | `GameTheory.UtilityGame.normGain_mem_Icc` | focused Core build | Uses finite-law expectation monotonicity; no finite outcome carrier is stored in the game. |
| same | `expect_normGain` | theorem | adapt | `GameTheory.UtilityGame.expect_normGain` | focused Core build | Retains the affine normalization identity. |
| same | `eu_deviation_eq_W_mul_normGain` | theorem | adapt | `GameTheory.UtilityGame.expectedUtility_deviation_eq_width_mul_normGain` | focused Core build | The payoff-scale identity is stated without a parallel mixed-game evaluator. |
| same | `selfPlay_timeAverage_isεCCE` | theorem | adapt | `GameTheory.UtilityGame.selfPlay_timeAverage_isεCoarseCorrelatedEq` | focused Core and test builds | The target is the sole canonical `IsεCoarseCorrelatedEq`; a product law is only the round-law input. |
| `GameTheory/Concepts/Learning/MWSelfPlay.lean` | `mwScore` | def | adapt | `GameTheory.UtilityGame.mwScore` | EXP-049; focused Analysis build | Structural score recurrence over normalized Core gains, with no game-independent mathematics duplicated. |
| same | `mwProfile` | def | adapt | `GameTheory.UtilityGame.mwProfile` | EXP-049; focused Analysis build | Each player receives the canonical `FinDist` exponential-weights law from the probability adapter. |
| same | `mwScore_eq_cumGain` | theorem | adapt | `GameTheory.UtilityGame.mwScore_eq_cumGain` | focused Analysis build | Identifies the structural recurrence with `GameTheoryMath.OnlineLearning.cumGain`. |
| same | `mwProfile_eq_mwDist` | theorem | adapt | `GameTheory.UtilityGame.mwProfile_eq_multiplicativeWeights` | focused Analysis build | The mathematical identity survives, replacing the predecessor's `PMF` representation with the sole canonical finite-law adapter. |
| same | `mwSelfPlay_timeAverage_isεCCE` | theorem | adapt | `GameTheory.UtilityGame.mwSelfPlay_timeAverage_isεCoarseCorrelatedEq` | focused Analysis build | The fixed-rate MW regret bound composes with the recovered product-law bridge and the canonical approximate CCE predicate. |
| same | `exists_mwSelfPlay_isεCCE` | theorem | adapt | `GameTheory.UtilityGame.exists_mwSelfPlay_isεCoarseCorrelatedEq` | focused Analysis build | An explicit finite-horizon MW trajectory exhibits the law; finite player instances are stated explicitly. |
| same | `mwSelfPlay_exists_isεCCE_of_pos` | theorem | adapt | `GameTheory.UtilityGame.mwSelfPlay_exists_isεCoarseCorrelatedEq_of_pos` | focused Analysis build | A positive tolerance chooses a concrete rate and horizon using only EXP-049's finite exponential remainder estimate. |
| `GameTheory/Concepts/Learning/Tests.lean` | `coordinationGame` | def | subsumed | `GameTheory.Tests.Learning.game` | focused test build | The canonical two-player coordination trace has the same finite Boolean payoff witness without the obsolete `KernelGame.ofPureEU` constructor. |

Attribution: `SelfPlay.lean` supplies the product-law regret identity, payoff
normalization, and reduction plan. `MWSelfPlay.lean` supplies the structural
score/profile recursion and the composition of its regret bound with
self-play. EXP-049 supplies the extracted game-independent cumulative-gain,
exponential-weights, fixed-action-regret, and finite exponential-remainder
proof spine. The successor preserves the mathematics while replacing `PMF`
with the canonical finite-law adapter and retaining a one-way Analysis import.

Validation:

```text
lake build GameTheory.Analysis.LearningTest GameTheory.Tests.Learning
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```

`GameTheory.Core.Learning` remains free of `Real.exp`, `Real.log`, topology,
`PMF`, and raw `Function.update`. The MW consumer imports only Core, the
probability adapter, and the game-independent math module; its conclusions are
finite-horizon certificates, not topology or limit claims. The concrete
two-player test instantiates the arbitrarily-accurate capstone for every
positive tolerance, so the final tuning theorem is checked at its public API
rather than only through its defining-module build.
