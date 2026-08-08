# D-LEARN: fictitious play in exact-potential games

Title: Empirical-potential route to approximate Nash
Family ID: D-LEARN
Pinned root: `GameTheory/Concepts/Learning/FictitiousPlayPotential.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `f2dbd5c`
Canonical destinations: `GameTheory.Core.FictitiousPlay`, `GameTheory.Core.FictitiousPlayPotential`, future `GameTheory.Analysis.FictitiousPlayPotential`
Domain contract / decision: D4-D5, D10, D21
Owner: Wave 2 / learning dynamics
Status: partial only at the weighted-potential gate; exact-potential convergence recovered
Last verified: 2026-08-09

The successor takes the direct route from canonical mixed expected utility and
mixed potential.  Played gains and empirical recurrences are topology-free and
therefore live in Core.  The boundedness, summability, and convergence chain is
reserved for the opt-in Analysis consumer.  The predecessor's synthetic
identical-interest comparison game is not revived; exact potential already
identifies utility and potential increments on the canonical mixed form.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Learning/FictitiousPlayPotential.lean` | `fictitiousPlayPlayedGain` | def | adapt | `GameTheory.UtilityGame.aggregatePlayedGain` | focused Core/test build | Per-player `playedGain` is also exposed, avoiding repeated summand expressions. |
| same | `fictitiousPlayWeightedPlayedGain` | def | adapt | `GameTheory.UtilityGame.weightedPlayedGain` | focused Core/test build | Cardinality weighting is theorem-local. |
| same | `IsFictitiousPlay.playedGain_nonneg` | theorem | adapt | `GameTheory.UtilityGame.IsFictitiousPlay.playedGain_nonneg` | hostile improving trace | Uses expected own gain zero; no `Fintype.ofFinite`. |
| same | `IsFictitiousPlay.fictitiousPlayPlayedGain_nonneg` | theorem | adapt | `GameTheory.UtilityGame.IsFictitiousPlay.aggregatePlayedGain_nonneg` | focused Core build | Finite player sum. |
| same | `IsFictitiousPlay.mixedImprovement_le_weightedPlayedGain` | theorem | adapt | same name under `GameTheory.UtilityGame.IsFictitiousPlay` | hostile improving trace | Consumes canonical mixed-improvement certificate. |
| same | `mixedExtension_eu_update_empiricalMarginal_succ` | theorem | adapt | `GameTheory.UtilityGame.expectedUtility_update_empiricalMarginal_succ` | focused Core build | Canonical mixed form, arbitrary outcome carrier. |
| same | `mixedExtension_eu_update_empiricalMarginal_succ_sub` | theorem | adapt | `GameTheory.UtilityGame.expectedUtility_update_empiricalMarginal_succ_sub` | focused Core build | Difference form. |
| same | `mixedExtension_eu_belief_update_empiricalMarginal_succ_sub` | theorem | adapt | `GameTheory.UtilityGame.expectedUtility_belief_update_empiricalMarginal_succ_sub` | focused Core build | Identifies the increment with `playedGain`. |
| same | `IsTeamGame.mixedExtension_eu_belief_update_empiricalMarginal_succ_sub` | theorem | adapt | `GameTheory.UtilityGame.IsTeamGame.expectedUtility_belief_update_empiricalMarginal_succ_sub` | focused Core build | Common-payoff observer generalization. |
| same | `mixedPotential_update_empiricalMarginal_succ` | theorem | adapt | `GameTheory.UtilityGame.mixedPotential_update_empiricalMarginal_succ` | focused Core build | Affine empirical update. |
| same | `mixedPotential_update_empiricalMarginal_succ_sub` | theorem | adapt | `GameTheory.UtilityGame.mixedPotential_update_empiricalMarginal_succ_sub` | focused Core build | Difference form. |
| same | `mixedPotentialPureGain` | def | adapt | `GameTheory.UtilityGame.mixedPotentialGain` | focused Core build | Shorter canonical name. |
| same | `mixedPotential_update_empiricalMarginal_succ_sub_of_eq` | theorem | adapt | same descriptive theorem under `GameTheory.UtilityGame` | focused Core build | Coordinate-equality form. |
| same | `IsExactPotential.mixedPotential_belief_update_empiricalMarginal_succ_sub` | theorem | adapt | same descriptive theorem under `GameTheory.UtilityGame.IsExactPotential` | nonzero half-step witness | The first empirical step is verified as `1/2`. |
| same | `IsExactPotential.mixedPotentialPureGain_eq_mixedGain` | theorem | adapt | `GameTheory.UtilityGame.IsExactPotential.mixedPotentialGain_eq_mixedGain` | focused Core build | Direct canonical exact-potential identity. |
| same | `mixedPotential_abs_le_of_abs_bound` | theorem | adapt | `GameTheory.UtilityGame.mixedPotential_abs_le_of_abs_bound` | focused Core build | Generic `FinDist` support bound removes finite carrier assumptions. |
| same | `exists_profile_abs_bound` | theorem | adapt | `GameTheory.UtilityGame.exists_profile_abs_bound` | focused Core build | Explicit `Fintype` is required only here. |
| same | `mixedPotential_update_empiricalMarginal_succ_abs_sub_le` | theorem | adapt | same name under `GameTheory.UtilityGame` | nonzero improving trace | Sharp one-coordinate `2C/(t+2)` estimate. |
| same | `mixedPotential_pureGain_update_empiricalMarginal_succ_abs_sub_le` | theorem | adapt | `GameTheory.UtilityGame.mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le_of_ne` | focused Core build | Cross-coordinate `4C/(t+2)` estimate. |
| same | `mixedPotentialPureGain_update_empiricalMarginal_succ_self_abs_sub_le` | theorem | adapt | `GameTheory.UtilityGame.mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le_self` | focused Core build | Stronger `2C/(t+2)` self-coordinate estimate. |
| same | `mixedPotentialPureGain_update_empiricalMarginal_succ_abs_sub_le` | theorem | adapt | `GameTheory.UtilityGame.mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le` | hostile self-coordinate specialization | Uniform coordinate estimate. |
| same | `mixedPotentialPureGain_foldl_update_empiricalMarginal_succ_abs_sub_le` | theorem | adapt | `GameTheory.UtilityGame.mixedPotentialGain_advanceMarginals_abs_sub_le` | focused Core build | Duplicate-free finite sweep over a named `advanceMarginals`. |
| same | `mixedPotential_foldl_update_empiricalMarginal_succ_sub_ge` | theorem | adapt | `GameTheory.UtilityGame.mixedPotential_advanceMarginals_sub_ge` | focused Core build | First-order sum minus quadratic error. |
| same | `foldl_update_empiricalMarginal_succ_eq_belief_succ` | theorem | adapt | `GameTheory.UtilityGame.advanceMarginals_univ_eq_empiricalBelief_succ` | hostile first sweep | Uses general `Profile.foldl_update_eq`, not a PMF-product helper. |
| same | `mixedPotentialPureGain_belief_succ_abs_sub_le` | theorem | adapt | `GameTheory.UtilityGame.mixedPotentialGain_empiricalBelief_succ_abs_sub_le` | focused Core build | Whole-belief stability. |
| same | `IsExactPotential.mixedGain_belief_succ_abs_sub_le` | theorem | adapt | `GameTheory.UtilityGame.IsExactPotential.mixedGain_empiricalBelief_succ_abs_sub_le` | focused Core build | Transfers potential stability to canonical utility gain. |
| same | `IsExactPotential.fictitiousPlayPlayedGain_succ_abs_sub_le` | theorem | adapt | `GameTheory.UtilityGame.IsExactPotential.aggregatePlayedGain_succ_abs_sub_le` | focused Core build | Uses consecutive best-response comparisons. |
| same | `IsExactPotential.mixedPotential_belief_succ_sub_ge` | theorem | adapt | `GameTheory.UtilityGame.IsExactPotential.mixedPotential_empiricalBelief_succ_sub_ge` | nonzero first-gain witness | Complete topology-free Lyapunov lower bound. |
| same | `IsExactPotential.summable_one_div_mul_fictitiousPlayPlayedGain` | theorem | adapt | `GameTheory.UtilityGame.IsExactPotential.summable_harmonic_aggregatePlayedGain` | focused Analysis build | Telescoping Lyapunov sum plus square-summable error. |
| same | `frequently_lt_of_summable_one_div_mul` | theorem | adapt | `GameTheoryMath.frequently_lt_of_summable_one_div_mul` | focused GameTheoryMath build | General sequence lemma is game-independent. |
| same | `tendsto_zero_of_summable_one_div_mul_of_succ_abs_sub_le` | theorem | adapt | `GameTheoryMath.tendsto_zero_of_summable_one_div_mul_of_succ_abs_sub_le` | focused GameTheoryMath build | General harmonic-energy Tauberian estimate. |
| same | `IsExactPotential.frequently_fictitiousPlayPlayedGain_lt` | theorem | adapt | `GameTheory.UtilityGame.IsExactPotential.frequently_aggregatePlayedGain_lt` | focused Analysis build | Consequence of summability. |
| same | `IsExactPotential.fictitiousPlayPlayedGain_tendsto_zero` | theorem | adapt | `GameTheory.UtilityGame.IsExactPotential.aggregatePlayedGain_tendsto_zero` | focused Analysis build | Central convergence lemma. |
| same | `IsFictitiousPlay.fictitiousPlayWeightedPlayedGain_nonneg` | theorem | adapt | `GameTheory.UtilityGame.IsFictitiousPlay.weightedPlayedGain_nonneg` | focused Analysis build | Weighted finite-sum order. |
| same | `IsFictitiousPlay.fictitiousPlayWeightedPlayedGain_le_cardSum_mul_playedGain` | theorem | adapt | `GameTheory.UtilityGame.IsFictitiousPlay.weightedPlayedGain_le_cardSum_mul_aggregate` | focused Analysis build | Cardinality comparison. |
| same | `IsExactPotential.fictitiousPlayWeightedPlayedGain_tendsto_zero` | theorem | adapt | `GameTheory.UtilityGame.IsExactPotential.weightedPlayedGain_tendsto_zero` | focused Analysis build | Squeeze from aggregate convergence. |
| same | `IsExactPotential.mixedImprovement_belief_tendsto_zero_of_abs_bound` | theorem | adapt | `GameTheory.UtilityGame.IsExactPotential.mixedImprovement_empiricalBelief_tendsto_zero_of_abs_bound` | focused Analysis build | Direct predecessor of approximate Nash. |
| same | `IsExactPotential.mixedImprovement_belief_tendsto_zero` | theorem | adapt | `GameTheory.UtilityGame.IsExactPotential.mixedImprovement_empiricalBelief_tendsto_zero` | hostile analytic consumer | Finite-profile boundedness specialization. |
| same | `IsExactPotential.eventually_isεNash_of_isFictitiousPlay_of_abs_bound` | theorem | adapt | same name under `GameTheory.UtilityGame.IsExactPotential` | focused Analysis build | Explicit-bound flagship. |
| same | `IsExactPotential.eventually_isεNash_of_isFictitiousPlay` | theorem | adapt | same name under `GameTheory.UtilityGame.IsExactPotential` | nonstationary hostile consumer | Release capability target. |
| same | `IsFictitiousPlay.eventually_isεNash_of_weightedPlayedGain_tendsto_zero` | theorem | adapt | same name under `GameTheory.UtilityGame.IsFictitiousPlay` | focused Analysis build | Generic final bridge from weighted gain. |
| same | `IsWeightedExactPotential.isFictitiousPlay_iff_finitePotentialTeamGame` | theorem | deferred | S-POT weighted-potential gate | ownership classification | Weighted potential has not earned a native owner. |
| same | `IsExactPotential.isFictitiousPlay_iff_finitePotentialTeamGame` | theorem | subsumed | direct canonical exact-potential recurrence | design comparison | The synthetic team game is retired. |
| same | `IsWeightedExactPotential.isεNash_of_finitePotentialTeamGame_isεNash` | theorem | deferred | S-POT weighted-potential gate | ownership classification | No surrogate-game transfer will be introduced. |
| same | `IsWeightedExactPotential.eventually_isεNash_of_isFictitiousPlay` | theorem | deferred | S-POT weighted-potential gate | ownership classification | Reconsider only after weighted semantics passes its gate. |

Attribution: the pinned file supplies the played-gain Lyapunov strategy, the
one-coordinate recurrence, the finite sweep/error estimates, and the
summability-to-approximate-Nash chain.  The successor has recovered the full
topology-free recurrence, estimate, and Lyapunov spine over canonical `FinDist`
and exact
potential without the predecessor's PMF products, synthetic team game, or
stored outcome finiteness.  The exact-potential convergence path is complete;
only the three declarations that genuinely require weighted-potential semantics
remain behind the named S-POT gate.

Validation:

```text
lake build GameTheory.Core.FictitiousPlay GameTheory.Core.FictitiousPlayPotential GameTheory.Tests.FictitiousPlayPotential
lake build GameTheoryMath.HarmonicSequence GameTheory.Analysis.FictitiousPlayPotential GameTheory.Analysis.FictitiousPlayPotentialTest
git diff --check
```

The hostile fixture has one inferior initial action and a strict best action
thereafter.  Its first played gain is `1`, its first potential increment is
`1/2`, and the generic improvement bound is specialized on the same genuine
fictitious-play path.
