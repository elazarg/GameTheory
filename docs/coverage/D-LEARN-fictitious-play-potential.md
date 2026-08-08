# D-LEARN: fictitious play in exact-potential games

Title: Empirical-potential route to approximate Nash
Family ID: D-LEARN
Pinned root: `GameTheory/Concepts/Learning/FictitiousPlayPotential.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `f2dbd5c`
Canonical destinations: `GameTheory.Core.FictitiousPlay`, `GameTheory.Core.FictitiousPlayPotential`, future `GameTheory.Analysis.FictitiousPlayPotential`
Domain contract / decision: D4-D5, D10, D21
Owner: Wave 2 / learning dynamics
Status: partial; 45/45 declarations classified, finite recurrence spine recovered
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
| same | `mixedPotential_abs_le_of_abs_bound` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Needed for Lyapunov boundedness, not Core recurrence. |
| same | `exists_profile_abs_bound` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Finite pure-profile bound. |
| same | `mixedPotential_update_empiricalMarginal_succ_abs_sub_le` | theorem | deferred | exact-potential Analysis continuation | dependency gate | First error estimate. |
| same | `mixedPotential_pureGain_update_empiricalMarginal_succ_abs_sub_le` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Cross-coordinate error estimate. |
| same | `mixedPotentialPureGain_update_empiricalMarginal_succ_self_abs_sub_le` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Self-coordinate error estimate. |
| same | `mixedPotentialPureGain_update_empiricalMarginal_succ_abs_sub_le` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Uniform coordinate estimate. |
| same | `mixedPotentialPureGain_foldl_update_empiricalMarginal_succ_abs_sub_le` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Finite sweep estimate. |
| same | `mixedPotential_foldl_update_empiricalMarginal_succ_sub_ge` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Lyapunov sweep lower bound. |
| same | `foldl_update_empiricalMarginal_succ_eq_belief_succ` | theorem | deferred | exact-potential Analysis continuation | dependency gate | All-player update identity. |
| same | `mixedPotentialPureGain_belief_succ_abs_sub_le` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Consecutive-belief stability. |
| same | `IsExactPotential.mixedGain_belief_succ_abs_sub_le` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Transfers potential stability to utility gain. |
| same | `IsExactPotential.fictitiousPlayPlayedGain_succ_abs_sub_le` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Aggregate-gain regularity. |
| same | `IsExactPotential.mixedPotential_belief_succ_sub_ge` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Main Lyapunov lower bound. |
| same | `IsExactPotential.summable_one_div_mul_fictitiousPlayPlayedGain` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Summability conclusion. |
| same | `frequently_lt_of_summable_one_div_mul` | theorem | deferred | `GameTheoryMath` candidate | upstreamability review | General sequence lemma must remain game-independent. |
| same | `tendsto_zero_of_summable_one_div_mul_of_succ_abs_sub_le` | theorem | deferred | `GameTheoryMath` candidate | upstreamability review | General Tauberian-style sequence lemma. |
| same | `IsExactPotential.frequently_fictitiousPlayPlayedGain_lt` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Consequence of summability. |
| same | `IsExactPotential.fictitiousPlayPlayedGain_tendsto_zero` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Central convergence lemma. |
| same | `IsFictitiousPlay.fictitiousPlayWeightedPlayedGain_nonneg` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Weighted finite-sum order. |
| same | `IsFictitiousPlay.fictitiousPlayWeightedPlayedGain_le_cardSum_mul_playedGain` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Cardinality comparison. |
| same | `IsExactPotential.fictitiousPlayWeightedPlayedGain_tendsto_zero` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Weighted convergence. |
| same | `IsExactPotential.mixedImprovement_belief_tendsto_zero_of_abs_bound` | theorem | deferred | exact-potential Analysis continuation | flagship chain | Direct predecessor of approximate Nash. |
| same | `IsExactPotential.mixedImprovement_belief_tendsto_zero` | theorem | deferred | exact-potential Analysis continuation | flagship chain | Finite-profile boundedness specialization. |
| same | `IsExactPotential.eventually_isεNash_of_isFictitiousPlay_of_abs_bound` | theorem | deferred | exact-potential Analysis continuation | flagship chain | Explicit-bound flagship. |
| same | `IsExactPotential.eventually_isεNash_of_isFictitiousPlay` | theorem | deferred | exact-potential Analysis continuation | flagship chain | Release capability target. |
| same | `IsFictitiousPlay.eventually_isεNash_of_weightedPlayedGain_tendsto_zero` | theorem | deferred | exact-potential Analysis continuation | dependency gate | Generic final bridge from the weighted gain. |
| same | `IsWeightedExactPotential.isFictitiousPlay_iff_finitePotentialTeamGame` | theorem | deferred | S-POT weighted-potential gate | ownership classification | Weighted potential has not earned a native owner. |
| same | `IsExactPotential.isFictitiousPlay_iff_finitePotentialTeamGame` | theorem | subsumed | direct canonical exact-potential recurrence | design comparison | The synthetic team game is retired. |
| same | `IsWeightedExactPotential.isεNash_of_finitePotentialTeamGame_isεNash` | theorem | deferred | S-POT weighted-potential gate | ownership classification | No surrogate-game transfer will be introduced. |
| same | `IsWeightedExactPotential.eventually_isεNash_of_isFictitiousPlay` | theorem | deferred | S-POT weighted-potential gate | ownership classification | Reconsider only after weighted semantics passes its gate. |

Attribution: the pinned file supplies the played-gain Lyapunov strategy, the
one-coordinate recurrence, the finite sweep/error estimates, and the
summability-to-approximate-Nash chain.  The successor has recovered the entire
finite recurrence spine over canonical `FinDist` and exact potential without
the predecessor's PMF products, synthetic team game, or stored outcome
finiteness.  The remaining direct path is intentionally concentrated in the
Analysis continuation rather than scattered through Core.

Validation:

```text
lake build GameTheory.Core.FictitiousPlay GameTheory.Core.FictitiousPlayPotential GameTheory.Tests.FictitiousPlayPotential
git diff --check
```

The hostile fixture has one inferior initial action and a strict best action
thereafter.  Its first played gain is `1`, its first potential increment is
`1/2`, and the generic improvement bound is specialized on the same genuine
fictitious-play path.

