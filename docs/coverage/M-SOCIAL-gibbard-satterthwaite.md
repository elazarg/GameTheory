# M-SOCIAL: Gibbard--Satterthwaite

Title: Strategyproof social choice through the canonical Arrow theorem
Family ID: M-SOCIAL
Pinned root: `GameTheory/Mechanism/SocialChoice/GibbardSatterthwaite.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `29e2778`
Canonical destination: `GameTheory.Core.SocialChoice`; `GameTheory.Core.GibbardSatterthwaite`; `GameTheory.Core.Arrow`
Domain contract / decision: D4; post-architecture M-SOCIAL BFS gate
Owner: Wave 2 / Core social choice
Status: complete bounded file; all 39 declarations reviewed with no deferred rows
Last verified: 2026-08-09

The successor states social choice functions over the existing weak linear
rankings.  Strategyproofness tests a unilateral report against the voter's
truthful strict ranking, onto witnesses remain inside the linear domain, and
dictatorship means that the selected alternative is weakly top-ranked by the
dictator.  The proof constructs its raised rankings, staged voter changes, and
induced social-welfare relation privately, then applies the canonical
`Arrow.impossibility`.  It introduces no second ranking, profile, or aggregator
surface and keeps the main theorem free of alternative-carrier finiteness.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Mechanism/SocialChoice/GibbardSatterthwaite.lean` | `IsTop` | def | retired | inline weak-top premise | source/API audit | A second public top predicate is unnecessary beside canonical ranking application. |
| same | `IsTop.unique` | theorem | subsumed | `SocialChoiceFunction.IsDictator.eq_of_forall_ranks` | focused build | Canonical `Rank.Linear` antisymmetry supplies the uniqueness step. |
| same | `raiseTop` | def | retired | private raised-ranking construction | theorem proof | Proof scaffolding is not a second public ranking transformer. |
| same | `raiseTop_above` | theorem | retired | private raised-ranking construction | theorem proof | Internal support for the Arrow reduction. |
| same | `raiseTop_not_above` | theorem | retired | private raised-ranking construction | theorem proof | Internal support for the Arrow reduction. |
| same | `raiseTop_same` | theorem | retired | private raised-ranking construction | theorem proof | Internal support for the Arrow reduction. |
| same | `raiseTop_ranking` | theorem | retired | private `raiseTop_linear` | theorem proof | Linearity is discharged inside the reduction. |
| same | `raiseTop_congr` | theorem | retired | private `raiseTop_congr` | theorem proof | Implementation congruence has no independent consumer. |
| same | `SCF` | abbrev | adapt | `SocialChoiceFunction` | focused Core build | Uses the canonical weak-ranking profile. |
| same | `replacePreference` | def | adapt | `SocialChoiceFunction.replaceRanking` | hostile own-report fixture | Implemented without raw `Function.update`. |
| same | `replacePreference_self` | theorem | adapt | `SocialChoiceFunction.replaceRanking_self` | focused Core build | Transparent own-report law. |
| same | `replacePreference_of_ne` | theorem | adapt | `SocialChoiceFunction.replaceRanking_of_ne` | focused Core build | Other voters are unchanged. |
| same | `replacePreference_restore` | theorem | adapt | `SocialChoiceFunction.replaceRanking_restore` | focused Core build | Replacing a report twice restores the latest report. |
| same | `mixProfile` | def | retired | private `mixRankings` | theorem proof | Finite staged replacement remains proof-local. |
| same | `mixProfile_mem` | theorem | retired | private `mixRankings_of_mem` | theorem proof | Internal finite-voter induction law. |
| same | `mixProfile_not_mem` | theorem | retired | private `mixRankings_of_not_mem` | theorem proof | Internal finite-voter induction law. |
| same | `mixProfile_empty` | theorem | retired | private `mixRankings_empty` | theorem proof | Internal finite-voter induction law. |
| same | `mixProfile_univ` | theorem | retired | private `mixRankings_univ` | theorem proof | Internal finite-voter induction law. |
| same | `mixProfile_insert` | theorem | retired | private `mixRankings_insert` | theorem proof | Internal finite-voter induction law. |
| same | `IsStrategyProof` | def | adapt | `SocialChoiceFunction.IsStrategyProof` | manipulation fixture | Strict improvement is evaluated by the truthful ranking. |
| same | `IsOnto` | def | adapt | `SocialChoiceFunction.IsOnto` | three-report fixture | Range witnesses must be linear profiles. |
| same | `IsDictator` | def | adapt | `SocialChoiceFunction.IsDictator` | hostile nondictatorship fixture | Dictatorship is weak-top choice on every linear profile. |
| same | `IsDictator.eq_of_isTop` | theorem | adapt | `SocialChoiceFunction.IsDictator.eq_of_forall_ranks` | focused build | Uses canonical linear-ranking antisymmetry. |
| same | `monotone_step` | theorem | adapt | `SocialChoiceFunction.IsStrategyProof.monotone_step` | focused build | One report change preserves the selected alternative under the stated comparison. |
| same | `monotone` | theorem | adapt | `SocialChoiceFunction.IsStrategyProof.monotone` | focused build | Finite voter induction composes the one-step law. |
| same | `unanimous` | theorem | adapt | `SocialChoiceFunction.IsStrategyProof.unanimous` | focused build | The weak-top premise is inline, so no private predicate leaks. |
| same | `pareto` | theorem | adapt | `SocialChoiceFunction.IsStrategyProof.pareto` | focused build | Strategyproof full-range choice cannot select a unanimously strictly dominated alternative. |
| same | `lift_winner_beats` | theorem | retired | private pair-lift theorem | theorem proof | Reduction-specific lifting stays private. |
| same | `inducedSWF` | def | retired | private induced canonical `Aggregator` | boundary audit | No parallel public social-welfare-function surface is introduced. |
| same | `induced_choice` | theorem | retired | private induced-choice theorem | theorem proof | Reduction-specific helper. |
| same | `induced_lift_swap` | theorem | retired | private lift-swap theorem | theorem proof | Reduction-specific helper. |
| same | `triple_choice` | theorem | retired | private triple-lift theorem | theorem proof | Reduction-specific helper. |
| same | `induced_isSWO` | theorem | retired | private collective-rationality proof | theorem proof | Targets canonical `Aggregator.IsCollectivelyRational`. |
| same | `induced_isParetoOnRankings` | theorem | retired | private Pareto proof | theorem proof | Targets canonical `Aggregator.IsPareto`. |
| same | `induced_lift_eq` | theorem | retired | private lift equality | theorem proof | Reduction-specific helper. |
| same | `induced_isIIAOnRankings` | theorem | retired | private IIA proof | theorem proof | Targets canonical `Aggregator.IsIIA`. |
| same | `dictator_transfer` | theorem | retired | private dictator-transfer theorem | theorem proof | Transfers the canonical Arrow dictator without exporting reduction machinery. |
| same | `gibbard_satterthwaite` | theorem | adapt | `GibbardSatterthwaite.impossibility` | focused theorem/test build | The main theorem needs finite voters but permits an infinite alternative carrier. |
| same | `gibbard_satterthwaite_of_natCard` | theorem | adapt | `GibbardSatterthwaite.impossibility_of_card` | hostile finite fixture | Finite alternatives occur only in the cardinality convenience theorem. |

Disposition count: 15 adapted, 1 subsumed, and 23 retired.

The hostile one-voter, three-alternative selector reads two pairwise reports.
Three explicit linear rankings make it onto, while a truthful ranking that
selects its bottom alternative has a linear misreport selecting its top.  The
same profile refutes dictatorship, so the fixture catches strict-direction,
truthful-versus-reported, admissible-domain, replacement, and range mistakes.
It also applies the cardinality flagship to an arbitrary strategyproof onto
selector on the same public surface.

Attribution: the pinned file supplies the finite-voter monotonicity and induced
Arrow reduction.  The successor reuses the existing weak `Ranking`,
`Preference.Linear`, canonical `Aggregator`, and `Arrow.impossibility` rather
than recreating the predecessor's strict-ranking social-welfare layer.

Validation: the focused social-choice theorem, Core umbrella, and hostile test
targets build warning-free.  The structural audit reaches the four intended
ranking/SCF/Arrow/flagship inputs through `GameTheory.Core` and rejects all five
probability, strategic-form, Nash, Protocol, and Analysis boundaries from the
focused theorem leaf.  The public surface and fixture depend only on
`propext`, `Classical.choice`, and `Quot.sound`.  Exact coverage returns
`VERIFIED=1` at 68 ledgers and 2,676/8,324 claimed rows.  The warning-clean
default build completes all 3,536 jobs.
