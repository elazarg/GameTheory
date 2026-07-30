# D-COMM: Communication, babbling, and Electronic Mail

Title: Communication, babbling, and Electronic Mail
Family ID: D-COMM
Pinned roots: `GameTheory/Concepts/Communication/Babbling.lean`; `GameTheory/Concepts/Communication/CheapTalkPublicRandomness.lean`; `GameTheory/Concepts/Communication/CheapTalkPublicRandomnessConstantSum.lean`; `GameTheory/Core/Babbling.lean`; `GameTheory/Languages/ElectronicMailGame.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `2fc8dfc`
Canonical destination: GameTheory.Core.CheapTalk; GameTheory.Examples; GameTheory.Epistemic; Protocol where timing is theorem-observable
Domain contract / decision: D4-D10, D16, D18, EXP-043, EXP-046
Owner: Wave 2 / communication and information
Status: in progress; exact seed, classification pending
Last verified: 2026-07-30

This ledger is an exact generated review queue for the D-COMM family.
No declarations are already accounted for in earlier bounded ledgers. Every
row below is deliberately `unreviewed`: the generated index supplies spelling,
location, kind, and visibility only. It does not infer a mathematical
disposition.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Communication/Babbling.lean` | `babbling_nashFor@32` | theorem | unreviewed | review required | generated index seed only | public, pinned line 32 |
| same | `babbling_nashFor@50` | theorem | unreviewed | review required | generated index seed only | public, pinned line 50 |
| same | `babblingDeviationPreservingFor` | theorem | unreviewed | review required | generated index seed only | public, pinned line 66 |
| same | `babbling_nashFor@78` | theorem | unreviewed | review required | generated index seed only | public, pinned line 78 |
| same | `babbling_nashFor@93` | theorem | unreviewed | review required | generated index seed only | public, pinned line 93 |
| same | `babbling_nash@108` | theorem | unreviewed | review required | generated index seed only | public, pinned line 108 |
| same | `CheapTalkExtension` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 138 |
| same | `game` | def | unreviewed | review required | generated index seed only | public, pinned line 145 |
| same | `babbling_eu` | theorem | unreviewed | review required | generated index seed only | public, pinned line 155 |
| same | `babbling_nash@170` | theorem | unreviewed | review required | generated index seed only | public, pinned line 170 |
| same | `actionProfile_isNash_of_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 184 |
| same | `outcomeKernel_eq_base_nash_outcomeKernel_of_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 198 |
| same | `exists_nash_outcomeKernel_iff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 209 |
| same | `constantSum_eu_eq_base_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 225 |
| same | `zeroSum_eu_eq_base_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 238 |
| `GameTheory/Concepts/Communication/CheapTalkPublicRandomness.lean` | `MessageProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 47 |
| same | `instFiniteGameOutcome` | instance | unreviewed | review required | generated index seed only | public, pinned line 50 |
| same | `mixedMessageMarginal` | def | unreviewed | review required | generated index seed only | public, pinned line 57 |
| same | `mixedMessageLaw` | def | unreviewed | review required | generated index seed only | public, pinned line 63 |
| same | `conditionalCheapTalkStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 71 |
| same | `conditionalCheapTalkProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 78 |
| same | `publicPlay` | def | unreviewed | review required | generated index seed only | public, pinned line 86 |
| same | `actionLaw` | def | unreviewed | review required | generated index seed only | public, pinned line 94 |
| same | `mixedActionLaw` | def | unreviewed | review required | generated index seed only | public, pinned line 100 |
| same | `liftActionDeviation` | def | unreviewed | review required | generated index seed only | public, pinned line 107 |
| same | `actionProfile_update_liftActionDeviation` | theorem | unreviewed | review required | generated index seed only | public, pinned line 112 |
| same | `correlatedEu_actionLaw_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 141 |
| same | `unilateralDeviationDistribution_actionLaw` | theorem | unreviewed | review required | generated index seed only | public, pinned line 166 |
| same | `pmf_map_congr_on_support` | theorem | unreviewed | review required | generated index seed only | private, pinned line 182 |
| same | `mixedStrategyLaw_eq_message_bind_conditional` | theorem | unreviewed | review required | generated index seed only | public, pinned line 193 |
| same | `messageProfile_eq_of_conditionalCheapTalkProfile_ne_zero` | theorem | unreviewed | review required | generated index seed only | public, pinned line 257 |
| same | `actionProfile_map_conditional_eq_pmfPi_publicPlay` | theorem | unreviewed | review required | generated index seed only | public, pinned line 293 |
| same | `mixedActionLaw_eq_publicCorrelatedLaw` | theorem | unreviewed | review required | generated index seed only | public, pinned line 346 |
| same | `InducesPublicSignalNash` | def | unreviewed | review required | generated index seed only | public, pinned line 368 |
| same | `mixedNash_mixedActionLaw_isCorrelatedEq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 380 |
| same | `mixedNash_mixedActionLaw_isCoarseCorrelatedEq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 421 |
| same | `InducesPublicSignalNash.mixedActionLaw_isCorrelatedEq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 430 |
| same | `InducesPublicSignalNash.mixedActionLaw_isCoarseCorrelatedEq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 440 |
| same | `InducesPublicSignalNash.mixedActionLaw_payoff_isMixedNashPayoffMixture` | theorem | unreviewed | review required | generated index seed only | public, pinned line 450 |
| same | `mixedExtension_eu_eq_correlatedEu_mixedActionLaw_of_bounded` | theorem | unreviewed | review required | generated index seed only | public, pinned line 465 |
| same | `mixedExtension_eu_eq_correlatedEu_mixedActionLaw` | theorem | unreviewed | review required | generated index seed only | public, pinned line 496 |
| `GameTheory/Concepts/Communication/CheapTalkPublicRandomnessConstantSum.lean` | `InducesPublicSignalNash.constantSum_mixedExtension_eu_eq_base_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 28 |
| same | `mixedNash_constantSum_mixedExtension_eu_eq_base_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 42 |
| same | `InducesPublicSignalNash.zeroSum_mixedExtension_eu_eq_base_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 55 |
| same | `mixedNash_zeroSum_mixedExtension_eu_eq_base_nash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 67 |
| `GameTheory/Core/Babbling.lean` | `BabblingDeviationPreservingFor@33` | def | unreviewed | review required | generated index seed only | public, pinned line 33 |
| same | `CheapTalkExtension` | structure | unreviewed | review required | generated index seed only | public, pinned line 57 |
| same | `Strategy'` | def | unreviewed | review required | generated index seed only | public, pinned line 66 |
| same | `messageProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 70 |
| same | `actionProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 75 |
| same | `form` | def | unreviewed | review required | generated index seed only | public, pinned line 80 |
| same | `embed` | def | unreviewed | review required | generated index seed only | public, pinned line 87 |
| same | `embedProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 92 |
| same | `proj` | def | unreviewed | review required | generated index seed only | public, pinned line 101 |
| same | `proj_embed` | theorem | unreviewed | review required | generated index seed only | public, pinned line 105 |
| same | `outcomeKernel_embedProfile` | theorem | unreviewed | review required | generated index seed only | public, pinned line 111 |
| same | `messageProfile_update_embedProfile` | theorem | unreviewed | review required | generated index seed only | public, pinned line 116 |
| same | `actionProfile_update_embedProfile` | theorem | unreviewed | review required | generated index seed only | public, pinned line 126 |
| same | `messageProfile_update_sameMessage` | theorem | unreviewed | review required | generated index seed only | public, pinned line 136 |
| same | `actionProfile_update_sameMessage_constPlan` | theorem | unreviewed | review required | generated index seed only | public, pinned line 147 |
| same | `outcomeKernel_update_embedProfile` | theorem | unreviewed | review required | generated index seed only | public, pinned line 158 |
| same | `babblingDeviationPreservingFor@167` | theorem | unreviewed | review required | generated index seed only | public, pinned line 167 |
| `GameTheory/Languages/ElectronicMailGame.lean` | `EmailWorld` | inductive | unreviewed | review required | generated index seed only | public, pinned line 41 |
| same | `<anonymous@47>` | instance | unreviewed | review required | generated index seed only | public, pinned line 47 |
| same | `EmailView` | inductive | unreviewed | review required | generated index seed only | public, pinned line 50 |
| same | `EmailAction` | inductive | unreviewed | review required | generated index seed only | public, pinned line 56 |
| same | `viewOf` | def | unreviewed | review required | generated index seed only | public, pinned line 64 |
| same | `typeProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 71 |
| same | `emailPrior` | def | unreviewed | review required | generated index seed only | public, pinned line 75 |
| same | `attackState` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 79 |
| same | `emailUtility` | def | unreviewed | review required | generated index seed only | public, pinned line 84 |
| same | `game` | def | unreviewed | review required | generated index seed only | public, pinned line 90 |
| same | `attackOnMessage` | def | unreviewed | review required | generated index seed only | public, pinned line 97 |
| same | `trueNeverAttack` | def | unreviewed | review required | generated index seed only | public, pinned line 104 |
| same | `worldPrior` | def | unreviewed | review required | generated index seed only | public, pinned line 108 |
| same | `emailPartition` | def | unreviewed | review required | generated index seed only | public, pinned line 111 |
| same | `attackStateEvent` | def | unreviewed | review required | generated index seed only | public, pinned line 120 |
| same | `viewOf_noMessage` | theorem | unreviewed | review required | generated index seed only | public, pinned line 122 |
| same | `viewOf_onlyFirst_true` | theorem | unreviewed | review required | generated index seed only | public, pinned line 126 |
| same | `viewOf_onlyFirst_false` | theorem | unreviewed | review required | generated index seed only | public, pinned line 129 |
| same | `viewOf_bothConfirmed` | theorem | unreviewed | review required | generated index seed only | public, pinned line 132 |
| same | `EmailWorld_univ` | theorem | unreviewed | review required | generated index seed only | private, pinned line 136 |
| same | `bothConfirmed_mem_mutualPBelief_attackStateEvent` | theorem | unreviewed | review required | generated index seed only | public, pinned line 144 |
| same | `not_commonPBeliefAt_attackStateEvent_bothConfirmed_of_half_lt` | theorem | unreviewed | review required | generated index seed only | public, pinned line 163 |
| same | `exAnte_attackOnMessage_true` | theorem | unreviewed | review required | generated index seed only | public, pinned line 204 |
| same | `exAnte_trueNeverAttack` | theorem | unreviewed | review required | generated index seed only | public, pinned line 221 |
| same | `attackOnMessage_not_bayesNash` | theorem | unreviewed | review required | generated index seed only | public, pinned line 230 |

Before this ledger can become complete, each row must be reviewed against the
canonical successor API and assigned an allowed non-`unreviewed` disposition
with concrete build, theorem, decision, or counterexample evidence. Generated
name similarity is never sufficient.
