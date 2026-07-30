# D-COMM: Communication, babbling, and Electronic Mail

Title: Communication, babbling, and Electronic Mail
Family ID: D-COMM
Pinned roots: `GameTheory/Concepts/Communication/Babbling.lean`; `GameTheory/Concepts/Communication/CheapTalkPublicRandomness.lean`; `GameTheory/Concepts/Communication/CheapTalkPublicRandomnessConstantSum.lean`; `GameTheory/Core/Babbling.lean`; `GameTheory/Languages/ElectronicMailGame.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `2fc8dfc`
Canonical destination: GameTheory.Core.CheapTalk; GameTheory.Examples; GameTheory.Epistemic; Protocol where timing is theorem-observable
Domain contract / decision: D4-D10, D16, D18, EXP-043, EXP-046
Owner: Wave 2 / communication and information
Status: in progress; 32/87 reviewed, 2 deferred to the zero-sum communication gate
Last verified: 2026-07-30

This ledger is an exact generated review queue for the D-COMM family.
No declarations are already accounted for in earlier bounded ledgers. Every
row below is deliberately `unreviewed`: the generated index supplies spelling,
location, kind, and visibility only. It does not infer a mathematical
disposition.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Communication/Babbling.lean` | `babbling_nashFor@32` | theorem | retired | D18 direct projection theorem | EXP-046/D18 | The generic preservation predicate was a proof scaffold, not a surviving public concept. |
| same | `babbling_nashFor@50` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.babbling_isNash` | focused build (1,719 jobs) | Preference-parametric statement recovered through the sole canonical `IsNash`. |
| same | `babblingDeviationPreservingFor` | theorem | retired | D18 rejects a public inert-extension hierarchy | EXP-046/D18 competing design 3 | The old inert-extension instance existed only to feed the retired generic predicate. |
| same | `babbling_nashFor@78` | theorem | retired | D18 rejects a public inert-extension hierarchy | EXP-046/D18 competing design 3 | No live communication consumer earns the generic inert wrapper. |
| same | `babbling_nashFor@93` | theorem | retired | D18 direct cheap-talk theorem | EXP-046/D18 | Generic cross-game preservation is broader than the communication construction and had no surviving consumer. |
| same | `babbling_nash@108` | theorem | retired | D18 direct cheap-talk theorem | EXP-046/D18 | Utility-preservation plumbing is unnecessary when the exact play law is preserved. |
| same | `CheapTalkExtension` | abbrev | subsumed | `GameTheory.GameForm.CheapTalkExtension` | focused build (1,719 jobs) | Utility is separate data in v2; the canonical construction attaches directly to the form. |
| same | `game` | def | retired | use `C.form` with `euPreference G.utility` | D4 and D18 | Rebundling the same evaluator would recreate a parallel utility-game surface. |
| same | `babbling_eu` | theorem | subsumed | `GameTheory.GameForm.CheapTalkExtension.form_play_update_embedProfile` | focused build (1,719 jobs) | Equality of complete outcome laws is stronger than the EU specialization. |
| same | `babbling_nash@170` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.babbling_isNash` | focused build (1,719 jobs) | Instantiate the generic preference with `euPreference`; no utility-specific Nash predicate remains. |
| same | `actionProfile_isNash_of_nash` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.actionProfile_isNash_of_isNash` | focused build (1,719 jobs) | Recovered for arbitrary weak preferences. |
| same | `outcomeKernel_eq_base_nash_outcomeKernel_of_nash` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.exists_base_isNash_play_eq_of_isNash` | focused build (1,719 jobs) | Recovered for the canonical finite outcome law. |
| same | `exists_nash_outcomeKernel_iff` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.exists_isNash_play_iff` | focused build (1,719 jobs) | Exact pure-Nash outcome-law preservation is recovered preference-parametrically. |
| same | `constantSum_eu_eq_base_nash` | theorem | deferred | S-ZERO/D-COMM constant-sum value slice | D18; post-architecture zero-sum lane | Reopen with the constant-sum API and prove the communication value corollary without a wrapper game. |
| same | `zeroSum_eu_eq_base_nash` | theorem | deferred | S-ZERO/D-COMM zero-sum value slice | D18; post-architecture zero-sum lane | Reopen from saddle-point value uniqueness after the pure/mixed bridge is fixed. |
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
| `GameTheory/Core/Babbling.lean` | `BabblingDeviationPreservingFor@33` | def | retired | D18 direct projection theorem | EXP-046/D18 | The predicate duplicated no mathematical object and existed only to abstract one proof. |
| same | `CheapTalkExtension` | structure | adapt | `GameTheory.GameForm.CheapTalkExtension` | EXP-046/D18; focused build | Recovered with explicit universes and the canonical signature/profile surface. |
| same | `Strategy'` | def | adapt | `GameTheory.GameForm.CheapTalkExtension.Strategy` | focused build (1,719 jobs) | Message plus a plan over the complete public message profile. |
| same | `messageProfile` | def | adapt | `GameTheory.GameForm.CheapTalkExtension.messageProfile` | focused build (1,719 jobs) | Canonical dependent profile. |
| same | `actionProfile` | def | adapt | `GameTheory.GameForm.CheapTalkExtension.actionProfile` | focused build (1,719 jobs) | Canonical induced base profile. |
| same | `form` | def | adapt | `GameTheory.GameForm.CheapTalkExtension.form` | focused build (1,719 jobs) | Recovered as a reducible literal `GameForm` with no second evaluator. |
| same | `embed` | def | adapt | `GameTheory.GameForm.CheapTalkExtension.embed` | focused build (1,719 jobs) | Canonical babbling strategy. |
| same | `embedProfile` | def | adapt | `GameTheory.GameForm.CheapTalkExtension.embedProfile` | focused build (1,719 jobs) | Coordinatewise canonical embedding. |
| same | `proj` | def | adapt | `GameTheory.GameForm.CheapTalkExtension.project` | focused build (1,719 jobs) | Renamed descriptively; uses only canonical `Profile.update`. |
| same | `proj_embed` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.project_embed` | focused build (1,719 jobs) | Exact section law recovered. |
| same | `outcomeKernel_embedProfile` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.form_play_embedProfile` | focused build (1,719 jobs) | Exact finite outcome-law equality in the successor representation. |
| same | `messageProfile_update_embedProfile` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.messageProfile_update_embedProfile` | focused build (1,719 jobs) | Hostile message-plus-plan deviation law recovered. |
| same | `actionProfile_update_embedProfile` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.actionProfile_update_embedProfile` | focused build (1,719 jobs) | The hostile deviation projects to one base deviation. |
| same | `messageProfile_update_sameMessage` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.messageProfile_update_sameMessage` | focused build (1,719 jobs) | Same-message deviation law recovered generically. |
| same | `actionProfile_update_sameMessage_constPlan` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.actionProfile_update_sameMessage_constPlan` | focused build (1,719 jobs) | This law drives the converse Nash theorem. |
| same | `outcomeKernel_update_embedProfile` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.form_play_update_embedProfile` | focused build (1,719 jobs) | Exact finite outcome-law equality in the successor representation. |
| same | `babblingDeviationPreservingFor@167` | theorem | retired | `GameTheory.GameForm.CheapTalkExtension.babbling_isNash` | EXP-046/D18 | The direct theorem eliminates its single-use proof predicate. |
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
