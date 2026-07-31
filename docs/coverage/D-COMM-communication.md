# D-COMM: Communication, babbling, and Electronic Mail

Title: Communication, babbling, and Electronic Mail
Family ID: D-COMM
Pinned roots: `GameTheory/Concepts/Communication/Babbling.lean`; `GameTheory/Concepts/Communication/CheapTalkPublicRandomness.lean`; `GameTheory/Concepts/Communication/CheapTalkPublicRandomnessConstantSum.lean`; `GameTheory/Core/Babbling.lean`; `GameTheory/Languages/ElectronicMailGame.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `2fc8dfc`
Canonical destination: GameTheory.Core.CheapTalk; GameTheory.Examples; GameTheory.Epistemic; Protocol where timing is theorem-observable
Domain contract / decision: D4-D10, D16, D18, EXP-043, EXP-046
Owner: Wave 2 / communication and information
Status: in progress; 87/87 reviewed, 19 deferred to public-signal and zero-sum gates
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
| `GameTheory/Concepts/Communication/CheapTalkPublicRandomness.lean` | `MessageProfile` | abbrev | retired | use `Profile C.messageSignature` | D18/D19 | The abbreviation duplicates the canonical dependent profile type. |
| same | `instFiniteGameOutcome` | instance | retired | no successor instance | D9 and D19 | The extension retains the base outcome type definitionally, and finite laws do not require a global finite outcome capability. |
| same | `mixedMessageMarginal` | def | deferred | D-COMM public-signal disintegration slice | D19 scope boundary | Reopen when a live theorem needs message-conditioned representation through `FinDist.condOnFibre`. |
| same | `mixedMessageLaw` | def | deferred | D-COMM public-signal disintegration slice | D19 scope boundary | The correlation theorem does not require a separate public-signal object. |
| same | `conditionalCheapTalkStrategy` | def | deferred | D-COMM public-signal disintegration slice | D19 scope boundary | Reopen together with a proved finite-law disintegration. |
| same | `conditionalCheapTalkProfile` | def | deferred | D-COMM public-signal disintegration slice | D19 scope boundary | Reopen together with the message support theorem. |
| same | `publicPlay` | def | deferred | D-COMM public-signal disintegration slice | D19 scope boundary | A conditional mixed profile is not needed for mixed-Nash-to-CE. |
| same | `actionLaw` | def | retired | `GameTheory.GameForm.CheapTalkExtension.mixedActionLaw` | EXP-047/D19 | The arbitrary-law helper had no independent consumer; the live bridge maps the canonical independent mixed law directly. |
| same | `mixedActionLaw` | def | adapt | `GameTheory.GameForm.CheapTalkExtension.mixedActionLaw` | EXP-047/D19; focused build | Recovered over the canonical `FinDist.pi`. |
| same | `liftActionDeviation` | def | adapt | `GameTheory.GameForm.CheapTalkExtension.liftActionDeviation` | EXP-047/D19; focused build | Retains the message and maps every contingent action. |
| same | `actionProfile_update_liftActionDeviation` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.actionProfile_update_liftActionDeviation` | focused build (1,720 jobs) | Exact hostile profile commutation recovered. |
| same | `correlatedEu_actionLaw_eq` | theorem | subsumed | `GameTheory.GameForm.CheapTalkExtension.mixed_play_eq_outcomeLaw_mixedActionLaw` | EXP-047/D19 | Equality of complete finite outcome laws is stronger than the utility-specific equality needed by the live mixed consumer. |
| same | `unilateralDeviationDistribution_actionLaw` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.mixedActionLaw_update_map_liftActionDeviation` | EXP-047/D19 | Narrowed to the canonical independent mixed law and strengthened to preference-free exact equality. |
| same | `pmf_map_congr_on_support` | theorem | retired | `FinDist` extensionality and map laws | D9/D19 | Private PMF implementation detail is unnecessary in the finite-law proof. |
| same | `mixedStrategyLaw_eq_message_bind_conditional` | theorem | deferred | D-COMM public-signal disintegration slice | D19 scope boundary | This is the central deferred disintegration statement. |
| same | `messageProfile_eq_of_conditionalCheapTalkProfile_ne_zero` | theorem | deferred | D-COMM public-signal disintegration slice | D19 scope boundary | Reopen only with the conditional strategy law. |
| same | `actionProfile_map_conditional_eq_pmfPi_publicPlay` | theorem | deferred | D-COMM public-signal disintegration slice | D19 scope boundary | Reopen only with the conditional action representation. |
| same | `mixedActionLaw_eq_publicCorrelatedLaw` | theorem | deferred | D-COMM public-signal disintegration slice | D19 scope boundary | D19 proves correlation directly and does not claim this stronger representation theorem. |
| same | `InducesPublicSignalNash` | def | deferred | D-COMM public-signal disintegration slice | D19 scope boundary | Admit only if a conditional public-regime consumer earns the named predicate. |
| same | `mixedNash_mixedActionLaw_isCorrelatedEq` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.mixedNash_mixedActionLaw_isCorrelatedEq` | EXP-047/D19; focused build | Recovered for arbitrary weak preferences and without a finite outcome assumption. |
| same | `mixedNash_mixedActionLaw_isCoarseCorrelatedEq` | theorem | adapt | `GameTheory.GameForm.CheapTalkExtension.mixedNash_mixedActionLaw_isCoarseCorrelatedEq` | EXP-047/D19; focused build | Recovered from the canonical CE-to-CCE implication. |
| same | `InducesPublicSignalNash.mixedActionLaw_isCorrelatedEq` | theorem | deferred | D-COMM public-signal disintegration slice | D19 scope boundary | Depends on the deferred public-signal regime. |
| same | `InducesPublicSignalNash.mixedActionLaw_isCoarseCorrelatedEq` | theorem | deferred | D-COMM public-signal disintegration slice | D19 scope boundary | Depends on the deferred public-signal regime. |
| same | `InducesPublicSignalNash.mixedActionLaw_payoff_isMixedNashPayoffMixture` | theorem | deferred | D-COMM/S-MIX public-signal payoff-mixture slice | D19 scope boundary | Reopen after the conditional regime and payoff-mixture API have live consumers. |
| same | `mixedExtension_eu_eq_correlatedEu_mixedActionLaw_of_bounded` | theorem | subsumed | `GameTheory.GameForm.CheapTalkExtension.mixed_play_eq_outcomeLaw_mixedActionLaw` | EXP-047/D19 | Exact outcome-law equality removes boundedness and utility specialization. |
| same | `mixedExtension_eu_eq_correlatedEu_mixedActionLaw` | theorem | subsumed | `GameTheory.GameForm.CheapTalkExtension.mixed_play_eq_outcomeLaw_mixedActionLaw` | EXP-047/D19 | The finite-outcome wrapper is unnecessary in the canonical finite-law representation. |
| `GameTheory/Concepts/Communication/CheapTalkPublicRandomnessConstantSum.lean` | `InducesPublicSignalNash.constantSum_mixedExtension_eu_eq_base_nash` | theorem | deferred | S-ZERO/D-COMM constant-sum public-signal value slice | D19 scope boundary | Requires both the deferred public regime and the constant-sum value API. |
| same | `mixedNash_constantSum_mixedExtension_eu_eq_base_nash` | theorem | deferred | S-ZERO/D-COMM constant-sum mixed-value slice | D19; zero-sum lane | Reopen from value uniqueness without introducing a communication-specific game wrapper. |
| same | `InducesPublicSignalNash.zeroSum_mixedExtension_eu_eq_base_nash` | theorem | deferred | S-ZERO/D-COMM zero-sum public-signal value slice | D19 scope boundary | Requires both the deferred public regime and the zero-sum value bridge. |
| same | `mixedNash_zeroSum_mixedExtension_eu_eq_base_nash` | theorem | deferred | S-ZERO/D-COMM zero-sum mixed-value slice | D19; zero-sum lane | Reopen from saddle-point value uniqueness and the canonical induced action law. |
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
| `GameTheory/Languages/ElectronicMailGame.lean` | `EmailWorld` | inductive | adapt | `GameTheory.Examples.ElectronicMail.EmailWorld` | EXP-048/D20; focused build | Endpoint state carrier recovered under Examples rather than a language root. |
| same | `<anonymous@47>` | instance | retired | no successor instance | D9 and EXP-048 | The old `Nonempty` instance existed for its probability constructor; the canonical explicit finite law needs no stored capability. |
| same | `EmailView` | inductive | adapt | `GameTheory.Examples.ElectronicMail.EmailView` | EXP-048/D20; focused build | Private observation carrier recovered. |
| same | `EmailAction` | inductive | adapt | `GameTheory.Examples.ElectronicMail.EmailAction` | EXP-048/D20; focused build | Coordinated-attack action carrier recovered. |
| same | `viewOf` | def | adapt | `GameTheory.Examples.ElectronicMail.viewOf` | focused build (1,725 jobs) | Endpoint observation law recovered. |
| same | `typeProfile` | def | adapt | `GameTheory.Examples.ElectronicMail.typeProfile` | focused build (1,725 jobs) | Canonical dependent type profile. |
| same | `emailPrior` | def | adapt | `GameTheory.Examples.ElectronicMail.emailPrior` | EXP-048/D20 | Now explicitly the pushforward of the shared canonical world law. |
| same | `attackState` | abbrev | adapt | `GameTheory.Examples.ElectronicMail.attackState` | focused build (1,725 jobs) | Payoff-relevant type event recovered. |
| same | `emailUtility` | def | adapt | `GameTheory.Examples.ElectronicMail.emailPayoff` | focused build (1,725 jobs) | Renamed to match the canonical `BayesianGame.payoff` field. |
| same | `game` | def | adapt | `GameTheory.Examples.ElectronicMail.game` | EXP-048/D20; focused build | Canonical static `BayesianGame`, not a communication-local game type. |
| same | `attackOnMessage` | def | adapt | `GameTheory.Examples.ElectronicMail.attackOnMessage` | focused build (1,725 jobs) | Canonical type-contingent plan. |
| same | `trueNeverAttack` | def | adapt | `GameTheory.Examples.ElectronicMail.trueNeverAttack` | focused build (1,725 jobs) | Canonical unilateral replacement plan. |
| same | `worldPrior` | def | adapt | `GameTheory.Examples.ElectronicMail.worldPrior` | EXP-048/D20 | Strengthened from a real weight function to the canonical uniform `FinDist`, shared by both subfields. |
| same | `emailPartition` | def | adapt | `GameTheory.Examples.ElectronicMail.emailPartition` | EXP-048/D20; focused build | Canonical `Epistemic.InfoPartition`. |
| same | `attackStateEvent` | def | adapt | `GameTheory.Examples.ElectronicMail.attackStateEvent` | focused build (1,725 jobs) | World-level finite event recovered. |
| same | `viewOf_noMessage` | theorem | adapt | `GameTheory.Examples.ElectronicMail.viewOf_noMessage` | focused build (1,725 jobs) | Computation law recovered. |
| same | `viewOf_onlyFirst_true` | theorem | adapt | `GameTheory.Examples.ElectronicMail.viewOf_onlyFirst_true` | focused build (1,725 jobs) | Computation law recovered. |
| same | `viewOf_onlyFirst_false` | theorem | adapt | `GameTheory.Examples.ElectronicMail.viewOf_onlyFirst_false` | focused build (1,725 jobs) | Computation law recovered. |
| same | `viewOf_bothConfirmed` | theorem | adapt | `GameTheory.Examples.ElectronicMail.viewOf_bothConfirmed` | focused build (1,725 jobs) | Computation law recovered. |
| same | `EmailWorld_univ` | theorem | retired | local enumeration proof | EXP-048/D20 | Private proof helper is rederived locally and is not public API. |
| same | `bothConfirmed_mem_mutualPBelief_attackStateEvent` | theorem | adapt | `GameTheory.Examples.ElectronicMail.bothConfirmed_mem_mutualPBelief_attackStateEvent` | EXP-048/D20; focused build | Recovered over the canonical `FinDist` posterior. |
| same | `not_commonPBeliefAt_attackStateEvent_bothConfirmed_of_half_lt` | theorem | adapt | `GameTheory.Examples.ElectronicMail.not_commonPBeliefAt_attackStateEvent_bothConfirmed_of_half_lt` | EXP-048/D20; focused build | Finite mutual/common-belief separation recovered. |
| same | `exAnte_attackOnMessage_true` | theorem | adapt | `GameTheory.Examples.ElectronicMail.expectedUtility_attackOnMessage_true` | EXP-048/D20; focused build | Uses canonical `expectedUtility` rather than a Bayesian wrapper evaluator. |
| same | `exAnte_trueNeverAttack` | theorem | adapt | `GameTheory.Examples.ElectronicMail.expectedUtility_trueNeverAttack` | EXP-048/D20; focused build | Uses canonical `Profile.update` and exact value zero. |
| same | `attackOnMessage_not_bayesNash` | theorem | adapt | `GameTheory.Examples.ElectronicMail.attackOnMessage_not_isNash` | EXP-048/D20; focused build | Ordinary `IsNash` of `BayesianGame.toForm`; no second Bayes-Nash predicate. |

Before this ledger can become complete, each row must be reviewed against the
canonical successor API and assigned an allowed non-`unreviewed` disposition
with concrete build, theorem, decision, or counterexample evidence. Generated
name similarity is never sufficient.
