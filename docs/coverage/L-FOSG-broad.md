# L-FOSG: Broad factored-observation stochastic-game recovery

Title: Broad factored-observation stochastic-game recovery
Family ID: L-FOSG
Pinned roots: `GameTheory/Languages/FOSG/Basic.lean`; `GameTheory/Languages/FOSG/Compile.lean`; `GameTheory/Languages/FOSG/Examples.lean`; `GameTheory/Languages/FOSG/Execution.lean`; `GameTheory/Languages/FOSG/History.lean`; `GameTheory/Languages/FOSG/Information.lean`; `GameTheory/Languages/FOSG/Native/History.lean`; `GameTheory/Languages/FOSG/Native/HistoryMarginal.lean`; `GameTheory/Languages/FOSG/Native/Reachable.lean`; `GameTheory/Languages/FOSG/Native/StepIndependence.lean`; `GameTheory/Languages/FOSG/Native/TerminalLaw.lean`; `GameTheory/Languages/FOSG/OutcomeClosure.lean`; `GameTheory/Languages/FOSG/ReachableHistory/Law.lean`; `GameTheory/Languages/FOSG/ReachableHistory/Native.lean`; `GameTheory/Languages/FOSG/ReachableHistory/ObsModelFacts.lean`; `GameTheory/Languages/FOSG/Serial.lean`; `GameTheory/Languages/FOSG/Strategy.lean`; `GameTheory/Languages/FOSG/Values.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `01f790a`
Canonical destination: GameTheory.Languages.FOSG; GameTheory.Protocol; named EFG/FOSG bridges
Domain contract / decision: D6, D7, D11, D12, D15, EXP-042
Owner: Wave 3 / sequential and language recovery
Status: in progress; 165/776 reviewed, 611 unreviewed
Last verified: 2026-08-02

This ledger is an exact generated review queue for the L-FOSG family.
0 declarations are already accounted for in earlier bounded ledgers and are
not duplicated here. Rows not yet classified remain deliberately
`unreviewed`: the generated index supplies spelling, location, kind, and
visibility only. It does not infer a mathematical disposition. Reviewed batches
cover the complete `Basic.lean` legality substrate, `History.lean` canonical
history migration, `Information.lean` canonical information-model migration,
and `Values.lean` external-value fold.

The declaration-free pinned umbrella and test files
`ReachableHistory.lean`, `Theorems.lean`, `Kuhn.lean`, `Native.lean`, and
`Tests.lean` are retired as re-export/compilation entrypoints.  They introduce
no theorem inventory of their own; their substantive children remain in this
review queue, and successor consumers import the specific Protocol or language
module they require rather than a FOSG-wide umbrella.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Languages/FOSG/Basic.lean` | `FOSG` | structure | adapt | `GameTheory.Languages.FOSG.Game`; `GameTheory.Protocol.ExecutionProtocol`; `InformationModel` | EXP-042/D15; focused build (1,723 jobs) | Execution and factored information remain paired, while reward/utility stays external and all semantic runners are canonical Protocol objects. |
| same | `legal` | abbrev | adapt | `GameTheory.Protocol.ExecutionProtocol.Legal` | EXP-042/D15; focused build (1,723 jobs) | Non-terminality and pointwise joint legality are defined once in Protocol. |
| same | `availableActionsAtState` | abbrev | retired | `GameTheory.Protocol.ExecutionProtocol.available` | D6/D15; focused build | A second name for the state-indexed available-action projection adds no theorem-facing information. |
| same | `mem_availableActionsAtState_iff` | theorem | retired | `GameTheory.Protocol.ExecutionProtocol.available` | D6/D15; focused build | Reflexive membership wrapper for the retired abbreviation. |
| same | `locallyLegalAtState` | def | adapt | `GameTheory.Protocol.LegalOption` | focused build (1,723 jobs) | Canonical per-player legality has the same active/some and inactive/none cases. |
| same | `legal_iff_forall` | theorem | adapt | `GameTheory.Protocol.isLegalJoint_iff_legalOption`; `ExecutionProtocol.Legal` | focused build (1,723 jobs) | The pointwise decomposition is public at the shared Protocol layer. |
| same | `LegalAction` | abbrev | retired | subtype accepted by `ExecutionProtocol.step`; `ExecutionProtocol.Chooser` | D6/D7 | A named language-local certificate would duplicate the canonical legal-joint subtype. |
| same | `legalAction_val` | theorem | retired | subtype projection | D7 | Projection theorem for the retired wrapper carries no mathematical payload. |
| same | `inactive_eq_none` | theorem | adapt | `GameTheory.Protocol.LegalOption.eq_none_of_inactive`; `ExecutionProtocol.legalOption_of_legal` | focused build (1,723 jobs) | The shared pointwise theorem applies to any canonical legal joint action. |
| same | `legal_inactive_none` | theorem | subsumed | `LegalOption.eq_none_of_inactive`; `ExecutionProtocol.legalOption_of_legal` | focused build (1,723 jobs) | Duplicate predecessor spelling follows through the same checked theorem chain. |
| same | `active_has_some` | theorem | adapt | `GameTheory.Protocol.LegalOption.exists_eq_some_of_active`; `ExecutionProtocol.legalOption_of_legal` | focused build (1,723 jobs) | An active coordinate of a legal joint action contains an action. |
| same | `legal_active_some` | theorem | subsumed | `LegalOption.exists_eq_some_of_active`; `ExecutionProtocol.legalOption_of_legal` | focused build (1,723 jobs) | Duplicate predecessor spelling follows through the same checked theorem chain. |
| same | `active_eq_empty_of_terminal` | theorem | retired | `GameTheory.Protocol.ExecutionProtocol.terminal_no_legal` | D6/D15 | Protocol intentionally leaves `active` unconstrained after stopping; terminality itself makes every joint action illegal, which is the behavior consumers require. |
| same | `not_legal_of_terminal` | theorem | adapt | `GameTheory.Protocol.ExecutionProtocol.terminal_no_legal` | focused build (1,723 jobs) | Terminal execution stops without consulting activity or a chooser. |
| same | `exists_legal_of_not_terminal` | theorem | adapt | `GameTheory.Protocol.ExecutionProtocol.exists_legal` | focused build (1,723 jobs) | The operation-local progress field supplies a canonical legal joint action. |
| same | `legal_noopAction_of_active_empty_of_not_terminal` | theorem | adapt | `GameTheory.Protocol.ExecutionProtocol.noop_isLegal` | focused build (1,723 jobs) | Finset emptiness becomes the sharper pointwise inactivity premise. |
| same | `legal_iff_active_eq_empty` | theorem | adapt | `GameTheory.Protocol.ExecutionProtocol.legal_iff_eq_noop_of_inactive` | focused build (1,723 jobs); axiom audit | At an idle state, a joint action is legal exactly when play continues and it is the canonical no-op. |
| same | `LegalAction.val_eq_noop_of_active_empty` | theorem | adapt | `GameTheory.Protocol.ExecutionProtocol.eq_noop_of_legal_of_inactive` | focused build (1,723 jobs); axiom audit | The mathematical uniqueness fact is public without preserving the retired subtype wrapper. |
| same | `noopLegalAction` | def | retired | `ExecutionProtocol.noop_isLegal`; `ExecutionProtocol.chanceLaw` | D6/D7; focused build | Canonical code constructs the step subtype locally; a language-specific certificate constructor is unnecessary. |
| same | `noopLegalAction_val` | theorem | retired | `ExecutionProtocol.noop` | D7 | Reflexive projection theorem for the retired constructor. |
| `GameTheory/Languages/FOSG/Compile.lean` | `extendByOutcome` | def | unreviewed | review required | generated index seed only | public, pinned line 39 |
| same | `extendByOutcome_of_support` | theorem | unreviewed | review required | generated index seed only | public, pinned line 43 |
| same | `extendByOutcome_of_no_support` | theorem | unreviewed | review required | generated index seed only | public, pinned line 49 |
| same | `extendByOutcome_isPrefix` | theorem | unreviewed | review required | generated index seed only | public, pinned line 55 |
| same | `extendByOutcome_prefix_canonical_imp` | theorem | unreviewed | review required | generated index seed only | public, pinned line 65 |
| same | `extendByOutcome_eq_appendStep_of_head` | theorem | unreviewed | review required | generated index seed only | public, pinned line 87 |
| same | `initialSegment` | def | unreviewed | review required | generated index seed only | public, pinned line 101 |
| same | `initialSegment_steps` | theorem | unreviewed | review required | generated index seed only | public, pinned line 109 |
| same | `initialSegment_isPrefix` | theorem | unreviewed | review required | generated index seed only | public, pinned line 112 |
| same | `initialSegment_length` | theorem | unreviewed | review required | generated index seed only | public, pinned line 117 |
| same | `runDistFrom` | def | unreviewed | review required | generated index seed only | public, pinned line 124 |
| same | `runDistFrom_zero` | theorem | unreviewed | review required | generated index seed only | public, pinned line 138 |
| same | `runDistFrom_succ_terminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 145 |
| same | `runDistFrom_terminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 154 |
| same | `runDistFrom_succ_nonterminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 165 |
| same | `runDistFrom_congr` | theorem | unreviewed | review required | generated index seed only | public, pinned line 177 |
| same | `runDistFrom_bind_runDistFrom` | theorem | unreviewed | review required | generated index seed only | public, pinned line 200 |
| same | `runDistFrom_succ_active_empty` | theorem | unreviewed | review required | generated index seed only | public, pinned line 228 |
| same | `runDistFrom_eq_zero_of_exactHorizon_not_prefix` | theorem | unreviewed | review required | generated index seed only | public, pinned line 244 |
| same | `ExactHorizon` | def | unreviewed | review required | generated index seed only | public, pinned line 302 |
| same | `BoundedHorizon` | def | unreviewed | review required | generated index seed only | public, pinned line 309 |
| same | `exactHorizon_iff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 313 |
| same | `ExactHorizon.bounded` | theorem | unreviewed | review required | generated index seed only | public, pinned line 319 |
| same | `runDistFrom_eq_zero_of_length_gt` | theorem | unreviewed | review required | generated index seed only | public, pinned line 326 |
| same | `runDistFrom_eq_zero_of_nonterminal_target_lt` | theorem | unreviewed | review required | generated index seed only | public, pinned line 373 |
| same | `runDistFrom_eq_zero_of_exactHorizon_length_ne` | theorem | unreviewed | review required | generated index seed only | public, pinned line 420 |
| same | `runDist` | def | unreviewed | review required | generated index seed only | public, pinned line 469 |
| same | `runDist_congr` | theorem | unreviewed | review required | generated index seed only | public, pinned line 476 |
| same | `runDist_zero` | theorem | unreviewed | review required | generated index seed only | public, pinned line 486 |
| same | `runDist_eq_zero_of_exactHorizon_length_ne` | theorem | unreviewed | review required | generated index seed only | public, pinned line 493 |
| same | `runDist_eq_zero_of_length_gt` | theorem | unreviewed | review required | generated index seed only | public, pinned line 505 |
| same | `runDist_eq_zero_of_nonterminal_of_boundedHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 516 |
| same | `runDist_support_isTerminal_of_boundedHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 535 |
| same | `runDistFrom_eq_zero_of_terminal_not_prefix` | theorem | unreviewed | review required | generated index seed only | public, pinned line 548 |
| same | `runDistFrom_eq_probFrom_of_terminal_target` | theorem | unreviewed | review required | generated index seed only | public, pinned line 601 |
| same | `runDist_support_isTerminal_of_exactHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 785 |
| same | `runDistFrom_eq_probFrom_of_exactHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 801 |
| same | `runDist_eq_terminalWeight_of_exactHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 988 |
| same | `length_le_of_boundedHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1011 |
| same | `history_length_le_of_boundedHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1042 |
| same | `historyFintypeOfLengthLe` | def | unreviewed | review required | generated index seed only | public, pinned line 1075 |
| same | `historyFintypeOfBoundedHorizon` | def | unreviewed | review required | generated index seed only | public, pinned line 1098 |
| same | `runDist_eq_terminalWeight_of_boundedHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1105 |
| same | `HasNormalizedTerminalLaw` | def | unreviewed | review required | generated index seed only | public, pinned line 1130 |
| same | `hasNormalizedTerminalLaw_of_exactHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1140 |
| same | `hasNormalizedTerminalLaw_of_boundedHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1159 |
| same | `terminalLawPMF` | def | unreviewed | review required | generated index seed only | public, pinned line 1182 |
| same | `terminalLawPMF_apply` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1192 |
| same | `terminalLawPMF_eq_runDist_of_boundedHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1200 |
| same | `terminalLawPMF_eq_runDist_of_exactHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1210 |
| same | `toKernelGame` | def | unreviewed | review required | generated index seed only | public, pinned line 1222 |
| same | `toKernelGame_outcomeKernel` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1231 |
| same | `toKernelGame_eu_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1240 |
| same | `toKernelGameAtHorizon` | def | unreviewed | review required | generated index seed only | public, pinned line 1257 |
| same | `toKernelGameAtHorizon_outcomeKernel` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1267 |
| same | `toKernelGameAtHorizon_eu_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1274 |
| same | `toKernelGameOfBoundedHorizon` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 1287 |
| same | `toKernelGameOfBoundedHorizon_outcomeKernel` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1294 |
| same | `toKernelGameOfBoundedHorizon_support_isTerminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1304 |
| same | `toKernelGameAtHorizon_eq_toKernelGameOfBoundedHorizon_outcomeKernel` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1319 |
| same | `toKernelGameOfBoundedHorizon_eu_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1328 |
| same | `toKernelGameOfExactHorizon` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 1344 |
| same | `toKernelGameOfExactHorizon_outcomeKernel` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1351 |
| same | `toKernelGameOfExactHorizon_support_isTerminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1361 |
| same | `toKernelGameOfExactHorizon_eu_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1376 |
| `GameTheory/Languages/FOSG/Examples.lean` | `historyFintypeOfLengthLeOne` | def | unreviewed | review required | generated index seed only | public, pinned line 32 |
| same | `Solo` | inductive | unreviewed | review required | generated index seed only | public, pinned line 90 |
| same | `soloIndex` | def | unreviewed | review required | generated index seed only | private, pinned line 94 |
| same | `<anonymous@97>` | instance | unreviewed | review required | generated index seed only | public, pinned line 97 |
| same | `SoloAct` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 104 |
| same | `SoloObs` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 105 |
| same | `SoloPub` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 106 |
| same | `SoloState` | inductive | unreviewed | review required | generated index seed only | public, pinned line 108 |
| same | `binaryChoiceActive` | def | unreviewed | review required | generated index seed only | public, pinned line 113 |
| same | `binaryChoiceAvailable` | def | unreviewed | review required | generated index seed only | public, pinned line 117 |
| same | `binaryChoiceTerminal` | def | unreviewed | review required | generated index seed only | public, pinned line 121 |
| same | `binaryChoicePick` | def | unreviewed | review required | generated index seed only | public, pinned line 125 |
| same | `binaryChoiceTransition` | def | unreviewed | review required | generated index seed only | public, pinned line 142 |
| same | `binaryChoice` | def | unreviewed | review required | generated index seed only | public, pinned line 161 |
| same | `<anonymous@195>` | instance | unreviewed | review required | generated index seed only | public, pinned line 195 |
| same | `startAction` | def | unreviewed | review required | generated index seed only | public, pinned line 201 |
| same | `startAction_legal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 204 |
| same | `startLegalAction` | def | unreviewed | review required | generated index seed only | public, pinned line 218 |
| same | `binaryChoice_step_from_start_isTerminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 221 |
| same | `binaryChoiceBoundedHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 243 |
| same | `<anonymous@262>` | instance | unreviewed | review required | generated index seed only | public, pinned line 262 |
| same | `binaryChoiceKernel` | def | unreviewed | review required | generated index seed only | public, pinned line 267 |
| same | `Player` | inductive | unreviewed | review required | generated index seed only | public, pinned line 272 |
| same | `playerIndex` | def | unreviewed | review required | generated index seed only | private, pinned line 277 |
| same | `<anonymous@281>` | instance | unreviewed | review required | generated index seed only | public, pinned line 281 |
| same | `Act` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 286 |
| same | `PrivObs` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 287 |
| same | `PubObs` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 288 |
| same | `State` | inductive | unreviewed | review required | generated index seed only | public, pinned line 290 |
| same | `active` | def | unreviewed | review required | generated index seed only | public, pinned line 295 |
| same | `availableActions` | def | unreviewed | review required | generated index seed only | public, pinned line 299 |
| same | `terminal` | def | unreviewed | review required | generated index seed only | public, pinned line 303 |
| same | `payoff` | def | unreviewed | review required | generated index seed only | public, pinned line 307 |
| same | `leftMove` | def | unreviewed | review required | generated index seed only | public, pinned line 314 |
| same | `rightMove` | def | unreviewed | review required | generated index seed only | public, pinned line 330 |
| same | `transition` | def | unreviewed | review required | generated index seed only | public, pinned line 343 |
| same | `game` | def | unreviewed | review required | generated index seed only | public, pinned line 357 |
| same | `<anonymous@396>` | instance | unreviewed | review required | generated index seed only | public, pinned line 396 |
| same | `step_from_start_isTerminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 402 |
| same | `boundedHorizon` | theorem | unreviewed | review required | generated index seed only | public, pinned line 436 |
| same | `<anonymous@454>` | instance | unreviewed | review required | generated index seed only | public, pinned line 454 |
| same | `kernel` | def | unreviewed | review required | generated index seed only | public, pinned line 459 |
| `GameTheory/Languages/FOSG/Execution.lean` | `extendBySteps` | def | unreviewed | review required | generated index seed only | public, pinned line 33 |
| same | `extendBySteps_nil` | theorem | unreviewed | review required | generated index seed only | public, pinned line 40 |
| same | `extendBySteps_cons` | theorem | unreviewed | review required | generated index seed only | public, pinned line 44 |
| same | `steps_extendBySteps` | theorem | unreviewed | review required | generated index seed only | public, pinned line 51 |
| same | `lastState_extendBySteps` | theorem | unreviewed | review required | generated index seed only | public, pinned line 64 |
| same | `extendBySteps_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 77 |
| same | `jointActionDist` | def | unreviewed | review required | generated index seed only | public, pinned line 90 |
| same | `jointActionDist_apply` | theorem | unreviewed | review required | generated index seed only | public, pinned line 97 |
| same | `jointActionDist_congr` | theorem | unreviewed | review required | generated index seed only | public, pinned line 105 |
| same | `legalBehavioralProfile_jointActionDist_eq_zero_of_not_legal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 116 |
| same | `legalBehavioralProfile_legalJointMass_eq_one` | theorem | unreviewed | review required | generated index seed only | public, pinned line 139 |
| same | `legalActionLaw` | def | unreviewed | review required | generated index seed only | public, pinned line 171 |
| same | `legalActionLaw_apply` | theorem | unreviewed | review required | generated index seed only | public, pinned line 181 |
| same | `legalActionLaw_congr` | theorem | unreviewed | review required | generated index seed only | public, pinned line 189 |
| same | `legalActionLaw_bind_eq_jointActionDist_bind` | theorem | unreviewed | review required | generated index seed only | public, pinned line 207 |
| same | `legalActionLaw_bind_coord` | theorem | unreviewed | review required | generated index seed only | public, pinned line 255 |
| same | `legalActionLaw_bind_of_coord` | theorem | unreviewed | review required | generated index seed only | public, pinned line 272 |
| same | `legalActionLaw_eq_pure_noop_of_active_empty` | theorem | unreviewed | review required | generated index seed only | public, pinned line 295 |
| same | `nextStateLaw` | def | unreviewed | review required | generated index seed only | public, pinned line 330 |
| same | `nextStateLaw_apply` | theorem | unreviewed | review required | generated index seed only | public, pinned line 338 |
| same | `legalBehavioralProfile_jointStepMass_eq_one` | theorem | unreviewed | review required | generated index seed only | public, pinned line 349 |
| same | `nextStateLaw_eq_bind_legalActionLaw` | theorem | unreviewed | review required | generated index seed only | public, pinned line 361 |
| same | `AgreeOff` | def | unreviewed | review required | generated index seed only | public, pinned line 371 |
| same | `stepActionProb` | def | unreviewed | review required | generated index seed only | public, pinned line 378 |
| same | `playerStepActionProb` | def | unreviewed | review required | generated index seed only | public, pinned line 384 |
| same | `othersStepActionProb` | def | unreviewed | review required | generated index seed only | public, pinned line 391 |
| same | `stepProb` | def | unreviewed | review required | generated index seed only | public, pinned line 399 |
| same | `stepActionProb_ne_top` | theorem | unreviewed | review required | generated index seed only | public, pinned line 404 |
| same | `stepProb_ne_top` | theorem | unreviewed | review required | generated index seed only | public, pinned line 414 |
| same | `stepProb_eq_stepActionProb_mul_transition` | theorem | unreviewed | review required | generated index seed only | public, pinned line 422 |
| same | `stepProb_eq_transition_mul_stepActionProb` | theorem | unreviewed | review required | generated index seed only | public, pinned line 428 |
| same | `legalBehavioralProfile_stepActionProb_eq_one_of_active_empty` | theorem | unreviewed | review required | generated index seed only | public, pinned line 435 |
| same | `legalBehavioralProfile_stepProb_eq_transition_of_active_empty` | theorem | unreviewed | review required | generated index seed only | public, pinned line 458 |
| same | `stepActionProb_eq_player_mul_others` | theorem | unreviewed | review required | generated index seed only | public, pinned line 468 |
| same | `stepActionProb_eq_others_mul_player` | theorem | unreviewed | review required | generated index seed only | public, pinned line 480 |
| same | `othersStepActionProb_eq_of_agreeOff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 487 |
| same | `counterfactualStepProb` | def | unreviewed | review required | generated index seed only | public, pinned line 501 |
| same | `stepProb_eq_player_mul_counterfactual` | theorem | unreviewed | review required | generated index seed only | public, pinned line 506 |
| same | `stepProb_eq_counterfactual_mul_player` | theorem | unreviewed | review required | generated index seed only | public, pinned line 519 |
| same | `counterfactualStepProb_eq_of_agreeOff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 526 |
| same | `probFrom` | def | unreviewed | review required | generated index seed only | public, pinned line 539 |
| same | `playerProbFrom` | def | unreviewed | review required | generated index seed only | public, pinned line 550 |
| same | `counterfactualProbFrom` | def | unreviewed | review required | generated index seed only | public, pinned line 561 |
| same | `probFrom_nil` | theorem | unreviewed | review required | generated index seed only | public, pinned line 570 |
| same | `probFrom_cons` | theorem | unreviewed | review required | generated index seed only | public, pinned line 574 |
| same | `playerProbFrom_nil` | theorem | unreviewed | review required | generated index seed only | public, pinned line 584 |
| same | `playerProbFrom_cons` | theorem | unreviewed | review required | generated index seed only | public, pinned line 589 |
| same | `counterfactualProbFrom_nil` | theorem | unreviewed | review required | generated index seed only | public, pinned line 598 |
| same | `counterfactualProbFrom_cons` | theorem | unreviewed | review required | generated index seed only | public, pinned line 602 |
| same | `counterfactualProbFrom_eq_of_agreeOff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 611 |
| same | `prob` | def | unreviewed | review required | generated index seed only | public, pinned line 630 |
| same | `prob_nil` | theorem | unreviewed | review required | generated index seed only | public, pinned line 635 |
| same | `probFrom_ne_top` | theorem | unreviewed | review required | generated index seed only | public, pinned line 639 |
| same | `prob_ne_top` | theorem | unreviewed | review required | generated index seed only | public, pinned line 652 |
| same | `probFrom_eq_playerProbFrom_mul_counterfactualProbFrom` | theorem | unreviewed | review required | generated index seed only | public, pinned line 660 |
| same | `probFrom_append` | theorem | unreviewed | review required | generated index seed only | public, pinned line 683 |
| same | `probFrom_append_singleton` | theorem | unreviewed | review required | generated index seed only | public, pinned line 706 |
| same | `prob_snoc` | theorem | unreviewed | review required | generated index seed only | public, pinned line 720 |
| same | `playerProb` | def | unreviewed | review required | generated index seed only | public, pinned line 736 |
| same | `counterfactualProb` | def | unreviewed | review required | generated index seed only | public, pinned line 743 |
| same | `counterfactualProb_eq_of_agreeOff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 748 |
| same | `prob_eq_playerProb_mul_counterfactualProb` | theorem | unreviewed | review required | generated index seed only | public, pinned line 757 |
| same | `prob_extendBySteps` | theorem | unreviewed | review required | generated index seed only | public, pinned line 767 |
| same | `prob_appendStep` | theorem | unreviewed | review required | generated index seed only | public, pinned line 780 |
| same | `terminalWeight` | def | unreviewed | review required | generated index seed only | public, pinned line 793 |
| same | `terminalWeight_ne_top` | theorem | unreviewed | review required | generated index seed only | public, pinned line 798 |
| same | `terminalWeight_of_terminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 806 |
| same | `terminalWeight_of_not_terminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 813 |
| same | `terminalMassOn` | def | unreviewed | review required | generated index seed only | public, pinned line 822 |
| same | `terminalLaw` | def | unreviewed | review required | generated index seed only | public, pinned line 828 |
| same | `terminalMassOn_empty` | theorem | unreviewed | review required | generated index seed only | public, pinned line 833 |
| same | `terminalMassOn_singleton` | theorem | unreviewed | review required | generated index seed only | public, pinned line 840 |
| same | `terminalLaw_apply` | theorem | unreviewed | review required | generated index seed only | public, pinned line 847 |
| `GameTheory/Languages/FOSG/History.lean` | `Step` | structure | adapt | `GameTheory.Protocol.ExecutionProtocol.StepEvent` | pinned `History.lean:26`; focused Protocol History build | Canonical event stores the same realized transition with legality and support evidence. |
| same | `ownAction?` | abbrev | adapt | `ExecutionProtocol.StepEvent.joint` | pinned `History.lean:37`; focused Protocol History build | A player contribution is the canonical joint-action coordinate. |
| same | `publicObs` | abbrev | adapt | `GameTheory.Protocol.InfoSignals.publicSignal` | pinned `History.lean:41`; focused Protocol History build | Signals consume canonical `StepEvent`; FOSG owns no observation projection. |
| same | `privateObs` | abbrev | adapt | `GameTheory.Protocol.InfoSignals.privateSignal` | pinned `History.lean:45`; focused Protocol History build | Signals consume canonical `StepEvent`; FOSG owns no observation projection. |
| same | `ownAction?_eq_none_of_not_mem_active` | theorem | adapt | `GameTheory.Protocol.LegalOption.eq_none_of_inactive` | pinned `History.lean:48`; focused Protocol History build | Canonical pointwise legality proves an inactive coordinate is `none`. |
| same | `exists_ownAction_of_mem_active` | theorem | adapt | `GameTheory.Protocol.LegalOption.exists_eq_some_of_active` | pinned `History.lean:53`; focused Protocol History build | Canonical pointwise legality proves an active coordinate is `some`. |
| same | `instFintypeLegalAction` | instance | retired | explicit finite enumerations at algorithm boundary | D6/D7; pinned `History.lean:66` | No global noncomputable `Fintype` synthesized from language-local optional actions. |
| same | `StepData` | abbrev | retired | `ExecutionProtocol.StepEvent` | pinned `History.lean:72` | Private sigma encoding only supported the retired automatic instance. |
| same | `instFintypeStep` | instance | retired | explicit finite enumerations at algorithm boundary | D6/D7; pinned `History.lean:76` | No global finite enumeration of proof-carrying realized transitions. |
| same | `StepChainFrom` | def | retired | `ExecutionProtocol.Trace` | pinned `History.lean:99`; focused Protocol History build | Indexed traces enforce chaining in their type instead of a list predicate. |
| same | `lastStateFrom` | def | retired | `ExecutionProtocol.Trace`; `ExecutionProtocol.History.state` | pinned `History.lean:105` | Endpoint is carried by the trace index and history field. |
| same | `stateTraceFrom` | def | retired | `ExecutionProtocol.Trace` | pinned `History.lean:111` | The list-shaped diagnostic view is not protocol semantics. |
| same | `lastStateFrom_nil` | theorem | retired | `ExecutionProtocol.initHistory_state` | pinned `History.lean:116` | List-recursion base theorem retired with the list encoding. |
| same | `lastStateFrom_cons` | theorem | retired | `ExecutionProtocol.History.extend_state` | pinned `History.lean:120` | List-recursion step theorem retired with the list encoding. |
| same | `stateTraceFrom_nil` | theorem | retired | `ExecutionProtocol.Trace.start` | pinned `History.lean:124` | List trace display retired. |
| same | `stateTraceFrom_cons` | theorem | retired | `ExecutionProtocol.Trace.extend` | pinned `History.lean:128` | List trace display retired. |
| same | `stateTraceFrom_length` | theorem | retired | `ExecutionProtocol.Trace.length` | pinned `History.lean:132`; source comparison | The state-list length equation disappears with the redundant unindexed state-list view; canonical traces store transition length directly. |
| same | `lastStateFrom_append_singleton` | theorem | retired | `ExecutionProtocol.History.extend_state` | pinned `History.lean:141` | Endpoint-after-extension is direct rather than a list append proof. |
| same | `lastStateFrom_append` | theorem | retired | `ExecutionProtocol.Trace` | pinned `History.lean:150` | Concatenating unindexed traces would duplicate the indexed transition representation. |
| same | `stateTraceFrom_append_singleton` | theorem | retired | `ExecutionProtocol.Trace.extend` | pinned `History.lean:160` | List display append retired. |
| same | `StepChainFrom.snoc` | theorem | retired | `ExecutionProtocol.Trace.extend` | pinned `History.lean:172` | Extension constructs a well-formed indexed trace directly. |
| same | `StepChainFrom.append` | theorem | retired | `ExecutionProtocol.Trace` | pinned `History.lean:187` | No unindexed trace concatenation API is needed. |
| same | `StepChainFrom.left` | theorem | retired | `ExecutionProtocol.Trace` | pinned `History.lean:201` | List-prefix decomposition retired. |
| same | `StepChainFrom.right` | theorem | retired | `ExecutionProtocol.Trace` | pinned `History.lean:214` | List-suffix decomposition retired. |
| same | `History` | structure | adapt | `GameTheory.Protocol.ExecutionProtocol.History` | pinned `History.lean:228`; focused Protocol History build | A complete history packages its endpoint with a type-indexed canonical trace. |
| same | `ext` | theorem | retired | indexed `ExecutionProtocol.History` | pinned `History.lean:236`; source and symbol audit | The old one-field extensionality discarded a propositional chaining proof; the canonical endpoint-indexed trace has no honest one-field analogue without exposing equality transport. |
| same | `nil` | def | adapt | `ExecutionProtocol.initHistory` | pinned `History.lean:245`; focused Protocol History build | Canonical empty history starts at the protocol initial state. |
| same | `lastState` | def | adapt | `ExecutionProtocol.History.state` | pinned `History.lean:249`; focused Protocol History build | The endpoint is a canonical history field. |
| same | `stateTrace` | def | retired | `ExecutionProtocol.Trace` | pinned `History.lean:253` | A redundant unindexed state-list view is intentionally absent. |
| same | `actionTrace` | def | retired | `ExecutionProtocol.Trace` | pinned `History.lean:257` | A redundant unindexed action-list view is intentionally absent. |
| same | `snoc` | def | adapt | `ExecutionProtocol.History.extend` | pinned `History.lean:261`; focused Protocol History build | Extension takes exactly a legal realized transition. |
| same | `appendStep` | def | adapt | `ExecutionProtocol.History.extend` | pinned `History.lean:268`; focused Protocol History build | The source-match proof is absorbed by the history endpoint index. |
| same | `steps_nil` | theorem | retired | `ExecutionProtocol.initHistory` | pinned `History.lean:274` | Projection of retired list representation. |
| same | `lastState_nil` | theorem | adapt | `ExecutionProtocol.initHistory_state` | pinned `History.lean:277`; focused Protocol History build | Canonical initial-history endpoint theorem. |
| same | `stateTrace_nil` | theorem | retired | `ExecutionProtocol.Trace.start` | pinned `History.lean:280` | List display theorem retired. |
| same | `actionTrace_nil` | theorem | retired | `ExecutionProtocol.Trace.start` | pinned `History.lean:283` | List display theorem retired. |
| same | `steps_snoc` | theorem | retired | `ExecutionProtocol.History.extend` | pinned `History.lean:286` | Projection of retired list representation. |
| same | `steps_appendStep` | theorem | retired | `ExecutionProtocol.History.extend` | pinned `History.lean:291` | Projection of retired list representation. |
| same | `lastState_snoc` | theorem | adapt | `ExecutionProtocol.History.extend_state` | pinned `History.lean:295`; focused Protocol History build | Endpoint after canonical extension is definitionally its realized target. |
| same | `stateTrace_snoc` | theorem | retired | `ExecutionProtocol.Trace.extend` | pinned `History.lean:302` | List display theorem retired. |
| same | `actionTrace_snoc` | theorem | retired | `ExecutionProtocol.Trace.extend` | pinned `History.lean:309` | List display theorem retired. |
| same | `stateTrace_length` | theorem | retired | `ExecutionProtocol.Trace.length` | pinned `History.lean:315`; source comparison | The state-list length equation disappears with the redundant unindexed state-list view; canonical traces store transition length directly. |
| same | `lastState_appendStep` | theorem | adapt | `ExecutionProtocol.History.extend_state` | pinned `History.lean:320`; focused Protocol History build | Endpoint after canonical extension is definitionally its realized target. |
| same | `stateTrace_appendStep` | theorem | retired | `ExecutionProtocol.Trace.extend` | pinned `History.lean:326` | List display theorem retired. |
| same | `appendStep_eq_snoc` | theorem | retired | `ExecutionProtocol.History.extend` | pinned `History.lean:332` | One canonical extension constructor makes duplicate append APIs unnecessary. |
| same | `length_states_eq_actions_succ` | theorem | retired | `ExecutionProtocol.Trace.length` | pinned `History.lean:337` | The statement depends on retired list display projections. |
| same | `IsPrefix` | def | retired | `ExecutionProtocol.ReachesWithin` | pinned `History.lean:343` | Bounded semantic reachability replaces raw list-prefix bookkeeping. |
| same | `IsDescendant` | def | retired | `ExecutionProtocol.ReachesWithin` | pinned `History.lean:347` | Bounded semantic reachability replaces raw list-suffix bookkeeping. |
| same | `IsTerminal` | def | adapt | `ExecutionProtocol.History.isTerminal` | pinned `History.lean:351`; focused Protocol History build | New Protocol-level history view uses the one terminality predicate. |
| same | `terminalHistories` | def | adapt | `ExecutionProtocol.terminalHistories` | pinned `History.lean:355`; focused Protocol History build | New Protocol-level terminal-history set is reusable by EFG and FOSG. |
| same | `isPrefix_iff` | theorem | retired | `ExecutionProtocol.ReachesWithin` | pinned `History.lean:358` | Reflexive list-prefix wrapper retired. |
| same | `isDescendant_iff` | theorem | retired | `ExecutionProtocol.ReachesWithin` | pinned `History.lean:363` | Reflexive list-descendant wrapper retired. |
| same | `prefix_refl` | theorem | adapt | `ExecutionProtocol.ReachesWithin.refl` | pinned `History.lean:368`; focused Protocol History build | Semantic bounded reachability is reflexive at every available fuel budget. |
| same | `nil_prefix` | theorem | adapt | `ExecutionProtocol.reachesWithin_from_init` | pinned `History.lean:373`; focused Protocol History build | Every canonical history is reached from `initHistory`, with its indexed trace length as the exact budget. |
| same | `prefix_of_eq` | theorem | adapt | `ExecutionProtocol.ReachesWithin.refl` | pinned `History.lean:378`; focused Protocol History build | Equality becomes bounded semantic reachability reflexivity without a list witness. |
| same | `prefix_snoc` | theorem | adapt | `ExecutionProtocol.ReachesWithin.step` | pinned `History.lean:384`; focused Protocol History build | One realized extension is represented by the semantic reachability constructor. |
| same | `prefix_trans` | theorem | adapt | `ExecutionProtocol.ReachesWithin.trans` | pinned `History.lean:391`; focused Protocol History build | Canonical transitivity records the honest sum of the two finite reachability budgets. |
| same | `descendant_refl` | theorem | retired | `ExecutionProtocol.ReachesWithin.refl` | pinned `History.lean:400` | Semantic bounded reachability is reflexive. |
| same | `descendant_trans` | theorem | retired | `ExecutionProtocol.ReachesWithin.trans` | pinned `History.lean:405`; focused Protocol History build | The reverse-argument descendant vocabulary carries no independent payload; canonical reachability composes with explicit additive fuel. |
| same | `mem_terminalHistories_iff` | theorem | adapt | `ExecutionProtocol.mem_terminalHistories_iff` | pinned `History.lean:411`; focused Protocol History build | New canonical terminal-history membership theorem. |
| same | `not_isTerminal_of_legalAction` | theorem | adapt | `ExecutionProtocol.History.not_isTerminal_of_legal` | pinned `History.lean:416`; focused Protocol History build | A legal joint action proves the endpoint is non-terminal. |
| same | `exists_legalAction_of_not_terminal` | theorem | adapt | `ExecutionProtocol.History.exists_legal_of_not_terminal` | pinned `History.lean:422`; focused Protocol History build | Protocol progress supplies a legal joint action at a non-terminal endpoint. |
| `GameTheory/Languages/FOSG/Information.lean` | `PlayerEvent` | inductive | retired | `ExecutionProtocol.StepEvent`; `InfoSignals.publicSignal`/`privateSignal` | D6/D15; Protocol Information API review (2026-08-02) | The old action-or-observation sum fixes one FOSG observation representation; Protocol consumes one realized step and leaves signal alphabets to the model. |
| same | `publicPart` | def | retired | `InfoSignals.publicSignal` | D6/D15; API review | There is no canonical projection from a player-local information state to a public signal. |
| same | `actionPart` | def | retired | `StepEvent.joint` | D6/D15; API review | A realized joint action is already available before any language-specific view encoding. |
| same | `observationPart` | def | retired | `InfoSignals.privateSignal`; `InfoSignals.publicSignal` | D6/D15; API review | Private and public signals need not be paired or retained verbatim. |
| same | `publicPart_act` | theorem | retired | `InfoSignals.publicSignal` | D6/D15; API review | Constructor equation for retired event syntax. |
| same | `publicPart_obs` | theorem | retired | `InfoSignals.publicSignal` | D6/D15; API review | Constructor equation for retired event syntax. |
| same | `actionPart_act` | theorem | retired | `StepEvent.joint` | D6/D15; API review | Constructor equation for retired event syntax. |
| same | `actionPart_obs` | theorem | retired | `InfoSignals.privateSignal` | D6/D15; API review | Constructor equation for retired event syntax. |
| same | `observationPart_act` | theorem | retired | `InfoSignals.privateSignal`; `InfoSignals.publicSignal` | D6/D15; API review | Constructor equation for retired event syntax. |
| same | `observationPart_obs` | theorem | retired | `InfoSignals.privateSignal`; `InfoSignals.publicSignal` | D6/D15; API review | Constructor equation for retired event syntax. |
| same | `InfoState` | abbrev | adapt | `InformationModel.InfoState` | D6/D15; Protocol Information API review (2026-08-02) | Information states are model-owned and may be compressed; they are not fixed action-observation lists. |
| same | `PublicState` | abbrev | retired | `InfoSignals.PublicSignal` | D6/D15; API review | A public signal is canonical; a list of signals is only one model's chosen information state. |
| same | `last?` | def | retired | no canonical successor | D6/D15; API review | The shared model does not privilege list-encoded observations. |
| same | `last?_append_singleton` | theorem | retired | no canonical successor | D6/D15; API review | List lemma for the retired observation encoding. |
| same | `observationEvents` | def | retired | `InfoSignals.infoOf` | D6/D15; API review | Information is updated by the model's `pushInfo`, not extracted from a fixed event list. |
| same | `latestObservation?` | def | retired | no canonical successor | D6/D15; API review | A latest observation is application-specific, not Protocol semantics. |
| same | `observationEvents_nil` | theorem | retired | `InfoSignals.infoOf_start` | D6/D15; API review | The valid canonical initial-state equation is for `infoOf`, not a raw event list. |
| same | `latestObservation?_nil` | theorem | retired | `InfoSignals.infoOf_start` | D6/D15; API review | The valid canonical initial-state equation is for `infoOf`, not a raw event list. |
| same | `latestObservation?_append_obs` | theorem | retired | `InfoSignals.infoOf_extend` | D6/D15; API review | The model determines how a signal affects information. |
| same | `latestObservation?_append_act_obs` | theorem | retired | `InfoSignals.infoOf_extend` | D6/D15; API review | The model determines how a signal affects information. |
| same | `playerView@130` | def | retired | `InfoSignals.infoOf` | D6/D15; API review | The old per-step list is replaced by the model-selected information update. |
| same | `playerView_of_some` | theorem | retired | `InfoSignals.infoOf_extend` | D6/D15; API review | Case equation for the retired per-step list. |
| same | `playerView_of_none` | theorem | retired | `InfoSignals.infoOf_extend` | D6/D15; API review | Case equation for the retired per-step list. |
| same | `filterMap_publicPart_playerView` | theorem | retired | no canonical successor | D6/D15; API review | Public observability need not be recoverable from local information. |
| same | `playerView_length_pos` | theorem | retired | no canonical successor | D6/D15; API review | A compressed information state has no event-list length invariant. |
| same | `latestObservation?_append_playerView` | theorem | retired | `InfoSignals.infoOf_extend` | D6/D15; API review | The canonical update theorem leaves retention to `pushInfo`. |
| same | `publicViewFrom` | def | retired | `InfoSignals.publicSignal` | D6/D15; API review | Protocol does not impose a public-history list representation. |
| same | `playerViewFrom` | def | retired | `InfoSignals.infoOf` | D6/D15; API review | Protocol computes model-selected information directly from an indexed trace. |
| same | `publicView` | def | retired | `InfoSignals.publicSignal` | D6/D15; API review | A complete history does not carry a mandated public-view projection. |
| same | `playerView@194` | def | retired | `InfoSignals.infoOf` | D6/D15; API review | The canonical history-to-information map is `infoOf`. |
| same | `projectActions` | def | retired | `InfoSignals.ownPlay` | D6; Protocol Information API review (2026-08-02) | The canonical own-action record retains the information state at each own move, which the old projection discarded. |
| same | `projectObservations` | def | retired | no canonical successor | D6/D15; API review | Observation recall is not forced by arbitrary information compression. |
| same | `publicViewFrom_append_singleton` | theorem | retired | no canonical successor | D6/D15; API review | List append law for retired public-history syntax. |
| same | `publicViewFrom_append` | theorem | retired | no canonical successor | D6/D15; API review | List append law for retired public-history syntax. |
| same | `playerViewFrom_append_singleton` | theorem | retired | `InfoSignals.infoOf_extend` | D6/D15; API review | Indexed trace extension replaces raw-list append. |
| same | `playerViewFrom_append` | theorem | retired | no canonical successor | D6/D15; API review | Raw list append cannot preserve indexed trace endpoints. |
| same | `publicView_nil` | theorem | retired | `InfoSignals.infoOf_start` | D6/D15; API review | The canonical initial observation fact is model-specific. |
| same | `playerView_nil` | theorem | retired | `InfoSignals.infoOf_start` | D6/D15; API review | The canonical initial information fact is `infoOf_start`. |
| same | `publicView_snoc` | theorem | retired | `InfoSignals.infoOf_extend` | D6/D15; API review | A signal update is not necessarily list append. |
| same | `playerView_snoc` | theorem | retired | `InfoSignals.infoOf_extend` | D6/D15; API review | A player's information update is not necessarily list append. |
| same | `latestObservation?_playerView_snoc` | theorem | retired | `InfoSignals.infoOf_extend` | D6/D15; API review | Latest-observation retention is model-specific. |
| same | `latestObservation?_playerView_appendStep` | theorem | retired | `InfoSignals.infoOf_extend` | D6/D15; API review | Latest-observation retention is model-specific. |
| same | `publicViewFrom_eq_filterMap_playerViewFrom` | theorem | retired | no canonical successor | D6/D15; API review | The shared interface permits private information that omits public signals. |
| same | `publicView_eq_filterMap_playerView` | theorem | retired | no canonical successor | D6/D15; API review | The shared interface permits private information that omits public signals. |
| same | `publicView_eq_of_playerView_eq` | theorem | retired | no canonical successor | D6/D15; API review | Equal local information need not determine a retained public-signal history. |
| same | `projectActions_eq_of_playerView_eq` | theorem | retired | `InfoSignals.PerfectRecall` | D6; API review | This conclusion is a recall hypothesis in the general model, not a free FOSG theorem. |
| same | `projectObservations_eq_of_playerView_eq` | theorem | retired | no canonical successor | D6/D15; API review | Observation recall is not an architectural invariant. |
| same | `playerView_length_snoc` | theorem | retired | no canonical successor | D6/D15; API review | Compressed information has no event-list length. |
| same | `playerView_length_lt_snoc` | theorem | retired | no canonical successor | D6/D15; API review | Compressed information need not grow at every step. |
| same | `playerView_ne_snoc` | theorem | retired | no canonical successor | D6/D15; API review | Information may intentionally remain unchanged after a step. |
| same | `playerView_eq_append_of_prefix` | theorem | retired | no canonical successor | D6/D15; API review | The general model supplies no append decomposition of information values. |
| same | `playerView_length_lt_of_properPrefix` | theorem | retired | no canonical successor | D6/D15; API review | Proper execution extension need not enlarge compressed information. |
| same | `playerView_ne_of_properPrefix` | theorem | retired | no canonical successor | D6/D15; API review | Proper execution extension may leave an information state unchanged. |
| same | `infoSet` | def | subsumed | `InformationModel.InformationHistory`; `InformationModel.InfoSet` | Protocol BehavioralAssessment/Information API review (2026-08-02) | The former history fiber is `InformationHistory`; the state-facing information set is also available for state beliefs. |
| same | `IsDecisionHistory` | def | subsumed | `InformationModel.InformationSite` | Protocol BehavioralAssessment API review (2026-08-02) | A canonical decision site additionally requires a reached history, nonterminality, and a genuine menu action. |
| same | `decisionInfoSet` | def | subsumed | `InformationModel.InformationSite`; `InformationModel.InformationHistory` | Protocol BehavioralAssessment API review (2026-08-02) | The assessment interface packages exactly the reachable decision information needed by downstream reasoning. |
| same | `publicSet` | def | retired | no canonical successor | D6/D15; API review | Public histories are a language/model choice, not a generic FOSG object. |
| same | `mem_publicSet_of_mem_infoSet` | theorem | retired | no canonical successor | D6/D15; API review | It relies on the retired filtering representation of public signals. |
| same | `infoSet_subset_publicSet` | theorem | retired | no canonical successor | D6/D15; API review | It relies on the retired filtering representation of public signals. |
| same | `decisionInfoSet_subset_infoSet` | theorem | subsumed | `InformationModel.InformationSite` | Protocol BehavioralAssessment API review (2026-08-02) | An information site contains its witnessing `InformationHistory` by construction. |
| same | `mem_decisionInfoSet_iff` | theorem | retired | `InformationModel.InformationSite` | Protocol BehavioralAssessment API review (2026-08-02) | The old set-membership wrapper is replaced by the dependent site witness. |
| same | `infoSet_mem_publicSet` | theorem | retired | no canonical successor | D6/D15; API review | Equal local information does not generally determine retained public history. |
| same | `ObsRecall@447` | def | retired | no canonical successor | D6/D15; API review | The old property presupposes a raw observation-list encoding. |
| same | `ActionRecall@454` | def | retired | `InfoSignals.PerfectRecall` | D6; API review | The general recall predicate retains the stronger `(information state, action)` own-play record. |
| same | `PerfectRecall@464` | def | adapt | `InfoSignals.PerfectRecall` | D6; Protocol Information API review (2026-08-02) | Recall is a property of `infoOf`, not a language-owned conjunction of projections. |
| same | `obsRecall` | theorem | retired | no canonical successor | D6/D15; API review | Automatic observation recall was an artefact of the retired list representation. |
| same | `actionRecall` | theorem | retired | `InfoSignals.PerfectRecall` | D6; API review | Automatic action recall is not a theorem for arbitrary information models. |
| same | `perfectRecall` | theorem | refuted | `GameTheory/Tests/Randomized.lean:single_not_perfectRecall` | EXP-018; focused Randomized test | The accepted general FOSG pairing admits a signal model that forgets its own vote, so global perfect recall cannot be claimed. |
| same | `perfectRecall_obs` | theorem | subsumed | `InfoSignals.actedAt_eq_of_perfectRecall` | D6; Protocol Information API review (2026-08-02) | Under canonical recall, equality of own-play records yields the retained decision-site record. |
| same | `perfectRecall_action` | theorem | subsumed | `InfoSignals.PerfectRecall` | D6; Protocol Information API review (2026-08-02) | The canonical hypothesis directly retains equality of the complete own-play action record. |
| `GameTheory/Languages/FOSG/Native/History.lean` | `ExecutionState` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 39 |
| same | `KuhnLocalStrategy` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 43 |
| same | `KuhnPureProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 47 |
| same | `KuhnBehavioralProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 51 |
| same | `runDist` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 55 |
| same | `runDistPure` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 62 |
| same | `executionBehavioralToMixedJoint` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 70 |
| same | `NoNontrivialInfoStateRepeat` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 79 |
| same | `StepMassInvariant` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 85 |
| same | `StepSupportFactorization` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 91 |
| same | `ActionPosteriorLocal` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 97 |
| same | `ObsLocalFeasibilityFull` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 104 |
| same | `behavioral_to_mixed_runDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 116 |
| same | `mixed_to_behavioral_semantic` | theorem | unreviewed | review required | generated index seed only | public, pinned line 138 |
| same | `mixed_to_behavioral_of_obsLocal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 165 |
| same | `PureStrategy` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 184 |
| same | `MixedProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 189 |
| same | `mixedProfilePureStrategyFintype` | instance | unreviewed | review required | generated index seed only | public, pinned line 192 |
| same | `BehavioralProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 200 |
| same | `mixedProfileJoint` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 204 |
| same | `liftPureStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 210 |
| same | `liftPureProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 216 |
| same | `liftMixedProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 221 |
| same | `liftMixedProfile_joint` | theorem | unreviewed | review required | generated index seed only | public, pinned line 226 |
| same | `behavioralToMixed` | def | unreviewed | review required | generated index seed only | public, pinned line 243 |
| same | `behavioralToMixedJoint` | def | unreviewed | review required | generated index seed only | public, pinned line 252 |
| same | `mixed_to_behavioral_runDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 267 |
| same | `mixed_to_behavioral_runDist_of_obsLocal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 293 |
| same | `toHistoryObsModelCore` | def | unreviewed | review required | generated index seed only | public, pinned line 324 |
| same | `historyInfoStateFintype` | instance | unreviewed | review required | generated index seed only | public, pinned line 343 |
| `GameTheory/Languages/FOSG/Native/HistoryMarginal.lean` | `SeenBefore` | def | unreviewed | review required | generated index seed only | public, pinned line 49 |
| same | `stepChainFrom_prefix` | theorem | unreviewed | review required | generated index seed only | public, pinned line 54 |
| same | `stepChainFrom_last_src` | theorem | unreviewed | review required | generated index seed only | public, pinned line 66 |
| same | `seenBefore_mono_appendStep` | theorem | unreviewed | review required | generated index seed only | public, pinned line 78 |
| same | `seenBefore_current_appendStep` | theorem | unreviewed | review required | generated index seed only | public, pinned line 94 |
| same | `not_seenBefore_current` | theorem | unreviewed | review required | generated index seed only | public, pinned line 104 |
| same | `stepProb_pure_congr_at_history` | theorem | unreviewed | review required | generated index seed only | public, pinned line 112 |
| same | `prob_pure_congr_of_agreeOnSeenBefore` | theorem | unreviewed | review required | generated index seed only | public, pinned line 131 |
| same | `marginal_prob` | theorem | unreviewed | review required | generated index seed only | public, pinned line 180 |
| `GameTheory/Languages/FOSG/Native/Reachable.lean` | `ReachablePureStrategy` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 37 |
| same | `ReachableBehavioralProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 41 |
| same | `reachableBehavioralToMixed` | def | unreviewed | review required | generated index seed only | public, pinned line 59 |
| same | `reachableBehavioralToMixedJoint` | def | unreviewed | review required | generated index seed only | public, pinned line 67 |
| same | `reachable_stepActionProb_pureToBehavioral` | theorem | unreviewed | review required | generated index seed only | public, pinned line 75 |
| same | `reachable_marginal_stepActionProb` | theorem | unreviewed | review required | generated index seed only | public, pinned line 87 |
| same | `reachable_marginal_stepProb` | theorem | unreviewed | review required | generated index seed only | public, pinned line 152 |
| same | `swapReachableProfileBy` | def | unreviewed | review required | generated index seed only | public, pinned line 176 |
| same | `swapReachableProfileBy_involutive` | theorem | unreviewed | review required | generated index seed only | public, pinned line 184 |
| same | `swapReachableBy_weight_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 200 |
| same | `reachable_scalar_indep` | theorem | unreviewed | review required | generated index seed only | public, pinned line 219 |
| same | `ReachableSeenBefore` | def | unreviewed | review required | generated index seed only | public, pinned line 309 |
| same | `reachable_seenBefore_mono_appendStep` | theorem | unreviewed | review required | generated index seed only | public, pinned line 314 |
| same | `reachable_seenBefore_current_appendStep` | theorem | unreviewed | review required | generated index seed only | public, pinned line 330 |
| same | `reachable_not_seenBefore_current` | theorem | unreviewed | review required | generated index seed only | public, pinned line 341 |
| same | `reachable_stepProb_pure_congr_at_history` | theorem | unreviewed | review required | generated index seed only | public, pinned line 351 |
| same | `reachable_prob_pure_congr_of_agreeOnSeenBefore` | theorem | unreviewed | review required | generated index seed only | public, pinned line 371 |
| same | `reachable_scalar_indep_stepProb` | theorem | unreviewed | review required | generated index seed only | public, pinned line 420 |
| same | `reachable_marginal_prob` | theorem | unreviewed | review required | generated index seed only | public, pinned line 454 |
| same | `reachable_marginal_terminalWeight` | theorem | unreviewed | review required | generated index seed only | public, pinned line 512 |
| same | `reachable_marginal_terminalMassOn` | theorem | unreviewed | review required | generated index seed only | public, pinned line 541 |
| same | `reachable_marginal_terminalLaw` | theorem | unreviewed | review required | generated index seed only | public, pinned line 565 |
| same | `reachable_marginal_terminalWeight_toReal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 574 |
| same | `reachable_marginal_terminalUtilitySum` | theorem | unreviewed | review required | generated index seed only | public, pinned line 600 |
| same | `reachable_marginal_terminalExpectation` | theorem | unreviewed | review required | generated index seed only | public, pinned line 644 |
| same | `behavioral_to_mixed_prob_reachable` | theorem | unreviewed | review required | generated index seed only | public, pinned line 690 |
| same | `behavioral_to_mixed_terminalWeight_reachable` | theorem | unreviewed | review required | generated index seed only | public, pinned line 698 |
| same | `behavioral_to_mixed_terminalMassOn_reachable` | theorem | unreviewed | review required | generated index seed only | public, pinned line 706 |
| same | `behavioral_to_mixed_terminalLaw_reachable` | theorem | unreviewed | review required | generated index seed only | public, pinned line 714 |
| same | `behavioral_to_mixed_eu_reachable` | theorem | unreviewed | review required | generated index seed only | public, pinned line 723 |
| `GameTheory/Languages/FOSG/Native/StepIndependence.lean` | `stepActionProb_pureToBehavioral` | theorem | unreviewed | review required | generated index seed only | public, pinned line 51 |
| same | `marginal_stepActionProb_raw` | theorem | unreviewed | review required | generated index seed only | public, pinned line 67 |
| same | `marginal_stepActionProb` | theorem | unreviewed | review required | generated index seed only | public, pinned line 124 |
| same | `marginal_stepProb` | theorem | unreviewed | review required | generated index seed only | public, pinned line 144 |
| same | `swapProfileBy` | def | unreviewed | review required | generated index seed only | public, pinned line 188 |
| same | `swapProfileBy_involutive` | theorem | unreviewed | review required | generated index seed only | public, pinned line 196 |
| same | `swapBy_weight_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 212 |
| same | `scalar_indep` | theorem | unreviewed | review required | generated index seed only | public, pinned line 234 |
| same | `scalar_indep_stepProb` | theorem | unreviewed | review required | generated index seed only | public, pinned line 329 |
| `GameTheory/Languages/FOSG/Native/TerminalLaw.lean` | `marginal_terminalWeight` | theorem | unreviewed | review required | generated index seed only | public, pinned line 49 |
| same | `marginal_terminalMassOn` | theorem | unreviewed | review required | generated index seed only | public, pinned line 81 |
| same | `marginal_terminalLaw` | theorem | unreviewed | review required | generated index seed only | public, pinned line 108 |
| same | `marginal_terminalWeight_toReal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 120 |
| same | `terminalWeightClassical` | def | unreviewed | review required | generated index seed only | public, pinned line 149 |
| same | `marginal_terminalUtilitySum` | theorem | unreviewed | review required | generated index seed only | public, pinned line 157 |
| same | `behavioral_to_mixed_prob` | theorem | unreviewed | review required | generated index seed only | public, pinned line 209 |
| same | `behavioral_to_mixed_terminalWeight` | theorem | unreviewed | review required | generated index seed only | public, pinned line 220 |
| same | `behavioral_to_mixed_terminalMassOn` | theorem | unreviewed | review required | generated index seed only | public, pinned line 231 |
| same | `behavioral_to_mixed_terminalLaw` | theorem | unreviewed | review required | generated index seed only | public, pinned line 242 |
| same | `behavioral_to_mixed_eu` | theorem | unreviewed | review required | generated index seed only | public, pinned line 254 |
| `GameTheory/Languages/FOSG/OutcomeClosure.lean` | `valueStep` | def | unreviewed | review required | generated index seed only | public, pinned line 38 |
| same | `valueStep_terminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 49 |
| same | `valueStep_nonterminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 57 |
| same | `OutcomeValue` | structure | unreviewed | review required | generated index seed only | public, pinned line 70 |
| same | `ofProjectedStep` | def | unreviewed | review required | generated index seed only | public, pinned line 99 |
| same | `ofLastStateValue` | def | unreviewed | review required | generated index seed only | public, pinned line 165 |
| same | `stateStepValue_of_projectedStep` | theorem | unreviewed | review required | generated index seed only | public, pinned line 207 |
| same | `ofProjectedLastStateStep` | def | unreviewed | review required | generated index seed only | public, pinned line 276 |
| same | `toValueProcess` | def | unreviewed | review required | generated index seed only | public, pinned line 326 |
| same | `runDistFrom_eq_run` | theorem | unreviewed | review required | generated index seed only | public, pinned line 370 |
| same | `map_observe_runDistFrom_eq_value` | theorem | unreviewed | review required | generated index seed only | public, pinned line 405 |
| same | `map_observe_runDist_eq_value` | theorem | unreviewed | review required | generated index seed only | public, pinned line 415 |
| `GameTheory/Languages/FOSG/ReachableHistory/Law.lean` | `reachableHistoryBehavioralToMixedStrategy_factorAt_of_ignores` | theorem | unreviewed | review required | generated index seed only | public, pinned line 36 |
| same | `reachableHistoryBehavioralToMixedStrategy_factorAt` | theorem | unreviewed | review required | generated index seed only | public, pinned line 100 |
| same | `liftReachableHistoryPureProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 127 |
| same | `reachableHistoryOutcomeDistPureProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 134 |
| same | `liftReachableHistoryMixedProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 144 |
| same | `liftReachableHistoryMixedProfile_joint` | theorem | unreviewed | review required | generated index seed only | public, pinned line 152 |
| same | `reachableHistoryOutcomeDistPure_liftReachableHistoryPureProfile` | theorem | unreviewed | review required | generated index seed only | public, pinned line 170 |
| same | `reachableHistoryPureStepDist_eq_runDistFrom_one` | theorem | unreviewed | review required | generated index seed only | public, pinned line 179 |
| same | `reachableHistoryOutcomeDistPureProfile_eq_runDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 272 |
| same | `reachableLegalFallbackBehavioral` | def | unreviewed | review required | generated index seed only | public, pinned line 316 |
| same | `eraseReachableHistoryBehavioral` | def | unreviewed | review required | generated index seed only | public, pinned line 324 |
| same | `reachableHistoryBehavioralJointActionDist_map_val` | theorem | unreviewed | review required | generated index seed only | public, pinned line 330 |
| same | `reachableHistoryBehavioralStepDist_eq_runDistFrom_one` | theorem | unreviewed | review required | generated index seed only | public, pinned line 380 |
| same | `reachableHistoryOutcomeDist_eq_runDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 487 |
| same | `eraseReachableHistoryBehavioral_isLegal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 526 |
| same | `reachableLegalHistoryMixedToBehavioral` | def | unreviewed | review required | generated index seed only | public, pinned line 545 |
| same | `reachableMixedToLegalBehavioral` | def | unreviewed | review required | generated index seed only | public, pinned line 562 |
| same | `reachableMixedToLegalBehavioral_toProfile` | theorem | unreviewed | review required | generated index seed only | public, pinned line 574 |
| same | `reachableLegalHistoryMixedToBehavioral_historyOutcomeDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 584 |
| same | `reachable_mixed_to_behavioral` | theorem | unreviewed | review required | generated index seed only | public, pinned line 631 |
| same | `reachable_mixed_to_legal_behavioral` | theorem | unreviewed | review required | generated index seed only | public, pinned line 656 |
| same | `reachable_mixed_to_legal_behavioral_runDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 688 |
| same | `reachableMixedToLegalBehavioral_runDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 711 |
| same | `reachable_mixed_to_canonical_behavioral_unilateral_deviation_runDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 742 |
| same | `reachableLegalHistoryMixedToBehavioral_unilateral_deviation_runDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 767 |
| same | `reachable_unilateral_target_toProfile` | theorem | unreviewed | review required | generated index seed only | public, pinned line 904 |
| same | `reachable_mixed_to_behavioral_unilateral_deviation_runDist_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 951 |
| same | `reachable_mixed_to_behavioral_unilateral_deviation_runDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1022 |
| same | `reachableLegalPureStrategyDefault` | def | unreviewed | review required | generated index seed only | public, pinned line 1042 |
| same | `reachableDefaultMixedProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 1056 |
| same | `reachableMixedToLegalBehavioralStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 1063 |
| same | `reachableMixedToLegalBehavioralStrategy_eq_component` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1071 |
| same | `reachableMixedPureGameFormAtHorizon` | def | unreviewed | review required | generated index seed only | public, pinned line 1086 |
| same | `reachableBehavioralGameFormAtHorizon` | def | unreviewed | review required | generated index seed only | public, pinned line 1096 |
| same | `reachableKuhnNashDeviationSimulation` | def | unreviewed | review required | generated index seed only | public, pinned line 1107 |
| same | `reachableKuhn_target_nashFor_of_source_nashFor` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1137 |
| same | `reachableKuhnCoarseCorrelatedDeviationSimulation` | def | unreviewed | review required | generated index seed only | public, pinned line 1158 |
| same | `reachableKuhnCorrelatedDeviationSimulation` | def | unreviewed | review required | generated index seed only | public, pinned line 1192 |
| same | `reachable_mixed_to_legal_behavioral_mapped_runDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1238 |
| same | `legalPureMixedProfileRestrictReachable` | def | unreviewed | review required | generated index seed only | public, pinned line 1262 |
| same | `legalPureProfileRestrictReachable` | def | unreviewed | review required | generated index seed only | public, pinned line 1268 |
| same | `legalBehavioralProfileRestrictReachable` | def | unreviewed | review required | generated index seed only | public, pinned line 1273 |
| same | `legalPureMixedProfileRestrictReachable_joint` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1277 |
| same | `legalPureProfileRestrictReachable_extend_runDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1297 |
| same | `legalBehavioralProfileRestrictReachable_extend_runDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1317 |
| same | `mixed_legalPure_to_legalBehavioral_runDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1338 |
| `GameTheory/Languages/FOSG/ReachableHistory/Native.lean` | `HistoryPureProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 32 |
| same | `HistoryBehavioralProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 36 |
| same | `liftHistoryPureStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 40 |
| same | `liftHistoryPureProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 47 |
| same | `liftHistoryMixedProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 53 |
| same | `liftHistoryMixedProfile_joint` | theorem | unreviewed | review required | generated index seed only | public, pinned line 58 |
| same | `historyTraceLast` | def | unreviewed | review required | generated index seed only | public, pinned line 75 |
| same | `historyOutcomeDist` | def | unreviewed | review required | generated index seed only | public, pinned line 80 |
| same | `historyOutcomeDistPure` | def | unreviewed | review required | generated index seed only | public, pinned line 88 |
| same | `HistoryStepMassInvariant` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 95 |
| same | `HistoryStepSupportFactorization` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 100 |
| same | `HistoryActionPosteriorLocal` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 105 |
| same | `mixed_to_behavioral_native_history` | theorem | unreviewed | review required | generated index seed only | public, pinned line 116 |
| same | `historyOutcomeDistPure_liftHistoryPureProfile` | theorem | unreviewed | review required | generated index seed only | public, pinned line 145 |
| same | `mixed_to_behavioral` | theorem | unreviewed | review required | generated index seed only | public, pinned line 159 |
| same | `mixed_to_behavioral_historyProb` | theorem | unreviewed | review required | generated index seed only | public, pinned line 179 |
| same | `mixed_to_behavioral_historyMassOn` | theorem | unreviewed | review required | generated index seed only | public, pinned line 199 |
| same | `IsLegalMixedProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 224 |
| same | `legalFallbackBehavioral` | def | unreviewed | review required | generated index seed only | public, pinned line 231 |
| same | `legalFallbackBehavioral_isLegal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 240 |
| same | `legalHistoryMixedToBehavioral` | def | unreviewed | review required | generated index seed only | public, pinned line 263 |
| same | `legalHistoryMixedToBehavioral_historyOutcomeDist` | theorem | unreviewed | review required | generated index seed only | public, pinned line 276 |
| same | `legalHistoryMixedToBehavioral_isLegal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 307 |
| same | `mixed_to_legal_behavioral` | theorem | unreviewed | review required | generated index seed only | public, pinned line 372 |
| same | `ReachableInfoLegalMove` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 403 |
| same | `reachable_availableMoves_nonempty` | theorem | unreviewed | review required | generated index seed only | public, pinned line 408 |
| same | `reachableInfoLegalMoveDefault` | def | unreviewed | review required | generated index seed only | public, pinned line 415 |
| same | `ReachableMixedProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 435 |
| same | `reachableLegalPureStrategyFintype` | instance | unreviewed | review required | generated index seed only | public, pinned line 438 |
| same | `reachableInfoStateDecidableEq` | instance | unreviewed | review required | generated index seed only | public, pinned line 446 |
| same | `reachableMixedProfileJoint` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 451 |
| same | `toReachableHistoryObsModelCore` | def | unreviewed | review required | generated index seed only | public, pinned line 464 |
| same | `reachableHistoryInfoStateFintype` | instance | unreviewed | review required | generated index seed only | public, pinned line 495 |
| same | `reachableInfoLegalMoveFintype` | instance | unreviewed | review required | generated index seed only | public, pinned line 502 |
| same | `reachableHistoryLocalStrategyFintype` | instance | unreviewed | review required | generated index seed only | public, pinned line 510 |
| `GameTheory/Languages/FOSG/ReachableHistory/ObsModelFacts.lean` | `reachableHistoryOutcomeDist` | def | unreviewed | review required | generated index seed only | public, pinned line 33 |
| same | `reachableHistoryOutcomeDistPure` | def | unreviewed | review required | generated index seed only | public, pinned line 43 |
| same | `ReachableHistoryStepMassInvariant` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 53 |
| same | `ReachableHistoryStepSupportFactorization` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 60 |
| same | `ReachableHistoryActionPosteriorLocal` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 67 |
| same | `reachableInfoLegalMove_eq_none_of_terminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 72 |
| same | `reachableHistory_stepActionDeterminism` | theorem | unreviewed | review required | generated index seed only | public, pinned line 92 |
| same | `reachableHistory_stepMassInvariant` | theorem | unreviewed | review required | generated index seed only | public, pinned line 198 |
| same | `reachableHistory_stepSupportFactorization` | theorem | unreviewed | review required | generated index seed only | public, pinned line 204 |
| same | `playerViewFrom_cons_eq_cons_view` | theorem | unreviewed | review required | generated index seed only | public, pinned line 210 |
| same | `playerViewFrom_cons_eq_cons_action` | theorem | unreviewed | review required | generated index seed only | public, pinned line 238 |
| same | `playerViewFrom_cons_ne_nil` | theorem | unreviewed | review required | generated index seed only | public, pinned line 266 |
| same | `playerViewFrom_append_singleton_ne_nil` | theorem | unreviewed | review required | generated index seed only | public, pinned line 275 |
| same | `playerViewFrom_append_singleton_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 284 |
| same | `publicViewFrom_length` | theorem | unreviewed | review required | generated index seed only | public, pinned line 343 |
| same | `publicView_length` | theorem | unreviewed | review required | generated index seed only | public, pinned line 350 |
| same | `reachableInfoLegalMove_eq_none_of_terminal_view_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 354 |
| same | `reachableInfoLegalMove_subsingleton_of_terminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 379 |
| same | `reachableHistory_projectStates_eq_last` | theorem | unreviewed | review required | generated index seed only | public, pinned line 388 |
| same | `reachableInfoLegalMove_cast_val` | theorem | unreviewed | review required | generated index seed only | public, pinned line 396 |
| same | `reachableInfoLegalMove_cast_currentObs_val` | theorem | unreviewed | review required | generated index seed only | public, pinned line 403 |
| same | `subst_heq_fosg` | theorem | unreviewed | review required | generated index seed only | public, pinned line 415 |
| same | `reachableHistory_castJointAction_val` | theorem | unreviewed | review required | generated index seed only | public, pinned line 420 |
| same | `projectActions_snoc_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 435 |
| same | `sourceView_and_ownAction_eq_of_target_view_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 472 |
| same | `reachableHistory_pureStep_snoc` | theorem | unreviewed | review required | generated index seed only | public, pinned line 496 |
| same | `reachableHistory_source_nonterminal_of_target_nonterminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 568 |
| same | `reachableHistory_pureRun_last_steps_length_le` | theorem | unreviewed | review required | generated index seed only | public, pinned line 598 |
| same | `reachableHistory_pureStep_component_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 656 |
| same | `reachableHistory_pureRun_update_obs_local_nonterminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 725 |
| same | `reachableHistory_pureRun_nonterminal_last_steps_length` | theorem | unreviewed | review required | generated index seed only | public, pinned line 835 |
| same | `reachableHistory_repeated_projectStates_subsingleton` | theorem | unreviewed | review required | generated index seed only | public, pinned line 876 |
| same | `reachableHistory_current_coord_ignores_of_reachable` | theorem | unreviewed | review required | generated index seed only | public, pinned line 937 |
| same | `reachableHistory_obsLocalFeasibility` | theorem | unreviewed | review required | generated index seed only | public, pinned line 996 |
| same | `reachableHistory_actionPosteriorLocal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1067 |
| same | `ownAction_eq_of_source_target_view_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1080 |
| same | `liftReachableHistoryPureStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 1121 |
| same | `reachableInfoLegalMoveOfBehavioralSupport` | def | unreviewed | review required | generated index seed only | public, pinned line 1140 |
| same | `liftReachableHistoryBehavioralStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 1158 |
| same | `erase_liftReachableHistoryBehavioralStrategy` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1168 |
| same | `eraseReachableHistoryPureStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 1211 |
| same | `liftReachableHistoryPureStrategy_erase` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1224 |
| same | `reachableHistoryBehavioralToMixedStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 1237 |
| same | `reachableLegalBehavioralToMixed` | def | unreviewed | review required | generated index seed only | public, pinned line 1254 |
| same | `reachableLegalBehavioralToMixed_lift` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1262 |
| same | `liftReachableHistoryBehavioralProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 1281 |
| `GameTheory/Languages/FOSG/Serial.lean` | `singleMove` | def | unreviewed | review required | generated index seed only | public, pinned line 46 |
| same | `singleMove_self` | theorem | unreviewed | review required | generated index seed only | public, pinned line 53 |
| same | `singleMove_other` | theorem | unreviewed | review required | generated index seed only | public, pinned line 57 |
| same | `ExtendsPartial` | def | unreviewed | review required | generated index seed only | public, pinned line 63 |
| same | `recordChoice` | def | unreviewed | review required | generated index seed only | public, pinned line 69 |
| same | `recordChoice_self` | theorem | unreviewed | review required | generated index seed only | public, pinned line 73 |
| same | `recordChoice_other` | theorem | unreviewed | review required | generated index seed only | public, pinned line 78 |
| same | `extendsPartial_noop` | theorem | unreviewed | review required | generated index seed only | public, pinned line 83 |
| same | `extendsPartial_recordChoice` | theorem | unreviewed | review required | generated index seed only | public, pinned line 91 |
| same | `MatchesActedPrefix` | def | unreviewed | review required | generated index seed only | public, pinned line 108 |
| same | `prefixChoice` | def | unreviewed | review required | generated index seed only | public, pinned line 115 |
| same | `playerLegal` | def | unreviewed | review required | generated index seed only | public, pinned line 125 |
| same | `eq_singleMove_of_current_some_other_none` | theorem | unreviewed | review required | generated index seed only | public, pinned line 131 |
| same | `playerLegal_iff_exists_singleMove` | theorem | unreviewed | review required | generated index seed only | public, pinned line 142 |
| same | `playerLegal_current_some` | theorem | unreviewed | review required | generated index seed only | public, pinned line 157 |
| same | `playerLegal_other_none` | theorem | unreviewed | review required | generated index seed only | public, pinned line 162 |
| same | `baseChanceLegalAction` | def | unreviewed | review required | generated index seed only | public, pinned line 168 |
| same | `baseChanceLegalAction_val` | theorem | unreviewed | review required | generated index seed only | public, pinned line 172 |
| same | `actionAtActive` | def | unreviewed | review required | generated index seed only | public, pinned line 178 |
| same | `actionAtActive_spec` | theorem | unreviewed | review required | generated index seed only | public, pinned line 182 |
| same | `moveOfLegalAction` | def | unreviewed | review required | generated index seed only | public, pinned line 189 |
| same | `moveOfLegalAction_current` | theorem | unreviewed | review required | generated index seed only | public, pinned line 194 |
| same | `moveOfLegalAction_other` | theorem | unreviewed | review required | generated index seed only | public, pinned line 200 |
| same | `matchesActedPrefix_noop` | theorem | unreviewed | review required | generated index seed only | public, pinned line 206 |
| same | `matchesActedPrefix_prefixChoice` | theorem | unreviewed | review required | generated index seed only | public, pinned line 212 |
| same | `prefixChoice_nil` | theorem | unreviewed | review required | generated index seed only | public, pinned line 218 |
| same | `prefixChoice_apply_of_mem` | theorem | unreviewed | review required | generated index seed only | public, pinned line 224 |
| same | `prefixChoice_apply_of_not_mem` | theorem | unreviewed | review required | generated index seed only | public, pinned line 230 |
| same | `matchesActedPrefix_recordChoice_move` | theorem | unreviewed | review required | generated index seed only | public, pinned line 236 |
| same | `prefixChoice_recordChoice_move` | theorem | unreviewed | review required | generated index seed only | public, pinned line 250 |
| same | `orderedActive` | def | unreviewed | review required | generated index seed only | public, pinned line 270 |
| same | `mem_orderedActive_iff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 274 |
| same | `orderedActive_eq_nil_of_active_eq_empty` | theorem | unreviewed | review required | generated index seed only | public, pinned line 279 |
| same | `active_eq_empty_of_orderedActive_eq_nil` | theorem | unreviewed | review required | generated index seed only | public, pinned line 292 |
| same | `current_mem_active_of_split` | theorem | unreviewed | review required | generated index seed only | public, pinned line 301 |
| same | `current_not_mem_rest_of_split` | theorem | unreviewed | review required | generated index seed only | public, pinned line 312 |
| same | `ValidDecision` | def | unreviewed | review required | generated index seed only | public, pinned line 329 |
| same | `SerialState` | inductive | unreviewed | review required | generated index seed only | public, pinned line 340 |
| same | `active` | def | unreviewed | review required | generated index seed only | public, pinned line 357 |
| same | `terminal` | def | unreviewed | review required | generated index seed only | public, pinned line 367 |
| same | `instDecidablePredTerminal` | instance | unreviewed | review required | generated index seed only | public, pinned line 372 |
| same | `world` | def | unreviewed | review required | generated index seed only | public, pinned line 384 |
| same | `world_base` | theorem | unreviewed | review required | generated index seed only | public, pinned line 389 |
| same | `world_decide` | theorem | unreviewed | review required | generated index seed only | public, pinned line 392 |
| same | `world_chance` | theorem | unreviewed | review required | generated index seed only | public, pinned line 397 |
| same | `legal` | def | unreviewed | review required | generated index seed only | public, pinned line 402 |
| same | `availableActions` | def | unreviewed | review required | generated index seed only | public, pinned line 414 |
| same | `legal_iff_jointActionLegal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 430 |
| same | `LegalAction` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 587 |
| same | `FOSGLegalAction` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 590 |
| same | `toFOSGLegalAction` | def | unreviewed | review required | generated index seed only | public, pinned line 595 |
| same | `ofFOSGLegalAction` | def | unreviewed | review required | generated index seed only | public, pinned line 599 |
| same | `toFOSGLegalAction_val` | theorem | unreviewed | review required | generated index seed only | public, pinned line 603 |
| same | `ofFOSGLegalAction_val` | theorem | unreviewed | review required | generated index seed only | public, pinned line 606 |
| same | `active_eq_empty_of_base_terminal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 609 |
| same | `legalAction_eq_of_extends_matchesOrderedActive` | theorem | unreviewed | review required | generated index seed only | public, pinned line 616 |
| same | `not_mem_acted_of_mem_remaining` | theorem | unreviewed | review required | generated index seed only | public, pinned line 640 |
| same | `validDecision_of_prefix` | theorem | unreviewed | review required | generated index seed only | public, pinned line 654 |
| same | `base_playerLegal_of_legalAction` | theorem | unreviewed | review required | generated index seed only | public, pinned line 670 |
| same | `decide_playerLegal_of_legalAction` | theorem | unreviewed | review required | generated index seed only | public, pinned line 684 |
| same | `validDecision_from_base` | theorem | unreviewed | review required | generated index seed only | public, pinned line 701 |
| same | `validDecision_step` | theorem | unreviewed | review required | generated index seed only | public, pinned line 718 |
| same | `basePlayerSuccessorWithOrder` | def | unreviewed | review required | generated index seed only | public, pinned line 740 |
| same | `basePlayerSuccessor` | def | unreviewed | review required | generated index seed only | public, pinned line 758 |
| same | `world_basePlayerSuccessorWithOrder` | theorem | unreviewed | review required | generated index seed only | public, pinned line 763 |
| same | `world_basePlayerSuccessor` | theorem | unreviewed | review required | generated index seed only | public, pinned line 778 |
| same | `decidePlayerSuccessor` | def | unreviewed | review required | generated index seed only | public, pinned line 786 |
| same | `world_decidePlayerSuccessor` | theorem | unreviewed | review required | generated index seed only | public, pinned line 803 |
| same | `baseReplayAction` | def | unreviewed | review required | generated index seed only | public, pinned line 815 |
| same | `basePlayerSuccessorWithOrder_replay_cons` | theorem | unreviewed | review required | generated index seed only | public, pinned line 825 |
| same | `basePlayerSuccessorWithOrder_replay_last` | theorem | unreviewed | review required | generated index seed only | public, pinned line 843 |
| same | `basePlayerSuccessor_replay_cons` | theorem | unreviewed | review required | generated index seed only | public, pinned line 877 |
| same | `basePlayerSuccessor_replay_last` | theorem | unreviewed | review required | generated index seed only | public, pinned line 892 |
| same | `decideReplayAction` | def | unreviewed | review required | generated index seed only | public, pinned line 907 |
| same | `decidePlayerSuccessor_replay_cons` | theorem | unreviewed | review required | generated index seed only | public, pinned line 927 |
| same | `decidePlayerSuccessor_replay_last` | theorem | unreviewed | review required | generated index seed only | public, pinned line 946 |
| same | `chanceResolutionAction` | def | unreviewed | review required | generated index seed only | public, pinned line 991 |
| same | `transition` | def | unreviewed | review required | generated index seed only | public, pinned line 997 |
| same | `transition_base_empty_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1013 |
| same | `transition_base_nonempty_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1025 |
| same | `transition_decide_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1032 |
| same | `reward` | def | unreviewed | review required | generated index seed only | public, pinned line 1043 |
| same | `reward_decide_eq_zero` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1063 |
| same | `reward_chance_base_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1072 |
| same | `reward_decide_successor_eq_zero` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1079 |
| same | `reward_basePlayerSuccessor_eq_zero` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1089 |
| same | `reward_base_empty_base_eq_of_active_empty` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1097 |
| same | `privObs` | def | unreviewed | review required | generated index seed only | public, pinned line 1148 |
| same | `privObs_decide_eq_none` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1169 |
| same | `privObs_chance_base_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1178 |
| same | `privObs_decide_successor_eq_none` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1185 |
| same | `pubObs` | def | unreviewed | review required | generated index seed only | public, pinned line 1197 |
| same | `pubObs_decide_eq_none` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1217 |
| same | `pubObs_chance_base_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1226 |
| same | `pubObs_decide_successor_eq_none` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1233 |
| same | `pubObs_basePlayerSuccessor_eq_none` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1242 |
| same | `pubObs_base_empty_base_eq_of_active_empty` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1250 |
| same | `bookkeeping_decide_step` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1302 |
| same | `resolution_chance_step` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1323 |
| same | `map_base_apply` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1337 |
| same | `map_base_apply_decide` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1349 |
| same | `map_base_apply_chance` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1358 |
| same | `base_empty_support` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1366 |
| same | `chance_support` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1387 |
| same | `serialize` | def | unreviewed | review required | generated index seed only | public, pinned line 1396 |
| same | `instDecidablePredSerializeTerminal` | instance | unreviewed | review required | generated index seed only | public, pinned line 1453 |
| same | `IsSerial` | def | unreviewed | review required | generated index seed only | public, pinned line 1466 |
| same | `serialize_isSerial` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1471 |
| `GameTheory/Languages/FOSG/Strategy.lean` | `availableMovesAtState` | def | unreviewed | review required | generated index seed only | public, pinned line 40 |
| same | `mem_availableMovesAtState_iff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 45 |
| same | `availableActionsAtHistory` | def | unreviewed | review required | generated index seed only | public, pinned line 53 |
| same | `mem_availableActionsAtHistory_iff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 58 |
| same | `availableActionsAtHistory_eq_availableActionsAtState_of_mem_active` | theorem | unreviewed | review required | generated index seed only | public, pinned line 65 |
| same | `availableActionsAtHistory_eq_empty_of_not_mem_active` | theorem | unreviewed | review required | generated index seed only | public, pinned line 71 |
| same | `availableMoves` | def | unreviewed | review required | generated index seed only | public, pinned line 79 |
| same | `mem_availableMoves_iff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 84 |
| same | `availableMoves_nonempty` | theorem | unreviewed | review required | generated index seed only | public, pinned line 95 |
| same | `availableMoves_eq_availableMovesAtState` | theorem | unreviewed | review required | generated index seed only | public, pinned line 110 |
| same | `availableMoves_eq_singleton_none_of_not_mem_active` | theorem | unreviewed | review required | generated index seed only | public, pinned line 116 |
| same | `LegalObservable` | def | unreviewed | review required | generated index seed only | public, pinned line 129 |
| same | `availableMoves_eq_of_playerView_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 134 |
| same | `availableActions_eq_of_playerView_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 142 |
| same | `availableMovesAtInfoState` | def | unreviewed | review required | generated index seed only | public, pinned line 163 |
| same | `mem_availableMovesAtInfoState_iff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 168 |
| same | `mem_availableMovesAtInfoState_of_history` | theorem | unreviewed | review required | generated index seed only | public, pinned line 175 |
| same | `availableMovesAtInfoState_eq_of_history` | theorem | unreviewed | review required | generated index seed only | public, pinned line 182 |
| same | `availableActionsAtInfoState` | def | unreviewed | review required | generated index seed only | public, pinned line 197 |
| same | `availableActionsAtInfoState_eq_of_history` | theorem | unreviewed | review required | generated index seed only | public, pinned line 202 |
| same | `PureStrategy` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 216 |
| same | `BehavioralStrategy` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 221 |
| same | `PureProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 225 |
| same | `BehavioralProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 229 |
| same | `ofLatestObservation@238` | def | unreviewed | review required | generated index seed only | public, pinned line 238 |
| same | `ofLatestObservation_nil@247` | theorem | unreviewed | review required | generated index seed only | public, pinned line 247 |
| same | `ofLatestObservation_eq_policy@252` | theorem | unreviewed | review required | generated index seed only | public, pinned line 252 |
| same | `ofLatestObservation@269` | def | unreviewed | review required | generated index seed only | public, pinned line 269 |
| same | `ofLatestObservation_nil@278` | theorem | unreviewed | review required | generated index seed only | public, pinned line 278 |
| same | `ofLatestObservation_eq_policy@283` | theorem | unreviewed | review required | generated index seed only | public, pinned line 283 |
| same | `ofLatestObservation@299` | def | unreviewed | review required | generated index seed only | public, pinned line 299 |
| same | `ofLatestObservation_nil@307` | theorem | unreviewed | review required | generated index seed only | public, pinned line 307 |
| same | `ofLatestObservation@321` | def | unreviewed | review required | generated index seed only | public, pinned line 321 |
| same | `ofLatestObservation_nil@329` | theorem | unreviewed | review required | generated index seed only | public, pinned line 329 |
| same | `IsLegalPureStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 339 |
| same | `IsLegalBehavioralStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 346 |
| same | `IsLegalPureProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 354 |
| same | `IsLegalBehavioralProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 360 |
| same | `legalBehavioralStrategy_eq_pure_none_of_not_mem_active` | theorem | unreviewed | review required | generated index seed only | public, pinned line 365 |
| same | `LegalPureStrategy` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 398 |
| same | `LegalBehavioralStrategy` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 403 |
| same | `LegalPureProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 408 |
| same | `LegalBehavioralProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 413 |
| same | `LegalPureProfile.toProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 418 |
| same | `LegalBehavioralProfile.toProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 424 |
| same | `legalPureProfile_toProfile_apply` | theorem | unreviewed | review required | generated index seed only | public, pinned line 429 |
| same | `legalBehavioralProfile_toProfile_apply` | theorem | unreviewed | review required | generated index seed only | public, pinned line 434 |
| same | `ReachableInfoState` | def | unreviewed | review required | generated index seed only | public, pinned line 440 |
| same | `reachableInfoStateOfHistory` | def | unreviewed | review required | generated index seed only | public, pinned line 445 |
| same | `reachableInfoStateOfHistory_val` | theorem | unreviewed | review required | generated index seed only | public, pinned line 450 |
| same | `instFintypeReachableInfoState` | instance | unreviewed | review required | generated index seed only | public, pinned line 454 |
| same | `ReachablePureStrategy` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 470 |
| same | `ReachableBehavioralStrategy` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 475 |
| same | `ReachablePureProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 480 |
| same | `ReachableBehavioralProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 484 |
| same | `instFintypeReachablePureStrategy` | instance | unreviewed | review required | generated index seed only | public, pinned line 487 |
| same | `instFintypeReachablePureProfile` | instance | unreviewed | review required | generated index seed only | public, pinned line 495 |
| same | `IsLegalReachablePureStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 505 |
| same | `IsLegalReachableBehavioralStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 512 |
| same | `ReachableLegalPureStrategy` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 520 |
| same | `ReachableLegalBehavioralStrategy` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 525 |
| same | `ReachableLegalPureProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 530 |
| same | `ReachableLegalBehavioralProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 534 |
| same | `ReachableLegalPureProfile.toProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 538 |
| same | `ReachableLegalBehavioralProfile.toProfile` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 544 |
| same | `PureStrategy.restrictReachable` | def | unreviewed | review required | generated index seed only | public, pinned line 550 |
| same | `BehavioralStrategy.restrictReachable` | def | unreviewed | review required | generated index seed only | public, pinned line 556 |
| same | `LegalPureStrategy.restrictReachable` | def | unreviewed | review required | generated index seed only | public, pinned line 562 |
| same | `LegalBehavioralStrategy.restrictReachable` | def | unreviewed | review required | generated index seed only | public, pinned line 568 |
| same | `ReachablePureStrategy.extend` | def | unreviewed | review required | generated index seed only | public, pinned line 575 |
| same | `ReachableBehavioralStrategy.extend` | def | unreviewed | review required | generated index seed only | public, pinned line 584 |
| same | `ReachablePureStrategy.extend_apply_history` | theorem | unreviewed | review required | generated index seed only | public, pinned line 591 |
| same | `ReachableBehavioralStrategy.extend_apply_history` | theorem | unreviewed | review required | generated index seed only | public, pinned line 602 |
| same | `ReachablePureProfile.extend` | def | unreviewed | review required | generated index seed only | public, pinned line 614 |
| same | `ReachableBehavioralProfile.extend` | def | unreviewed | review required | generated index seed only | public, pinned line 620 |
| same | `ReachablePureStrategy.isLegal_extend` | theorem | unreviewed | review required | generated index seed only | public, pinned line 625 |
| same | `ReachableBehavioralStrategy.isLegal_extend` | theorem | unreviewed | review required | generated index seed only | public, pinned line 633 |
| same | `ReachableLegalPureProfile.extend` | def | unreviewed | review required | generated index seed only | public, pinned line 642 |
| same | `ReachableLegalBehavioralProfile.extend` | def | unreviewed | review required | generated index seed only | public, pinned line 650 |
| same | `pureToBehavioral` | def | unreviewed | review required | generated index seed only | public, pinned line 657 |
| same | `pureToBehavioral_apply` | theorem | unreviewed | review required | generated index seed only | public, pinned line 662 |
| same | `legalBehavioral_of_legalPure` | theorem | unreviewed | review required | generated index seed only | public, pinned line 667 |
| same | `legalPureToBehavioral` | def | unreviewed | review required | generated index seed only | public, pinned line 679 |
| same | `MarkovJointPolicy` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 691 |
| same | `PureMarkovJointPolicy` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 695 |
| same | `pureMarkovToBehavioral` | def | unreviewed | review required | generated index seed only | public, pinned line 699 |
| same | `pureMarkovToBehavioral_apply` | theorem | unreviewed | review required | generated index seed only | public, pinned line 704 |
| same | `stepProb` | def | unreviewed | review required | generated index seed only | public, pinned line 710 |
| same | `pathProb` | def | unreviewed | review required | generated index seed only | public, pinned line 716 |
| same | `prob` | def | unreviewed | review required | generated index seed only | public, pinned line 723 |
| same | `pathProb_nil` | theorem | unreviewed | review required | generated index seed only | public, pinned line 728 |
| same | `pathProb_cons` | theorem | unreviewed | review required | generated index seed only | public, pinned line 733 |
| same | `prob_nil` | theorem | unreviewed | review required | generated index seed only | public, pinned line 738 |
| same | `pathProb_append_singleton` | theorem | unreviewed | review required | generated index seed only | public, pinned line 743 |
| same | `prob_snoc` | theorem | unreviewed | review required | generated index seed only | public, pinned line 753 |
| `GameTheory/Languages/FOSG/Values.lean` | `reward` | abbrev | adapt | external `value` parameter of `FOSG.Game.cumulativeValue` | `GameTheory.Protocol.History`; focused Values build (1,722 jobs) | A FOSG has no privileged reward field; transition values remain application data. |
| same | `rewardSumFrom` | def | retired | `ExecutionProtocol.Trace.valueSum` | focused Values build (1,722 jobs) | The predecessor fold consumed a bare list, which cannot certify that adjacent steps form one realized execution. |
| same | `rewardSum` | def | adapt | `FOSG.Game.cumulativeValue`; `ExecutionProtocol.History.valueSum` | focused Values build (1,722 jobs) | The canonical indexed history is folded directly. |
| same | `utility` | abbrev | retired | caller vocabulary | D15; focused Values build (1,722 jobs) | Protocol and FOSG deliberately do not choose whether an external value is a utility, reward, cost, or vector payoff. |
| same | `rewardSumFrom_nil` | theorem | retired | `ExecutionProtocol.Trace.valueSum_start` | focused Values build (1,722 jobs) | The checked zero law is stated on an indexed trace rather than an arbitrary list. |
| same | `rewardSumFrom_cons` | theorem | retired | `ExecutionProtocol.Trace.valueSum_extend` | focused Values build (1,722 jobs) | An indexed realized extension replaces unconstrained list cons. |
| same | `rewardSumFrom_append_singleton` | theorem | retired | `ExecutionProtocol.History.valueSum_extend` | focused Values build (1,722 jobs) | Complete traces have dependent endpoints and no sound unrestricted append operation. |
| same | `rewardSumFrom_append` | theorem | retired | no canonical successor | focused Values build (1,722 jobs) | Arbitrary list append would lose the endpoint witness supplied by the indexed trace. |
| same | `rewardSum_nil` | theorem | adapt | `ExecutionProtocol.History.valueSum_init`; `FOSG.Game.cumulativeValue_init` | focused Values build (1,722 jobs) | Initial canonical history has zero cumulative externally supplied value. |
| same | `utility_nil` | theorem | retired | `ExecutionProtocol.History.valueSum_init` | focused Values build (1,722 jobs) | The value law survives; the language-local utility alias does not. |
| same | `rewardSum_snoc` | theorem | adapt | `ExecutionProtocol.History.valueSum_extend`; `FOSG.Game.cumulativeValue_extend` | focused Values build (1,722 jobs) | One realized legal extension adds exactly its caller-supplied transition value. |
| same | `utility_snoc` | theorem | retired | `FOSG.Game.cumulativeValue_extend` | focused Values build (1,722 jobs) | The mathematical extension law survives without fixing a utility vocabulary. |
| same | `utility_def` | theorem | retired | `FOSG.Game.cumulativeValue` | D15; focused Values build (1,722 jobs) | No second name is needed for a transparent external value fold. |

The Values batch has 4 adapted and 9 retired declarations.  Its focused build,
the integrated Phase 2/3 gates, and the coverage audit pass; `#print axioms`
for both canonical extension laws reports only `propext`, `Classical.choice`,
and `Quot.sound`.

Before this ledger can become complete, each row must be reviewed against
the canonical successor API and assigned an allowed non-`unreviewed`
disposition with concrete build, theorem, decision, or counterexample
evidence. Generated name similarity is never sufficient.
