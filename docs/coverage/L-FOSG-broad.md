# L-FOSG: Broad factored-observation stochastic-game recovery

Title: Broad factored-observation stochastic-game recovery
Family ID: L-FOSG
Pinned roots: `GameTheory/Languages/FOSG/Basic.lean`; `GameTheory/Languages/FOSG/Compile.lean`; `GameTheory/Languages/FOSG/Examples.lean`; `GameTheory/Languages/FOSG/Execution.lean`; `GameTheory/Languages/FOSG/History.lean`; `GameTheory/Languages/FOSG/Information.lean`; `GameTheory/Languages/FOSG/Native/History.lean`; `GameTheory/Languages/FOSG/Native/HistoryMarginal.lean`; `GameTheory/Languages/FOSG/Native/Reachable.lean`; `GameTheory/Languages/FOSG/Native/StepIndependence.lean`; `GameTheory/Languages/FOSG/Native/TerminalLaw.lean`; `GameTheory/Languages/FOSG/OutcomeClosure.lean`; `GameTheory/Languages/FOSG/ReachableHistory/Law.lean`; `GameTheory/Languages/FOSG/ReachableHistory/Native.lean`; `GameTheory/Languages/FOSG/ReachableHistory/ObsModelFacts.lean`; `GameTheory/Languages/FOSG/Serial.lean`; `GameTheory/Languages/FOSG/Strategy.lean`; `GameTheory/Languages/FOSG/Values.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `01f790a`
Canonical destination: GameTheory.Languages.FOSG; GameTheory.Protocol; named EFG/FOSG bridges
Domain contract / decision: D6, D7, D11, D12, D15, EXP-042, EXP-057/D28, EXP-058/D29, EXP-059/060/061/D30
Owner: Wave 3 / sequential and language recovery
Status: in progress; 695/776 reviewed, 81 unreviewed
Last verified: 2026-08-03

This ledger is an exact generated review queue for the L-FOSG family.
0 declarations are already accounted for in earlier bounded ledgers and are
not duplicated here. Rows not yet classified remain deliberately
`unreviewed`: the generated index supplies spelling, location, kind, and
visibility only. It does not infer a mathematical disposition. Reviewed batches
cover the complete `Basic.lean` legality substrate, `History.lean` canonical
history migration, `Information.lean` canonical information-model migration,
`Strategy.lean` canonical policy migration, `Execution.lean` canonical
law-valued execution migration, `Values.lean` external-value fold, and the
`Native/History.lean` / `Native/HistoryMarginal.lean` Kuhn batch.  EXP-057/D28
attributes the latter to those exact pinned paths: `Protocol.Information`
owns the canonical policy and law machinery, while `Languages.FOSG.Kuhn`
supplies the named FOSG-facing correspondence.  It does not revive the native scalar
marginal calculus.

The `Native/Reachable.lean`, `Native/StepIndependence.lean`,
`Native/TerminalLaw.lean`, and `OutcomeClosure.lean` batch is now classified.
Canonical behavioral-to-mixed equality adapts three complete-history rows with
the explicit `ActsOnceWhereItMatters` premise it actually needs.  Four
mixture-over-pure-policy marginal identities remain behind a named canonical
behavioral-mixture marginal gate; definitions of the joint law and runner are
not credited as proofs.  The parallel scalar, profile-swapping, and seen-before
machinery is retired.  Terminal-support and ordinary continuation
coefficients remain deferred to the ordinary-continuation/terminal-support
gate; utility and expectation transfer remain deferred to the
external-evaluation/strategic gate.  `OutcomeClosure` retains neither a
language-local outcome-value process nor a parallel runner: its stopped-step
equations are subsumed by the audited Protocol runner laws, and its remaining
outcome-value/process closure surface awaits the
ordinary-continuation/outcome-value-process gate.

EXP-059/061/D30 disposes the 65-declaration `Compile.lean` batch (the earlier
54-row estimate missed attributed declarations). Canonical Protocol runners and
`BoundedHorizon` retain the genuine execution fragments; the duplicate PMF
terminal-law, finite enumeration, transport, and KernelGame compiler are
retired. Terminal-support and coefficient laws remain deferred to the
ordinary-continuation coefficient gate; generic serialization no longer blocks
them but does not by itself prove their scalar coefficient statements.
EXP-060 closes the required two-round signal-replay risk with exact source
history carriage, resolver-only public/private/own-action replay, inactive
slots, arbitrary target-profile projection, and a literal six-step/two-round
history law in either order.  EXP-061 promotes the stable generic
explicit-order adapter after reproducing those obligations for every target
behavioral profile and finite round count.  The existing `Compile.lean`
dispositions and counts remain unchanged: canonical Protocol runners still
subsume its live execution fragments, while the promoted serializer supplies a
different named FOSG-to-EFG comparison rather than reviving the pinned
scalar/PMF compiler.

The complete `Examples.lean` batch contributes one stable code recovery:
`GameTheory.Examples.FOSG`, a utility-free simultaneous two-bit FOSG compiled
through the canonical NFG-to-FOSG path and used for exact FOSG-to-EFG
history-law regressions.  Eleven declarations adapt to that witness, five are
subsumed by canonical one-shot execution, and the remaining fixture,
enumeration, handwritten kernel, and bounded-evaluator surface is retired.
`Serial.lean` is fully accounted: 46 structural declarations are subsumed by
`Languages.Bridges.FOSGToEFG`; its other 62 declarations are retired.  In
particular, its reward and support facts are not deferred ports: they describe
a serializer the pinned module itself says is not semantics-preserving.  Any
future utility or terminal-support bridge theorem begins over the canonical
generic bridge under its own gate.

EXP-058/D29 disposes `ReachableHistory/ObsModelFacts.lean`.  Only its two
final-law definitions project directly to canonical Protocol execution, and
its action-projection append theorem is subsumed by the richer
`InfoSignals.ownPlay_extend`.  The remaining rows are implementation facts for
the removed reachable-history observation model: scalar invariants, posterior
predicates, cast transport, raw-history arithmetic, and lift/erase
machinery.  This disposition does not credit counterfactual reach or CFR;
those remain separately gated.

The Execution batch maps ordinary one-step, continuation, and complete-history
reach to `behavioralJoint`, `runBehavioralFrom`, and
`historyReachProbability`.  Two narrowly separated proof spines remain
deferred: an ordinary continuation/history-reach coefficient calculus over
those canonical laws, and the player/counterfactual decomposition calculus
needed by CFR.  Neither gate authorizes a parallel scalar execution semantics.
The exact one-step congruence is now
`InformationModel.behavioralJoint_congr`.

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
| `GameTheory/Languages/FOSG/Compile.lean` | `extendByOutcome` | def | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 39 |
| same | `extendByOutcome_of_support` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 43 |
| same | `extendByOutcome_of_no_support` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 49 |
| same | `extendByOutcome_isPrefix` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 55 |
| same | `extendByOutcome_prefix_canonical_imp` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 65 |
| same | `extendByOutcome_eq_appendStep_of_head` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 87 |
| same | `initialSegment` | def | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 101 |
| same | `initialSegment_steps` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 109 |
| same | `initialSegment_isPrefix` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 112 |
| same | `initialSegment_length` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 117 |
| same | `runDistFrom` | def | adapt | InformationModel.runBehavioralFrom | EXP-059/D30 hostile serialization witness | Canonical Protocol history-runner/horizon API owns this semantic fragment. | public, pinned line 124 |
| same | `runDistFrom_zero` | theorem | subsumed | `InformationModel.runBehavioralFrom` at zero fuel | EXP-059/061/D30 | The canonical Protocol runner reduces definitionally to the pure starting history. | public, pinned line 138 |
| same | `runDistFrom_succ_terminal` | theorem | adapt | ExecutionProtocol.runRandomizedFor_of_terminal | EXP-059/D30 hostile serialization witness | Canonical Protocol history-runner/horizon API owns this semantic fragment. | public, pinned line 145 |
| same | `runDistFrom_terminal` | theorem | adapt | ExecutionProtocol.runRandomizedFor_of_terminal | EXP-059/D30 hostile serialization witness | Canonical Protocol history-runner/horizon API owns this semantic fragment. | public, pinned line 154 |
| same | `runDistFrom_succ_nonterminal` | theorem | adapt | ExecutionProtocol.runRandomizedFor_succ_of_not_terminal | EXP-059/D30 hostile serialization witness | Canonical Protocol history-runner/horizon API owns this semantic fragment. | public, pinned line 165 |
| same | `runDistFrom_congr` | theorem | adapt | InformationModel.runBehavioralFrom_congr | EXP-059/D30 hostile serialization witness | Canonical Protocol history-runner/horizon API owns this semantic fragment. | public, pinned line 177 |
| same | `runDistFrom_bind_runDistFrom` | theorem | adapt | `InformationModel.runBehavioralFrom_add` | EXP-059/061/D30 | Canonical behavioral execution composes across adjacent fuel blocks at full `FinDist History` equality. | public, pinned line 200 |
| same | `runDistFrom_succ_active_empty` | theorem | adapt | ExecutionProtocol.chanceLaw | EXP-059/D30 hostile serialization witness | Canonical Protocol history-runner/horizon API owns this semantic fragment. | public, pinned line 228 |
| same | `runDistFrom_eq_zero_of_exactHorizon_not_prefix` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 244 |
| same | `ExactHorizon` | def | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 302 |
| same | `BoundedHorizon` | def | adapt | ExecutionProtocol.BoundedHorizon | EXP-059/D30 hostile serialization witness | Canonical Protocol history-runner/horizon API owns this semantic fragment. | public, pinned line 309 |
| same | `exactHorizon_iff` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 313 |
| same | `ExactHorizon.bounded` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 319 |
| same | `runDistFrom_eq_zero_of_length_gt` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 326 |
| same | `runDistFrom_eq_zero_of_nonterminal_target_lt` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 373 |
| same | `runDistFrom_eq_zero_of_exactHorizon_length_ne` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 420 |
| same | `runDist` | def | adapt | InformationModel.runBehavioral | EXP-059/D30 hostile serialization witness | Canonical Protocol history-runner/horizon API owns this semantic fragment. | public, pinned line 469 |
| same | `runDist_congr` | theorem | adapt | InformationModel.runBehavioralFrom_congr at initHistory | EXP-059/D30 hostile serialization witness | Canonical Protocol history-runner/horizon API owns this semantic fragment. | public, pinned line 476 |
| same | `runDist_zero` | theorem | subsumed | `InformationModel.runBehavioral` at zero fuel | EXP-059/061/D30 | The canonical initial-history runner reduces definitionally to a point mass. | public, pinned line 486 |
| same | `runDist_eq_zero_of_exactHorizon_length_ne` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 493 |
| same | `runDist_eq_zero_of_length_gt` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 505 |
| same | `runDist_eq_zero_of_nonterminal_of_boundedHorizon` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 516 |
| same | `runDist_support_isTerminal_of_boundedHorizon` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 535 |
| same | `runDistFrom_eq_zero_of_terminal_not_prefix` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 548 |
| same | `runDistFrom_eq_probFrom_of_terminal_target` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 601 |
| same | `runDist_support_isTerminal_of_exactHorizon` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 785 |
| same | `runDistFrom_eq_probFrom_of_exactHorizon` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 801 |
| same | `runDist_eq_terminalWeight_of_exactHorizon` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 988 |
| same | `length_le_of_boundedHorizon` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 1011 |
| same | `history_length_le_of_boundedHorizon` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 1042 |
| same | `historyFintypeOfLengthLe` | def | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1075 |
| same | `historyFintypeOfBoundedHorizon` | def | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1098 |
| same | `runDist_eq_terminalWeight_of_boundedHorizon` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 1105 |
| same | `HasNormalizedTerminalLaw` | def | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1130 |
| same | `hasNormalizedTerminalLaw_of_exactHorizon` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 1140 |
| same | `hasNormalizedTerminalLaw_of_boundedHorizon` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 1159 |
| same | `terminalLawPMF` | def | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1182 |
| same | `terminalLawPMF_apply` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1192 |
| same | `terminalLawPMF_eq_runDist_of_boundedHorizon` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 1200 |
| same | `terminalLawPMF_eq_runDist_of_exactHorizon` | theorem | deferred | ordinary-continuation coefficient/terminal-support gate | EXP-059/D30 | No exact current terminal-support or coefficient theorem; reopen only with the ordinary continuation law. | public, pinned line 1210 |
| same | `toKernelGame` | def | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1222 |
| same | `toKernelGame_outcomeKernel` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1231 |
| same | `toKernelGame_eu_eq` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1240 |
| same | `toKernelGameAtHorizon` | def | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1257 |
| same | `toKernelGameAtHorizon_outcomeKernel` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1267 |
| same | `toKernelGameAtHorizon_eu_eq` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1274 |
| same | `toKernelGameOfBoundedHorizon` | abbrev | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1287 |
| same | `toKernelGameOfBoundedHorizon_outcomeKernel` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1294 |
| same | `toKernelGameOfBoundedHorizon_support_isTerminal` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1304 |
| same | `toKernelGameAtHorizon_eq_toKernelGameOfBoundedHorizon_outcomeKernel` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1319 |
| same | `toKernelGameOfBoundedHorizon_eu_eq` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1328 |
| same | `toKernelGameOfExactHorizon` | abbrev | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1344 |
| same | `toKernelGameOfExactHorizon_outcomeKernel` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1351 |
| same | `toKernelGameOfExactHorizon_support_isTerminal` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1361 |
| same | `toKernelGameOfExactHorizon_eu_eq` | theorem | retired | no successor; retired scalar/PMF compiler | EXP-059/D30 | The stable serializer does not revive this scalar/PMF or transport machinery. | public, pinned line 1376 |
| `GameTheory/Languages/FOSG/Examples.lean` | `historyFintypeOfLengthLeOne` | def | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `Solo` | inductive | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `soloIndex` | def | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `<anonymous@97>` | instance | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `SoloAct` | abbrev | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `SoloObs` | abbrev | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `SoloPub` | abbrev | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `SoloState` | inductive | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `binaryChoiceActive` | def | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `binaryChoiceAvailable` | def | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `binaryChoiceTerminal` | def | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `binaryChoicePick` | def | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `binaryChoiceTransition` | def | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `binaryChoice` | def | subsumed | `NFG.OneShotFOSG.game` | EXP-061/D30 | Generic one-shot compiler replaces the manual fixture. |
| same | `<anonymous@195>` | instance | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `startAction` | def | subsumed | canonical `policyProfile` | EXP-061/D30 | The canonical policy supplies its only use. |
| same | `startAction_legal` | theorem | subsumed | `ExecutionProtocol.Legal` | EXP-061/D30 | Joint legality is canonical. |
| same | `startLegalAction` | def | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `binaryChoice_step_from_start_isTerminal` | theorem | subsumed | canonical one-step runner law | EXP-061/D30 | The result follows from canonical execution. |
| same | `binaryChoiceBoundedHorizon` | theorem | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `<anonymous@262>` | instance | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `binaryChoiceKernel` | def | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `Player` | inductive | adapt | `Bool` in `GameTheory.Examples.FOSG` | EXP-061/D30 | The stable two-bit witness needs no bespoke player type. |
| same | `playerIndex` | def | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `<anonymous@281>` | instance | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `Act` | abbrev | adapt | `twoBitSource.Action` | EXP-061/D30 | The canonical one-shot action family is used directly. |
| same | `PrivObs` | abbrev | adapt | canonical one-shot signals | EXP-061/D30 | Signals are supplied by the NFG-to-FOSG compiler. |
| same | `PubObs` | abbrev | adapt | canonical one-shot signals | EXP-061/D30 | Signals are supplied by the NFG-to-FOSG compiler. |
| same | `State` | inductive | adapt | `NFG.OneShotFOSG.State` | EXP-061/D30 | The compiled state is canonical. |
| same | `active` | def | adapt | canonical one-shot execution | EXP-061/D30 | No handwritten execution field remains. |
| same | `availableActions` | def | adapt | canonical one-shot execution | EXP-061/D30 | No handwritten execution field remains. |
| same | `terminal` | def | adapt | canonical one-shot execution | EXP-061/D30 | No handwritten execution field remains. |
| same | `payoff` | def | adapt | `GameTheory.Examples.matchingPennies.payoff` | EXP-061/D30 | Payoff remains external, not FOSG syntax. |
| same | `leftMove` | def | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `rightMove` | def | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `transition` | def | adapt | `NFG.OneShotFOSG.execution` | EXP-061/D30 | The compiler owns the transition. |
| same | `game` | def | adapt | `GameTheory.Examples.FOSG.twoBit` | EXP-061/D30 | Stable utility-free FOSG witness and bridge regression. |
| same | `<anonymous@396>` | instance | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `step_from_start_isTerminal` | theorem | subsumed | canonical one-step runner law | EXP-061/D30 | The result follows from canonical execution. |
| same | `boundedHorizon` | theorem | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `<anonymous@454>` | instance | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| same | `kernel` | def | retired | no successor | EXP-061/D30 | Legacy fixture, enumeration, kernel, or manual extraction is intentionally absent. |
| `GameTheory/Languages/FOSG/Execution.lean` | `extendBySteps` | def | retired | `ExecutionProtocol.Trace`; `ExecutionProtocol.History.extend` | D6/D15; Protocol History API review (2026-08-02) | Indexed traces already carry chained realized transitions; a bare step-list extension would duplicate history semantics. |
| same | `extendBySteps_nil` | theorem | retired | `ExecutionProtocol.Trace.start` | D6/D15; API review | Base equation for the retired list extension. |
| same | `extendBySteps_cons` | theorem | retired | `ExecutionProtocol.Trace.extend` | D6/D15; API review | Step extension is the canonical trace constructor. |
| same | `steps_extendBySteps` | theorem | retired | indexed trace construction | D6/D15; API review | Canonical histories do not erase endpoint witnesses to a list. |
| same | `lastState_extendBySteps` | theorem | retired | indexed `Trace` endpoint | D6/D15; API review | The endpoint is carried by the trace index rather than recomputed. |
| same | `extendBySteps_eq` | theorem | retired | `ExecutionProtocol.History.trace` | D6/D15; API review | A canonical history already is its indexed realized trace. |
| same | `jointActionDist` | def | adapt | `InformationModel.behavioralJoint` | D6; Protocol Information API review (2026-08-02) | Independent local laws combine directly into a finite law over legal joint actions. |
| same | `jointActionDist_apply` | theorem | subsumed | `FinDist.prob_pi`; `FinDist.prob_map_of_injective` | D6; finite-law API review | The product point mass is `prob_pi`; the legal-subtype packaging is an injective map. |
| same | `jointActionDist_congr` | theorem | subsumed | `InformationModel.behavioralJoint_congr` | focused Protocol Information bridge review (2026-08-02) | The exact one-step joint-law congruence now exists independently of runner congruence. |
| same | `legalBehavioralProfile_jointActionDist_eq_zero_of_not_legal` | theorem | subsumed | `InformationModel.behavioralJoint` | D6; API review | Illegal joint actions cannot inhabit the law's dependent codomain. |
| same | `legalBehavioralProfile_legalJointMass_eq_one` | theorem | subsumed | `Probability.FinDist.tsum_prob` | D6; finite-law API review | Normalization is intrinsic to `FinDist`. |
| same | `legalActionLaw` | def | adapt | `InformationModel.behavioralJoint` | D6; Protocol Information API review (2026-08-02) | This is the canonical law over legal joint actions at a history. |
| same | `legalActionLaw_apply` | theorem | subsumed | `InformationModel.behavioralJoint`; `FinDist.prob_pi`; `FinDist.prob_map_of_injective` | D6; API review | Point probability is the independent product probability transported by the injective legal-action packaging. |
| same | `legalActionLaw_congr` | theorem | subsumed | `InformationModel.behavioralJoint_congr` | focused Protocol Information bridge review (2026-08-02) | Agreement at the realized information states gives exact equality of legal one-step action laws. |
| same | `legalActionLaw_bind_eq_jointActionDist_bind` | theorem | subsumed | `InformationModel.behavioralJoint` | D6; API review | No illegal ambient law is constructed, so no restriction bridge is needed. |
| same | `legalActionLaw_bind_coord` | theorem | subsumed | `FinDist.map_apply_pi`; `InformationModel.behavioralJoint` | D6; finite-law API review | `map_apply_pi` is the exact coordinate-marginal law; bind follows by monad congruence. |
| same | `legalActionLaw_bind_of_coord` | theorem | subsumed | `FinDist.map_apply_pi`; `InformationModel.behavioralJoint` | D6; finite-law API review | A continuation depending only on one coordinate factors through the exact coordinate marginal. |
| same | `legalActionLaw_eq_pure_noop_of_active_empty` | theorem | subsumed | `InformationModel.behavioral_eq_of_not_active`; `behavioralJoint` | D6; API review | Every inactive coordinate has one typed choice, so the joint law is a point mass. |
| same | `nextStateLaw` | def | subsumed | `ExecutionProtocol.runRandomizedFor_succ_of_not_terminal` | D6; Protocol Randomized API review (2026-08-02) | The canonical runner binds the legal joint law through the transition and retains history. |
| same | `nextStateLaw_apply` | theorem | subsumed | `ExecutionProtocol.runRandomizedFor_succ_of_not_terminal` | D6; API review | The bind equation is stated at the stronger history-law level. |
| same | `legalBehavioralProfile_jointStepMass_eq_one` | theorem | subsumed | `Probability.FinDist.tsum_prob` | D6; finite-law API review | The composed one-step result is normalized by construction. |
| same | `nextStateLaw_eq_bind_legalActionLaw` | theorem | subsumed | `ExecutionProtocol.runRandomizedFor_succ_of_not_terminal` | D6; API review | The canonical equation is draw, transition bind, and continuation. |
| same | `AgreeOff` | def | retired | `Profile.update`; `Profile.update_of_ne` | D4/D6; canonical profile API review | Unilateral changes use shared profile update rather than a second agreement predicate. |
| same | `stepActionProb` | def | subsumed | `InformationModel.behavioralJoint`; `FinDist.prob_pi` | D6; finite-law API review | Ordinary action probability is the point mass of the canonical independent joint draw. |
| same | `playerStepActionProb` | def | subsumed | `FinDist.prob` of the player's behavioral choice law | finite-law API review | One player's factor is already the point probability of its local law. |
| same | `othersStepActionProb` | def | adapt | `FinDist.pi` over `{j // j ≠ i}`; `FinDist.prob_pi` | finite-law API review | The player-excluded one-step product has an exact canonical dependent-product presentation. |
| same | `stepProb` | def | adapt | `InformationModel.behavioralJoint`; `ExecutionProtocol.step` | D6; Protocol Randomized API review | Ordinary one-step reach is the joint draw probability times the transition probability inside the canonical bind. |
| same | `stepActionProb_ne_top` | theorem | subsumed | `FinDist.prob_le_one` | finite-law API review | Canonical point probabilities are real and bounded. |
| same | `stepProb_ne_top` | theorem | subsumed | `FinDist.prob_le_one` | finite-law API review | The canonical real-valued one-step coefficient has no `⊤` case. |
| same | `stepProb_eq_stepActionProb_mul_transition` | theorem | subsumed | `ExecutionProtocol.runRandomizedFor_succ_of_not_terminal` | D6; Protocol Randomized API review | The runner's bind order is joint draw followed by transition. |
| same | `stepProb_eq_transition_mul_stepActionProb` | theorem | subsumed | preceding bind factorization plus commutativity | D6; API review | Commuted scalar wrapper adds no API. |
| same | `legalBehavioralProfile_stepActionProb_eq_one_of_active_empty` | theorem | subsumed | `InformationModel.behavioral_eq_of_not_active`; `FinDist.prob_pure_self` | D6; finite-law API review | Every inactive coordinate is the unique typed choice. |
| same | `legalBehavioralProfile_stepProb_eq_transition_of_active_empty` | theorem | subsumed | `behavioralJoint`; `FinDist.prob_pure_self` | D6; API review | The joint draw is a point mass, leaving only transition probability. |
| same | `stepActionProb_eq_player_mul_others` | theorem | subsumed | `FinDist.pi_eq_map_product`; `FinDist.prob_pi` | finite-law API review | The canonical product law factors exactly at one coordinate. |
| same | `stepActionProb_eq_others_mul_player` | theorem | subsumed | `FinDist.pi_eq_map_product`; `FinDist.prob_pi` | finite-law API review | Commuted wrapper of the exact product factorization. |
| same | `othersStepActionProb_eq_of_agreeOff` | theorem | subsumed | `FinDist.pi` congruence over `{j // j ≠ i}` | finite-law API review | Equality of all excluded coordinate laws gives equality of their canonical product law. |
| same | `counterfactualStepProb` | def | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Genuine counterfactual reach object; representation must derive from the accepted runner. |
| same | `stepProb_eq_player_mul_counterfactual` | theorem | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Flagship one-step counterfactual factorization. |
| same | `stepProb_eq_counterfactual_mul_player` | theorem | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Commuted wrapper follows the flagship factorization. |
| same | `counterfactualStepProb_eq_of_agreeOff` | theorem | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Counterfactual invariance should use shared unilateral update. |
| same | `probFrom` | def | adapt | `InformationModel.runBehavioralFrom`; `FinDist.prob` | D6; BehavioralAssessment API review | Ordinary continuation reach is the target-history point probability under the canonical history law at the suffix length. |
| same | `playerProbFrom` | def | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Player continuation factor remains part of the deferred spine. |
| same | `counterfactualProbFrom` | def | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Counterfactual continuation factor remains part of the deferred spine. |
| same | `probFrom_nil` | theorem | subsumed | `ExecutionProtocol.runRandomizedFor_zero`; `FinDist.prob_pure_self` | D6; finite-law API review | Zero-step continuation is the point mass at its starting history. |
| same | `probFrom_cons` | theorem | deferred | Protocol ordinary continuation/history-reach coefficient calculus slice | source comparison; D6 boundary | The runner successor equation and `FinDist.prob_bind` supply the ingredients, but the exact recursive point-coefficient bridge remains to be proved. |
| same | `playerProbFrom_nil` | theorem | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Base player-factor law. |
| same | `playerProbFrom_cons` | theorem | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Recursive player-factor law. |
| same | `counterfactualProbFrom_nil` | theorem | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Base counterfactual-factor law. |
| same | `counterfactualProbFrom_cons` | theorem | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Recursive counterfactual-factor law. |
| same | `counterfactualProbFrom_eq_of_agreeOff` | theorem | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Restate over canonical unilateral profile updates. |
| same | `prob` | def | adapt | `InformationModel.historyReachProbability` | Protocol BehavioralAssessment API review (2026-08-02) | This is exactly the probability of a complete history under behavioral play at its trace length, now real-valued. |
| same | `prob_nil` | theorem | subsumed | `InformationModel.historyReachProbability`; `FinDist.prob_pure_self` | D6; API review | The initial history has trace length zero and canonical probability one. |
| same | `probFrom_ne_top` | theorem | subsumed | `FinDist.prob_le_one` | finite-law API review | Canonical continuation reach is real-valued and at most one. |
| same | `prob_ne_top` | theorem | subsumed | `FinDist.prob_le_one` | finite-law API review | `historyReachProbability` is real-valued and has no `⊤` case. |
| same | `probFrom_eq_playerProbFrom_mul_counterfactualProbFrom` | theorem | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Main continuation-level player/counterfactual factorization. |
| same | `probFrom_append` | theorem | deferred | Protocol ordinary continuation/history-reach coefficient calculus slice | source comparison; D6 boundary | Runner composition and fuel transitivity exist, but their exact point-coefficient composition law still needs a canonical bridge. |
| same | `probFrom_append_singleton` | theorem | deferred | Protocol ordinary continuation/history-reach coefficient calculus slice | source comparison; D6 boundary | Specialization of the missing ordinary continuation coefficient-composition bridge. |
| same | `prob_snoc` | theorem | deferred | Protocol ordinary continuation/history-reach coefficient calculus slice | source comparison; D6 boundary | The canonical history law exists, but its exact one-history extension coefficient equation remains to be exposed. |
| same | `playerProb` | def | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Full-history player reach factor. |
| same | `counterfactualProb` | def | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Full-history counterfactual reach factor. |
| same | `counterfactualProb_eq_of_agreeOff` | theorem | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Full-history invariance under unilateral update. |
| same | `prob_eq_playerProb_mul_counterfactualProb` | theorem | deferred | Protocol counterfactual-reach/CFR slice | source comparison; D6 boundary | Main full-history reach factorization. |
| same | `prob_extendBySteps` | theorem | deferred | Protocol ordinary continuation/history-reach coefficient calculus slice | source comparison; D6 boundary | Recover the mathematical composition law over indexed histories without reviving the retired bare step-list wrapper. |
| same | `prob_appendStep` | theorem | deferred | Protocol ordinary continuation/history-reach coefficient calculus slice | source comparison; D6 boundary | The runner successor bind supplies the law-valued equation; its exact history point-coefficient bridge remains to be proved. |
| same | `terminalWeight` | def | adapt | terminal indicator of `InformationModel.historyReachProbability` | D6; BehavioralAssessment API review | Preserve the per-history terminal filter over canonical reach probability; it is not one unspecified-horizon `probOf`. |
| same | `terminalWeight_ne_top` | theorem | subsumed | `FinDist.prob_le_one` for `historyReachProbability` | finite-law API review | The adapted weight is real-valued and bounded. |
| same | `terminalWeight_of_terminal` | theorem | subsumed | terminal indicator of `historyReachProbability` | D6; API review | At a terminal history the indicator reduces to canonical reach probability. |
| same | `terminalWeight_of_not_terminal` | theorem | subsumed | terminal indicator of `historyReachProbability` | D6; API review | At a nonterminal history the indicator is zero. |
| same | `terminalMassOn` | def | adapt | finite sum of terminal-filtered `historyReachProbability` | D6; BehavioralAssessment API review | Histories in the finite event may have different trace lengths, so no single-horizon `FinDist.probOf` is claimed. |
| same | `terminalLaw` | def | retired | `terminalMassOn` adaptation directly | D6/D15; API review | This was only a second name for the finite-event terminal mass functional. |
| same | `terminalMassOn_empty` | theorem | subsumed | `Finset.sum_empty` for the adapted terminal mass | finite-sum API review | Empty finite event has zero terminal-filtered reach sum. |
| same | `terminalMassOn_singleton` | theorem | subsumed | `Finset.sum_singleton` for the adapted terminal mass | finite-sum API review | Singleton finite event reduces to its terminal-filtered history reach. |
| same | `terminalLaw_apply` | theorem | retired | no alias to unfold | D6/D15; API review | Reflexive theorem for the retired `terminalLaw` alias. |
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
| `GameTheory/Languages/FOSG/Native/History.lean` | `ExecutionState` | abbrev | adapt | `GameTheory.Protocol.ExecutionProtocol.State` and `History` | EXP-042/D15; `Languages/FOSG/Kuhn.lean` focused build | Native execution state is the canonical Protocol execution history/state pair, not a second FOSG machine. |
| same | `KuhnLocalStrategy` | abbrev | adapt | `InformationModel.Policy` | EXP-042/D15; `Languages/FOSG/Kuhn.lean` | Information-local deterministic policy is owned by Protocol. |
| same | `KuhnPureProfile` | abbrev | adapt | `Profile G.information.strategicSignature.pure` | `Languages/FOSG/Kuhn.lean` | Canonical pure-policy profile. |
| same | `KuhnBehavioralProfile` | abbrev | adapt | `Profile G.behavioralSignature` | `Game.BehavioralPlan`; `Languages/FOSG/Kuhn.lean` | FOSG wrapper exposes the Protocol behavioral policy family. |
| same | `runDist` | abbrev | adapt | `InformationModel.runBehavioral` | `Game.toBehavioralGameForm_play`; `Languages/FOSG/Kuhn.lean` | Complete-history law, not a native scalar run distribution. |
| same | `runDistPure` | abbrev | adapt | `InformationModel.run` | `Protocol/Information.lean` | Initial deterministic-policy law is canonical Protocol execution. |
| same | `executionBehavioralToMixedJoint` | abbrev | subsumed | `FinDist.pi` over `InformationModel.MixedPolicy` | `InformationModel.runMixed` | Product of local mixed policies is internal to the canonical mixed runner. |
| same | `NoNontrivialInfoStateRepeat` | abbrev | adapt | `InformationModel.ActsOnceWhereItMatters` | `Game.kuhn_behavioral_to_mixed` | The sharp no-repeat premise has a semantic Protocol name. |
| same | `StepMassInvariant` | abbrev | retired | no successor; obsolete native scalar factorization | EXP-042/D15 | Law equality replaces a separate step-mass invariant. |
| same | `StepSupportFactorization` | abbrev | retired | no successor; obsolete native scalar factorization | EXP-042/D15 | Native support-factorization bookkeeping is not a stable API. |
| same | `ActionPosteriorLocal` | abbrev | retired | no successor; obsolete native posterior predicate | EXP-042/D15 | The recovered theorem uses `PerfectRecall`, not a duplicate posterior formulation. |
| same | `ObsLocalFeasibilityFull` | abbrev | retired | no successor; obsolete native observation predicate | EXP-042/D15 | The recovered theorem uses `ActsOnceWhereItMatters`, not this wrapper. |
| same | `behavioral_to_mixed_runDist` | theorem | adapt | `Game.kuhn_behavioral_to_mixed` | `Languages/FOSG/Kuhn.lean`; pinned line 116 | Named FOSG history-law correspondence under the sharp acts-once premise. |
| same | `mixed_to_behavioral_semantic` | theorem | adapt | `Game.kuhn_mixed_to_behavioral` | `Languages/FOSG/Kuhn.lean`; pinned line 138 | Named FOSG history-law correspondence under `PerfectRecall`. |
| same | `mixed_to_behavioral_of_obsLocal` | theorem | retired | replaced by `Game.kuhn_mixed_to_behavioral` with `PerfectRecall` | `Languages/FOSG/Kuhn.lean`; pinned line 165 | Old observation-local sufficient condition is not retained beside the semantic premise. |
| same | `PureStrategy` | abbrev | adapt | `InformationModel.Policy` | `Protocol/Information.lean` | Canonical deterministic information policy. |
| same | `MixedProfile` | abbrev | adapt | `Profile G.information.strategicSignature.mixed` | `Game.MixedPlan`; `Languages/FOSG/Kuhn.lean` | Canonical once-drawn policy profile. |
| same | `mixedProfilePureStrategyFintype` | instance | subsumed | inherited finite-policy instances | `InformationModel.BehavioralPolicy.toMixed` | No language-local instance surface is needed. |
| same | `BehavioralProfile` | abbrev | adapt | `Profile G.behavioralSignature` | `Game.BehavioralPlan`; `Languages/FOSG/Kuhn.lean` | Canonical independently randomized local policies. |
| same | `mixedProfileJoint` | abbrev | subsumed | `FinDist.pi` in `InformationModel.runMixed` | `Protocol/Information.lean` | Internal product law, not a public FOSG alias. |
| same | `liftPureStrategy` | def | retired | `InformationModel.Policy.toBehavioral` where needed | `Protocol/Information.lean` | Language-local lifting wrapper adds no recovered theorem surface. |
| same | `liftPureProfile` | def | retired | pointwise `Policy.toBehavioral` | `Protocol/Information.lean` | A profile-wide wrapper is intentionally not duplicated. |
| same | `liftMixedProfile` | def | retired | `MixedPolicy.toBehavioral` under `PerfectRecall` | `Game.kuhn_mixed_to_behavioral` | The semantic conversion is exposed by the named correspondence theorem. |
| same | `liftMixedProfile_joint` | theorem | retired | `Game.kuhn_mixed_to_behavioral` | `Languages/FOSG/Kuhn.lean` | Joint-law wrapper is subsumed by complete-history law equality, without preserving the old construction. |
| same | `behavioralToMixed` | def | subsumed | `BehavioralPolicy.toMixed` | `InformationModel.runMixed_toMixed` | Canonical policy conversion is already the Protocol definition. |
| same | `behavioralToMixedJoint` | def | subsumed | pointwise `BehavioralPolicy.toMixed`; `FinDist.pi` | `InformationModel.runMixed_toMixed` | Joint conversion is internal to the canonical runner. |
| same | `mixed_to_behavioral_runDist` | theorem | adapt | `Game.kuhn_mixed_to_behavioral` | `Languages/FOSG/Kuhn.lean`; pinned line 267 | Named complete-history law theorem replaces the native runner equality. |
| same | `mixed_to_behavioral_runDist_of_obsLocal` | theorem | retired | replaced by `Game.kuhn_mixed_to_behavioral` with `PerfectRecall` | `Languages/FOSG/Kuhn.lean`; pinned line 293 | Do not retain the old observation-local alternative premise. |
| same | `toHistoryObsModelCore` | def | retired | no successor; native observation-model encoding | EXP-042/D15 | Canonical `InformationModel` is primary, without a history-specific adapter. |
| same | `historyInfoStateFintype` | instance | subsumed | ambient `Fintype (InformationModel.InfoState who)` assumption | `Game.kuhn_behavioral_to_mixed` | The theorem asks only for the needed finite information-state instance. |
| `GameTheory/Languages/FOSG/Native/HistoryMarginal.lean` | `SeenBefore` | def | retired | no successor; native history-prefix predicate | EXP-042/D15 | `ownPlay`/recall are canonical, but this scalar marginal helper is not recovered. |
| same | `stepChainFrom_prefix` | theorem | retired | no successor; native chain helper | EXP-042/D15 | Internal history-chain bookkeeping has no stable consumer. |
| same | `stepChainFrom_last_src` | theorem | retired | no successor; native chain helper | EXP-042/D15 | Internal history-chain bookkeeping has no stable consumer. |
| same | `seenBefore_mono_appendStep` | theorem | retired | no successor; native marginal helper | EXP-042/D15 | No parallel `SeenBefore` calculus is retained. |
| same | `seenBefore_current_appendStep` | theorem | retired | no successor; native marginal helper | EXP-042/D15 | No parallel `SeenBefore` calculus is retained. |
| same | `not_seenBefore_current` | theorem | retired | no successor; native marginal helper | EXP-042/D15 | No parallel `SeenBefore` calculus is retained. |
| same | `stepProb_pure_congr_at_history` | theorem | retired | `InformationModel.behavioralJoint_congr` only for canonical law steps | EXP-042/D15 | The old scalar pure-step probability API is intentionally not reconstructed. |
| same | `prob_pure_congr_of_agreeOnSeenBefore` | theorem | retired | `InformationModel.runBehavioralFrom_congr` where a canonical law congruence is needed | `Protocol/Information.lean` | Recovered congruence is law-valued and premise-specific, not `SeenBefore`-based. |
| same | `marginal_prob` | theorem | subsumed | `InformationModel.runMixed_toMixed` | `Game.kuhn_behavioral_to_mixed`; pinned line 180 | Behavioral-to-predrawn-mixed complete-history equality subsumes each scalar marginal consequence. |
| `GameTheory/Languages/FOSG/Native/Reachable.lean` | `ReachablePureStrategy` | abbrev | retired | no successor; retired reachable scalar profile API | EXP-057/D28 | The reachable specialization duplicates the retired native scalar profile surface. |
| same | `ReachableBehavioralProfile` | abbrev | retired | no successor; retired reachable scalar profile API | EXP-057/D28 | The reachable specialization duplicates the retired native scalar profile surface. |
| same | `reachableBehavioralToMixed` | def | retired | no successor; retired reachable scalar profile API | EXP-057/D28 | Canonical mixed conversion is law-valued and does not retain the reachable wrapper. |
| same | `reachableBehavioralToMixedJoint` | def | retired | no successor; retired reachable scalar profile API | EXP-057/D28 | Canonical mixed conversion is law-valued and does not retain the reachable wrapper. |
| same | `reachable_stepActionProb_pureToBehavioral` | theorem | retired | no successor; retired reachable scalar probability API | EXP-057/D28 | The scalar pure-to-behavioral step equation is not reconstructed. |
| same | `reachable_marginal_stepActionProb` | theorem | deferred | canonical behavioral-mixture marginal gate | D28/D29 | `behavioralJoint` is a definition, not yet a checked mixture-over-pure-policy marginal theorem. |
| same | `reachable_marginal_stepProb` | theorem | deferred | canonical behavioral-mixture marginal gate | D28/D29 | `runBehavioralFrom` is a runner, not yet a checked mixture-over-pure-policy marginal theorem. |
| same | `swapReachableProfileBy` | def | retired | no successor; retired profile-swapping API | EXP-057/D28 | No parallel profile-swapping calculus is retained. |
| same | `swapReachableProfileBy_involutive` | theorem | retired | no successor; retired profile-swapping API | EXP-057/D28 | No parallel profile-swapping calculus is retained. |
| same | `swapReachableBy_weight_eq` | theorem | retired | no successor; retired profile-swapping API | EXP-057/D28 | No scalar weight transport is retained. |
| same | `reachable_scalar_indep` | theorem | retired | no successor; retired scalar independence API | EXP-057/D28 | Canonical execution is law-valued rather than a scalar calculus. |
| same | `ReachableSeenBefore` | def | retired | no successor; retired seen-before API | EXP-057/D28 | No reachable seen-before predicate is retained. |
| same | `reachable_seenBefore_mono_appendStep` | theorem | retired | no successor; retired seen-before API | EXP-057/D28 | No reachable seen-before calculus is retained. |
| same | `reachable_seenBefore_current_appendStep` | theorem | retired | no successor; retired seen-before API | EXP-057/D28 | No reachable seen-before calculus is retained. |
| same | `reachable_not_seenBefore_current` | theorem | retired | no successor; retired seen-before API | EXP-057/D28 | No reachable seen-before calculus is retained. |
| same | `reachable_stepProb_pure_congr_at_history` | theorem | retired | no successor; retired scalar congruence API | EXP-057/D28 | Canonical congruence is law-valued and premise-specific. |
| same | `reachable_prob_pure_congr_of_agreeOnSeenBefore` | theorem | retired | no successor; retired scalar congruence API | EXP-057/D28 | Canonical congruence is law-valued and premise-specific. |
| same | `reachable_scalar_indep_stepProb` | theorem | retired | no successor; retired scalar independence API | EXP-057/D28 | No scalar step-probability calculus is retained. |
| same | `reachable_marginal_prob` | theorem | adapt | `InformationModel.runMixed_toMixed` under `ActsOnceWhereItMatters` | audited `Protocol.Information` theorem | The canonical complete-history equality retains the operational no-revisit premise instead of claiming an unconditional scalar identity. |
| same | `reachable_marginal_terminalWeight` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `reachable_marginal_terminalMassOn` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `reachable_marginal_terminalLaw` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `reachable_marginal_terminalWeight_toReal` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `reachable_marginal_terminalUtilitySum` | theorem | deferred | external-evaluation/strategic gate | EXP-057/D28 | Utility transfer requires the external evaluation surface. |
| same | `reachable_marginal_terminalExpectation` | theorem | deferred | external-evaluation/strategic gate | EXP-057/D28 | Expectation transfer requires the external evaluation surface. |
| same | `behavioral_to_mixed_prob_reachable` | theorem | adapt | `InformationModel.runMixed_toMixed` under `ActsOnceWhereItMatters` | audited `Protocol.Information` theorem | The canonical law equality is retained with its explicit operational premise. |
| same | `behavioral_to_mixed_terminalWeight_reachable` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `behavioral_to_mixed_terminalMassOn_reachable` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `behavioral_to_mixed_terminalLaw_reachable` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `behavioral_to_mixed_eu_reachable` | theorem | deferred | external-evaluation/strategic gate | EXP-057/D28 | Expected-utility transfer requires the external evaluation surface. |
| `GameTheory/Languages/FOSG/Native/StepIndependence.lean` | `stepActionProb_pureToBehavioral` | theorem | retired | no successor; retired scalar probability API | EXP-057/D28 | The scalar pure-to-behavioral step equation is not reconstructed. |
| same | `marginal_stepActionProb_raw` | theorem | retired | no successor; retired raw scalar marginal API | EXP-057/D28 | The raw scalar marginal is not a canonical execution surface. |
| same | `marginal_stepActionProb` | theorem | deferred | canonical behavioral-mixture marginal gate | D28/D29 | `behavioralJoint` does not by itself prove the mixture-over-pure-policy marginal identity. |
| same | `marginal_stepProb` | theorem | deferred | canonical behavioral-mixture marginal gate | D28/D29 | `runBehavioralFrom` does not by itself prove the mixture-over-pure-policy marginal identity. |
| same | `swapProfileBy` | def | retired | no successor; retired profile-swapping API | EXP-057/D28 | No parallel profile-swapping calculus is retained. |
| same | `swapProfileBy_involutive` | theorem | retired | no successor; retired profile-swapping API | EXP-057/D28 | No parallel profile-swapping calculus is retained. |
| same | `swapBy_weight_eq` | theorem | retired | no successor; retired profile-swapping API | EXP-057/D28 | No scalar weight transport is retained. |
| same | `scalar_indep` | theorem | retired | no successor; retired scalar independence API | EXP-057/D28 | Canonical execution is law-valued rather than a scalar calculus. |
| same | `scalar_indep_stepProb` | theorem | retired | no successor; retired scalar independence API | EXP-057/D28 | No scalar step-probability calculus is retained. |
| `GameTheory/Languages/FOSG/Native/TerminalLaw.lean` | `marginal_terminalWeight` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `marginal_terminalMassOn` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `marginal_terminalLaw` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `marginal_terminalWeight_toReal` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `terminalWeightClassical` | def | retired | no successor; retired scalar terminal-weight API | EXP-057/D28 | Classical scalar terminal weights are not a canonical surface. |
| same | `marginal_terminalUtilitySum` | theorem | deferred | external-evaluation/strategic gate | EXP-057/D28 | Utility transfer requires the external evaluation surface. |
| same | `behavioral_to_mixed_prob` | theorem | adapt | `InformationModel.runMixed_toMixed` under `ActsOnceWhereItMatters` | audited `Protocol.Information` theorem | The canonical equality states the no-revisit premise needed by predrawn mixed play. |
| same | `behavioral_to_mixed_terminalWeight` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `behavioral_to_mixed_terminalMassOn` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `behavioral_to_mixed_terminalLaw` | theorem | deferred | ordinary-continuation/terminal-support gate | EXP-057/D28 | Reopen with canonical terminal-support coefficients. |
| same | `behavioral_to_mixed_eu` | theorem | deferred | external-evaluation/strategic gate | EXP-057/D28 | Expected-utility transfer requires the external evaluation surface. |
| `GameTheory/Languages/FOSG/OutcomeClosure.lean` | `valueStep` | def | deferred | ordinary-continuation/outcome-value-process gate | EXP-057/D28 | A language-local stopped process awaits the ordinary continuation outcome-value surface. |
| same | `valueStep_terminal` | theorem | subsumed | `InformationModel.runBehavioralFrom_of_terminal` | audited `Protocol.Information` theorem | The canonical behavioral runner self-loops from a terminal history. |
| same | `valueStep_nonterminal` | theorem | subsumed | `ExecutionProtocol.runRandomizedFor_succ_of_not_terminal` | audited `Protocol.Execution` theorem | The canonical runner supplies the nonterminal one-step bind equation. |
| same | `OutcomeValue` | structure | deferred | ordinary-continuation/outcome-value-process gate | EXP-057/D28 | No language-local outcome-value certificate is retained before that gate. |
| same | `ofProjectedStep` | def | deferred | ordinary-continuation/outcome-value-process gate | EXP-057/D28 | Projection construction awaits the canonical outcome-value process. |
| same | `ofLastStateValue` | def | deferred | ordinary-continuation/outcome-value-process gate | EXP-057/D28 | State-value construction awaits the canonical outcome-value process. |
| same | `stateStepValue_of_projectedStep` | theorem | deferred | ordinary-continuation/outcome-value-process gate | EXP-057/D28 | Projected step preservation awaits the canonical outcome-value process. |
| same | `ofProjectedLastStateStep` | def | deferred | ordinary-continuation/outcome-value-process gate | EXP-057/D28 | Projection construction awaits the canonical outcome-value process. |
| same | `toValueProcess` | def | deferred | ordinary-continuation/outcome-value-process gate | EXP-057/D28 | Generic process conversion awaits the canonical outcome-value process. |
| same | `runDistFrom_eq_run` | theorem | deferred | ordinary-continuation/outcome-value-process gate | EXP-057/D28 | Runner/process comparison awaits the canonical outcome-value process. |
| same | `map_observe_runDistFrom_eq_value` | theorem | deferred | ordinary-continuation/outcome-value-process gate | EXP-057/D28 | Prefix outcome closure awaits the canonical outcome-value process. |
| same | `map_observe_runDist_eq_value` | theorem | deferred | ordinary-continuation/outcome-value-process gate | EXP-057/D28 | Initial outcome closure awaits the canonical outcome-value process. |
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
| `GameTheory/Languages/FOSG/ReachableHistory/ObsModelFacts.lean` | `reachableHistoryOutcomeDist` | def | adapt | `InformationModel.runBehavioral` | EXP-058/D29 hostile witness | Canonical behavioral history law replaces the native reachable-history outcome PMF. |
| same | `reachableHistoryOutcomeDistPure` | def | adapt | `InformationModel.run` | EXP-058/D29 hostile witness | Canonical initial deterministic-policy history law replaces the native outcome PMF. |
| same | `ReachableHistoryStepMassInvariant` | abbrev | retired | no successor; removed scalar invariant | EXP-058/D29 | Native step-mass factorization is not a stable law interface. |
| same | `ReachableHistoryStepSupportFactorization` | abbrev | retired | no successor; removed scalar invariant | EXP-058/D29 | Native support factorization is not retained. |
| same | `ReachableHistoryActionPosteriorLocal` | abbrev | retired | no successor; removed posterior interface | EXP-058/D29 | D28 proves the canonical law directly and exposes no posterior certificate. |
| same | `reachableInfoLegalMove_eq_none_of_terminal` | theorem | retired | no successor; removed legal-move carrier | EXP-058/D29 hostile witness | Machine-refuted as a general Protocol claim because terminal activity is deliberately unconstrained. |
| same | `reachableHistory_stepActionDeterminism` | theorem | retired | no successor; removed native execution model | EXP-058/D29 | Determinism served only the old scalar proof machine. |
| same | `reachableHistory_stepMassInvariant` | theorem | retired | no successor; removed scalar invariant | EXP-058/D29 | Consequence of retired native determinism. |
| same | `reachableHistory_stepSupportFactorization` | theorem | retired | no successor; removed scalar invariant | EXP-058/D29 | Consequence of retired native determinism. |
| same | `playerViewFrom_cons_eq_cons_view` | theorem | retired | no successor; removed compressed view encoding | EXP-058/D29 | Native list decomposition has no canonical consumer. |
| same | `playerViewFrom_cons_eq_cons_action` | theorem | retired | no successor; removed compressed view encoding | EXP-058/D29 | Native list decomposition has no canonical consumer. |
| same | `playerViewFrom_cons_ne_nil` | theorem | retired | no successor; removed compressed view encoding | EXP-058/D29 | Native event-list nonemptiness has no canonical consumer. |
| same | `playerViewFrom_append_singleton_ne_nil` | theorem | retired | no successor; removed compressed view encoding | EXP-058/D29 | Native event-list nonemptiness has no canonical consumer. |
| same | `playerViewFrom_append_singleton_eq` | theorem | retired | no successor; removed compressed view encoding | EXP-058/D29 | Native event-list cancellation has no canonical consumer. |
| same | `publicViewFrom_length` | theorem | retired | no successor; removed compressed public view | EXP-058/D29 | The Protocol information recursion has no duplicate list encoding. |
| same | `publicView_length` | theorem | retired | no successor; removed compressed public view | EXP-058/D29 | The Protocol information recursion has no duplicate list encoding. |
| same | `reachableInfoLegalMove_eq_none_of_terminal_view_eq` | theorem | retired | no successor; old reachable view bridge | EXP-058/D29 | Requires the removed reachable observation carrier. |
| same | `reachableInfoLegalMove_subsingleton_of_terminal` | theorem | retired | no successor; removed legal-move carrier | EXP-058/D29 hostile witness | A terminal state may retain two local choices; inactivity has the canonical subsingleton theorem. |
| same | `reachableHistory_projectStates_eq_last` | theorem | retired | no successor; removed projected-state encoding | EXP-058/D29 | Projection equality is transport machinery for the retired model. |
| same | `reachableInfoLegalMove_cast_val` | theorem | retired | no successor; forbidden transport helper | EXP-058/D29 | User-visible cast plumbing is deliberately absent. |
| same | `reachableInfoLegalMove_cast_currentObs_val` | theorem | retired | no successor; forbidden transport helper | EXP-058/D29 | User-visible cast plumbing is deliberately absent. |
| same | `subst_heq_fosg` | theorem | retired | no successor; forbidden transport helper | EXP-058/D29 | `HEq` transport is outside the public surface. |
| same | `reachableHistory_castJointAction_val` | theorem | retired | no successor; forbidden transport helper | EXP-058/D29 | Casted joint actions belong only to the removed model. |
| same | `projectActions_snoc_eq` | theorem | subsumed | `InfoSignals.ownPlay_extend` | EXP-058/D29; `Protocol/Information.lean` | Canonical own-play recursion records the action component and is richer than the old append formula. |
| same | `sourceView_and_ownAction_eq_of_target_view_eq` | theorem | retired | no successor; old view-equality bridge | EXP-058/D29 hostile witness | Compressed information does not decode prior own actions without an explicit recall hypothesis. |
| same | `reachableHistory_pureStep_snoc` | theorem | retired | no successor; removed native pure runner | EXP-058/D29 | Native pure-step representation is not retained. |
| same | `reachableHistory_source_nonterminal_of_target_nonterminal` | theorem | retired | no successor; old source/target proof | EXP-058/D29 | `History.not_isTerminal_of_legal` is not a native-run bridge. |
| same | `reachableHistory_pureRun_last_steps_length_le` | theorem | retired | no successor; native run-list arithmetic | EXP-058/D29 | Protocol histories use indexed traces rather than this list machine. |
| same | `reachableHistory_pureStep_component_eq` | theorem | retired | no successor; native pure runner | EXP-058/D29 | Component equality is internal native-run bookkeeping. |
| same | `reachableHistory_pureRun_update_obs_local_nonterminal` | theorem | retired | no successor; retired observation-locality proof | EXP-058/D29 | Raw updates proved an internal property of the removed pure runner. |
| same | `reachableHistory_pureRun_nonterminal_last_steps_length` | theorem | retired | no successor; native run-list arithmetic | EXP-058/D29 | Protocol histories use indexed traces rather than this list machine. |
| same | `reachableHistory_repeated_projectStates_subsingleton` | theorem | retired | no successor; projected-state transport | EXP-058/D29 | Repetition/subsingleton fact serves the removed model. |
| same | `reachableHistory_current_coord_ignores_of_reachable` | theorem | retired | no successor; native coordinate projection | EXP-058/D29 | No canonical counterpart without rebuilding the carrier. |
| same | `reachableHistory_obsLocalFeasibility` | theorem | retired | no successor; retired observation-locality proof | EXP-058/D29 | This proof-machine premise is not the `PerfectRecall` theorem used by D28. |
| same | `reachableHistory_actionPosteriorLocal` | theorem | retired | no successor; removed posterior interface | EXP-058/D29 | D28 replaces its only Kuhn-law consumer; future CFR is a distinct theorem family. |
| same | `ownAction_eq_of_source_target_view_eq` | theorem | retired | no successor; old view-equality bridge | EXP-058/D29 hostile witness | Compressed information does not decode prior own actions without an explicit recall hypothesis. |
| same | `liftReachableHistoryPureStrategy` | def | retired | `InformationModel.Policy` without a reachable-history lift | EXP-058/D29 | Do not reproduce the auxiliary strategy carrier. |
| same | `reachableInfoLegalMoveOfBehavioralSupport` | def | retired | no successor; removed legal-move carrier | EXP-058/D29 | Support witnesses are internal to canonical law semantics. |
| same | `liftReachableHistoryBehavioralStrategy` | def | retired | `InformationModel.BehavioralPolicy` without a lift | EXP-058/D29 | Do not reproduce the auxiliary strategy carrier. |
| same | `erase_liftReachableHistoryBehavioralStrategy` | theorem | retired | no successor; removed lift/erase pair | EXP-058/D29 | Inverse proof has no stable surface absent the carrier. |
| same | `eraseReachableHistoryPureStrategy` | def | retired | no successor; removed lift/erase pair | EXP-058/D29 | Do not reproduce the auxiliary strategy carrier. |
| same | `liftReachableHistoryPureStrategy_erase` | theorem | retired | no successor; removed lift/erase pair | EXP-058/D29 | Inverse proof has no stable surface absent the carrier. |
| same | `reachableHistoryBehavioralToMixedStrategy` | def | retired | `BehavioralPolicy.toMixed` without reachable-history conversion | EXP-058/D29 | Old conversion was tied to the removed carrier. |
| same | `reachableLegalBehavioralToMixed` | def | retired | no successor; removed legal-move carrier | EXP-058/D29 | Canonical `toMixed` operates on `InformationModel` policies. |
| same | `reachableLegalBehavioralToMixed_lift` | theorem | retired | no successor; removed lift proof | EXP-058/D29 | Compatibility theorem has no independent result. |
| same | `liftReachableHistoryBehavioralProfile` | def | retired | `Profile G.behavioralSignature` without a lift | EXP-058/D29 | Do not reproduce the auxiliary profile carrier. |
| `GameTheory/Languages/FOSG/Serial.lean` | `singleMove` | def | subsumed | `FOSGToEFG.ChoiceAt`; `selectedJoint` | EXP-061/D30 | Single-owner selection is canonical without fabricated dependent joint moves. |
| same | `singleMove_self` | theorem | subsumed | `FOSGToEFG.ChoiceAt`; `selectedJoint` | EXP-061/D30 | Single-owner selection is canonical without fabricated dependent joint moves. |
| same | `singleMove_other` | theorem | subsumed | `FOSGToEFG.ChoiceAt`; `selectedJoint` | EXP-061/D30 | Single-owner selection is canonical without fabricated dependent joint moves. |
| same | `ExtendsPartial` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `recordChoice` | def | subsumed | `FOSGToEFG.Prefix.advance` | EXP-061/D30 | Certified prefix extension replaces equality-update plumbing. |
| same | `recordChoice_self` | theorem | subsumed | `FOSGToEFG.Prefix.advance` | EXP-061/D30 | Certified prefix extension replaces equality-update plumbing. |
| same | `recordChoice_other` | theorem | subsumed | `FOSGToEFG.Prefix.advance` | EXP-061/D30 | Certified prefix extension replaces equality-update plumbing. |
| same | `extendsPartial_noop` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `extendsPartial_recordChoice` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `MatchesActedPrefix` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `prefixChoice` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `playerLegal` | def | subsumed | `FOSGToEFG.menu`; `legalOption_scheduled` | EXP-061/D30 | Canonical local choices replace the joint-action wrapper. |
| same | `eq_singleMove_of_current_some_other_none` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `playerLegal_iff_exists_singleMove` | theorem | subsumed | `FOSGToEFG.menu`; `legalOption_scheduled` | EXP-061/D30 | Canonical local choices replace the joint-action wrapper. |
| same | `playerLegal_current_some` | theorem | subsumed | `FOSGToEFG.menu`; `legalOption_scheduled` | EXP-061/D30 | Canonical local choices replace the joint-action wrapper. |
| same | `playerLegal_other_none` | theorem | subsumed | `FOSGToEFG.menu`; `legalOption_scheduled` | EXP-061/D30 | Canonical local choices replace the joint-action wrapper. |
| same | `baseChanceLegalAction` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `baseChanceLegalAction_val` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `actionAtActive` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `actionAtActive_spec` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `moveOfLegalAction` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `moveOfLegalAction_current` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `moveOfLegalAction_other` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `matchesActedPrefix_noop` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `matchesActedPrefix_prefixChoice` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `prefixChoice_nil` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `prefixChoice_apply_of_mem` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `prefixChoice_apply_of_not_mem` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `matchesActedPrefix_recordChoice_move` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `prefixChoice_recordChoice_move` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `orderedActive` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `mem_orderedActive_iff` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `orderedActive_eq_nil_of_active_eq_empty` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `active_eq_empty_of_orderedActive_eq_nil` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `current_mem_active_of_split` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `current_not_mem_rest_of_split` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `ValidDecision` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `SerialState` | inductive | subsumed | `FOSGToEFG.State`; `execution`; `singleMover` | EXP-061/D30 | The generic EFG state carries canonical source history and a certified prefix. |
| same | `active` | def | subsumed | `FOSGToEFG.State`; `execution`; `singleMover` | EXP-061/D30 | The generic EFG state carries canonical source history and a certified prefix. |
| same | `terminal` | def | subsumed | `FOSGToEFG.State`; `execution`; `singleMover` | EXP-061/D30 | The generic EFG state carries canonical source history and a certified prefix. |
| same | `instDecidablePredTerminal` | instance | subsumed | `FOSGToEFG.State`; `execution`; `singleMover` | EXP-061/D30 | The generic EFG state carries canonical source history and a certified prefix. |
| same | `world` | def | subsumed | `FOSGToEFG.State`; `execution`; `singleMover` | EXP-061/D30 | The generic EFG state carries canonical source history and a certified prefix. |
| same | `world_base` | theorem | subsumed | `FOSGToEFG.State`; `execution`; `singleMover` | EXP-061/D30 | The generic EFG state carries canonical source history and a certified prefix. |
| same | `world_decide` | theorem | subsumed | `FOSGToEFG.State`; `execution`; `singleMover` | EXP-061/D30 | The generic EFG state carries canonical source history and a certified prefix. |
| same | `world_chance` | theorem | subsumed | `FOSGToEFG.State`; `execution`; `singleMover` | EXP-061/D30 | The generic EFG state carries canonical source history and a certified prefix. |
| same | `legal` | def | subsumed | `FOSGToEFG.State`; `execution`; `singleMover` | EXP-061/D30 | The generic EFG state carries canonical source history and a certified prefix. |
| same | `availableActions` | def | subsumed | `FOSGToEFG.State`; `execution`; `singleMover` | EXP-061/D30 | The generic EFG state carries canonical source history and a certified prefix. |
| same | `legal_iff_jointActionLegal` | theorem | subsumed | `FOSGToEFG.State`; `execution`; `singleMover` | EXP-061/D30 | The generic EFG state carries canonical source history and a certified prefix. |
| same | `LegalAction` | abbrev | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `FOSGLegalAction` | abbrev | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `toFOSGLegalAction` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `ofFOSGLegalAction` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `toFOSGLegalAction_val` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `ofFOSGLegalAction_val` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `active_eq_empty_of_base_terminal` | theorem | subsumed | `FOSGToEFG.execution` terminal invariant | EXP-061/D30 | Terminal activity is owned by canonical execution. |
| same | `legalAction_eq_of_extends_matchesOrderedActive` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `not_mem_acted_of_mem_remaining` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `validDecision_of_prefix` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `base_playerLegal_of_legalAction` | theorem | subsumed | `legalOption_scheduled` | EXP-061/D30 | Scheduled owner menus are exactly the source legal options. |
| same | `decide_playerLegal_of_legalAction` | theorem | subsumed | `legalOption_scheduled` | EXP-061/D30 | Scheduled owner menus are exactly the source legal options. |
| same | `validDecision_from_base` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `validDecision_step` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `basePlayerSuccessorWithOrder` | def | subsumed | `FOSGToEFG.execution`; `step_select`; `State.history` | EXP-061/D30 | Fixed explicit order and target steps replace active-set sorting and replay. |
| same | `basePlayerSuccessor` | def | subsumed | `FOSGToEFG.execution`; `step_select`; `State.history` | EXP-061/D30 | Fixed explicit order and target steps replace active-set sorting and replay. |
| same | `world_basePlayerSuccessorWithOrder` | theorem | subsumed | `FOSGToEFG.execution`; `step_select`; `State.history` | EXP-061/D30 | Fixed explicit order and target steps replace active-set sorting and replay. |
| same | `world_basePlayerSuccessor` | theorem | subsumed | `FOSGToEFG.execution`; `step_select`; `State.history` | EXP-061/D30 | Fixed explicit order and target steps replace active-set sorting and replay. |
| same | `decidePlayerSuccessor` | def | subsumed | `FOSGToEFG.execution`; `step_select`; `State.history` | EXP-061/D30 | Fixed explicit order and target steps replace active-set sorting and replay. |
| same | `world_decidePlayerSuccessor` | theorem | subsumed | `FOSGToEFG.execution`; `step_select`; `State.history` | EXP-061/D30 | Fixed explicit order and target steps replace active-set sorting and replay. |
| same | `baseReplayAction` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `basePlayerSuccessorWithOrder_replay_cons` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `basePlayerSuccessorWithOrder_replay_last` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `basePlayerSuccessor_replay_cons` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `basePlayerSuccessor_replay_last` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `decideReplayAction` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `decidePlayerSuccessor_replay_cons` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `decidePlayerSuccessor_replay_last` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `chanceResolutionAction` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `transition` | def | subsumed | `FOSGToEFG.execution`; `step_select`; `step_resolve` | EXP-061/D30 | Canonical FinDist execution owns selection and resolution. |
| same | `transition_base_empty_eq` | theorem | subsumed | `FOSGToEFG.execution`; `step_select`; `step_resolve` | EXP-061/D30 | Canonical FinDist execution owns selection and resolution. |
| same | `transition_base_nonempty_eq` | theorem | subsumed | `FOSGToEFG.execution`; `step_select`; `step_resolve` | EXP-061/D30 | Canonical FinDist execution owns selection and resolution. |
| same | `transition_decide_eq` | theorem | subsumed | `FOSGToEFG.execution`; `step_select`; `step_resolve` | EXP-061/D30 | Canonical FinDist execution owns selection and resolution. |
| same | `reward` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `reward_decide_eq_zero` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `reward_chance_base_eq` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `reward_decide_successor_eq_zero` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `reward_basePlayerSuccessor_eq_zero` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `reward_base_empty_base_eq_of_active_empty` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `privObs` | def | subsumed | `FOSGToEFG.signals`; resolver replay | EXP-061/D30 | Resolver-only source signal replay is stronger than option-wrapped bookkeeping. |
| same | `privObs_decide_eq_none` | theorem | subsumed | `FOSGToEFG.signals`; resolver replay | EXP-061/D30 | Resolver-only source signal replay is stronger than option-wrapped bookkeeping. |
| same | `privObs_chance_base_eq` | theorem | subsumed | `FOSGToEFG.signals`; resolver replay | EXP-061/D30 | Resolver-only source signal replay is stronger than option-wrapped bookkeeping. |
| same | `privObs_decide_successor_eq_none` | theorem | subsumed | `FOSGToEFG.signals`; resolver replay | EXP-061/D30 | Resolver-only source signal replay is stronger than option-wrapped bookkeeping. |
| same | `pubObs` | def | subsumed | `FOSGToEFG.signals`; resolver replay | EXP-061/D30 | Resolver-only source signal replay is stronger than option-wrapped bookkeeping. |
| same | `pubObs_decide_eq_none` | theorem | subsumed | `FOSGToEFG.signals`; resolver replay | EXP-061/D30 | Resolver-only source signal replay is stronger than option-wrapped bookkeeping. |
| same | `pubObs_chance_base_eq` | theorem | subsumed | `FOSGToEFG.signals`; resolver replay | EXP-061/D30 | Resolver-only source signal replay is stronger than option-wrapped bookkeeping. |
| same | `pubObs_decide_successor_eq_none` | theorem | subsumed | `FOSGToEFG.signals`; resolver replay | EXP-061/D30 | Resolver-only source signal replay is stronger than option-wrapped bookkeeping. |
| same | `pubObs_basePlayerSuccessor_eq_none` | theorem | subsumed | `FOSGToEFG.signals`; resolver replay | EXP-061/D30 | Resolver-only source signal replay is stronger than option-wrapped bookkeeping. |
| same | `pubObs_base_empty_base_eq_of_active_empty` | theorem | subsumed | `FOSGToEFG.signals`; resolver replay | EXP-061/D30 | Resolver-only source signal replay is stronger than option-wrapped bookkeeping. |
| same | `bookkeeping_decide_step` | theorem | subsumed | `step_select`; `step_resolve`; exact erased-history law | EXP-061/D30 | The generic bridge supplies the structural result at canonical law level. |
| same | `resolution_chance_step` | theorem | subsumed | `step_select`; `step_resolve`; exact erased-history law | EXP-061/D30 | The generic bridge supplies the structural result at canonical law level. |
| same | `map_base_apply` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `map_base_apply_decide` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `map_base_apply_chance` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `base_empty_support` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `chance_support` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `serialize` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `instDecidablePredSerializeTerminal` | instance | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `IsSerial` | def | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| same | `serialize_isSerial` | theorem | retired | no successor | EXP-061/D30 | D30 rejects the non-semantics-preserving serial-FOSG representation; any future canonical bridge result starts over. |
| `GameTheory/Languages/FOSG/Strategy.lean` | `availableMovesAtState` | def | adapt | `GameTheory.Protocol.LegalOption` | D6/D15; Protocol policy API review (2026-08-02) | Optional action legality is defined once at the execution/information boundary. |
| same | `mem_availableMovesAtState_iff` | theorem | subsumed | `GameTheory.Protocol.LegalOption` | D6/D15; API review | The predecessor membership theorem only unfolded its wrapper. |
| same | `availableActionsAtHistory` | def | subsumed | `ExecutionProtocol.available`; `InformationModel.menu_adequate` | D6/D15; API review | Actual actions remain state availability; information-local choice uses the canonical optional menu. |
| same | `mem_availableActionsAtHistory_iff` | theorem | subsumed | `LegalOption`; `InformationModel.menu_adequate` | D6/D15; API review | Active/some legality is the `LegalOption` constructor case. |
| same | `availableActionsAtHistory_eq_availableActionsAtState_of_mem_active` | theorem | subsumed | `ExecutionProtocol.available` | D6/D15; API review | No history wrapper separates the endpoint from its canonical availability set. |
| same | `availableActionsAtHistory_eq_empty_of_not_mem_active` | theorem | subsumed | `LegalOption.eq_none_of_inactive` | D6/D15; API review | Inactivity is expressed by the unique legal optional contribution `none`. |
| same | `availableMoves` | def | adapt | `InformationModel.menu`; `InformationModel.infoOf` | D6/D15; Protocol policy API review (2026-08-02) | The menu at the information state produced by a trace is the canonical history-facing move set. |
| same | `mem_availableMoves_iff` | theorem | subsumed | `InformationModel.menu_adequate` | D6/D15; API review | Menu adequacy is the exact equivalence with endpoint `LegalOption`. |
| same | `availableMoves_nonempty` | theorem | subsumed | `InformationModel.Choice`; `ExecutionProtocol.progress` | D6/D15; API review | Reached nonterminal menus inherit a legal joint coordinate; inactive or terminal coordinates use `none`. |
| same | `availableMoves_eq_availableMovesAtState` | theorem | subsumed | `InformationModel.menu_adequate` | D6/D15; API review | The canonical interface relates information-local and state-local legality pointwise. |
| same | `availableMoves_eq_singleton_none_of_not_mem_active` | theorem | subsumed | `InformationModel.subsingleton_choice_of_not_active` | D6; focused Protocol Information build evidence | The stronger typed result says every legal choice at an inactive reached state is equal. |
| same | `LegalObservable` | def | subsumed | `InformationModel.menu_adequate` | D6/D15; API review | Legal observability is enforced by one menu function on information states plus its adequacy law. |
| same | `availableMoves_eq_of_playerView_eq` | theorem | subsumed | `InformationModel.menu` | D6/D15; API review | Equal canonical information states select definitionally the same menu. |
| same | `availableActions_eq_of_playerView_eq` | theorem | subsumed | `InformationModel.menu_adequate` | D6/D15; API review | Actual-action equality follows from the shared optional menu; no raw player-view premise remains. |
| same | `availableMovesAtInfoState` | def | adapt | `InformationModel.menu` | D6/D15; Protocol policy API review (2026-08-02) | The information-local menu is a field with exact adequacy, not an existential union over histories. |
| same | `mem_availableMovesAtInfoState_iff` | theorem | subsumed | `InformationModel.menu` | D6/D15; API review | Membership is directly membership in the canonical menu. |
| same | `mem_availableMovesAtInfoState_of_history` | theorem | subsumed | `InformationModel.menu_adequate` | D6/D15; API review | Any endpoint-legal option belongs to the menu produced by that trace. |
| same | `availableMovesAtInfoState_eq_of_history` | theorem | subsumed | `InformationModel.menu_adequate` | D6/D15; API review | Adequacy replaces the predecessor's separate observability hypothesis. |
| same | `availableActionsAtInfoState` | def | subsumed | `InformationModel.Choice` | D6/D15; API review | Actual actions are the `some` case of the proof-carrying optional choice type. |
| same | `availableActionsAtInfoState_eq_of_history` | theorem | subsumed | `InformationModel.menu_adequate` | D6/D15; API review | The equality is carried pointwise by menu adequacy. |
| same | `PureStrategy` | abbrev | adapt | `InformationModel.Policy` | D6/D15; Protocol policy API review (2026-08-02) | A deterministic policy chooses from the dependent legal menu by construction. |
| same | `BehavioralStrategy` | abbrev | adapt | `InformationModel.BehavioralPolicy` | D6/D15; Protocol policy API review (2026-08-02) | Local randomization is a finite law over the dependent legal choice type. |
| same | `PureProfile` | abbrev | adapt | `Profile M.strategicSignature` | D6/D15; Protocol Strategic API review (2026-08-02) | The shared signature owns information-local pure profiles. |
| same | `BehavioralProfile` | abbrev | adapt | `Profile M.behavioralSignature` | D6/D15; Protocol Strategic API review (2026-08-02) | The shared behavioral signature owns locally randomized profiles. |
| same | `ofLatestObservation@238` | def | retired | model-specific policy constructor | D6/D15; Information slice review | Arbitrary information states need not expose a latest private/public observation. |
| same | `ofLatestObservation_nil@247` | theorem | retired | model-specific policy constructor | D6/D15; Information slice review | Equation for the retired raw-list policy adapter. |
| same | `ofLatestObservation_eq_policy@252` | theorem | retired | model-specific policy constructor | D6/D15; Information slice review | Equation for the retired raw-list policy adapter. |
| same | `ofLatestObservation@269` | def | retired | model-specific behavioral constructor | D6/D15; Information slice review | Arbitrary information states need not expose a latest observation. |
| same | `ofLatestObservation_nil@278` | theorem | retired | model-specific behavioral constructor | D6/D15; Information slice review | Equation for the retired raw-list behavioral adapter. |
| same | `ofLatestObservation_eq_policy@283` | theorem | retired | model-specific behavioral constructor | D6/D15; Information slice review | Equation for the retired raw-list behavioral adapter. |
| same | `ofLatestObservation@299` | def | retired | `Profile M.strategicSignature` | D6/D15; Information slice review | Profile construction is pointwise over the model's real information type; no latest-observation wrapper is canonical. |
| same | `ofLatestObservation_nil@307` | theorem | retired | `Profile M.strategicSignature` | D6/D15; Information slice review | Equation for the retired profile adapter. |
| same | `ofLatestObservation@321` | def | retired | `Profile M.behavioralSignature` | D6/D15; Information slice review | No FOSG-wide latest-observation behavioral profile exists. |
| same | `ofLatestObservation_nil@329` | theorem | retired | `Profile M.behavioralSignature` | D6/D15; Information slice review | Equation for the retired profile adapter. |
| same | `IsLegalPureStrategy` | def | subsumed | `InformationModel.Policy`; `InformationModel.Choice` | D6/D15; API review | Legality is carried in every dependent choice, not checked afterward. |
| same | `IsLegalBehavioralStrategy` | def | subsumed | `InformationModel.BehavioralPolicy`; `InformationModel.Choice` | D6/D15; API review | Every support point is typed as a legal menu choice. |
| same | `IsLegalPureProfile` | def | subsumed | `Profile M.strategicSignature` | D6/D15; API review | Every coordinate is already a legal canonical policy. |
| same | `IsLegalBehavioralProfile` | def | subsumed | `Profile M.behavioralSignature` | D6/D15; API review | Every coordinate randomizes only over legal choices. |
| same | `legalBehavioralStrategy_eq_pure_none_of_not_mem_active` | theorem | subsumed | `InformationModel.behavioral_eq_of_not_active` | D6; Protocol Information API review (2026-08-02) | The canonical theorem states that all behavioral laws coincide at an inactive reached state. |
| same | `LegalPureStrategy` | abbrev | retired | `InformationModel.Policy` | D6/D15; API review | A second subtype would duplicate legality already stored in `Choice`. |
| same | `LegalBehavioralStrategy` | abbrev | retired | `InformationModel.BehavioralPolicy` | D6/D15; API review | A second subtype would duplicate legality already stored in behavioral support. |
| same | `LegalPureProfile` | abbrev | retired | `Profile M.strategicSignature` | D6/D15; API review | Proof-wrapped profiles collapse to the canonical profile type. |
| same | `LegalBehavioralProfile` | abbrev | retired | `Profile M.behavioralSignature` | D6/D15; API review | Proof-wrapped profiles collapse to the canonical behavioral profile type. |
| same | `LegalPureProfile.toProfile` | abbrev | retired | identity on `Profile M.strategicSignature` | D6/D15; API review | There is no legality wrapper to forget. |
| same | `LegalBehavioralProfile.toProfile` | abbrev | retired | identity on `Profile M.behavioralSignature` | D6/D15; API review | There is no legality wrapper to forget. |
| same | `legalPureProfile_toProfile_apply` | theorem | retired | no wrapper projection | D6/D15; API review | Reflexive theorem for a retired wrapper. |
| same | `legalBehavioralProfile_toProfile_apply` | theorem | retired | no wrapper projection | D6/D15; API review | Reflexive theorem for a retired wrapper. |
| same | `ReachableInfoState` | def | retired | no second reachable information-state carrier | D6/D15; BehavioralAssessment API review | `InformationHistory` is a history fibre, not this subtype; canonical consumers use `infoOf` and indexed histories directly. |
| same | `reachableInfoStateOfHistory` | def | subsumed | `InformationModel.infoOf`; `InformationModel.mem_infoSet` | D6; API review | A history directly computes its canonical information value and witnesses membership. |
| same | `reachableInfoStateOfHistory_val` | theorem | subsumed | `InformationModel.infoOf` | D6; API review | The separate subtype projection has disappeared. |
| same | `instFintypeReachableInfoState` | instance | retired | operation-local `Fintype (M.InfoState i)` | greenfield finiteness rule; API review | The predecessor globally converted `Finite` with `Fintype.ofFinite`; finite capabilities now belong on consumers. |
| same | `ReachablePureStrategy` | abbrev | retired | `InformationModel.Policy` | D6/D15; API review | A second reachable-only strategy universe would fork canonical policy semantics. |
| same | `ReachableBehavioralStrategy` | abbrev | retired | `InformationModel.BehavioralPolicy` | D6/D15; API review | A second reachable-only behavioral universe would fork canonical policy semantics. |
| same | `ReachablePureProfile` | abbrev | retired | `Profile M.strategicSignature` | D6/D15; API review | Canonical profiles use the model-owned information type. |
| same | `ReachableBehavioralProfile` | abbrev | retired | `Profile M.behavioralSignature` | D6/D15; API review | Canonical behavioral profiles use the model-owned information type. |
| same | `instFintypeReachablePureStrategy` | instance | retired | operation-local `Fintype (M.InfoState i)` | greenfield finiteness rule; API review | Finite strategy enumeration is requested by the theorem that needs it. |
| same | `instFintypeReachablePureProfile` | instance | retired | operation-local finite profile assumptions | greenfield finiteness rule; API review | No global reachable-profile instance or `Fintype.ofFinite` escape hatch is retained. |
| same | `IsLegalReachablePureStrategy` | def | retired | `InformationModel.Policy` | D6/D15; API review | Both the reachable carrier and post-hoc legality predicate are unnecessary. |
| same | `IsLegalReachableBehavioralStrategy` | def | retired | `InformationModel.BehavioralPolicy` | D6/D15; API review | Both the reachable carrier and post-hoc legality predicate are unnecessary. |
| same | `ReachableLegalPureStrategy` | abbrev | retired | `InformationModel.Policy` | D6/D15; API review | Duplicate reachable/legal wrapper. |
| same | `ReachableLegalBehavioralStrategy` | abbrev | retired | `InformationModel.BehavioralPolicy` | D6/D15; API review | Duplicate reachable/legal wrapper. |
| same | `ReachableLegalPureProfile` | abbrev | retired | `Profile M.strategicSignature` | D6/D15; API review | Duplicate reachable/legal profile wrapper. |
| same | `ReachableLegalBehavioralProfile` | abbrev | retired | `Profile M.behavioralSignature` | D6/D15; API review | Duplicate reachable/legal behavioral profile wrapper. |
| same | `ReachableLegalPureProfile.toProfile` | abbrev | retired | no wrapper projection | D6/D15; API review | The duplicate carrier and its projection are both retired. |
| same | `ReachableLegalBehavioralProfile.toProfile` | abbrev | retired | no wrapper projection | D6/D15; API review | The duplicate carrier and its projection are both retired. |
| same | `PureStrategy.restrictReachable` | def | retired | canonical `InformationModel.Policy` | D6/D15; API review | Restriction would create a parallel strategy universe. |
| same | `BehavioralStrategy.restrictReachable` | def | retired | canonical `InformationModel.BehavioralPolicy` | D6/D15; API review | Restriction would create a parallel behavioral universe. |
| same | `LegalPureStrategy.restrictReachable` | def | retired | canonical `InformationModel.Policy` | D6/D15; API review | Legality is already in the canonical codomain. |
| same | `LegalBehavioralStrategy.restrictReachable` | def | retired | canonical `InformationModel.BehavioralPolicy` | D6/D15; API review | Legality is already in the canonical behavioral codomain. |
| same | `ReachablePureStrategy.extend` | def | retired | canonical `InformationModel.Policy` | D6/D15; API review | Defaulting to `none` at unreachable information values is unsound when their unconstrained menu omits `none`. |
| same | `ReachableBehavioralStrategy.extend` | def | retired | canonical `InformationModel.BehavioralPolicy` | D6/D15; API review | Defaulting to a point mass at `none` need not inhabit an unreachable menu. |
| same | `ReachablePureStrategy.extend_apply_history` | theorem | retired | no reachable extension | D6/D15; API review | Equation for the retired and generally ill-typed extension. |
| same | `ReachableBehavioralStrategy.extend_apply_history` | theorem | retired | no reachable extension | D6/D15; API review | Equation for the retired and generally ill-typed extension. |
| same | `ReachablePureProfile.extend` | def | retired | canonical `Profile M.strategicSignature` | D6/D15; API review | No reachable-only profile is extended. |
| same | `ReachableBehavioralProfile.extend` | def | retired | canonical `Profile M.behavioralSignature` | D6/D15; API review | No reachable-only behavioral profile is extended. |
| same | `ReachablePureStrategy.isLegal_extend` | theorem | retired | legality by `InformationModel.Choice` | D6/D15; API review | Post-hoc legality theorem for a retired extension. |
| same | `ReachableBehavioralStrategy.isLegal_extend` | theorem | retired | legality by `InformationModel.Choice` | D6/D15; API review | Post-hoc legality theorem for a retired extension. |
| same | `ReachableLegalPureProfile.extend` | def | retired | canonical `Profile M.strategicSignature` | D6/D15; API review | Composite wrapper/extension machinery is unnecessary. |
| same | `ReachableLegalBehavioralProfile.extend` | def | retired | canonical `Profile M.behavioralSignature` | D6/D15; API review | Composite wrapper/extension machinery is unnecessary. |
| same | `pureToBehavioral` | def | adapt | `InformationModel.Policy.toBehavioral` | D6; Protocol Information API review (2026-08-02) | A deterministic legal choice is lifted pointwise to a finite point mass. |
| same | `pureToBehavioral_apply` | theorem | subsumed | `InformationModel.Policy.toBehavioral` | D6; API review | The canonical lifting equation is definitional. |
| same | `legalBehavioral_of_legalPure` | theorem | subsumed | `InformationModel.Policy.toBehavioral` | D6; API review | The lifted law ranges over `Choice`, so legality requires no separate proof. |
| same | `legalPureToBehavioral` | def | retired | `InformationModel.Policy.toBehavioral` | D6; API review | A second lifting for proof-wrapped policies is unnecessary. |
| same | `MarkovJointPolicy` | abbrev | adapt | `ExecutionProtocol.RandomizedChooser` | D6; Protocol Randomized API review (2026-08-02) | The canonical randomized chooser is history-aware and typed by legal joint actions. |
| same | `PureMarkovJointPolicy` | abbrev | adapt | `ExecutionProtocol.HistoryChooser`; `ExecutionProtocol.Chooser` | D6; Protocol History API review (2026-08-02) | Canonical choosers request nonterminality at the operation that needs a legal joint action. |
| same | `pureMarkovToBehavioral` | def | subsumed | `ExecutionProtocol.HistoryChooser.toRandomized` | D6; Protocol Randomized API review (2026-08-02) | Deterministic choosers are lifted to point-mass randomized choosers once. |
| same | `pureMarkovToBehavioral_apply` | theorem | subsumed | `ExecutionProtocol.HistoryChooser.toRandomized` | D6; API review | The point-mass equation is definitional in the canonical lift. |
| same | `stepProb` | def | retired | `ExecutionProtocol.runRandomizedFor` | D6/D15; Protocol Randomized API review | The auxiliary product semantics is replaced by the canonical law-valued runner. |
| same | `pathProb` | def | retired | `ExecutionProtocol.runRandomizedFor` | D6/D15; Protocol Randomized API review | A bare list product is not a second execution semantics. |
| same | `prob` | def | retired | `ExecutionProtocol.runRandomizedFor` | D6/D15; Protocol Randomized API review | Complete history probabilities are read from the canonical finite law when needed. |
| same | `pathProb_nil` | theorem | retired | `ExecutionProtocol.runRandomizedFor_zero` | D6; API review | Base equation for retired product semantics. |
| same | `pathProb_cons` | theorem | retired | `ExecutionProtocol.runRandomizedFor_succ_of_not_terminal` | D6; API review | Recursive execution is expressed by finite-law bind, not scalar multiplication over a list. |
| same | `prob_nil` | theorem | retired | `ExecutionProtocol.runRandomizedFor_zero` | D6; API review | The canonical zero-fuel law is a point mass at the supplied history. |
| same | `pathProb_append_singleton` | theorem | retired | `ExecutionProtocol.runRandomizedFor_succ_of_not_terminal` | D6; API review | Arbitrary list append lacks the indexed endpoint witnesses of canonical histories. |
| same | `prob_snoc` | theorem | retired | `ExecutionProtocol.runRandomizedFor_succ_of_not_terminal` | D6; API review | One-step law composition is already the canonical runner equation. |
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
