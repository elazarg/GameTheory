# L-BRIDGE: Bounded pinned FOSG-to-EFG bridge chain

Title: Bounded pinned FOSG-to-EFG bridge chain
Family ID: L-BRIDGE
Pinned roots: `GameTheory/Languages/Bridges/FOSG/SerialExec.lean`; `GameTheory/Languages/Bridges/FOSG/AugmentedEFG/Base.lean`; `GameTheory/Languages/Bridges/FOSG/AugmentedEFG.lean`; `GameTheory/Languages/Expressiveness/EFG_FOSG.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `01f790a`
Canonical destination: `GameTheory.Languages.Bridges.FOSGToEFG`; future named strategic/kernel, ordinary-continuation/terminal-support, and augmentation/public-information gates
Domain contract / decision: D30; EXP-059, EXP-060, EXP-061
Owner: Wave 3 / named bridge recovery
Status: complete for this bounded FOSG bridge chain; 104/104 reviewed, with deferred rows explicitly retained as future gates (not a claim that all L-BRIDGE recovery is complete)
Last verified: 2026-08-03

This is the exact generated-index inventory for the four pinned paths above.
It attributes the mathematics to the pinned paths and commit, while retaining
only the canonical generic serializer and its named laws. EXP-059/060/061 and
D30 establish the hostile signal-replay shape, arbitrary target-profile
projection, exact all-round erased-history law, and order transport. The
focused bridge build and axiom audit are warning-free and use only `propext`,
`Classical.choice`, and `Quot.sound`.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Languages/Bridges/FOSG/SerialExec.lean` | `State` | abbrev | retired | none | EXP-061/D30 | Source-history identity state is not genuine serialization. |
| same | `erase` | abbrev | adapt | `FOSGToEFG.eraseHistory` | EXP-061/D30 | Canonical target-history erasure. |
| same | `root` | abbrev | adapt | `(FOSGToEFG.execution G order).initHistory` | EXP-061/D30 | Canonical serialized root. |
| same | `runOriginal` | def | retired | none | D30 | A second runner is forbidden. |
| same | `runOriginal_zero` | theorem | subsumed | `ExecutionProtocol.runRandomizedFor_zero` | EXP-061 | Canonical runner zero law. |
| same | `runOriginal_erases_to_native` | theorem | subsumed | `FOSGToEFG.map_erase_runBehavioral_eq_source` | EXP-061/D30 | Stronger all-profile, all-round literal history law. |
| `GameTheory/Languages/Bridges/FOSG/AugmentedEFG/Base.lean` | `PlayerIx` | abbrev | retired | none | D30 | No global finite player reindexing. |
| same | `playerEquiv` | def | retired | none | D30 | No `Fin` player transport. |
| same | `origPlayer` | def | retired | none | D30 | No `Fin` player transport. |
| same | `origPlayer_playerEquiv` | theorem | retired | none | D30 | Reindexing identity is obsolete. |
| same | `playerEquiv_origPlayer` | theorem | retired | none | D30 | Reindexing identity is obsolete. |
| same | `Word` | abbrev | retired | canonical source information | D30 | Fixed-width view encoding removed. |
| same | `ofList` | def | retired | canonical source information | D30 | Fixed-width view encoding removed. |
| same | `toList` | def | retired | canonical source information | D30 | Fixed-width view encoding removed. |
| same | `toList_ofList_eq_self` | theorem | retired | canonical source information | D30 | Fixed-width view encoding removed. |
| same | `instDecidableEqPlayerEvent` | instance | retired | none | D30 | Served the removed finite encoding. |
| same | `instFintypePlayerEvent` | instance | retired | none | D30 | Served the removed finite encoding. |
| same | `step_playerView_length_le_two` | theorem | retired | canonical source information | D30 | Bound only justified word encoding. |
| same | `playerViewFrom_length_le_two_mul` | theorem | retired | canonical source information | D30 | Bound only justified word encoding. |
| same | `history_playerView_length_le_two_mul_steps` | theorem | retired | canonical source information | D30 | Bound only justified word encoding. |
| same | `EncPlayerView` | abbrev | retired | `FOSGToEFG.View` | D30 | Target carries canonical source information. |
| same | `EncPublicView` | abbrev | retired | `FOSGToEFG.View` | D30 | Target carries canonical source information. |
| same | `encodePlayerView` | def | retired | `FOSGToEFG.scheduledView` | D30 | No encoded player view. |
| same | `encodePublicView` | def | retired | `FOSGToEFG.View.source` | D30 | No encoded public view. |
| same | `infoStructure` | def | retired | `FOSGToEFG.information` | EXP-061 | Certified canonical information, not finite action indices. |
| same | `actionOfIndex` | def | retired | `InformationModel.Choice` | D30 | No ambient invalid action index. |
| same | `indexOfAction` | def | retired | `InformationModel.Choice` | D30 | No ambient invalid action index. |
| same | `actionOfIndex_indexOfAction` | theorem | retired | `InformationModel.Choice` | D30 | Codec theorem has no successor surface. |
| same | `fintype_card_pos_of_pmf` | theorem | subsumed | `Fintype.card_pos_iff`; PMF support nonemptiness | Mathlib review | General finite-card fact. |
| same | `PayoffVec` | abbrev | retired | external utility layer | D30 | Bridge syntax owns no payoff vector. |
| same | `recordOption` | def | retired | `FOSGToEFG.Prefix.advance` | D30 | Typed prefix replaces raw joint update. |
| same | `legalize` | def | retired | none | D30 | Default/invalid-branch machinery is excluded. |
| same | `transitionChance` | def | adapt | `FOSGToEFG.resolve` | EXP-061 | Resolver applies certified source transition. |
| same | `choosePlayersFrom` | def | retired | `FOSGToEFG.execution` | D30 | No separate `GameTree` evaluator. |
| same | `fromHistory` | def | retired | `FOSGToEFG.execution` | D30 | No separate `GameTree` evaluator. |
| same | `tree_fromHistory_zero` | theorem | subsumed | canonical runner zero law | EXP-061 | Old evaluator unfolding removed. |
| same | `tree_fromHistory_succ_terminal` | theorem | subsumed | canonical terminal runner law | EXP-061 | Old evaluator unfolding removed. |
| same | `tree_fromHistory_succ_nonterminal` | theorem | subsumed | `FOSGToEFG.step_select`; `step_resolve` | EXP-061 | Serializer step structure is direct. |
| same | `choosePlayersFrom_decisionSpineThenChance` | theorem | subsumed | `FOSGToEFG.treeShaped`; `singleMover` | EXP-061/D30 | Direct EFG structural laws. |
| same | `fromHistory_succ_nonterminal_decisionSpineThenChance` | theorem | subsumed | `FOSGToEFG.treeShaped`; `singleMover` | EXP-061/D30 | Direct EFG structural laws. |
| same | `choosePlayersFrom_roundSpineShape` | theorem | subsumed | `FOSGToEFG.treeShaped`; `singleMover` | EXP-061/D30 | Direct EFG structural laws. |
| same | `fromHistory_fullTreeShape` | theorem | subsumed | `FOSGToEFG.treeShaped` | EXP-061/D30 | Generic serializer is tree-shaped. |
| same | `tree_eval_zero` | theorem | subsumed | canonical runner zero law | EXP-061 | No tree evaluator remains. |
| same | `toPlainEFGAtHorizon` | def | adapt | `FOSGToEFG.toEFG` | EXP-061/D30 | Generic EFG needs no horizon encoding. |
| same | `toPlainEFGAtHorizon_zero_outcomeKernel` | theorem | subsumed | canonical runner zero law | EXP-061 | Kernel wrapper removed. |
| same | `toPlainEFGOfBoundedHorizon` | def | retired | none | D30 | Bounded wrapper is obsolete packaging. |
| same | `translateBehavioralProfile` | def | adapt | `FOSGToEFG.translateBehavioral` | EXP-061 | Canonical source-to-target policy map. |
| same | `EFGProfileRespectsFOSG` | def | retired | certified target menu | EXP-061/D30 | Target choices are legal by construction. |
| same | `translateBehavioralProfile_respectsFOSG` | theorem | retired | certified target menu | EXP-061/D30 | No validity side predicate remains. |
| same | `tree_eval_zero_eq_runDistFrom_zero` | theorem | subsumed | canonical runner zero law | EXP-061 | No tree evaluator remains. |
| same | `tree_eval_succ_terminal_eq_runDistFrom` | theorem | subsumed | canonical terminal runner law | EXP-061 | No tree evaluator remains. |
| same | `tree_eval_succ_nonterminal_unfold` | theorem | subsumed | `FOSGToEFG.map_erase_runBehavioral_eq_source` | EXP-061 | Stronger canonical-run law. |
| same | `efgChoiceProfile` | def | retired | `FOSGToEFG.translateBehavioral` | D30 | Raw finite action encoding removed. |
| same | `efgChoicesEquiv` | def | retired | `FOSGToEFG.choiceEquiv` | D30 | Reindexing codec removed. |
| same | `efgJointActionDist` | def | retired | `InformationModel.behavioralJoint` | D30 | No parallel raw joint distribution. |
| same | `efgChoicesEquiv_symm_recordOption` | theorem | retired | none | D30 | Obsolete raw codec bookkeeping. |
| same | `efgJointActionDist_eq_jointActionDist` | theorem | subsumed | `FOSGToEFG.map_erase_runBehavioral_eq_source` | EXP-061 | Whole-history law is stronger. |
| same | `efgJointActionDist_bind_eq_jointActionDist_bind` | theorem | subsumed | `FOSGToEFG.map_erase_runBehavioral_eq_source` | EXP-061 | Whole-history law is stronger. |
| same | `choosePlayersFrom_evalDist_gen` | theorem | subsumed | `FOSGToEFG.map_erase_runBehavioral_eq_source` | EXP-061 | Tree-evaluator induction removed. |
| same | `choosePlayersFrom_zero_evalDist_eq_efgJointActionDist_bind` | theorem | subsumed | `FOSGToEFG.map_erase_runBehavioral_eq_source` | EXP-061 | Tree-evaluator induction removed. |
| same | `sum_subtype_eq_sum_ite` | theorem | subsumed | `Finset.sum_subtype_eq_sum_filter` | Mathlib review | General Mathlib algebra. |
| same | `jointActionDist_bind_legalize_eq_legalActionLaw_bind` | theorem | retired | none | D30 | Depends on retired legalization. |
| same | `jointActionDist_bind_legalize_eq_legalActionLaw_bind_coe` | theorem | retired | none | D30 | Depends on retired legalization. |
| same | `tree_eval_eq_runDistFrom_of_length_add_le` | theorem | subsumed | `FOSGToEFG.map_erase_runBehavioral_translate` | EXP-061/D30 | Stronger all-round exact history law. |
| same | `toPlainEFGAtHorizon_outcomeKernel_eq_runDist` | theorem | deferred | named strategic/kernel transfer gate | D30 | Exact history law exists; KernelGame packaging is separate. |
| same | `toPlainEFGOfBoundedHorizon_outcomeKernel_eq_runDist` | theorem | deferred | named strategic/kernel transfer gate | D30 | Exact history law exists; KernelGame packaging is separate. |
| same | `toPlainEFGOfBoundedHorizon_outcomeKernel_eq_nativeBounded` | theorem | deferred | named strategic/kernel transfer gate | D30 | Exact history law exists; KernelGame packaging is separate. |
| same | `toPlainEFGOfBoundedHorizon_support_isTerminal` | theorem | deferred | ordinary-continuation / terminal-support gate | D30 | Bounded terminal-support result is not D30. |
| `GameTheory/Languages/Bridges/FOSG/AugmentedEFG.lean` | `encodedInfoOfView` | def | retired | `FOSGToEFG.scheduledView` | D30 | Finite encoding/cast boundary removed. |
| same | `actionOfIndexForPlayer` | def | retired | `FOSGToEFG.choiceEquiv` | D30 | Finite encoding/cast boundary removed. |
| same | `availableMoves_cast_mem` | theorem | retired | none | D30 | Private cast helper for removed encoding. |
| same | `word_toList_cast_eq` | theorem | retired | none | D30 | Private cast helper for removed encoding. |
| same | `playerView_cast_eq_of_eq` | theorem | retired | none | D30 | Private cast helper for removed encoding. |
| same | `efgToFOSGProfile` | def | adapt | `FOSGToEFG.projectBehavioral` | EXP-061 | Unconditional inverse policy projection. |
| same | `efgToFOSGProfile_apply` | theorem | adapt | `FOSGToEFG.projectBehavioral` | EXP-061 | Projection reads scheduled target views. |
| same | `efgToFOSGProfile_translateBehavioralProfile_apply_aux` | theorem | subsumed | `FOSGToEFG.project_translate` | EXP-061 | Private finite-codec round-trip proof. |
| same | `efgToFOSGProfile_translateBehavioralProfile_apply` | theorem | subsumed | `FOSGToEFG.project_translate_profile` | EXP-061 | Exact source-profile round trip. |
| same | `translate_efgToFOSG_apply_encoded_aux` | theorem | retired | none | D30 | Private cast helper. |
| same | `translate_efgToFOSG_apply_encoded` | theorem | retired | none | D30 | Private encoded-view helper. |
| same | `choosePlayersFrom_evalDist_eq_translate_efgToFOSG_aux` | theorem | subsumed | `FOSGToEFG.translate_project_profile` | EXP-061 | Private tree-evaluator proof superseded. |
| same | `choosePlayersFrom_evalDist_eq_translate_efgToFOSG` | theorem | subsumed | `FOSGToEFG.translate_project_profile` | EXP-061 | Private tree-evaluator proof superseded. |
| same | `fromHistory_evalDist_eq_translate_efgToFOSG` | theorem | subsumed | `FOSGToEFG.map_erase_runBehavioral_eq_source` | EXP-061 | Exact canonical-run law supersedes it. |
| same | `toPlainEFGOfBoundedHorizon_outcomeKernel_eq_efgToFOSG` | theorem | subsumed | `FOSGToEFG.map_erase_runBehavioral_eq_source` | EXP-061 | Current law covers every target profile. |
| same | `toPlainEFGOfBoundedHorizon_eu_eq_native` | theorem | deferred | named strategic/utility transfer gate | D30 | Utility transport is outside D30. |
| same | `toPlainEFGOfBoundedHorizon_udistPlayer_eq_efgToFOSG` | theorem | deferred | named strategic/utility transfer gate | D30 | Utility transport is outside D30. |
| same | `toPlainEFGOfBoundedHorizon_eu_eq_efgToFOSG` | theorem | deferred | named strategic/utility transfer gate | D30 | Utility transport is outside D30. |
| same | `nodePlayerView` | def | retired | `FOSGToEFG.View.source` | D30 | Bounded encoded node view is not canonical. |
| same | `toAugmentedOfBoundedHorizon` | def | deferred | augmentation/public-information gate | D30 | No stable augmentation root exists. |
| same | `forget_toAugmentedOfBoundedHorizon` | theorem | deferred | augmentation/public-information gate | D30 | Depends on deferred augmentation. |
| same | `noThickPublicSets_toAugmentedOfBoundedHorizon` | theorem | deferred | augmentation/public-information gate | D30 | Length-stamped proxy is not reusable design. |
| `GameTheory/Languages/Expressiveness/EFG_FOSG.lean` | `BoundedFOSGPresentation` | structure | retired | none | D30 | Bundles global finiteness and horizon into syntax. |
| same | `historyFintype` | def | adapt | `EFG.Game.historyFintype` | D30 | Finiteness is theorem-local capability. |
| same | `toKernelGame` | def | deferred | named strategic/kernel transfer gate | D30 | Kernel wrapper remains separate. |
| same | `toPlainEFG` | def | adapt | `FOSGToEFG.toEFG` | EXP-061/D30 | Generic serializer is semantic successor. |
| same | `toPlainEFGKernelGame` | def | deferred | named strategic/kernel transfer gate | D30 | Kernel wrapper remains separate. |
| same | `toAugmentedEFG` | def | deferred | augmentation/public-information gate | D30 | No stable augmentation root exists. |
| same | `translateStrategy` | def | adapt | `FOSGToEFG.translateBehavioral` | EXP-061 | Canonical dependent policy translation. |
| same | `translateProfile` | def | adapt | `FOSGToEFG.translateBehavioral` | EXP-061 | Canonical profile translation. |
| same | `toPlainEFGKernelGame_outcomeKernel_eq_native` | theorem | deferred | named strategic/kernel transfer gate | D30 | History-law precursor exists; kernel theorem is separate. |
| same | `toPlainEFGKernelGame_udist_eq_native` | theorem | deferred | named strategic/utility transfer gate | D30 | Utility theorem is separate. |
| same | `BoundedFOSGLanguage` | def | deferred | named language-expressiveness gate | D0/D30 | No generic language wrapper is authorized. |
| same | `FOSGPlainEFGLanguage` | def | deferred | named language-expressiveness gate | D0/D30 | No generic language wrapper is authorized. |
| same | `boundedFOSGToPlainEFGProfileMapReduction` | def | deferred | named language-expressiveness gate | D0/D30 | Reduction hierarchy is not authorized. |
| same | `boundedFOSG_expressiveLe_plainEFG_profileMap` | theorem | deferred | named language-expressiveness gate | D0/D30 | Expressiveness packaging is a later gate. |

The 104 declarations are all classified: 11 adapt, 27 subsumed, 47 retired,
and 19 deferred; no row is unreviewed. The deferred rows are deliberately
counted rather than silently discarded: they reserve strategic/kernel and
utility transfer, ordinary-continuation terminal support, augmentation, and
language-expressiveness work without reopening the settled D30 serializer.

The generic adapter already subsumed the live semantic spine—tree shape,
single-mover structure, source/target policy projection, source-profile round
trip, and literal all-round history-law preservation. The only new stable
surface justified by this recovery was `translate_project_profile`: every
non-owner selection and resolver menu is singleton, so it upgrades the prior
scheduled-view inverse to a full target-profile inverse without an old
respectfulness predicate, bounded encoding, cast plumbing, or default action.
