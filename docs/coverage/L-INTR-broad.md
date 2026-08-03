# L-INTR: Broad intrinsic language recovery

Title: Broad intrinsic language recovery
Family ID: L-INTR
Pinned roots: `GameTheory/Languages/Intrinsic/Compile.lean`; `GameTheory/Languages/Intrinsic/Examples.lean`; `GameTheory/Languages/Intrinsic/PerfectRecall.lean`; `GameTheory/Languages/Intrinsic/Strategies.lean`; `GameTheory/Languages/Intrinsic/Syntax.lean`; `GameTheory/Languages/Intrinsic/Tests.lean`; `GameTheory/Languages/Intrinsic/Theorems.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `544528b`
Canonical destination: GameTheory.Languages.Intrinsic; separately gated temporal, mixed, utility, and Kuhn bridges
Domain contract / decision: D31 / EXP-062; Wave 3 sequential and language recovery
Owner: Wave 3 / intrinsic-language recovery
Status: in progress; 27/158 reviewed (12 adapt, 10 deferred, 5 retired), 131 unreviewed
Last verified: 2026-08-03

This ledger is an exact generated review queue for the L-INTR family.
0 declarations are already accounted for in earlier bounded ledgers and are
not duplicated here. The 27 declarations in the pinned `Syntax.lean` are
reviewed below against D31; the other 131 rows remain deliberately
`unreviewed`. The generated index supplies spelling, location, kind, and
visibility only. It does not infer a mathematical disposition.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Languages/Intrinsic/Compile.lean` | `liftProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 34 |
| same | `OpponentMixedProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 44 |
| same | `assembleMixedProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 50 |
| same | `mixedOutcomeAt` | def | unreviewed | review required | generated index seed only | public, pinned line 62 |
| same | `mixedOutcomeLaw` | def | unreviewed | review required | generated index seed only | public, pinned line 69 |
| same | `playerSolutionEvent` | def | unreviewed | review required | generated index seed only | public, pinned line 76 |
| same | `profileSolutionEvent` | def | unreviewed | review required | generated index seed only | public, pinned line 83 |
| same | `solutionMap_eq_iff_profileSolutionEvent` | theorem | unreviewed | review required | generated index seed only | public, pinned line 90 |
| same | `mixedOutcomeAt_apply_eq_prod` | theorem | unreviewed | review required | generated index seed only | public, pinned line 112 |
| same | `PlayerEventMassEquivalent` | def | unreviewed | review required | generated index seed only | public, pinned line 136 |
| same | `productMixed_playerSolutionEvent_mass_eq_prod` | theorem | unreviewed | review required | generated index seed only | public, pinned line 144 |
| same | `KuhnOutcomeEquivalent` | def | unreviewed | review required | generated index seed only | public, pinned line 172 |
| same | `kuhn_equivalence_of_player_event_mass` | theorem | unreviewed | review required | generated index seed only | public, pinned line 182 |
| same | `EUWGame.toKernelGame` | def | unreviewed | review required | generated index seed only | public, pinned line 214 |
| `GameTheory/Languages/Intrinsic/Examples.lean` | `Coin` | inductive | unreviewed | review required | generated index seed only | public, pinned line 28 |
| same | `<anonymous@31>` | instance | unreviewed | review required | generated index seed only | public, pinned line 31 |
| same | `matchingPenniesModel` | def | unreviewed | review required | generated index seed only | public, pinned line 37 |
| same | `mpUtility` | def | unreviewed | review required | generated index seed only | public, pinned line 45 |
| same | `matchingPennies` | def | unreviewed | review required | generated index seed only | public, pinned line 51 |
| same | `SigType` | inductive | unreviewed | review required | generated index seed only | public, pinned line 64 |
| same | `<anonymous@67>` | instance | unreviewed | review required | generated index seed only | public, pinned line 67 |
| same | `Message` | inductive | unreviewed | review required | generated index seed only | public, pinned line 70 |
| same | `<anonymous@73>` | instance | unreviewed | review required | generated index seed only | public, pinned line 73 |
| same | `RcvAction` | inductive | unreviewed | review required | generated index seed only | public, pinned line 76 |
| same | `<anonymous@79>` | instance | unreviewed | review required | generated index seed only | public, pinned line 79 |
| same | `sigDecision` | def | unreviewed | review required | generated index seed only | public, pinned line 83 |
| same | `sigDecisionFintype` | instance | unreviewed | review required | generated index seed only | public, pinned line 87 |
| same | `sigDecisionNonempty` | instance | unreviewed | review required | generated index seed only | public, pinned line 92 |
| same | `signalingModel` | def | unreviewed | review required | generated index seed only | public, pinned line 101 |
| same | `sigReceiverAction` | def | unreviewed | review required | generated index seed only | public, pinned line 114 |
| same | `signalingUtility` | def | unreviewed | review required | generated index seed only | public, pinned line 117 |
| same | `signalingGame` | def | unreviewed | review required | generated index seed only | public, pinned line 124 |
| same | `matchingPennies_solvable` | theorem | unreviewed | review required | generated index seed only | public, pinned line 138 |
| `GameTheory/Languages/Intrinsic/PerfectRecall.lean` | `choiceEquiv` | def | unreviewed | review required | generated index seed only | public, pinned line 50 |
| same | `playerChoiceEquiv` | def | unreviewed | review required | generated index seed only | public, pinned line 62 |
| same | `PerfectRecall` | def | unreviewed | review required | generated index seed only | public, pinned line 82 |
| same | `predecessorsInOrdering` | def | unreviewed | review required | generated index seed only | public, pinned line 100 |
| same | `prefixThroughInOrdering` | def | unreviewed | review required | generated index seed only | public, pinned line 106 |
| same | `prefixThroughInOrdering_idx_lt` | theorem | unreviewed | review required | generated index seed only | public, pinned line 111 |
| same | `prefixThroughInOrdering_val_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 116 |
| same | `prefixThroughInOrdering_ne_nil` | theorem | unreviewed | review required | generated index seed only | public, pinned line 128 |
| same | `prefixThroughInOrdering_last` | theorem | unreviewed | review required | generated index seed only | public, pinned line 135 |
| same | `prefixThroughInOrdering_mem_configSet` | theorem | unreviewed | review required | generated index seed only | public, pinned line 142 |
| same | `prefixThroughInOrdering_predecessors` | theorem | unreviewed | review required | generated index seed only | public, pinned line 150 |
| same | `prefixThroughInOrdering_eq_of_configSet_last` | theorem | unreviewed | review required | generated index seed only | public, pinned line 159 |
| same | `OrderInfoCompatibleWith` | def | unreviewed | review required | generated index seed only | public, pinned line 198 |
| same | `predecessorsInOrdering_eq_of_info` | theorem | unreviewed | review required | generated index seed only | public, pinned line 203 |
| same | `prefixThroughInOrdering_mem_configSet_of_info` | theorem | unreviewed | review required | generated index seed only | public, pinned line 211 |
| same | `prefixThroughInOrdering_eq_of_info_of_perfectRecall` | theorem | unreviewed | review required | generated index seed only | public, pinned line 219 |
| same | `orderInfoCompatibleWith_of_forall_perfectRecall` | theorem | unreviewed | review required | generated index seed only | public, pinned line 246 |
| same | `ownedAgentsInList` | def | unreviewed | review required | generated index seed only | public, pinned line 260 |
| same | `mem_ownedAgentsInList_iff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 270 |
| same | `ownedAgentsInList_nodup` | theorem | unreviewed | review required | generated index seed only | public, pinned line 300 |
| same | `ownedAgentsInList_toFinset_of_mem_all` | theorem | unreviewed | review required | generated index seed only | public, pinned line 323 |
| same | `ownedAgentsInList_append_singleton_of_not_owner` | theorem | unreviewed | review required | generated index seed only | public, pinned line 330 |
| same | `ownedAgentsInList_append` | theorem | unreviewed | review required | generated index seed only | public, pinned line 342 |
| same | `ownedAgentsInList_append_singleton_of_owner` | theorem | unreviewed | review required | generated index seed only | public, pinned line 355 |
| same | `playerAgentsInOrdering` | def | unreviewed | review required | generated index seed only | public, pinned line 370 |
| same | `playerAgentsInOrdering_nodup` | theorem | unreviewed | review required | generated index seed only | public, pinned line 375 |
| same | `playerAgentsInOrdering_mem` | theorem | unreviewed | review required | generated index seed only | public, pinned line 381 |
| same | `playerAgentsInOrdering_toFinset` | theorem | unreviewed | review required | generated index seed only | public, pinned line 388 |
| same | `playerAgentsInOrdering_prod_eq_univ` | theorem | unreviewed | review required | generated index seed only | public, pinned line 395 |
| same | `playerPastAgentsInOrdering` | def | unreviewed | review required | generated index seed only | public, pinned line 410 |
| same | `mem_playerPastAgentsInOrdering_predecessors` | theorem | unreviewed | review required | generated index seed only | public, pinned line 416 |
| same | `mem_playerPastAgentsInOrdering_iff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 426 |
| same | `playerPastAgentsInOrdering_mem_iff_of_info` | theorem | unreviewed | review required | generated index seed only | public, pinned line 436 |
| same | `ownedAgentsInList_eq_past_of_decomp` | theorem | unreviewed | review required | generated index seed only | public, pinned line 456 |
| same | `playerPastConsistent` | def | unreviewed | review required | generated index seed only | public, pinned line 481 |
| same | `playerAgentSolutionEvent` | def | unreviewed | review required | generated index seed only | public, pinned line 490 |
| same | `playerSolutionEventsInOrdering` | def | unreviewed | review required | generated index seed only | public, pinned line 497 |
| same | `allEvents_playerSolutionEventsInOrdering_iff` | theorem | unreviewed | review required | generated index seed only | public, pinned line 503 |
| same | `allEvents_playerSolutionEventsInOrdering_eq` | theorem | unreviewed | review required | generated index seed only | public, pinned line 522 |
| same | `allEvents_ownedAgentsInList_eq_playerPastConsistent` | theorem | unreviewed | review required | generated index seed only | public, pinned line 529 |
| same | `playerChainFallback` | def | unreviewed | review required | generated index seed only | public, pinned line 558 |
| same | `playerAgentsInOrdering_decomp_of_raw_decomp` | theorem | unreviewed | review required | generated index seed only | public, pinned line 568 |
| same | `playerChainFallback_eq_current` | theorem | unreviewed | review required | generated index seed only | public, pinned line 581 |
| same | `playerSolutionEvent_mass_eq_chainProduct` | theorem | unreviewed | review required | generated index seed only | public, pinned line 599 |
| same | `playerPastConsistent_eq_of_info` | theorem | unreviewed | review required | generated index seed only | public, pinned line 610 |
| same | `mixedToBehavioralKernelAt` | def | unreviewed | review required | generated index seed only | public, pinned line 674 |
| same | `MixedToBehavioralMeasurable` | def | unreviewed | review required | generated index seed only | public, pinned line 685 |
| same | `mixedToBehavioralMeasurable_of_perfectRecall` | theorem | unreviewed | review required | generated index seed only | public, pinned line 693 |
| same | `mixedToBehavioral` | def | unreviewed | review required | generated index seed only | public, pinned line 734 |
| same | `condEventFactor_playerPast_eq_kernel` | theorem | unreviewed | review required | generated index seed only | public, pinned line 745 |
| same | `defaultBehavioralStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 774 |
| same | `mixedToBehavioral_chainProduct_aux` | theorem | unreviewed | review required | generated index seed only | public, pinned line 782 |
| same | `KuhnEventRealizable` | def | unreviewed | review required | generated index seed only | public, pinned line 983 |
| same | `MixedToBehavioralEventMassIdentity` | def | unreviewed | review required | generated index seed only | public, pinned line 990 |
| same | `mixedToBehavioral_eventMassIdentity` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1000 |
| same | `kuhn_event_realizable_of_behavioral_event_mass` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1048 |
| same | `kuhn_event_realizable_of_mixedToBehavioral_identity` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1065 |
| same | `kuhn_equivalence_of_event_realizable` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1076 |
| same | `kuhn_equivalence` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1094 |
| same | `kuhn_equivalence_of_mixedToBehavioral_identity` | theorem | unreviewed | review required | generated index seed only | public, pinned line 1115 |
| `GameTheory/Languages/Intrinsic/Strategies.lean` | `PlayerStrategySpace` | def | unreviewed | review required | generated index seed only | public, pinned line 47 |
| same | `MixedStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 52 |
| same | `MixedProfile` | def | unreviewed | review required | generated index seed only | public, pinned line 56 |
| same | `mixedJoint` | def | unreviewed | review required | generated index seed only | public, pinned line 62 |
| same | `ProductMixedStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 73 |
| same | `productMixedAsMixed` | def | unreviewed | review required | generated index seed only | public, pinned line 79 |
| same | `BehavioralAgentStrategy` | structure | unreviewed | review required | generated index seed only | public, pinned line 93 |
| same | `BehavioralStrategy` | def | unreviewed | review required | generated index seed only | public, pinned line 101 |
| same | `productMixedToBehavioral` | def | unreviewed | review required | generated index seed only | public, pinned line 112 |
| same | `InfoClass` | abbrev | unreviewed | review required | generated index seed only | public, pinned line 132 |
| same | `<anonymous@136>` | instance | unreviewed | review required | generated index seed only | public, pinned line 136 |
| same | `PureStrategy.ext` | theorem | unreviewed | review required | generated index seed only | public, pinned line 139 |
| same | `PureStrategy.ofQuotientFun` | def | unreviewed | review required | generated index seed only | public, pinned line 144 |
| same | `PureStrategy.toQuotientFun` | def | unreviewed | review required | generated index seed only | public, pinned line 153 |
| same | `PureStrategy.ofQuotientFun_toQuotientFun` | theorem | unreviewed | review required | generated index seed only | public, pinned line 157 |
| same | `PureStrategy.toQuotientFun_ofQuotientFun` | theorem | unreviewed | review required | generated index seed only | public, pinned line 164 |
| same | `pureStrategyEquiv` | def | unreviewed | review required | generated index seed only | public, pinned line 173 |
| same | `<anonymous@181>` | instance | unreviewed | review required | generated index seed only | public, pinned line 181 |
| same | `BehavioralAgentStrategy.classKernel` | def | unreviewed | review required | generated index seed only | public, pinned line 190 |
| same | `BehavioralAgentStrategy.classKernel_mk` | theorem | unreviewed | review required | generated index seed only | public, pinned line 195 |
| same | `behavioralProductPMF` | def | unreviewed | review required | generated index seed only | public, pinned line 202 |
| same | `behavioralToPureStrategyPMF` | def | unreviewed | review required | generated index seed only | public, pinned line 209 |
| same | `ofQuotientFun_preimage_act` | theorem | unreviewed | review required | generated index seed only | public, pinned line 216 |
| same | `behavioralToPureStrategyPMF_marginal` | theorem | unreviewed | review required | generated index seed only | public, pinned line 228 |
| same | `behavioral_realizes_productMixed` | theorem | unreviewed | review required | generated index seed only | public, pinned line 252 |
| same | `productMixedToBehavioral_apply_eq_pmfMass` | theorem | unreviewed | review required | generated index seed only | public, pinned line 264 |
| `GameTheory/Languages/Intrinsic/Syntax.lean` | `Config` | structure | adapt | `GameTheory.Languages.Intrinsic.Config` | D31 / EXP-062; focused build | Native product configuration retained without the source's stored capabilities. |
| same | `<anonymous@58>` | instance | retired | no successor | D31 / EXP-062 | Source `Fintype` configuration instance contradicts the capability-light root; consumers supply finiteness locally. |
| same | `WModel` | structure | adapt | `GameTheory.Languages.Intrinsic.Model` | D31 / EXP-062; focused build | Renamed native model retains only agents, nature, decisions, and information setoids. |
| same | `WModel.H` | abbrev | adapt | `GameTheory.Languages.Intrinsic.Model.Configuration` | D31 / EXP-062; focused build | The complete configuration space is retained as a transparent model-owned abbreviation. |
| same | `OutcomeLaw` | abbrev | deferred | D31 outcome-law / PMF gate | D31 | Probability outcomes remain outside the approved native root. |
| same | `PureStrategy` | structure | adapt | `GameTheory.Languages.Intrinsic.Model.PureStrategy` | D31 / EXP-062; focused build | Information-local decision rule over the canonical configuration space. |
| same | `PureProfile` | abbrev | adapt | `GameTheory.Languages.Intrinsic.Model.PureProfile` | D31 / EXP-062; focused build | Canonical family of intrinsic pure strategies. |
| same | `isFixedPoint` | def | adapt | `GameTheory.Languages.Intrinsic.Model.IsFixedPoint` | D31 / EXP-062; focused build | Closed-loop equations are retained with explicit model ownership. |
| same | `Solvable` | def | adapt | `GameTheory.Languages.Intrinsic.Model.IsSolvable` | D31 / EXP-062; focused build | Unique fixed-point solvability is retained without a solution-extraction operation. |
| same | `solutionMap` | def | deferred | D31 solution-selection theorem gate | D31 | Derivable from `IsSolvable` by choice with no added model capability; deferred only to keep the first promoted surface minimal until a consumer needs selection. |
| same | `solutionMap_spec` | theorem | deferred | D31 solution-selection theorem gate | D31 | Reopen with the derived `solutionMap`; no additional nonemptiness premise is required beyond `IsSolvable` and the supplied profile/nature. |
| same | `solutionMap_unique` | theorem | deferred | D31 solution-selection theorem gate | D31 | Reopen with the derived `solutionMap` and its uniqueness consequence. |
| same | `TotalOrdering` | def | adapt | `GameTheory.Languages.Intrinsic.Model.Schedule` | D31 / EXP-062; focused build | Explicit slots and equivalences replace the source list ordering. |
| same | `ConfigOrdering` | def | adapt | `GameTheory.Languages.Intrinsic.Model.Schedule` | D31 / EXP-062; focused build | The schedule is configuration-dependent at the required semantic layer. |
| same | `OrderingPrefix` | def | retired | no successor | D31 / EXP-062 | Source list-prefix intermediary is replaced by direct `SamePrefixThrough`. |
| same | `predecessors` | def | retired | no successor | D31 / EXP-062 | Source list predecessor set is replaced by the slot-bounded `AgreeBefore` predicate. |
| same | `last` | def | retired | no successor | D31 / EXP-062 | Source list-last helper is an implementation detail of the retired ordering encoding. |
| same | `configSet` | def | adapt | `GameTheory.Languages.Intrinsic.Model.PrefixCell` | D31 / EXP-062; focused build | Configuration-prefix membership is retained directly for explicit schedules. |
| same | `agreeOnSubset` | def | adapt | `GameTheory.Languages.Intrinsic.Model.AgreeBefore` | D31 / EXP-062; focused build | Nature and predecessor-decision agreement is stated at the causal slot. |
| same | `coordinateAgreeSetoid` | def | retired | no successor | D31 / EXP-062 | Coordinate-setoid intermediary is not public API; direct causality carries the needed relation. |
| same | `CausalWith` | def | adapt | `GameTheory.Languages.Intrinsic.Model.IsCausalWith` | D31 / EXP-062; focused build | Causality retains both independently necessary schedule-prefix and predecessor premises. |
| same | `WGame` | structure | deferred | D31 ownership / outcome-preference gate | D31 | Player ownership and preferences over outcome laws were excluded from the native root; temporal compilation is a separate gate. |
| same | `WGame.agents` | def | deferred | D31 player-ownership gate | D31 | Reopen only with the `WGame` ownership layer. |
| same | `EUWGame` | structure | deferred | D31 ownership / prior / utility gate | D31 | Player ownership, probability, and utility remain separately gated. |
| same | `EUWGame.configLaw` | def | deferred | D31 outcome-law / PMF gate | D31 | Probability law is not present in the approved root. |
| same | `EUWGame.expectedUtilityLaw` | def | deferred | D31 utility / equilibrium gate | D31 | Expected utility is not present in the approved root. |
| same | `EUWGame.toWGame` | def | deferred | D31 ownership / outcome-preference / utility gate | D31 | Reopen after ownership, outcome-law preference, prior, and utility contracts; temporal compilation remains independent. |
| `GameTheory/Languages/Intrinsic/Tests.lean` | `alwaysHeads` | def | unreviewed | review required | generated index seed only | public, pinned line 31 |
| same | `mkSigConfig` | def | unreviewed | review required | generated index seed only | public, pinned line 51 |
| same | `matchingPenniesOrdering` | def | unreviewed | review required | generated index seed only | public, pinned line 80 |
| same | `oneAgentModel` | def | unreviewed | review required | generated index seed only | public, pinned line 99 |
| same | `oneAgentGame` | def | unreviewed | review required | generated index seed only | public, pinned line 107 |
| same | `oneAgentOrdering` | def | unreviewed | review required | generated index seed only | public, pinned line 115 |
| same | `futureLookingModel` | def | unreviewed | review required | generated index seed only | public, pinned line 148 |
| same | `futureLookingOrdering` | def | unreviewed | review required | generated index seed only | public, pinned line 159 |
| `GameTheory/Languages/Intrinsic/Theorems.lean` | `solutionMap_isFixedPoint` | theorem | unreviewed | review required | generated index seed only | public, pinned line 24 |
| same | `solutionMap_ext` | theorem | unreviewed | review required | generated index seed only | public, pinned line 30 |
| same | `liftProfile_apply` | theorem | unreviewed | review required | generated index seed only | public, pinned line 46 |
| same | `productMixedToBehavioral_meas` | theorem | unreviewed | review required | generated index seed only | public, pinned line 52 |

Before this ledger can become complete, each row must be reviewed against
the canonical successor API and assigned an allowed non-`unreviewed`
disposition with concrete build, theorem, decision, or counterexample
evidence. Generated name similarity is never sufficient.
