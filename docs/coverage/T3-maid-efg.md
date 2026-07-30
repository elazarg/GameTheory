# T3: MAID to EFG transfer

Title: General finite MAID evaluation and strategy-preserving EFG translation
Family ID: T3
Pinned roots: all declarations in
`GameTheory/Languages/Bridges/MAID_EFG.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `2b659df`
Canonical destination: `GameTheory.Languages.MAID` and its named EFG compiler
Domain contract / decision: D0, D6, D7, D14; post-architecture gate W1-F
Owner: Wave 1 / MAID transfer
Status: complete for frozen T3; non-flagship bridge recovery remains in L-MAID
Last verified: 2026-07-30

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Languages/Bridges/MAID_EFG.lean` | `maidInfoS` | definition | adapt | D14 general information-local MAID model | EXP-037 | Preserve decision-site information, not the predecessor's observation encoding. |
| same | `buildTree` | definition | adapt | T3 `toEFGAt` | D14 | The successor may serialize a frontier only after its direct frontier law is fixed. |
| same | `maidToEFGAt` | definition | adapt | T3 explicit-order EFG compiler | Phase 0 T3 | Required source-to-target object. |
| same | `maidToEFG` | definition | adapt | T3 order-free wrapper | Phase 0 T3 | Choice of order must be observationally irrelevant by theorem. |
| same | `maidToEFGWithOrder` | definition | subsumed | T3 `toEFGAt` | source inspection | Duplicate explicit-order spelling. |
| same | `maidInfoS_actEquiv` | definition | adapt | T3 local-action equivalence | source inspection | Retain the typed action correspondence, not predecessor casts. |
| same | `toEFGProfile` | definition | adapt | T3 behavioral profile forward map | Phase 0 T3 | Strategy correspondence is part of the frozen transfer. |
| same | `fromEFGProfile` | definition | adapt | T3 behavioral profile inverse map | Phase 0 T3 | Must exclude target strategies that see serialized incomparable actions. |
| same | `toFrom` | theorem | adapt | T3 behavioral left inverse | source inspection | Needed for a real strategy equivalence. |
| same | `fromTo` | theorem | adapt | T3 behavioral right inverse | source inspection | Needed for a real strategy equivalence. |
| same | `policyBehavioralEquiv` | definition | adapt | T3 behavioral profile equivalence | Phase 0 T3 | Public only if both inverse laws survive without transport. |
| same | `toEFGPureProfile` | definition | adapt | T3 pure profile forward map | source inspection | Required by the pure strategic transfer. |
| same | `fromEFGPureProfile` | definition | adapt | T3 pure profile inverse map | source inspection | Required by the pure strategic transfer. |
| same | `purePolicyEquiv` | definition | adapt | T3 pure profile equivalence | Phase 0 T3 | Keep as a transparent equivalence if earned. |
| same | `pureToBehavioral_toEFGPureProfile` | theorem | adapt | T3 pure/behavioral compatibility | source inspection | The two strategy maps must commute. |
| same | `pureStrategyEquivPlayer` | definition | adapt | T3 playerwise strategy equivalence | source inspection | Needed to state unilateral-deviation preservation. |
| same | `evalStep_pure` | private theorem | retired | T3 evaluation proof | implementation detail | No private proof-name compatibility. |
| same | `evalStep_bind` | theorem | subsumed | `Probability.FinDist` bind laws | D2 | General finite-law algebra already has the needed monad laws. |
| same | `foldl_evalStep_bind` | theorem | adapt | T3 serialized evaluation lemma | source inspection | Retain only if the explicit-order proof needs it. |
| same | `buildTree_evalDist` | theorem | adapt | T3 EFG run/evaluation equality | Phase 0 T3 | Core bridge lemma. |
| same | `maid_efg_evalDist_withOrder` | theorem | adapt | T3 explicit-order outcome law | Phase 0 T3 | Core bridge lemma. |
| same | `OrderSwapStep` | definition | retired | D14 frontier law | EXP-037 | Do not expose an implementation-specific order-rewrite relation. |
| same | `OrderSwapReachable` | abbreviation | retired | D14 frontier law | EXP-037 | Same reason. |
| same | `evalFold_swap_adj_any_order` | theorem | adapt | T3 order-independence theorem | D14 | Mathematical payload survives; statement should not expose the old evaluator. |
| same | `evalFold_orderSwapReachable` | theorem | retired | T3 order-independence theorem | D14 | Transitive bookkeeping is subsumed by the direct named law. |
| same | `maid_efg_evalDist_orderSwapReachable` | theorem | retired | T3 order-independence theorem | D14 | Intermediate bridge bookkeeping. |
| same | `maid_efg_evalDist_fold_at` | theorem | adapt | T3 explicit-order outcome law | Phase 0 T3 | Preserve only the direct evaluator/EFG equality. |
| same | `maid_efg_evalDist_at` | theorem | adapt | T3 explicit-order outcome law | Phase 0 T3 | Preserve the direct public form. |
| same | `buildTree_pol_irrel` | private theorem | retired | T3 compiler construction | D7 | Seed-policy irrelevance is an artifact of the old tree builder. |
| same | `maidToEFGAt_pol_irrel` | theorem | retired | T3 compiler construction | D7 | The successor compiler must not take irrelevant policy data. |
| same | `maidToEFGAt_outcomeKernel` | theorem | adapt | `FrontierEquivalence.nativeRun_eq_compiledBehavioralRun` | EXP-041/T3 | Exact arbitrary typed-DAG native/actual-compiled behavioral assignment law. |
| same | `maidToEFGAt_pure_outcomeKernel` | theorem | adapt | T3 pure outcome-law equality | frozen T3 | Keep the pure specialization if it is shorter than re-specializing at use sites. |
| same | `maidToEFGAt_pure_bisimulation` | definition | retired | direct named pure law | D7 | Generic certificate wrappers were rejected. |
| same | `maidToEFGAt_udist` | theorem | subsumed | `nativeRun_eq_compiledBehavioralRun` plus finite-law mapping | EXP-041/T3 | Utility remains external to both syntax and execution. |
| same | `maidToEFGAt_bisimulation` | definition | retired | direct named laws | D7 | Twenty-line certificate wrapper bought no extra theorem. |
| same | `maidToEFGAt_simulation` | definition | retired | direct named laws | D7 | Same certificate-hierarchy rejection. |
| same | `maidToEFGAt_morphism` | definition | retired | direct named laws | D7 | Same certificate-hierarchy rejection. |
| same | `buildTree_obs_stable` | private theorem | retired | T3 information proof | implementation detail | Preserve the fact, not the private name. |
| same | `buildTree_decNode_mem` | private theorem | retired | T3 information proof | implementation detail | Preserve the fact, not the private name. |
| same | `buildTree_reach_decision_unique` | private theorem | retired | T3 information proof | implementation detail | Preserve the fact, not the private name. |
| same | `buildTree_isPerfectInfo_of_pairwise_observation` | theorem | adapt | T3 perfect-information criterion | source inspection | Recover after the base outcome and strategy laws. |
| same | `buildTree_playerHistory_eq` | private theorem | retired | T3 recall proof | implementation detail | Preserve the fact, not the private name. |
| same | `buildTree_perfectRecall` | theorem | adapt | T3 perfect-recall transfer | W1-G and D14 | Must target the accepted `InformationModel.PerfectRecall`. |
| same | `kuhn_behavioral_to_mixed_udist_at` | theorem | subsumed | `Languages.EFG.kuhn_behavioral_to_mixed_expectedUtility` | W1-G | The generic EFG theorem applies after recall transfer. |
| same | `kuhn_mixed_to_behavioral_udist_at` | theorem | subsumed | `Languages.EFG.kuhn_mixed_to_behavioral_expectedUtility` | W1-G | The generic EFG theorem applies after recall transfer. |
| same | `maidToEFGAt_order_bisimulation` | definition | retired | T3 order-independence law | D7 | Do not package equality through a certificate layer. |
| same | `maidToEFG_bisimulation` | definition | retired | direct named laws | D7 | Order-free certificate wrapper. |
| same | `maidToEFG_pure_bisimulation` | definition | retired | direct named pure law | D7 | Order-free certificate wrapper. |
| same | `maidToEFG_udist` | theorem | adapt | T3 order-free expected-utility equality | frozen T3 | Public order-free theorem. |
| same | `maidToEFG_perfectRecall` | theorem | adapt | T3 order-free perfect-recall transfer | W1-G and D14 | Required before reusing the generic EFG Kuhn surface. |
| same | `kuhn_behavioral_to_mixed_udist` | theorem | subsumed | generic EFG Kuhn theorem after T3 recall | W1-G | No MAID-specific duplicate proof. |
| same | `kuhn_mixed_to_behavioral_udist` | theorem | subsumed | generic EFG Kuhn theorem after T3 recall | W1-G | No MAID-specific duplicate proof. |

The pinned bridge has 52 declarations: 27 are targeted for adaptation, 7 are
subsumed by accepted generic laws, and 18 are retired as duplicate spellings,
private implementation details, or D7 certificate wrappers. No row is
`unreviewed`. The frozen outcome, utility, strategy, and equilibrium transfer
is complete; remaining non-flagship `adapt` rows belong to broad L-MAID
recovery and do not reopen T3.

The source contains no named Nash-equilibrium iff theorem despite D0 freezing
an outcome, utility, and equilibrium transfer. T3 therefore has one explicit
successor-only obligation: after the profile equivalence and outcome law are
proved, expose pure and behavioral unilateral-deviation/Nash preservation using
the one canonical equilibrium predicate. A bisimulation record is not credit.

EXP-037 passed the first execution gate; EXP-038 then refuted a combined view
for same-owner incomparable decisions. EXP-040/041 supply the general typed
frontier evaluator, site-local explicit-order compiler, order independence,
and exact actual-runner law. `Strategic.ownerPolicyEquiv` regroups target
policies by source owner, `behavioralProfileEquiv_update` preserves unilateral
replacement at that coordinate, and `isNash_native_iff_compiled` proves the
canonical Nash equivalence. The full build and Phase 2/3 audits pass, and the
flagship declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
