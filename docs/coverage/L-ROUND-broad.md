# L-ROUND: canonical multi-round monitoring and compiler inventory

Title: Canonical multi-round monitoring, previous-action recall, and imperfect monitoring
Family ID: L-ROUND
Pinned roots: `GameTheory/Languages/MultiRound/AbsentMindedDriver.lean`; `GameTheory/Languages/MultiRound/Compile.lean`; `GameTheory/Languages/MultiRound/CompileObs.lean`; `GameTheory/Languages/MultiRound/CompileObsLin.lean`; `GameTheory/Languages/MultiRound/CompileObsLinAdequacy.lean`; `GameTheory/Languages/MultiRound/CompileObsLinRecall.lean`; `GameTheory/Languages/MultiRound/Kuhn.lean`; `GameTheory/Languages/MultiRound/RepeatedGame.lean`; `GameTheory/Languages/MultiRound/SOS.lean`; `GameTheory/Languages/MultiRound/StochasticGame.lean`; `GameTheory/Languages/MultiRound/Syntax.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `e0a1471`
Canonical destination: `GameTheory.Languages.MultiRound`, Protocol/FOSG, `GameTheory.Repeated`, and `GameTheory.Stochastic`
Domain contract / decision: D6, EXP-014, EXP-070, D37
Owner: Wave 3 / multi-round
Status: partial; all 233 declarations classified, the monitoring/previous-action gate is promoted, and absent-minded, finite-information Kuhn, and generic stagewise-Nash breadth is deferred
Last verified: 2026-08-09

The successor keeps one execution and information semantics. A thin monitoring
constructor records realized joint actions in hidden state while exposing only
the player's own choices and public/private signals to policies. It proves
canonical perfect recall and compiles directly through FOSG/Protocol. The large
predecessor serialization and adequacy stack is retired rather than ported; its
substantive repeated-game theorems are already recovered in the dedicated
Repeated root, while three bounded theorem queues remain explicit.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Languages/MultiRound/AbsentMindedDriver.lean` | `AMDState` | inductive | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `AMDView` | inductive | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `AMDAction` | inductive | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `absentMindedRound₁` | def | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `absentMindedRound₂` | def | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `absentMindedProtocol` | def | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `absentMindedProtocol_not_viewDeterminesRound` | theorem | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `absentMindedPayoff` | def | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `exAnteValue` | def | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `exAnteValue_eq_path_sum` | theorem | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `exAnteOptimalContinue` | def | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `exAnteValue_le_optimal` | theorem | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `exAnteValue_lt_optimal` | theorem | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `exAnteValue_optimal_value` | theorem | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `decisionValue` | def | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `decisionOptimalContinue` | def | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `decisionValue_le_optimal` | theorem | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `decisionValue_lt_optimal` | theorem | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `decisionOptimalContinue_at_exAnteOptimal` | theorem | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `exAnteOptimalContinue_ne_decisionOptimal` | theorem | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `decisionValue_at_exAnte_and_decisionOptimal` | theorem | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `decisionValue_at_exAnte_and_exAnteOptimal` | theorem | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| same | `decisionValue_exAnteOptimal_lt_decisionOptimal` | theorem | deferred | L-ROUND absent-minded-driver BFS gate | D37 named continuation | The puzzle and value comparison remain useful breadth after the monitoring owner is stable. |
| `GameTheory/Languages/MultiRound/Compile.lean` | `PreKernelStep` | structure | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `Policy` | abbrev | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `jointActDist` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `stepKernel` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `StepwiseGame` | structure | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `runDist` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `runDist_zero` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `toKernelGame` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `toKernelGame_outcomeKernel` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `pmfPi_pure` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `constPurePolicy` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `stepKernel_constPure` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `KernelGame.toOneStepStepwise` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `KernelGame.toOneStepStepwise_runDist_constPure` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `KernelGame.toOneStepStepwise_morphism` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `compileInfoOn` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `compile_step_iff` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `compile_reach_iff` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `compile_observe_eq_observe` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `compile_publicView_eq_publicPhase` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `nativeInfoBisimulation` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| `GameTheory/Languages/MultiRound/CompileObs.lean` | `configStepPMF` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `compileObsModel` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `pure_ne_zero_iff` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `compileObsModel_step_consistent` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `configStepPMF_mass_invariant` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `compileObsModelCore` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `compiledCoreObs` | abbrev | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| `GameTheory/Languages/MultiRound/CompileObsLin.lean` | `LinConfig` | inductive | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `linInitialConfig` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `RoundView` | abbrev | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `linObserve` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `LinAct` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `linActFintype` | instance | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `linActNonempty` | instance | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `advancePlayerTurn` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `extractPlayerAction` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `linConfigStepPMF` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `compileObsModelCoreLin` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `compiledLinObs` | abbrev | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `compiledLinObs_infoState_fintype` | instance | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `compiledLinObs_infoState_decidableEq` | instance | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `compiledLinObs_localStrategy_fintype` | instance | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `linObserve_ne_acting` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `pure_ne_zero_iff'` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `advancePlayerTurn_mass_invariant` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `advancePlayerTurn_accActs_eq` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `linConfigStepPMF_mass_invariant` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `stepMassInvariant_compiledLin` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `extractPlayerAction_congr` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `linConfigStepPMF_playerTurn_congr` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `linAct_eq_punit_of_ne` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `cast_dep_apply` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `pureStep_compiledLin_eq` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `pureStep_congr_compiledLin` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `stepSupportFactorization_compiledLin` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `getElem_concat_left` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `pureRun_update_eq_of_obs_agree` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `lastState_take_eq_getElem` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `pureRun_update_nonzero_agree` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `viewRound` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `viewRound_eq` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `liftLocalStrategy` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `liftPureProfile` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `descendLocalStrategy` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `descendPureProfile` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `descendLocalStrategy_liftLocalStrategy` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `descendPureProfile_liftPureProfile` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `liftBehavioralStrategy` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `liftBehavioralProfile` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `descendBehavioralProfile` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `descendBehavioralProfile_liftBehavioralProfile` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `descendBehavioralProfileVRD` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `descendBehavioralProfileVRD_liftBehavioralProfile` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `liftMixedProfile` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `liftMixedProfile_joint` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| `GameTheory/Languages/MultiRound/CompileObsLinAdequacy.lean` | `LinConfig.state` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `evalLinearized` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `pmf_foldl_bind` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `evalRounds_cons` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `pmf_foldl_bind_mixed` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `evalRoundsMixed_cons` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `evalLinearized_eq_evalRounds` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `evalLinearized_eq_eval` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `resolveActions` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `resolveActions_spec` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `resolveActions_eq` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `evalFromCfg` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `evalFromCfg_init` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `extractPlayerAction_lift` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `stepPMF_bind_evalFromCfg` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `lastState_snoc` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `runDistPure_bind_evalFromCfg` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `LinConfig.isDone` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `LinConfig.phase` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `evalFromCfg_of_isDone` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `isDone_of_phase_ge` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `phase_init_le` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `isDone_step_of_isDone` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `phase_step_progress` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `PMF.bind_congr_support` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `isDone_of_reachable` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `runDistPure_eq_eval` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `resolveActionsMixed` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `resolveActionsMixed_gen` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `resolveActionsMixed_eq_pmfPi` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `evalFromCfgMixed` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `evalFromCfgMixed_init` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `evalFromCfgMixed_of_isDone` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `stepDist_support_subset_step_support` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `isDone_of_reachable_behavioral` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `stepDist_liftBehavioral_bind_evalFromCfgMixed` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Private adequacy or serialization proof machinery. |
| same | `runDist_liftBehavioral_bind_evalFromCfgMixed` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `runDist_liftBehavioral_extractState_eq_evalMixed` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| `GameTheory/Languages/MultiRound/CompileObsLinRecall.lean` | `linObserve_some_playerTurn` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Compiler-specific recall/transport replaced by canonical information-local semantics. |
| same | `not_isDone_of_linObserve_some` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Private proof machinery for turn serialization. |
| same | `phase_of_linObserve_some` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Private proof machinery for turn serialization. |
| same | `not_isDone_of_later_not_isDone` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Private proof machinery for turn serialization. |
| same | `phase_strict_mono_of_not_done` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Private proof machinery for turn serialization. |
| same | `phase_eq_index` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Private proof machinery for turn serialization. |
| same | `linObserve_of_phase_eq` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Private proof machinery for turn serialization. |
| same | `earlier_i_step_exists` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Private proof machinery for turn serialization. |
| same | `unique_i_step_position` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Private proof machinery for turn serialization. |
| same | `round_lt_of_earlier_step` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Private proof machinery for turn serialization. |
| same | `fullRecall_view_action_match` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Private proof machinery for turn serialization. |
| same | `projectStates_eq_lastObs` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Compiler-specific recall/transport replaced by canonical information-local semantics. |
| same | `obsLocalFeasibility_of_fullRecall` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Compiler-specific recall/transport replaced by canonical information-local semantics. |
| same | `noNontrivialInfoStateRepeat_compiledLin` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Compiler-specific recall/transport replaced by canonical information-local semantics. |
| same | `liftBehavioralProfile_descendVRD_agree` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Compiler-specific recall/transport replaced by canonical information-local semantics. |
| same | `descendLocalStrategyVRD` | def | retired | D37 linearized-compiler retirement | D37 owner comparison | Compiler-specific recall/transport replaced by canonical information-local semantics. |
| same | `descendPureProfileVRD` | def | retired | D37 linearized-compiler retirement | D37 owner comparison | Compiler-specific recall/transport replaced by canonical information-local semantics. |
| same | `liftPureProfile_descendVRD_agree` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Compiler-specific recall/transport replaced by canonical information-local semantics. |
| `GameTheory/Languages/MultiRound/Kuhn.lean` | `compiledCoreObs'` | abbrev | retired | D37 linearized-compiler retirement | D37 owner comparison | Artifact of the predecessor second compiler or private projection machinery. |
| same | `kuhn_behavioral_to_mixed_core` | theorem | deferred | L-ROUND finite-information Kuhn BFS gate | D37 named continuation | Protocol owns the correspondence and monitoring supplies recall; finite reachable information is still needed for behavioral-to-mixed. |
| same | `stepMassInvariant_compiledCore` | theorem | retired | D37 linearized-compiler retirement | D37 owner comparison | Artifact of the predecessor second compiler or private projection machinery. |
| same | `compiledLinObs'` | abbrev | retired | D37 linearized-compiler retirement | D37 owner comparison | Artifact of the predecessor second compiler or private projection machinery. |
| same | `kuhn_mixed_to_behavioral_compiledLin` | theorem | deferred | L-ROUND finite-information Kuhn BFS gate | D37 named continuation | Protocol owns the correspondence and monitoring supplies recall; finite reachable information is still needed for behavioral-to-mixed. |
| same | `actionPosteriorLocal_of_fullRecall` | theorem | deferred | L-ROUND finite-information Kuhn BFS gate | D37 named continuation | Protocol owns the correspondence and monitoring supplies recall; finite reachable information is still needed for behavioral-to-mixed. |
| same | `kuhn_mixed_to_behavioral_fullRecall` | theorem | deferred | L-ROUND finite-information Kuhn BFS gate | D37 named continuation | Protocol owns the correspondence and monitoring supplies recall; finite reachable information is still needed for behavioral-to-mixed. |
| same | `extractState` | def | retired | D37 linearized-compiler retirement | D37 owner comparison | Artifact of the predecessor second compiler or private projection machinery. |
| same | `kuhn_mixed_to_behavioral_native` | theorem | deferred | L-ROUND finite-information Kuhn BFS gate | D37 named continuation | Protocol owns the correspondence and monitoring supplies recall; finite reachable information is still needed for behavioral-to-mixed. |
| same | `kuhn_mixed_to_behavioral_sequential` | theorem | deferred | L-ROUND finite-information Kuhn BFS gate | D37 named continuation | Protocol owns the correspondence and monitoring supplies recall; finite reachable information is still needed for behavioral-to-mixed. |
| same | `kuhn_behavioral_to_mixed_compiledLin` | theorem | deferred | L-ROUND finite-information Kuhn BFS gate | D37 named continuation | Protocol owns the correspondence and monitoring supplies recall; finite reachable information is still needed for behavioral-to-mixed. |
| same | `kuhn_behavioral_to_mixed_sequential` | theorem | deferred | L-ROUND finite-information Kuhn BFS gate | D37 named continuation | Protocol owns the correspondence and monitoring supplies recall; finite reachable information is still needed for behavioral-to-mixed. |
| `GameTheory/Languages/MultiRound/RepeatedGame.lean` | `RepeatedGame` | structure | adapt | `GameTheory.UtilityGame` | focused successor review | The successor starts from the canonical utility game instead of rebundling its action and payoff data. |
| same | `stageKernelGame` | abbrev | retired | D37 kernel-wrapper retirement | focused successor review | The predecessor-only `KernelGame` wrapper is not part of the greenfield API. |
| same | `History` | abbrev | adapt | `UtilityGame.ProfileHistory` | focused successor review | Canonical chronological stage-profile history. |
| same | `Strategy` | abbrev | adapt | `UtilityGame.RepeatedStrategy` | focused successor review | Canonical history-dependent repeated strategy. |
| same | `RProfile` | abbrev | adapt | `UtilityGame.RepeatedProfile` | focused successor review | Canonical signature-bound repeated profile. |
| same | `roundPayoff` | def | adapt | `UtilityGame.stagePayoff` | focused successor review | The successor also handles stochastic stage forms through expected utility. |
| same | `play` | abbrev | adapt | `UtilityGame.repeatedPlay` | focused successor review | One canonical generated stage path. |
| same | `constStrategy` | abbrev | adapt | `UtilityGame.stationaryRepeatedProfile` | focused successor review | Greenfield stationary-profile name. |
| same | `discountedPayoff` | abbrev | adapt | `UtilityGame.discountedPayoff` | focused successor review | Canonical normalized discounted payoff. |
| same | `discountedKernelGame` | abbrev | adapt | `UtilityGame.repeatedForm` plus `discountedUtility` | focused successor review | Equilibrium remains ordinary `IsNash`; no repeated-specific game wrapper. |
| same | `play_constStrategy` | theorem | subsumed | `UtilityGame.repeatedPlay_stationaryRepeatedProfile` | existing theorem builds | Exact stationary-path law. |
| same | `play_update_constStrategy` | theorem | subsumed | `UtilityGame.repeatedPlay_update_stationaryRepeatedProfile` | existing theorem builds | Uses canonical `Profile.update`. |
| same | `summable_discounted_stageUtil_of_abs_bound` | theorem | subsumed | `UtilityGame.summable_discounted_stagePayoff_of_abs_bound` | existing theorem builds | The successor theorem is stated over expected stage payoff. |
| same | `discountedPayoff_le_of_forall_stageUtil_le` | theorem | subsumed | `UtilityGame.discountedPayoff_le_of_forall_stagePayoff_le` | existing theorem builds | Exact pointwise-to-discounted comparison spine. |
| same | `discountedPayoff_constStrategy` | theorem | subsumed | `UtilityGame.discountedPayoff_stationaryRepeatedProfile` | existing theorem builds | Exact normalized stationary-payoff result. |
| same | `constStrategy_isDiscountedNash` | theorem | subsumed | `UtilityGame.stationaryRepeatedProfile_isNash_of_isNash_of_bounded` | existing theorem builds | Ordinary canonical Nash replaces the predecessor method. |
| `GameTheory/Languages/MultiRound/SOS.lean` | `JointSignal` | abbrev | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `JointControl` | abbrev | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `Config` | inductive | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `state` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `round?` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `initialConfig` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `Step` | inductive | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `ReachBy` | abbrev | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `PublicPhase` | inductive | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `publicPhase` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `observe` | def | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `observe_signal` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `observe_terminal` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `publicPhase_signal` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `publicPhase_action` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| same | `publicPhase_terminal` | theorem | retired | D37 duplicate compiler/evaluator retirement | D37 owner comparison | Predecessor operational/serialization surface; Protocol is the sole runner and compiler. |
| `GameTheory/Languages/MultiRound/StochasticGame.lean` | `StochasticGame` | structure | adapt | `GameTheory.Stochastic.Game` | EXP-050/D22 owner validation | The native successor removes stored discount and uses `FinDist`. |
| same | `MarkovStrategy` | abbrev | deferred | L-ROUND generic stagewise-Nash BFS gate | D37 named continuation | The stochastic branch is stronger on discounted zero-sum values but lacks this generic myopic surface. |
| same | `MarkovProfile` | abbrev | deferred | L-ROUND generic stagewise-Nash BFS gate | D37 named continuation | The stochastic branch is stronger on discounted zero-sum values but lacks this generic myopic surface. |
| same | `stageEU` | def | deferred | L-ROUND generic stagewise-Nash BFS gate | D37 named continuation | The stochastic branch is stronger on discounted zero-sum values but lacks this generic myopic surface. |
| same | `IsStagewiseNash` | def | deferred | L-ROUND generic stagewise-Nash BFS gate | D37 named continuation | The stochastic branch is stronger on discounted zero-sum values but lacks this generic myopic surface. |
| same | `stageKernelGame` | def | deferred | L-ROUND generic stagewise-Nash BFS gate | D37 named continuation | The stochastic branch is stronger on discounted zero-sum values but lacks this generic myopic surface. |
| same | `isStagewiseNash_iff_all_stage_nash` | theorem | deferred | L-ROUND generic stagewise-Nash BFS gate | D37 named continuation | The stochastic branch is stronger on discounted zero-sum values but lacks this generic myopic surface. |
| `GameTheory/Languages/MultiRound/Syntax.lean` | `Round` | structure | adapt | `MonitoringGame.signalLaw` | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `MultiRoundGame` | structure | adapt | `GameTheory.Languages.MultiRound.MonitoringGame` | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `PureStrategy` | abbrev | adapt | `InformationModel.Policy` | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `PureProfile` | abbrev | adapt | `Profile` of the canonical information signature | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `BehavioralStrategy` | abbrev | adapt | `InformationModel.BehavioralPolicy` | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `BehavioralProfile` | abbrev | adapt | `Profile` of the canonical behavioral signature | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `Round.eval` | def | retired | D37 duplicate-semantics retirement | D37 owner comparison | Predecessor evaluator or obsolete wrapper, not independent mathematics. |
| same | `Round.evalMixed` | def | retired | D37 duplicate-semantics retirement | D37 owner comparison | Predecessor evaluator or obsolete wrapper, not independent mathematics. |
| same | `evalRounds` | def | retired | D37 duplicate-semantics retirement | D37 owner comparison | Predecessor evaluator or obsolete wrapper, not independent mathematics. |
| same | `MultiRoundGame.eval` | def | retired | D37 duplicate-semantics retirement | D37 owner comparison | Predecessor evaluator or obsolete wrapper, not independent mathematics. |
| same | `evalRoundsMixed` | def | retired | D37 duplicate-semantics retirement | D37 owner comparison | Predecessor evaluator or obsolete wrapper, not independent mathematics. |
| same | `MultiRoundGame.evalMixed` | def | retired | D37 duplicate-semantics retirement | D37 owner comparison | Predecessor evaluator or obsolete wrapper, not independent mathematics. |
| same | `PureStrategy.toBehavioral` | def | adapt | `InformationModel.Policy.toBehavioral` | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `PureProfile.toBehavioral` | def | adapt | the pointwise canonical `Policy.toBehavioral` map | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `PureStrategy.toBehavioral_apply` | theorem | adapt | `InformationModel.Policy.toBehavioral` | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `PureProfile.toBehavioral_apply` | theorem | adapt | the pointwise canonical `Policy.toBehavioral` map | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `RoundRecord` | structure | adapt | `MonitoringGame.RoundRecord` | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `Round.playerView` | def | adapt | `MonitoringGame.InformationState` through `InfoSignals.infoOf` | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `ExecRecord` | structure | adapt | `ExecutionProtocol.History` and `MonitoringGame.InformationState` | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `ExecRecord.toRound` | def | adapt | canonical `ExecutionProtocol.History` projections | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `MultiRoundGame.PerfectRecall` | def | adapt | `InfoSignals.PerfectRecall` and `MonitoringGame.perfectRecall` | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `MultiRoundGame.FullRecall` | def | retired | D37 duplicate-semantics retirement | D37 owner comparison | Predecessor evaluator or obsolete wrapper, not independent mathematics. |
| same | `MultiRoundGame.FullRecall.toPerfectRecall` | theorem | retired | D37 duplicate-semantics retirement | D37 owner comparison | Predecessor evaluator or obsolete wrapper, not independent mathematics. |
| same | `MultiRoundGame.ViewDeterminesRound` | def | adapt | `InformationModel.ActsOnceWhereItMatters` | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `MultiRoundGame.toGameForm` | def | adapt | `MonitoringGame.toGameForm` | EXP-070 focused build | The successor uses canonical Protocol/FOSG semantics and no parallel evaluator. |
| same | `MultiRoundGame.toKernelGame` | def | retired | D37 duplicate-semantics retirement | D37 owner comparison | Predecessor evaluator or obsolete wrapper, not independent mathematics. |
| same | `MultiRoundGame.toKernelGame_toGameForm` | theorem | retired | D37 duplicate-semantics retirement | D37 owner comparison | Predecessor evaluator or obsolete wrapper, not independent mathematics. |

Attribution: the pinned predecessor supplied the previous-action requirement,
the imperfect-monitoring stress case, and the proofs identifying which compiler
properties mattered. The successor reuses those requirements while replacing
the predecessor's Round.eval/linearization stack with the already accepted
Protocol runner, information model, behavioral/mixed machinery, and static form.

Validation:

```text
lake build GameTheory.Languages.MultiRound GameTheory.Tests.MultiRoundMonitoring
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
lake build
git diff --check
```

The hostile fixture has two players, two rounds, and three actions. Distinct
hidden histories with opponent actions one and two induce identical local
information after player zero chooses zero and receives the same coarse
disagreement signal. Changing player zero's own action changes its information;
a second-round policy branches on that memory, and the canonical joint-action
and strategic-form runner expose the same branch.
