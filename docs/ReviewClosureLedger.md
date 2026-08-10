# Review closure ledger

This ledger records the disposition of the repository-wide review completed
in August 2026.  It is successor-native: evidence names current public modules,
tests, decisions, and delivery rows.  It does not treat declaration ancestry
or an archived implementation as part of the public API.

Status meanings:

- **closed**: the defect was corrected, removed, or falsified by current
  evidence;
- **retained**: inspection showed that the reported shape is intentional and
  already has a live consumer or a necessary type-level role; and
- **queued**: the observation is a real theorem-family extension, not a defect
  in the supported claim.  It is named in `DeliveryLedger.md` or
  `PostArchitectureDeliveryPlan.md` and remains explicitly unsupported.

No reviewed item is left without a disposition.

## Follow-up full-library review

The August 10 follow-up review was checked against the working tree rather
than accepted as an authority.  Its verified findings have the following
current dispositions; the original HTML artifact is not retained as project
documentation.

| ID | Finding | Status | Current disposition and evidence |
|---|---|---|---|
| R2-A1 | Finite-horizon one-shot optimality quantified fuel independently of history depth. | closed | EXP-077 couples trace depth and remaining fuel, preserves arbitrary-policy/Nash transfer, and `Tests.Assessment` checks a stopping branch, both valid decision depths, both invalid swapped fuels, and early absorption. |
| R2-A2 | Execution said terminal activity was immaterial while information-menu adequacy made it observable. | closed | `Execution`, `Information`, and `Zermelo` now state the exact split: the runner does not act after termination, but `menu_adequate` ranges over terminal traces and therefore constrains terminal activity at shared information values. |
| R2-A3 | Normalized reach mass was called Bayes conditioning without excluding nested histories in one information fiber. | closed | `DecisionInformationAntichain` is an explicit Bayes/sequential-consistency premise; Protocol proves it from perfect recall and the hidden-state EFG supplies the exact weaker certificate directly. |
| R2-B1 | Auction `IsExPostIR` named standard truthful ex-post IR while quantifying every outcome/report. | closed | The unrestricted outcome property is now `HasNonnegativeUtilityAtEveryOutcome`; truthful ex-post IR remains the distinct Bayesian-mechanism predicate. No compatibility alias remains. |
| R2-B2 | External-regret matching was attributed as Hart--Mas-Colell conditional-regret/CE matching. | closed | The module cites the Hannan-regret scope of Hart--Mas-Colell 2001 and explicitly disclaims a conditional-regret or correlated-equilibrium endpoint. |
| R2-B3 | Posterior feasibility claimed the splitting characterization but lacked the constructive converse. | closed | `PosteriorSignals.fromPosteriorLaw` disintegrates the canonical coupling and proves every Bayes-plausible finite posterior law is induced by a signal structure. The hostile test consumes the constructor. |
| R2-B4 | Five module citations did not support the exact formalized result. | closed | Fictitious play, cheap talk, the folk theorem, two-agent EFX, and round-robin EF1 headers now state their exact scope and use supporting primary attributions; unsupported attributions were removed. |
| R2-C1 | The ESS second-order tie clause and Nash-not-ESS distinction had no stable witness. | closed | `Tests.Evolutionary` makes the tie clause load-bearing and separately exhibits a symmetric Nash resident that is neither NSS nor ESS. |
| R2-C2 | Bayesian Nash, revelation, and BCE transfer had only one-player positive witnesses. | closed | `Tests.Revelation` uses a two-player type-matching coordination game, checks the nondeviator branch, truthful direct Nash, and BNE-to-BCE certification. |
| R2-C3 | Stochastic uniformity was positively witnessed only by zero utility. | closed | `Examples.StochasticUniform` proves a nonconstant transient payoff has history sums in `[0,2]`, a `2 / horizon` deviation cap, and the semantic uniform payoff. |
| R2-C4 | Auction participation, transfer-sign, and budget-balance tests used only zero payments. | closed | `Tests.AuctionSemantics` supplies nonzero fees, balanced payer/subsidy transfers, and negative controls for balance, positive transfers, and overcharging. |
| R2-C5 | The Monderer--Samet theorem had no `p < 1` unequal-report consumer. | closed | `Tests.Agreement` constructs a three-world `p = 3/4` common-belief event with reports `1/7` and `0` and applies the public report-bound theorem. |
| R2-C6 | The named Blackwell entry points had no B-set instantiation and the audit imported a stale module. | closed | `Tests.Approachability` discharges the nonpositive-orthant B-set conditions and consumes response existence, the finite-time bound, and convergence; the audit imports the current module. |
| R2-C7 | MAID Nash transfer lacked a multiplayer owner-to-site regrouping witness. | closed | `Tests.MAID` has two players and three sites, one owner with two distinct sites, and direct deviation-law plus Nash-transfer consumers. |
| R2-D1 | Closure rows D-02, D-04, and D-06 contradicted their code evidence. | closed | Repeated discount comparison now calls `GameTheoryMath.normalizedDiscountedSum_le`; D-04 names the actual nonconstant two-state witness; both zero-consumer dynamic helpers were removed and D-06 corrected. |
| R2-D2 | Closure row A-08 claimed evolutionary discriminators that did not exist. | closed | The witnesses now exist and A-08 cites their load-bearing properties rather than a generic positive/negative label. |
| R2-D3 | K-01, E-07, and dead-helper evidence drifted from source. | closed | K-01 cites the actual knapsack consumer; deferred acceptance no longer claims a first/least fixed iterate; the two dead helpers are gone. |
| R2-E1 | The Repeated umbrella implied public monitoring used the Protocol runner. | retained | Deterministic public-action prefixes compile through `Repeated.Protocol`; repeated public-signal histories deliberately remain the native recursion used by PPE theory. `Repeated`, `Monitoring`, and `Languages.MultiRound` now state this split; the last remains the Protocol-backed finite monitoring constructor. |
| R2-E2 | The Bayesian Protocol compiler lacked the generic Nash-transfer leaf already used by other languages. | closed | `Languages.Bayesian.Strategic` proves arbitrary-policy and plan-facing Nash equivalences; a two-player protocol/static coordination fixture consumes the theorem. |
| R2-E3 | The advertised opt-in Analysis root was a directory, not an importable module. | closed | `GameTheory.Analysis` is an importable one-way aggregator for the admitted analytic families. |
| R2-V1 | `mixedPolytope_nonempty` documented an unproved iff. | closed | The docstring now states only the proved nonemptiness direction. |
| R2-V2 | `currentState` and `SignalHistory.append` were dead public API. | closed | Both declarations were removed after zero-consumer searches; no alias was retained. |
| R2-V3 | Finite minimax lacked the recognizable maximin--minimax equality. | closed | `Analysis.Minimax` defines the lower-security and upper-security payoff sets and proves their attained `sSup = sInf` equality from the canonical saddle theorem. |
| R2-V4 | Persuasion looked feasibility-constrained even though a finite nonempty action set always admits a receiver-optimal rule. | closed | `exists_isPersuasive` selects a score maximizer after every message and feeds `exists_optimalPersuasive_of_nonempty`; zero-mass messages are documented as automatic. |
| R2-X1 | The B-set hypothesis was reported stronger than Blackwell's condition. | retained | Adversarial verification refuted the report; no code change was warranted. |

The single-pass panel observations were re-derived separately before action:

| ID | Finding | Status | Current disposition and evidence |
|---|---|---|---|
| R2-P1 | Pure strict-dominator survival still carried a rationalizability name. | closed | The predicate is `SurvivesAllPureEliminationRounds`; correlated rationalizability remains explicit and independent/product-belief rationalizability remains queued. |
| R2-P2 | Structurally identical EFG/FOSG carriers had no relation. | closed | `EFG.Game.toFOSG` transparently forgets only tree/single-mover certificates while preserving the exact execution and information objects. |
| R2-P3 | Analytic best-reply correspondences had no bridge to Core `IsBestResponse`. | closed | `prob_mem_bestReply_iff_isBestResponse`, the product correspondence theorem, and the fixed-point/Nash iff now connect the surfaces; mixed-Nash existence consumes the bridge. |
| R2-P4 | Fictitious-play limit theorems used only constant or eventually constant paths. | closed | `Analysis.FictitiousPlayTest` supplies a two-player path changing forever, proves empirical convergence to the uniform profile, and applies `limit_isNash`. |
| R2-P5 | Approximate public monitoring bypassed canonical approximate Nash. | closed | `IsεDiscountedPublicNash` is definitionally canonical `IsεNash`; exact-to-approximate, zero-error, continuation, and concrete PPE consumers are present. |
| R2-P6 | Stochastic uniform approximate Nash bypassed the canonical predicate. | retained | Re-derivation refuted this half of the report: `IsεHorizonNash` already abbreviates canonical `IsεNash`, and its public iff/monotonicity theorems consume the canonical API. |
| R2-P7 | Game-free discounted patience algebra lived under `UtilityGame`. | closed | The one-step patience threshold moved to `GameTheoryMath.Discounted`; the folk theorem consumes it. Periodic rotation helpers remain domain-local because their `ZMod`/cycle types are the repeated-game consumer shape. |
| R2-P8 | Banzhaf lacked a swing-count theorem and Shapley--Shubik accepted an ignored simple-game proof. | closed | Banzhaf now equals the normalized cardinality of `swingCoalitions`; Shapley--Shubik takes a bundled `CoalitionalGame.SimpleGame`; tests consume both. |
| R2-P9 | Bayesian interim decomposition requested finiteness for every player's type. | closed | `expectedUtility_update` now requests `Fintype`/`DecidableEq` only for the deviator's type carrier. |
| R2-P10 | Knapsack half approximation unnecessarily required positive weights. | closed | D27's proof derives positivity only for the first rejected item; the checker now requires duplicate freedom only and zero-weight guards/witnesses compile. |
| R2-P11 | Agreement and Shapley positive witnesses were degenerate. | closed | Agreement now includes unequal reports under `p = 3/4` common belief; Shapley includes an asymmetric singleton-unanimity game with shares `(1,0)`. |
| R2-P12 | General Groves theory lives in the auction namespace. | queued | This is a real public namespace move rather than a local theorem patch and is named under mechanism extensions in `PostArchitectureDeliveryPlan.md`. |
| R2-P13 | Three second-price presentations were disconnected. | retained | Reserve Vickrey now agrees with the generic strict-winner payoff at zero reserve when the opponents' maximum is nonnegative. The two-bidder language fixture intentionally resolves ties differently, so an unconditional equality would be false. |
| R2-P14 | Finite vNM callers had to reselect best/worst endpoints for uniqueness. | closed | `representsExpectedUtility_unique_positiveAffine_of_finite` derives extrema from a nonconstancy witness; `Tests.VNM` consumes it. |
| R2-P15 | Exact and ordinal potential were not separated by a fixture; the team-game surface appeared dead. | closed | `Tests.Potential` exhibits an ordinal potential that is not exact and uses the ordinal Nash theorem. `IsTeamGame` was retained after live consumers were found in FictitiousPlay, ZeroSum, Potential, and utility lemmas. |
| R2-P16 | A cluster of public docstrings had misleading scope, binder, namespace, or process wording. | closed | Strong Nash states the totality caveat; Pareto and ActsOnce wording is corrected; orthant declarations live in `OrthantProjection`; root, FOSG Kuhn, learning, MAID, knapsack, and eventuality headers state current semantics. |
| R2-P17 | Recorded mature limits omitted MAID strategic relevance. | queued | Existing Kuhn, BCE, Myerson, revelation, balancedness, Arrow, vNM, and Fink limits remain explicit. Koller--Milch strategic relevance/requisite analysis is now a named MAID delivery package. |

## Cross-cutting findings

| ID | Finding | Status | Current disposition and evidence |
|---|---|---|---|
| X-01 | Stable source contained experiment IDs, repository-history comparisons, and local provenance paths. | closed | Stable source was swept; architecture history remains only in `docs/ExperimentLog.md` and decisions. Fast audits reject regression. |
| X-02 | Classical theorem modules named results without published sources. | closed | Owning module headers now cite primary published sources for rationalizability, social choice, vNM, learning, approachability, refinements, repeated/stochastic games, mechanisms, congestion, cooperative, and epistemic theory. Mechanical bridge files do not repeat citations. |
| X-03 | Boundary rules needed verification. | retained | No direct `Function.update` outside the profile implementation, no `open Classical` or `Fintype.ofFinite` in executable algorithm modules, and no trusted placeholders/custom axioms. |
| X-04 | Audit scripts obstructed the edit/build loop. | closed | Phase audits are fast structural checks by default; elaborated reachability is opt-in through `-DeepReachability` and reserved for CI/gates. |
| X-05 | Bootstrap coverage/provenance machinery was being mistaken for delivery status. | closed | Retired. `DeliveryLedger.md`, `CapabilityMatrix.md`, and `SupportEvidenceMatrix.md` are the current sources of truth. |

## Core solution concepts, potential, and learning

| ID | Finding | Status | Current disposition and evidence |
|---|---|---|---|
| C-01 | Joint-opponent mixed-dominator elimination was called Bernheim--Pearce or standard rationalizability. | closed | EXP-076/D40 corrected the API to `correlatedSurvivors` and `IsCorrelatedRationalizable`; the pure predicate is `SurvivesAllPureEliminationRounds`; no unqualified rationalizability alias remains. Independent rationalizability is explicitly queued. |
| C-02 | Prose asserted an unproved all-round inclusion between mixed and pure survivor iterations. | closed | The claim was removed. `Core.Response` explicitly states that no all-round inclusion is asserted without further hypotheses. |
| C-03 | Learning documentation described existing consumers as future work. | closed | Documentation points to the live multiplicative-weights consumer in `Analysis.Learning`. |
| C-04 | Utility-independent empirical and averaging operations were attached to `UtilityGame`. | closed | `empiricalMarginal`, `empiricalBelief`, `timeAverage`, and mixed-potential lifting are owned by `GameForm`; utility-dependent predicates remain bundled only where useful. |
| C-05 | Fictitious-play convergence assumed histories without an existence constructor. | closed | `pureBestResponse`, `generatedFictitiousPlay`, and `generatedFictitiousPlay_isFictitiousPlay` provide finite nonempty existence. Positive and falsifying tests compile. |
| C-06 | `WeaklyAcyclic` was owned by the potential module. | closed | The predicate is in `Core.Response`; potential modules provide sufficient certificates. |
| C-07 | Approximate Nash and approximate CCE had inconsistent receiver styles. | closed | `IsεNash` and `IsεCoarseCorrelatedEq` are top-level form-plus-utility predicates; all consumers use the same shape. |
| C-08 | Potential-game header overstated ordinal theorem coverage. | closed | The header identifies exactly the equilibrium-existence family proved at ordinal strength. |
| C-09 | Fictitious-play potential bounds were documented as equalities/two-sided estimates. | closed | Docstrings now state their proved one-sided lower-bound content. |
| C-10 | `Core.lean` omitted major exported families from its description. | closed | The root header describes the stable static theory and its analysis boundary without an exhaustive fragile list. |
| C-11 | CE-to-obedience exists but the converse characterization is absent. | closed | `isCorrelatedEq_iff_conditional_obedience` proves both directions by disintegrating the finite law over observed recommendations, without a finite strategy-carrier assumption. `Tests.CorrelatedDominance` constructs a fair diagonal, non-product recommendation from local checks and rejects a crossed point mass by one profitable switch. |

## Social choice, Bayesian theory, and coalitional foundations

| ID | Finding | Status | Current disposition and evidence |
|---|---|---|---|
| S-01 | Arrow's theorem silently used a tie-free social-output domain. | closed | `Core.Arrow` states that `Rank.Linear` is total, transitive, antisymmetric, and tie-free. |
| S-02 | vNM lacked affine uniqueness and used a stronger-than-bare-Archimedean continuity axiom without saying so. | closed | Positive-affine uniqueness is proved; `MixtureContinuous` is documented as certainty-equivalent solvability stronger in presentation than a bare Archimedean/topological condition. |
| S-03 | Arrow and Gibbard--Satterthwaite duplicate private strict-ranking proof machinery. | queued | The duplication is private and semantically harmless, but factoring a shared rank helper remains a focused Core cleanup; it is not exported as two public concepts. |
| S-04 | Coalitional addition/scalar operations lived in `Shapley`. | closed | They are owned by `Core.Coalitional`; Banzhaf no longer imports the Shapley proof tower for algebra. |
| S-05 | `SocialChoice` implied its Condorcet witness lived in the foundational module. | closed | The header now points to the reader-facing `Examples.Voting` consumer. |
| S-06 | May imported the larger social-choice surface without using it and appeared to duplicate majority. | closed | It imports `Core.Rank` directly and explicitly describes its ranking-free `SignType` theorem as a distinct binary characterization. |
| S-07 | `BayesianGame.actionSignature` carried an unused outcome type. | closed | Its outcome is `Unit`; only the dependent action profile is represented there. |
| S-08 | `replaceRanking` looked like an illicit profile update and a helper had no consumer. | closed | `replaceRanking` is the social-choice domain operation with live GS/tests consumers; the unused dictator helper was removed. It does not use `Function.update`. |
| S-09 | GS assumptions lacked a positive strategyproof-and-onto witness. | closed | `dictatorialChoice_isStrategyProof_and_isOnto` supplies the canonical positive witness; tests retain onto, manipulable, and nondictatorial discriminators. |
| S-10 | BCE lacks the standard interim obedience iff and a reverse epistemic foundation theorem. | queued | Current BCE claims are ex-ante deviation-map obedience and BNE-to-BCE only. Interim characterization and converse information-structure results remain named correlation breadth. |
| S-11 | Arrow's Pareto label could be read as weak rather than strict unanimity. | closed | The definition and docstring state strict Pareto on linear rankings and quantify over the named strict parts. |

## Static foundations and transformations

| ID | Finding | Status | Current disposition and evidence |
|---|---|---|---|
| F-01 | `WeaklyDominates` meant reflexive everywhere-weak dominance. | closed | The old relation is `VeryWeaklyDominates`; textbook `WeaklyDominates` additionally requires a strict witness, with a constant-game falsifier. |
| F-02 | Strong-Nash prose used the no-all-strict-gain reading without totality. | closed | The definition is described through coalition preference; `isStrongNash_iff_not_all_gain` requests `Preference.Total` explicitly. |
| F-03 | An implicit undeclared type variable could be auto-bound in `Mixed`. | closed | `autoImplicit` is disabled in the module and the variable is declared explicitly. |
| F-04 | `Preference.comapOutcome` had no generic transformation consumer. | closed | `Core.Transform` proves generic Nash, CCE, and CE outcome-pullback squares; tests exercise the public theorem. |
| F-05 | The transformation invariance square was incomplete. | queued | Outcome relabeling has Nash/CCE/CE; player/strategy equivalences have selected exact laws. Remaining CCE/CE reindexing and mixed/strategy commutation are explicit static-family breadth, not silently claimed. |
| F-06 | Signature/Form headers contained stale exclusivity or design-process language. | closed | Headers describe current operations and semantics only. |
| F-07 | A generic finite-law expectation bound lived in `Mixed`. | closed | `FinDist.expect_le_of_forall` owns it and all callers use the probability API. |
| F-08 | Binary CE documentation claimed existence while proving uniqueness only. | closed | `fairProfile_isNash`, `fairProduct_isCorrelatedEq`, and `existsUnique_correlatedEq` now prove existence and uniqueness. |
| F-09 | Survivor monotonicity names obscured direction. | closed | General membership transport is named `mem_pureSurvivors_of_le` / `mem_correlatedSurvivors_of_le`; one-step set inclusion remains `*_antitone`. |

## Probability, reusable mathematics, and finite execution

| ID | Finding | Status | Current disposition and evidence |
|---|---|---|---|
| M-01 | Blackwell response was quantified after the adversary sequence. | closed | `blackwell_approaches` selects one stationary response before quantifying over sequences; `Tests.Approachability` discharges the orthant B-set hypotheses and consumes response existence, the finite-time bound, and the limit theorem. |
| M-02 | `GameTheoryMath` omitted live modules and used delivery-process prose. | closed | The root exports every admitted reusable module and describes its consumer-based admission rule. |
| M-03 | `AffineUtility` was dead game-free code. | closed | The module, umbrella import, and audit probes were removed. vNM uses its own live finite-law affine theory. |
| M-04 | Generic dependent-product normalization facts polluted the public `FinDist` API. | closed | Those implementation lemmas and `pmfPi` are private; only the finite-law product API is public. |
| M-05 | Orthant geometry was named as if it contained regret theory. | closed | It is `GameTheoryMath.OrthantProjection`; imports and root exports were updated. |
| M-06 | The extensionality attribute exposed the hidden PMF representation. | closed | `@[ext]` is on `ext_of_prob`; representation equality remains an untagged implementation theorem. |
| M-07 | Online learning lacks a standalone optimally tuned square-root corollary. | queued | The game-independent fixed-rate and quadratic bounds are stable and the arbitrary-ε tuning has a live game consumer. A general closed-form tuning theorem remains math breadth. |

## Analysis, tests, and examples

| ID | Finding | Status | Current disposition and evidence |
|---|---|---|---|
| A-01 | Fink was presented as arbitrary-history discounted equilibrium. | closed | The module and capability matrix say stationary Bellman equilibrium only; arbitrary history-dependent completion is not claimed. |
| A-02 | Hart--Mas-Colell naming obscured expectation-level rather than almost-sure scope. | closed | The analysis header explicitly limits the result to deterministic expectation-level geometry and disclaims sampled almost-sure convergence. |
| A-03 | Trembling-hand perfection lacked the refinement-to-Nash direction and a falsifier. | closed | `IsTremblingHandPerfect.isNash` is proved in both generic and utility-facing forms; `Analysis.TremblingHandTest` rejects a weak dominated Nash profile. General finite existence is queued as refinement breadth. |
| A-04 | Analysis imports created phantom dependencies. | closed | The unused approachability import was removed; the fictitious-play-potential import remains because the file uses it. |
| A-05 | Stochastic/example names and “flagship” prose were stale. | closed | The general-sum Bellman fixture and repeated example headers now name their actual objects and claims. |
| A-06 | Empty-index `iSup`/`iInf` conventions in punishment levels were undocumented. | closed | `Feasible` documents the convention and requests nonemptiness on operational punishment theorems. |
| A-07 | Prisoner's Dilemma asserted a false weak Pareto fact through a vacuous Strong-Nash premise. | closed | The example now proves both `¬ IsStrongNash` and `¬ IsWeaklyParetoEfficient` for mutual defection. |
| A-08 | Evolutionary theory had no stable tests and pure-mutant scope was unclear. | closed | `Tests.Evolutionary` has a load-bearing second-order ESS tie, a symmetric Nash resident that is neither NSS nor ESS, and the finite-law mixed specialization. |
| A-09 | A test asserted only `True`, and another imported Experimental with Prop-only smoke checks. | closed | The learning test is semantic; `Tests.Transfer` was removed. Stable tests do not import Experimental. |
| A-10 | Named concepts lacked falsifying/consumer tests. | closed | Added discriminating coverage for Strong Nash, ESS/NSS, trembling hand, sequential rationality, PPE, uniform equilibrium, BCE, plausibility, exact potential, fictitious play, auctions, agreement, Rosenthal, and backward prescriptions. |
| A-11 | Test headers and numbered “hostile test” labels exposed delivery bookkeeping. | closed | Headers describe mathematical fixtures; temporary test numbering was removed. |

## Protocol and dynamic games

| ID | Finding | Status | Current disposition and evidence |
|---|---|---|---|
| P-01 | Imperfect-information `IsSubgamePerfect` quantified at every history, including roots that cut information sets. | closed | EXP-075/D42 introduced information-set-closed subgame roots. `IsHistorywiseOptimal` retains the stronger property under an honest name; crossed-root tests separate them. |
| P-02 | Bayes consistency was unsatisfiable at zero-mass sites. | closed | Bayes' rule is required only through `IsBayesConsistentAt` at positive-mass sites; zero-mass beliefs are unrestricted. |
| P-03 | `Zermelo` implied a win/lose determinacy theorem it did not contain. | closed | The header identifies constructive perfect-information backward induction and explicitly disclaims two-player win/lose determinacy. |
| P-04 | Parallel one-shot formalisms and SPE-to-static-Nash were unexplained. | closed | Finite-horizon `IsOneShotOptimalWithin` couples remaining fuel to trace depth and reaches compiled Nash; well-founded historywise deviation serves a different scope. EXP-078 proves that neither can be collapsed into a general proper-subgame single-information-state iff: complementary changes at two information states defeat it under perfect recall. |
| P-05 | Protocol exposed orphan constructors/helpers. | closed | `RecommendedPolicy` and the unused state-indexed `Context.ofDeviation` bridge were removed. `BehavioralAssessment.ofStrategy` is retained as the canonical total assessment constructor. |
| P-06 | A 340-line backward probe lived in stable Protocol. | closed | The fixture moved to `Tests.Backward`; stable `Protocol.Backward` contains semantics and theorems only. |
| P-07 | Sequential-rationality tests were nondiscriminating. | closed | `Analysis.Protocol.EFGTest` includes a payoff-sensitive assessment that fails sequential rationality and sequential equilibrium. |
| P-08 | History-state sufficiency was called perfect recall. | closed | `Protocol.Information` distinguishes the Markov/history-sufficiency premise from perfect recall. |
| P-09 | Backward existence requests menus at unreachable information values. | queued | The current theorem honestly states the global finite/nonempty menu premise. A reachable-only capability weakening is optional protocol breadth, not used to justify the existing claim. |
| D-01 | PPE predicates had no public documentation or negative test. | closed | Exact/approximate public Nash and PPE now document public-strategy and off-path scope; `Tests.MonitoringEquilibrium` supplies positive and negative PPE witnesses. |
| D-02 | Normalized discounted-sum algebra was duplicated. | closed | `GameTheoryMath.Discounted` owns the reusable comparison; repeated and monitoring modules consume it. |
| D-03 | Uniform-tail quantification was duplicated across repeated and stochastic roots. | closed | `GameTheoryMath.EventuallyAtAll` owns the combinator; both concepts are transparent specializations. |
| D-04 | Stochastic uniform certificates were only mutually self-tested. | closed | `Examples.StochasticUniform` has a reachable two-state process with transient payoffs `1` and `2`, proves every history sum lies in `[0,2]`, and constructs the `2 / horizon` uniform cap. |
| D-05 | `Prefix` duplicated `ProfileHistory`. | retained | `Prefix` is a transparent abbreviation used to give the compiled Protocol state a domain-specific name; it defines no second carrier. |
| D-06 | Dynamic helpers appeared orphaned. | closed | Zero-consumer `SignalHistory.append` and `PublicHistory.currentState` were removed; `horizonGame` remains because its expected-utility bridge consumes it. |
| D-07 | Repeated uniform scope did not say that existence is absent. | closed | Repeated and stochastic headers distinguish profile/payoff properties and make no general existence claim. |
| D-08 | Discounted-payoff zero conventions and history order were implicit. | closed | Discounted definitions point to the normalized-series helper; repeated prefixes state chronological order and stochastic histories document their recursive convention. No conversion is silently inferred. |

## Mechanisms, cooperative games, congestion, and epistemics

| ID | Finding | Status | Current disposition and evidence |
|---|---|---|---|
| K-01 | Generic auction efficiency quantified against one fixed valuation while describing reported efficiency. | closed | Efficiency is profile-indexed over reported valuations and instantiated by the exact knapsack mechanism in `Mechanism.Knapsack.Mechanism`; the old unsatisfiable reading is gone. |
| K-02 | Parallel VCG towers did not reach canonical DSIC. | closed | `VCGSetup.toQuasiLinearMechanism_isDSIC`, affine-maximizer tests, and knapsack VCG bridges land in canonical `IsDSIC`. |
| K-03 | `AllPay` contained arithmetic only but was advertised by the coordinated mechanism root. | closed | It is no longer imported by `GameTheory.Mechanism`; arithmetic remains an explicitly opt-in leaf until an auction model exists. |
| K-04 | DSIC was described as Bayesian/interim incentive compatibility. | closed | Wording now says dominant-strategy or ex-post IC; Bayesian interim incentives have a separate compiled predicate surface. |
| K-05 | Executable and semantic knapsack towers did not meet. | closed | `Knapsack.ExactBridge` proves the exact solver's welfare agrees with the semantic maximizer. Truthful greedy approximation remains explicitly unsupported pending monotonicity and critical payments. |
| K-06 | Signal/information-design and posterior-law halves were disconnected. | closed | `Mechanism.PosteriorSignals` proves both induced-law plausibility and the splitting converse constructing a signal for every plausible posterior law; hostile tests consume the construction and reject false plausibility. |
| K-07 | Single-parameter docs promised nonexistent analysis. | closed | The header states topology-free algebra only; analytic envelope identities are a delivery seam. |
| K-08 | Combinatorial scaffolding was called a complete auction theory. | closed | The root is named/documented as combinatorial allocation and bundle valuations and explicitly disclaims bids, payments, and incentives. |
| K-09 | Namespace layout and definitional iff lemmas appeared inconsistent. | retained | Namespaces track language syntax versus domain semantics. The iff lemmas are the intentional simp-free unfolding API for opaque predicates (and the welfare form has a test consumer); unrelated dead wrappers were removed. |
| K-10 | Fair-division completeness carried spurious finiteness/equality assumptions. | closed | `IsComplete` is assumption-free; finiteness appears only on algorithms/theorems needing enumeration. |
| K-11 | Reserve and second-price surfaces looked duplicated or disconnected from single-parameter algebra. | retained | Zero-reserve Vickrey utility agrees with the generic strict-winner second-price payoff under its necessary nonnegative-opponent condition. The two-bidder language fixture has a deliberately different tie rule, so no false unconditional bridge is asserted. |
| E-01 | Generic ESS could be mistaken for resistance to mixed invasion. | closed | `Evolutionary.Basic` says the carrier determines the mutant class; `Evolutionary.Mixed` supplies the explicit finite-law specialization and Nash bridge. |
| E-02 | Aumann agreement did not use `CommonKnowledgeAt`. | closed | `aumann_full_agreement_of_commonKnowledgeAt` is exercised by `Tests.Agreement`. |
| E-03 | Matching/epistemic modules exposed dead wrappers or an unconnected mutual-knowledge iteration. | closed | `StableMatching`, `IsProbabilityThreshold`, the unused posterior/congestion helpers, and the unconsumed mutual-knowledge iteration were removed. Common knowledge retains its directly consumed public-event definition. |
| E-04 | Deterministic game-form construction was repeated at four sites. | closed | `GameForm.deterministic` owns the constructor; NFG, finite correctness, congestion, and evolutionary bridges reuse it. |
| E-05 | CCE welfare theorem was named as correlated. | closed | It is `coarseCorrelated_socialCost_le`. |
| E-06 | Epistemic root advertised a common-prior object it did not define. | closed | It now describes explicit shared finite-prior assumptions and disclaims a separate common-prior structure. |
| E-07 | Deferred-acceptance fixed point was called the first fixed point. | closed | Documentation says it selects a certified fixed iterate; it does not claim least/first without proof. |
| E-08 | Raw epistemic posteriors and `FinDist.condOn` lack an equality bridge. | queued | Both semantics are honest and independently consumed. A positive-cell bridge is epistemic breadth; no current theorem assumes it silently. |
| E-09 | Cooperative modules could be read as claiming missing hard converses/optimality. | closed | Headers and the delivery ledger state one-way balancedness, assumed bargaining uniqueness, and the exact matching scope; the hard converses are queued. |

## Language layers

| ID | Finding | Status | Current disposition and evidence |
|---|---|---|---|
| L-01 | EFG inherited the incorrect imperfect-information subgame predicate. | closed | It uses D42 proper roots and the crossed-information-set regression. |
| L-02 | Kuhn correspondence was whole-profile only and insufficient for Nash transfer. | closed | `Protocol.Strategic` proves both unilateral updated-law directions with nondeviators fixed; `Languages.EFG.Kuhn` transfers Nash both ways, and `Tests.EFGKuhnNash` supplies a two-player coordination consumer plus a law-changing nondeviator control. |
| L-03 | Kuhn callers repeated a redundant acts-once hypothesis. | closed | Perfect recall supplies the consequence internally; public history-law theorems request perfect recall directly. |
| L-04 | General MAID semantics had no nonexperimental consumer. | closed | `Tests.MAID` exercises a two-player, three-site diagram, owner/site deviation regrouping, native/compiled law equality, and Nash equivalence on the stable public surface. |
| L-05 | Superseded MAID unit-order theorem chains remained public. | closed | The duplicate chain and stranded finite-law helper were removed; general order theorems own the result. |
| L-06 | Mechanism syntax imported solution concepts. | closed | `Languages.Mechanism` and `Languages.BayesianMechanism` contain syntax/compilation only; incentive theorems live under `GameTheory.Mechanism`. |
| L-07 | Opt-in FOSG values, intrinsic solutions, and multi-round compilation had no consumers. | closed | `Tests.MultiRoundMonitoring` consumes `toFOSG` and cumulative values; `Tests.IntrinsicSolution` exercises selected solutions. |
| L-08 | `actionOfJoint` is privately rederived in several compilers. | retained | Each helper is private, dependent on a different language's action family and legality witness, and exports no competing semantic concept. A shared helper is not justified without another common consumer shape. |
| L-09 | MAID stored defaults without proving their semantic irrelevance. | closed | Order/frontier equivalence proves completed runs agree through the public semantics; defaults are initialization data for not-yet-assigned nodes, not an outcome-level parameter. |
| L-10 | NFG-to-FOSG looked like an equivalence. | closed | The header explicitly calls it a one-round lift and disclaims characterization/inversion. |
| L-11 | Stable language headers used validation/process terminology. | closed | Stable language documentation now describes syntax, compilation, hypotheses, and claims only. |

## Remaining delivery consequences

The queued rows are theorem breadth, not unresolved corrections:

1. independent rationalizability and remaining transformation/correlation
   characterizations;
2. selected mathematical tuning/conditioning lemmas;
3. MAID strategic-relevance/requisite analysis; and
4. the mature-family extensions already enumerated in
   `PostArchitectureDeliveryPlan.md`.

Their absence is represented as `partial` or as a named next seam in
`DeliveryLedger.md` and `CapabilityMatrix.md`; none is reported as supported.
