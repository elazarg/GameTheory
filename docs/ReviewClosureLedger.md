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
| C-01 | Joint-opponent mixed-dominator elimination was called Bernheim--Pearce or standard rationalizability. | closed | EXP-076/D40 corrected the API to `correlatedSurvivors` and `IsCorrelatedRationalizable`; no unqualified alias remains. Independent rationalizability is explicitly queued. |
| C-02 | Prose asserted an unproved all-round inclusion between mixed and pure survivor iterations. | closed | The claim was removed. `Core.Response` explicitly states that no all-round inclusion is asserted without further hypotheses. |
| C-03 | Learning documentation described existing consumers as future work. | closed | Documentation points to the live multiplicative-weights consumer in `Analysis.Learning`. |
| C-04 | Utility-independent empirical and averaging operations were attached to `UtilityGame`. | closed | `empiricalMarginal`, `empiricalBelief`, `timeAverage`, and mixed-potential lifting are owned by `GameForm`; utility-dependent predicates remain bundled only where useful. |
| C-05 | Fictitious-play convergence assumed histories without an existence constructor. | closed | `pureBestResponse`, `generatedFictitiousPlay`, and `generatedFictitiousPlay_isFictitiousPlay` provide finite nonempty existence. Positive and falsifying tests compile. |
| C-06 | `WeaklyAcyclic` was owned by the potential module. | closed | The predicate is in `Core.Response`; potential modules provide sufficient certificates. |
| C-07 | Approximate Nash and approximate CCE had inconsistent receiver styles. | closed | `IsεNash` and `IsεCoarseCorrelatedEq` are top-level form-plus-utility predicates; all consumers use the same shape. |
| C-08 | Potential-game header overstated ordinal theorem coverage. | closed | The header identifies exactly the equilibrium-existence family proved at ordinal strength. |
| C-09 | Fictitious-play potential bounds were documented as equalities/two-sided estimates. | closed | Docstrings now state their proved one-sided lower-bound content. |
| C-10 | `Core.lean` omitted major exported families from its description. | closed | The root header describes the stable static theory and its analysis boundary without an exhaustive fragile list. |
| C-11 | CE-to-obedience exists but the converse characterization is absent. | queued | This is a same-family correlation extension under “Correlation and Bayesian obedience” in `DeliveryLedger.md`; current docstrings claim only the proved direction. |

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
| M-01 | Blackwell response was quantified after the adversary sequence. | closed | `blackwell_approaches` selects one stationary response before quantifying over sequences; a finite-time squared-distance theorem is exported. |
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
| A-08 | Evolutionary theory had no stable tests and pure-mutant scope was unclear. | closed | `Evolutionary.Mixed` defines explicit finite-law mutants; `Tests.Evolutionary` has positive and Nash-but-not-ESS/NSS negative witnesses. |
| A-09 | A test asserted only `True`, and another imported Experimental with Prop-only smoke checks. | closed | The learning test is semantic; `Tests.Transfer` was removed. Stable tests do not import Experimental. |
| A-10 | Named concepts lacked falsifying/consumer tests. | closed | Added discriminating coverage for Strong Nash, ESS/NSS, trembling hand, sequential rationality, PPE, uniform equilibrium, BCE, plausibility, exact potential, fictitious play, auctions, agreement, Rosenthal, and backward prescriptions. |
| A-11 | Test headers and numbered “hostile test” labels exposed delivery bookkeeping. | closed | Headers describe mathematical fixtures; temporary test numbering was removed. |

## Protocol and dynamic games

| ID | Finding | Status | Current disposition and evidence |
|---|---|---|---|
| P-01 | Imperfect-information `IsSubgamePerfect` quantified at every history, including roots that cut information sets. | closed | EXP-075/D42 introduced information-set-closed subgame roots. `IsHistorywiseOptimal` retains the stronger property under an honest name; crossed-root tests separate them. |
| P-02 | Bayes consistency was unsatisfiable at zero-mass sites. | closed | Bayes' rule is required only through `IsBayesConsistentAt` at positive-mass sites; zero-mass beliefs are unrestricted. |
| P-03 | `Zermelo` implied a win/lose determinacy theorem it did not contain. | closed | The header identifies constructive perfect-information backward induction and explicitly disclaims two-player win/lose determinacy. |
| P-04 | Parallel one-shot formalisms and SPE-to-static-Nash were unexplained. | queued | Finite-horizon `IsOneShotOptimalWithin` and well-founded historywise deviation serve different scopes. The proper-subgame one-shot iff and associated static transfer are the highest-priority delivery package. |
| P-05 | Protocol exposed orphan constructors/helpers. | closed | `RecommendedPolicy` and the unused state-indexed `Context.ofDeviation` bridge were removed. `BehavioralAssessment.ofStrategy` is retained as the canonical total assessment constructor. |
| P-06 | A 340-line backward probe lived in stable Protocol. | closed | The fixture moved to `Tests.Backward`; stable `Protocol.Backward` contains semantics and theorems only. |
| P-07 | Sequential-rationality tests were nondiscriminating. | closed | `Analysis.Protocol.EFGTest` includes a payoff-sensitive assessment that fails sequential rationality and sequential equilibrium. |
| P-08 | History-state sufficiency was called perfect recall. | closed | `Protocol.Information` distinguishes the Markov/history-sufficiency premise from perfect recall. |
| P-09 | Backward existence requests menus at unreachable information values. | queued | The current theorem honestly states the global finite/nonempty menu premise. A reachable-only capability weakening is optional protocol breadth, not used to justify the existing claim. |
| D-01 | PPE predicates had no public documentation or negative test. | closed | Exact/approximate public Nash and PPE now document public-strategy and off-path scope; `Tests.MonitoringEquilibrium` supplies positive and negative PPE witnesses. |
| D-02 | Normalized discounted-sum algebra was duplicated. | closed | `GameTheoryMath.Discounted` owns the reusable comparison; repeated and monitoring modules consume it. |
| D-03 | Uniform-tail quantification was duplicated across repeated and stochastic roots. | closed | `GameTheoryMath.EventuallyAtAll` owns the combinator; both concepts are transparent specializations. |
| D-04 | Stochastic uniform certificates were only mutually self-tested. | closed | A concrete one-state nonconstant-payoff witness lives in `Examples.StochasticUniform`. |
| D-05 | `Prefix` duplicated `ProfileHistory`. | retained | `Prefix` is a transparent abbreviation used to give the compiled Protocol state a domain-specific name; it defines no second carrier. |
| D-06 | Dynamic helpers appeared orphaned. | retained | `SignalHistory.append` feeds continuation/after laws; `horizonGame` feeds its expected-utility bridge. The unused `PublicHistory.currentState` surface was removed. |
| D-07 | Repeated uniform scope did not say that existence is absent. | closed | Repeated and stochastic headers distinguish profile/payoff properties and make no general existence claim. |
| D-08 | Discounted-payoff zero conventions and history order were implicit. | closed | Discounted definitions point to the normalized-series helper; repeated prefixes state chronological order and stochastic histories document their recursive convention. No conversion is silently inferred. |

## Mechanisms, cooperative games, congestion, and epistemics

| ID | Finding | Status | Current disposition and evidence |
|---|---|---|---|
| K-01 | Generic auction efficiency quantified against one fixed valuation while describing reported efficiency. | closed | Efficiency is profile-indexed over reported valuations and exercised by `Tests.AuctionSemantics`; the old unsatisfiable reading is gone. |
| K-02 | Parallel VCG towers did not reach canonical DSIC. | closed | `VCGSetup.toQuasiLinearMechanism_isDSIC`, affine-maximizer tests, and knapsack VCG bridges land in canonical `IsDSIC`. |
| K-03 | `AllPay` contained arithmetic only but was advertised by the coordinated mechanism root. | closed | It is no longer imported by `GameTheory.Mechanism`; arithmetic remains an explicitly opt-in leaf until an auction model exists. |
| K-04 | DSIC was described as Bayesian/interim incentive compatibility. | closed | Wording now says dominant-strategy or ex-post IC; Bayesian interim incentives have a separate compiled predicate surface. |
| K-05 | Executable and semantic knapsack towers did not meet. | closed | `Knapsack.ExactBridge` proves the exact solver's welfare agrees with the semantic maximizer. Truthful greedy approximation remains explicitly unsupported pending monotonicity and critical payments. |
| K-06 | Signal/information-design and posterior-law halves were disconnected. | closed | `Mechanism.PosteriorSignals` proves induced posterior-law plausibility and the signal/coupling bridge; hostile posterior tests reject false plausibility. |
| K-07 | Single-parameter docs promised nonexistent analysis. | closed | The header states topology-free algebra only; analytic envelope identities are a delivery seam. |
| K-08 | Combinatorial scaffolding was called a complete auction theory. | closed | The root is named/documented as combinatorial allocation and bundle valuations and explicitly disclaims bids, payments, and incentives. |
| K-09 | Namespace layout and definitional iff lemmas appeared inconsistent. | retained | Namespaces track language syntax versus domain semantics. The iff lemmas are the intentional simp-free unfolding API for opaque predicates (and the welfare form has a test consumer); unrelated dead wrappers were removed. |
| K-10 | Fair-division completeness carried spurious finiteness/equality assumptions. | closed | `IsComplete` is assumption-free; finiteness appears only on algorithms/theorems needing enumeration. |
| K-11 | Reserve and second-price surfaces looked duplicated or disconnected from single-parameter algebra. | retained | Language syntax no longer contains a competing solution theorem. The n-bidder reserve model and direct single-parameter mechanism algebra are distinct layers, and both terminate in canonical dominance/Nash/DSIC predicates. |
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
| L-02 | Kuhn correspondence was whole-profile only and insufficient for Nash transfer. | queued | Whole-profile law equality is labeled partial. Unilateral realization fixing nondeviators and Nash transfer are delivery package B. |
| L-03 | Kuhn callers repeated a redundant acts-once hypothesis. | closed | Perfect recall supplies the consequence internally; public history-law theorems request perfect recall directly. |
| L-04 | General MAID semantics had no nonexperimental consumer. | closed | `Tests.MAID` exercises native/compiled run equality and Nash equivalence on the stable public surface. |
| L-05 | Superseded MAID unit-order theorem chains remained public. | closed | The duplicate chain and stranded finite-law helper were removed; general order theorems own the result. |
| L-06 | Mechanism syntax imported solution concepts. | closed | `Languages.Mechanism` and `Languages.BayesianMechanism` contain syntax/compilation only; incentive theorems live under `GameTheory.Mechanism`. |
| L-07 | Opt-in FOSG values, intrinsic solutions, and multi-round compilation had no consumers. | closed | `Tests.MultiRoundMonitoring` consumes `toFOSG` and cumulative values; `Tests.IntrinsicSolution` exercises selected solutions. |
| L-08 | `actionOfJoint` is privately rederived in several compilers. | retained | Each helper is private, dependent on a different language's action family and legality witness, and exports no competing semantic concept. A shared helper is not justified without another common consumer shape. |
| L-09 | MAID stored defaults without proving their semantic irrelevance. | closed | Order/frontier equivalence proves completed runs agree through the public semantics; defaults are initialization data for not-yet-assigned nodes, not an outcome-level parameter. |
| L-10 | NFG-to-FOSG looked like an equivalence. | closed | The header explicitly calls it a one-round lift and disclaims characterization/inversion. |
| L-11 | Stable language headers used validation/process terminology. | closed | Stable language documentation now describes syntax, compilation, hypotheses, and claims only. |

## Remaining delivery consequences

The queued rows are theorem breadth, not unresolved corrections:

1. proper-subgame one-shot characterization and static transfer;
2. unilateral Kuhn realization and Nash transfer;
3. independent rationalizability and remaining transformation/correlation
   characterizations;
4. selected mathematical tuning/conditioning lemmas; and
5. the mature-family extensions already enumerated in
   `PostArchitectureDeliveryPlan.md`.

Their absence is represented as `partial` or as a named next seam in
`DeliveryLedger.md` and `CapabilityMatrix.md`; none is reported as supported.
