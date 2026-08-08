# V1 capability matrix

Status: delivery comparator, derived from the pinned snapshot at
`a3d8c67ed91d58e197b8c978ddcc00ba96f87c29` and the current public sources.

This is the headline test for the rewrite: **is v2 at least as useful as v1
for a mature user workflow, while being better designed?**  It is deliberately
not a declaration-port quota.  The exact declaration ledgers under
[`docs/coverage/`](coverage/README.md) remain regression evidence: they say
which pinned claims have been reviewed, adapted, subsumed, refuted, retired, or
deferred.  They do not turn many small wrapper declarations into a substitute
for one missing mature workflow.

## Release and parity rule

A v1-scope release may not contain a **critical gap** in a mature, in-scope
workflow.  A stronger canonical theorem may subsume many v1 declarations, but
only where the declaration ledger records a checked theorem chain.  Conversely,
beyond-v1 work never compensates for a weakened mature field, and internal
wrappers, experiments, or an unexposed implementation do not count as user
support.  Usefulness includes architecture, trust, public-import shape, and
ergonomics: one canonical concept, local assumptions, an honest bridge, a
reader-facing example, and the required audit/build evidence matter alongside
the theorem statement.  This is the support standard in
[`docs/PostArchitectureDeliveryPlan.md`](PostArchitectureDeliveryPlan.md) and
the architecture/trust covenant in
[`docs/GameTheory2Design.md`](GameTheory2Design.md).

Verdicts are intentionally qualitative:

- **better** — a checked canonical successor covers the workflow and removes a
  material v1 design cost or adds a clearly relevant capability;
- **comparable** — the mature workflow is present, with no claimed material
  usability improvement;
- **partial** — a useful slice is proved, but the ledger or plan identifies
  significant remaining mature work;
- **critical gap** — a mature in-scope v1 workflow is not yet supported;
- **deliberately retired or out of scope** — v1 material is either obsolete
  transport/compatibility machinery or explicitly outside the finite/discrete
  release boundary.  This is not evidence of parity.

## Dashboard

The 45 workflow rows below contain 23 better, 5 comparable, and 9 partial
verdicts; 6 are critical gaps and 2 are deliberately retired or out of
scope.  The strongest evidence is the canonical static/protocol spine, NFG,
the frozen EFG/Kuhn/SPE transfers, finite learning, finite auctions, congestion,
finite information design, and the executable rational frontend.  The release
blockers are broader multi-round theory, learning dynamics, equilibrium
refinements, finite fair division, matching, and bargaining.  The many partial
rows are not treated as
release-ready merely because their declaration review is advanced; in
particular, the live FOSG queue still has 81 rows to classify
([`docs/V1CoverageLedger.md`](V1CoverageLedger.md)).

## Static theory

| Capability / user workflow | Pinned v1 evidence (paths / families) | v2 successor evidence | Verdict | Parity condition / next proof |
|---|---|---|---|---|
| State a finite-support strategic form and reason about unilateral deviations once | `Core/**`, `Concepts/Foundations/**` (S-FOUND); equilibrium families (S-EQ) | [`GameTheory/Core.lean`](../GameTheory/Core.lean): signature-bound profiles, forms, preferences, deviations, and one equilibrium surface | better | Maintain one canonical predicate; recover remaining S-FOUND/S-EQ invariance and foundation results. |
| Obtain finite mixed Nash and correlated/coarse-correlated existence without a second boundedness API | `Concepts/Existence/**` (S-EXIST), mixed/correlation families (S-MIX/S-CORR); `Theorems/CorrelatedEqExistence.lean` (T-CE) | [`GameTheory/Analysis/Nash.lean`](../GameTheory/Analysis/Nash.lean), [`GameTheory/Analysis/Correlated.lean`](../GameTheory/Analysis/Correlated.lean), and complete T-CE ledger | better | Finish S-EXIST and the nonexistence S-MIX/S-CORR inventories; no general solver is implied. |
| Turn finite no-regret play into approximate CCE and reuse multiplicative-weights facts | `Concepts/Learning/**` (D-LEARN); frozen F2 | [`GameTheory/Core/Learning.lean`](../GameTheory/Core/Learning.lean), [`GameTheory/Core/MixedImprovement.lean`](../GameTheory/Core/MixedImprovement.lean), [`GameTheoryMath/OnlineLearning.lean`](../GameTheoryMath/OnlineLearning.lean), and complete F2/self-play/improvement ledgers | better | Recover approachability after the active potential fictitious-play gate. |
| Prove finite exact-potential fictitious-play convergence to approximate Nash | `Concepts/Learning/FictitiousPlayPotential.lean` (D-LEARN) | [`GameTheory/Core/FictitiousPlayPotential.lean`](../GameTheory/Core/FictitiousPlayPotential.lean) owns the topology-free Lyapunov spine; [`GameTheoryMath/HarmonicSequence.lean`](../GameTheoryMath/HarmonicSequence.lean) owns the general sequence estimates; [`GameTheory/Analysis/FictitiousPlayPotential.lean`](../GameTheory/Analysis/FictitiousPlayPotential.lean) proves eventual ε-Nash on a nonstationary hostile trace | better | Keep weighted-potential generalization behind S-POT's named gate; no synthetic team-game evaluator. |
| Use approachability and its regret/convergence consequences | approachability files in `Concepts/Learning/**` (D-LEARN) | No native approachability bridge yet; canonical regret and finite-law semantics are available below it | critical gap | Recover the approachability bridge without duplicating regret, vector-payoff, or finite-law semantics. |
| Model observable cheap talk and finite electronic-mail communication without forcing static timing into Protocol | `Concepts/Communication/**`, `Core/Babbling.lean`, `Languages/ElectronicMailGame.lean` (D-COMM) | [`GameTheory/Core/CheapTalk.lean`](../GameTheory/Core/CheapTalk.lean), [`GameTheory/Examples/ElectronicMail.lean`](../GameTheory/Examples/ElectronicMail.lean); exact communication ledger | better | Conditional public-signal disintegration and staged cheap talk remain separate timing-sensitive work. |
| Prove/check dominance, rationalizability, and response properties | `Concepts/Dominance/**` (S-DOM); response material in S-FOUND | [`GameTheory/Core/Response.lean`](../GameTheory/Core/Response.lean) and finite dominance checks | partial | Classify and recover solvability, undominated, and rationalizability families. |
| Use potential structure and derive finite-improvement consequences | `Concepts/Potential/**` (S-POT) | [`GameTheory/Core/Potential.lean`](../GameTheory/Core/Potential.lean) and [`GameTheory/Core/MixedPotential.lean`](../GameTheory/Core/MixedPotential.lean); basic and mixed inventories each 22/22 reviewed | better | Recover decomposition and harmonic results; weighted potential remains a named gate. |
| Prove Rosenthal potential and pure/CCE affine price-of-anarchy bounds for congestion games | `Congestion/**` (P-CONG) | [`GameTheory/Congestion.lean`](../GameTheory/Congestion.lean); complete 50/50 pinned ledgers and Pigou/Braess examples | better | Keep congestion opt-in and layered over canonical potential and robust-welfare theory. |
| Apply smoothness and robust CCE smoothness to welfare/price-of-anarchy claims | `Concepts/Welfare/**` (S-WEL) | [`GameTheory/Core/Welfare.lean`](../GameTheory/Core/Welfare.lean), [`GameTheory/Core/RobustWelfare.lean`](../GameTheory/Core/RobustWelfare.lean); smoothness ledger 4/4 | better | Recover individual rationality and remaining welfare inventory. |
| Use security, minimax, and constant-sum/correlation facts | `Concepts/ZeroSum/**` (S-ZERO); `Theorems/Minimax.lean` (T-MIN) | [`GameTheory/Core/ZeroSum.lean`](../GameTheory/Core/ZeroSum.lean), [`GameTheory/Analysis/Minimax.lean`](../GameTheory/Analysis/Minimax.lean) | partial | Complete security, matrix geometry, complementarity, and T-MIN inventory. |
| Work with preference/rank foundations and expected-utility representation | S-FOUND: `Core/**`, `Concepts/Foundations/**` | [`GameTheory/Core/Preference.lean`](../GameTheory/Core/Preference.lean), [`GameTheory/Core/Rank.lean`](../GameTheory/Core/Rank.lean), [`GameTheory/Core/Utility.lean`](../GameTheory/Core/Utility.lean) | partial | Recover VNM, axiom-independence, utility invariance, and strategic-equivalence results. |
| Formalize social-choice impossibility and rule-characterization workflows | `Mechanism/SocialChoice/**` (M-SOCIAL) | [`GameTheory/Core/SocialChoice.lean`](../GameTheory/Core/SocialChoice.lean), [`GameTheory/Core/Arrow.lean`](../GameTheory/Core/Arrow.lean) | partial | Add May, Gibbard--Satterthwaite, and Sen without merging rankings into lottery preference. |
| State coalitional values, core, and Shapley-style foundations | `Core/Coalition.lean`, `Cooperative/CoalitionalGame/**` (P-COAL) | [`GameTheory/Core/Coalitional.lean`](../GameTheory/Core/Coalitional.lean), [`GameTheory/Core/Shapley.lean`](../GameTheory/Core/Shapley.lean) | partial | A native `Cooperative` branch needs convex core, Bondareva, Banzhaf, and cost-of-stability theorems. |
| Use static ESS/NSS and connect ESS to symmetric Nash | `Concepts/Classes/EvolutionaryStability.lean` (D-EVOL) | [`GameTheory/Evolutionary.lean`](../GameTheory/Evolutionary.lean), [`GameTheory/Evolutionary/Nash.lean`](../GameTheory/Evolutionary/Nash.lean); complete nine-row ledger | comparable | Keep dynamics opt-in; no unproved population-dynamics claim. |
| Reason about finite/approximate common knowledge and agreement | `Concepts/Knowledge/**` (D-KNOW) | [`GameTheory/Epistemic.lean`](../GameTheory/Epistemic.lean), [`GameTheory/Epistemic/Agreement.lean`](../GameTheory/Epistemic/Agreement.lean), complete 62/62 ledger | better | Any Protocol bridge must supply its extra state-view premise. |

## Sequential theory and languages

| Capability / user workflow | Pinned v1 evidence (paths / families) | v2 successor evidence | Verdict | Parity condition / next proof |
|---|---|---|---|---|
| Write deterministic normal-form syntax, compile it, and use the canonical Nash/CE API | `Languages/NFG.lean`, `Languages/NFG/**` (L-NFG) | [`GameTheory/Languages/NFG.lean`](../GameTheory/Languages/NFG.lean); complete 126/126 L-NFG ledger and T4 | better | Retain direct compilation; no language-specific equilibrium predicate. |
| Express history-local information, behavioral policies, and their induced execution law once | `Languages/InfoModel.lean`, `Languages/InfoModel/**` (L-INFO) | [`GameTheory/Protocol/Information.lean`](../GameTheory/Protocol/Information.lean) with EFG, FOSG, and Kuhn consumers | better | Finish classifying predecessor simulation/semantic-form wrappers; retain no second information runner. |
| Represent finite extensive forms with canonical histories and extract contingent-plan strategic forms | `Languages/EFG.lean`, `Languages/EFG/**` (L-EFG); frozen T1 | [`GameTheory/Languages/EFG.lean`](../GameTheory/Languages/EFG.lean), [`GameTheory/Protocol/Strategic.lean`](../GameTheory/Protocol/Strategic.lean); complete T1 ledger | better | Broader EFG syntax/refinement inventory remains to be classified. |
| Prove sequential rationality / one-shot deviation iff subgame perfection, including off-path histories | EFG refinement material; frozen F4 | [`GameTheory/Protocol/SubgamePerfect.lean`](../GameTheory/Protocol/SubgamePerfect.lean), EFG specialization, complete F4 ledger | better | Recover remaining EFG refinement declarations without weakening well-founded hypotheses. |
| Construct a pure SPE in a finite perfect-information game by backward induction | `Theorems/Zermelo.lean` (T-ZER) | [`GameTheory/Protocol/Zermelo.lean`](../GameTheory/Protocol/Zermelo.lean) constructs one information-local Bellman profile and proves SPE after every history; [`GameTheory/Languages/EFG/Zermelo.lean`](../GameTheory/Languages/EFG/Zermelo.lean) is the transparent EFG specialization; the chance/off-path witness is build evidence | better | Keep well-foundedness and finite local choices explicit; do not reintroduce subtree evaluators, bounded-utility wrappers, or global `Fintype.ofFinite`. |
| Move between behavioral and mixed strategies under sharp recall/no-revisit conditions | `Languages/Kuhn/**`, `Theorems/Kuhn/**` (L-KUHN); frozen F3/T2 | [`GameTheory/Protocol/Information.lean`](../GameTheory/Protocol/Information.lean), [`GameTheory/Languages/EFG/Kuhn.lean`](../GameTheory/Languages/EFG/Kuhn.lean); complete T2 ledger | better | Classify non-flagship generic/language-specific Kuhn material. |
| Use trembling-hand and assessment refinements beyond ordinary mixed Nash | refinement and sequential-assessment files in `Concepts/Mixed/**` (S-MIX) | Pointwise assessment consistency exists in the opt-in Analysis/Protocol bridge, but the mature refinement workflow is not recovered | critical gap | Recover one nondegenerate trembling-hand or perfect-equilibrium theorem with the topology boundary explicit. |
| Model simultaneous stochastic play with observation-local policies and serialize FOSG to EFG | `Languages/FOSG/**` (L-FOSG); `Languages/Bridges/**` (L-BRIDGE) | [`GameTheory/Languages/FOSG.lean`](../GameTheory/Languages/FOSG.lean), [`GameTheory/Languages/Bridges/FOSGToEFG.lean`](../GameTheory/Languages/Bridges/FOSGToEFG.lean) | partial | Finish the remaining L-FOSG and bridge queues; counterfactual reach, CFR, continuation coefficients, and strategic/utility transfer keep separate gates. |
| Compile a typed MAID while preserving native owner, policy, outcome law, and Nash transfer | `Languages/MAID.lean`, `Languages/MAID/**` (L-MAID); frozen T3 | [`GameTheory/Languages/MAID.lean`](../GameTheory/Languages/MAID.lean), [`GameTheory/Languages/MAID/ToEFG.lean`](../GameTheory/Languages/MAID/ToEFG.lean), complete T3 ledger | better | Recover broader MAID refinement, recall, and Kuhn-facing results. |
| Model multi-round games with previous-action information and imperfect monitoring | `Languages/MultiRound.lean`, `Languages/MultiRound/**` (L-ROUND) | [`GameTheory/Languages/Rounds.lean`](../GameTheory/Languages/Rounds.lean) is only a scoped successor | critical gap | Pass the L-ROUND gate and recover the mature monitoring/previous-action workflows. |
| State intrinsic closed-loop configurations, information-local rules, solvability, and causal schedules | `Languages/Intrinsic.lean`, `Languages/Intrinsic/**` (L-INTR) | [`GameTheory/Languages/Intrinsic.lean`](../GameTheory/Languages/Intrinsic.lean) and `Intrinsic/Solution.lean`; 58/158 reviewed | partial | Separate gates remain for ownership/preferences, temporal compilation, recall, mixed/behavioral strategy, PMF/utility, equilibrium, and Kuhn. |
| Use compositional open-game / expressiveness machinery | `Languages/OpenGame/**` (L-OPEN); residual expressiveness in L-BRIDGE | No stable successor; Frontier is reserved | deliberately retired or out of scope | Admit only after a compositional theorem and external semantic comparison; explicit named bridges may replace obsolete v1 transport. |

## Learning, repeated, and stochastic play

| Capability / user workflow | Pinned v1 evidence (paths / families) | v2 successor evidence | Verdict | Parity condition / next proof |
|---|---|---|---|---|
| Define public-history repeated play, discounted values, triggers, and use the discounted folk theorem | `Concepts/Repeated/**` (D-REPEAT); frozen F7 | [`GameTheory/Repeated.lean`](../GameTheory/Repeated.lean), [`GameTheory/Analysis/Repeated/Folk.lean`](../GameTheory/Analysis/Repeated/Folk.lean), F7 witness | comparable | Recover the remaining rank/uniform parts separately; stable root has no infinite-path law. |
| Propagate a finite public-monitoring signal prefix through successor/bind laws | D-REPEAT; frozen F8 | [`GameTheory/Repeated/Monitoring.lean`](../GameTheory/Repeated/Monitoring.lean), complete F8 ledger | comparable | The prefix law remains the lower layer; PPE and one-shot results come from the separately checked EXP-064 leaves. |
| Use the broader repeated-game monitoring, rank, and uniform-equilibrium hierarchy | `Concepts/Repeated/**` (D-REPEAT) | [`GameTheory/Repeated.lean`](../GameTheory/Repeated.lean) now exposes finite-prefix monitoring, continuation values, canonical PPE, and the bounded one-shot-deviation principle; EXP-064 hostile witness | partial | Harvest rank/self-generation, approximate allowances, and uniform results; infinite realized-path probability remains excluded. |
| Analyze finite stochastic games, uniform deviation caps, and discounted zero-sum stationary values | only `Languages/MultiRound/StochasticGame.lean` in L-ROUND; v1 lacks general value theory | [`GameTheory/Stochastic.lean`](../GameTheory/Stochastic.lean), [`GameTheory/Analysis/Stochastic.lean`](../GameTheory/Analysis/Stochastic.lean) | better | This beyond-v1 mature capability must remain opt-in and cannot discharge L-ROUND recovery; general uniform existence is excluded. |

## Mechanisms, social domains, and cooperation

| Capability / user workflow | Pinned v1 evidence (paths / families) | v2 successor evidence | Verdict | Parity condition / next proof |
|---|---|---|---|---|
| Relate Bayesian recommendation/obedience, incentive compatibility, and truthful Bayesian Nash | `Mechanism/Bayesian/**` (M-BAYES); frozen F5/F6 | [`GameTheory/Core/Bayesian.lean`](../GameTheory/Core/Bayesian.lean), [`GameTheory/Languages/BayesianMechanism.lean`](../GameTheory/Languages/BayesianMechanism.lean), canonical revelation, explicit truthful welfare/participation, feasible posterior laws, quasilinear weak monotonicity, positive-weight affine maximizers, and topology-free single-parameter payment bounds | comparable | Recover the Myerson envelope identity through the named D11 Analysis gate and classify the remaining Bayesian mechanism inventory. |
| Apply revelation principles and reason about information design | revelation, Bayes-correlated, feasible-posterior, and mechanism-design files in `Mechanism/Bayesian/**` (M-BAYES) | [`GameTheory/Mechanism/Revelation.lean`](../GameTheory/Mechanism/Revelation.lean) gives canonical finite-support revelation; [`GameTheory/Mechanism/InformationDesign.lean`](../GameTheory/Mechanism/InformationDesign.lean) recovers public persuasion; `FeasiblePosteriors` and `JointFeasiblePosteriors` recover all 19 posterior-law declarations and add joint full revelation | better | Keep public signaling and posterior laws on canonical `FinDist`; richer dynamic or measurable information design remains behind its own gate. |
| Specify and verify finite sealed-bid, reserve, VCG, combinatorial, all-pay, and knapsack mechanisms | `Auctions/**` (M-AUCT) | [`GameTheory/Mechanism.lean`](../GameTheory/Mechanism.lean), `Auction`, `ReserveVickrey`, `VCG`, `Combinatorial`, `AllPay`, and `Knapsack` modules | better | The Myerson envelope payment identity remains behind M-BAYES/D11; broad auction family stays partial. |
| Formalize contracts with an explicit participation/outside-option theorem | `Mechanism/Contracts/**` (M-CONTRACT) | [`GameTheory/Mechanism/PrincipalAgent.lean`](../GameTheory/Mechanism/PrincipalAgent.lean), stochastic hostile fixture, and complete 23/23 ledger | better | Maintain explicit outside options and theorem-local action finiteness; richer adverse-selection or executable contract search is a separate consumer. |
| Formalize finite fair division, including indivisible EF1 | `Mechanism/FairDivision.lean`, finite files (M-FAIR) | No finite fair-division successor | critical gap | Build finite round-robin EF1 plus one allocation theorem without importing measurable cake assumptions. |
| Formalize divisible cake cutting | divisible fair-division files (M-CAKE) | No continuous/measurable successor by D11 | deliberately retired or out of scope | Cake theory remains outside the finite release; reconsider only through the D11 measurable program. |
| Prove voting, majority, delegation, and power-index results | `Voting/**` (M-VOTE) | [`GameTheory/Examples/Voting.lean`](../GameTheory/Examples/Voting.lean) supplies examples but not the mature theorem families | partial | Recover median/majority, delegation, liquid-democracy, and power-index results against the ranking foundations. |
| Find and reason about stable matchings | matching and `GaleShapley/**` (P-MATCH) | `Cooperative` root is reserved; no successor domain is present | critical gap | Prove Gale--Shapley/perfect matching, then strategyproofness or rural hospitals. |
| Characterize bargaining solutions | `Cooperative/Bargaining.lean` (P-BARG) | No native feasible-utility successor is present | critical gap | Prove Nash-solution affine invariance on an honest feasible utility set. |

## Infrastructure and execution

| Capability / user workflow | Pinned v1 evidence (paths / families) | v2 successor evidence | Verdict | Parity condition / next proof |
|---|---|---|---|---|
| Construct finite-support laws and use map/bind/product/expectation in game semantics | `Math/FiniteProbabilityMassFunction.lean`, `Math/PMFProduct/**` (MATH) | [`GameTheory/Probability/FinDist.lean`](../GameTheory/Probability/FinDist.lean); finite-sum expectation ledger | better | Continue demand-driven probability recovery; no generic probability monad or measurable path layer. |
| Execute pure-Nash/dominance checks over rational finite tables and obtain semantic correctness | executable NFG/support material in L-NFG and MATH | [`GameTheory/Finite/Algorithm.lean`](../GameTheory/Finite/Algorithm.lean), [`GameTheory/Finite/Correctness.lean`](../GameTheory/Finite/Correctness.lean) | comparable | Broaden only with explicit enumeration, computable scalars, and a proved refinement theorem. |
| Reindex players/strategies, lift mixed forms, and transport Nash/CE facts | `Concepts/Transport/**` (S-TRANS) and language transports | [`GameTheory/Core/Transform.lean`](../GameTheory/Core/Transform.lean); D8 complete and named language bridges | better | Review each S-TRANS declaration as subsumed, named transfer, or retired; no generic certificate hierarchy. |
| Import stable theory without hidden Analysis/Frontier dependencies and rely on a clean trust surface | v1 package/import and transport machinery, pinned theorem tests (T-TEST), and the MATH support tree | [`GameTheory.lean`](../GameTheory.lean), public-root documentation in [`README.md`](../README.md), and the plan's support/audit rules | better | Release still requires public-import review, full/cold build, trust, reachability, transport, and coverage audits. |

## Reading this matrix with the ledgers

`better` and `comparable` rows are evidence for a user-facing release claim,
not automatic family completion.  A `partial` row remains partial until its
named mature workflow has a canonical theorem, a public owner, example, test,
and reviewed declaration evidence.  The exact ownership and dispositions live
in [`docs/V1CoverageLedger.md`](V1CoverageLedger.md) and its linked files under
[`docs/coverage/`](coverage/README.md); the mutable gates and exclusion policy
live in [`docs/PostArchitectureDeliveryPlan.md`](PostArchitectureDeliveryPlan.md).
Pinned theorem tests inherit the verdict of their owning workflow and earn no
separate capability credit.
