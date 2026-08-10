# Capability matrix

This matrix describes recognizable workflows supported by the current public
library. It is successor-native: evidence points to compiled modules and stable
discriminating examples, not to declaration ancestry.

Verdicts mean:

- **supported**: the public API and a representative semantic consumer build;
- **partial**: a useful stable surface exists, with a named mathematical limit;
- **opt-in**: supported outside the light default root; and
- **frontier**: intentionally absent from the stable library.

## Static and analytic game theory

| Workflow | Public evidence | Verdict | Limit or next seam |
|---|---|---|---|
| Import the coordinated analytic surface | [`GameTheory/Analysis.lean`](../GameTheory/Analysis.lean) | opt-in | Semantic roots do not import the analytic aggregator. |
| Define strategic forms, profiles, preferences, deviations, and Nash-like concepts | [`GameTheory/Core.lean`](../GameTheory/Core.lean) | supported | Keep one canonical equilibrium predicate and explicit deviation schemes. |
| Compute finite pure Nash over rational tables | [`GameTheory/Finite/Algorithm.lean`](../GameTheory/Finite/Algorithm.lean), [`GameTheory/Finite/Correctness.lean`](../GameTheory/Finite/Correctness.lean), [`GameTheory/Examples/Classic.lean`](../GameTheory/Examples/Classic.lean) | supported | Execution stays separate from real-valued proof semantics. |
| Obtain finite mixed Nash and correlated-equilibrium existence | [`GameTheory/Analysis/Nash.lean`](../GameTheory/Analysis/Nash.lean), [`GameTheory/Analysis/Correlated.lean`](../GameTheory/Analysis/Correlated.lean) | opt-in | No general equilibrium solver is implied. |
| Prove no-regret to approximate CCE and multiplicative-weights consequences | [`GameTheory/Core/Learning.lean`](../GameTheory/Core/Learning.lean), [`GameTheoryMath/OnlineLearning.lean`](../GameTheoryMath/OnlineLearning.lean) | supported | Weighted-potential extensions remain separate. |
| Construct and analyze fictitious play | [`GameTheory/Core/FictitiousPlay.lean`](../GameTheory/Core/FictitiousPlay.lean), [`GameTheory/Tests/FictitiousPlay.lean`](../GameTheory/Tests/FictitiousPlay.lean), [`GameTheory/Analysis/FictitiousPlayTest.lean`](../GameTheory/Analysis/FictitiousPlayTest.lean) | supported | The analytic consumer proves a forever-changing path converges to mixed Nash. |
| Use Blackwell approachability and regret matching | [`GameTheoryMath/Approachability.lean`](../GameTheoryMath/Approachability.lean), [`GameTheory/Tests/Approachability.lean`](../GameTheory/Tests/Approachability.lean) | opt-in | Response selection is proof-facing and stationary in the running average. |
| Reason about dominance, correlated rationalizability, pure elimination, response dynamics, and weak acyclicity | [`GameTheory/Core/Response.lean`](../GameTheory/Core/Response.lean), [`GameTheory/Core/Rationalizability.lean`](../GameTheory/Core/Rationalizability.lean) | supported | Pure-elimination survival is not called rationalizability; the independent product-belief notion is not yet exposed. |
| Use exact, ordinal, and mixed potential games | [`GameTheory/Core/Potential.lean`](../GameTheory/Core/Potential.lean), [`GameTheory/Core/MixedPotential.lean`](../GameTheory/Core/MixedPotential.lean), [`GameTheory/Tests/Potential.lean`](../GameTheory/Tests/Potential.lean) | supported | Weighted potential is not folded into the exact predicate. |
| Analyze zero-sum matrix security, maximin--minimax equality, and selected values | [`GameTheory/Core/MatrixGame.lean`](../GameTheory/Core/MatrixGame.lean), [`GameTheory/Analysis/Minimax.lean`](../GameTheory/Analysis/Minimax.lean) | supported | General measurable games are outside scope. |
| Use finite-outcome expected-utility representation and affine uniqueness | [`GameTheory/Core/VNM.lean`](../GameTheory/Core/VNM.lean), [`GameTheory/Tests/VNM.lean`](../GameTheory/Tests/VNM.lean) | supported | Infinite-outcome representation needs a separate analytic layer. |
| Apply Arrow, Gibbard–Satterthwaite, and May | [`GameTheory/Core/Arrow.lean`](../GameTheory/Core/Arrow.lean), [`GameTheory/Core/GibbardSatterthwaite.lean`](../GameTheory/Core/GibbardSatterthwaite.lean), [`GameTheory/Core/May.lean`](../GameTheory/Core/May.lean) | supported | Sen and median-voter extensions remain open. |
| State coalitional games, Shapley values, balancedness, and voting power | [`GameTheory/Cooperative.lean`](../GameTheory/Cooperative.lean), [`GameTheory/Tests/Banzhaf.lean`](../GameTheory/Tests/Banzhaf.lean), [`GameTheory/Tests/Shapley.lean`](../GameTheory/Tests/Shapley.lean) | opt-in | The hard balancedness converse and convex-game core theorem remain open. |
| Use static ESS/NSS and the symmetric Nash bridge | [`GameTheory/Evolutionary.lean`](../GameTheory/Evolutionary.lean), [`GameTheory/Tests/Evolutionary.lean`](../GameTheory/Tests/Evolutionary.lean) | supported | No population dynamics claim is made. |
| Reason about knowledge, posteriors, common knowledge, and agreement | [`GameTheory/Epistemic.lean`](../GameTheory/Epistemic.lean), [`GameTheory/Tests/Agreement.lean`](../GameTheory/Tests/Agreement.lean) | supported | A Protocol bridge needs an explicit state-view premise. |
| Prove Rosenthal potential and affine price-of-anarchy bounds | [`GameTheory/Congestion.lean`](../GameTheory/Congestion.lean), [`GameTheory/Tests/Congestion.lean`](../GameTheory/Tests/Congestion.lean) | opt-in | Congestion stays layered over canonical potential and welfare theory. |

## Sequential, repeated, and stochastic theory

| Workflow | Public evidence | Verdict | Limit or next seam |
|---|---|---|---|
| Model execution, chance, histories, information-local policies, and behavioral laws | [`GameTheory/Protocol.lean`](../GameTheory/Protocol.lean) | supported | No universal game hub or duplicate runner. |
| Extract strategic forms and transfer pure/mixed Nash | [`GameTheory/Languages/EFG/Strategic.lean`](../GameTheory/Languages/EFG/Strategic.lean) | supported | Extraction forgets sequential structure. |
| State textbook subgame perfection under imperfect information | [`GameTheory/Protocol/SubgamePerfect.lean`](../GameTheory/Protocol/SubgamePerfect.lean), [`GameTheory/Tests/SubgameRoots.lean`](../GameTheory/Tests/SubgameRoots.lean), [`GameTheory/Tests/SubgameOneShot.lean`](../GameTheory/Tests/SubgameOneShot.lean) | supported | Whole-policy deviations are essential: single-information-state tests do not characterize SPE even under perfect recall. |
| Construct a pure SPE by backward induction | [`GameTheory/Protocol/Zermelo.lean`](../GameTheory/Protocol/Zermelo.lean), [`GameTheory/Tests/EFGZermelo.lean`](../GameTheory/Tests/EFGZermelo.lean) | supported | Requires well-founded play, separated decision histories, and finite nonempty local choices. |
| Move between behavioral and mixed strategies under perfect recall | [`GameTheory/Protocol/Strategic.lean`](../GameTheory/Protocol/Strategic.lean), [`GameTheory/Languages/EFG/Kuhn.lean`](../GameTheory/Languages/EFG/Kuhn.lean), [`GameTheory/Tests/EFGKuhnNash.lean`](../GameTheory/Tests/EFGKuhnNash.lean) | supported | Exact updated laws fix every nondeviator and transfer expected-utility Nash both ways in the finite perfect-recall scope. |
| Use sequential equilibrium with finite behavioral assessments | [`GameTheory/Analysis/Protocol/EFG.lean`](../GameTheory/Analysis/Protocol/EFG.lean), [`GameTheory/Analysis/Protocol/EFGTest.lean`](../GameTheory/Analysis/Protocol/EFGTest.lean) | opt-in | Bayes consistency requires decision fibers to be history antichains; perfect recall is sufficient. |
| Use trembling-hand perfection | [`GameTheory/Analysis/TremblingHand.lean`](../GameTheory/Analysis/TremblingHand.lean), [`GameTheory/Analysis/TremblingHandTest.lean`](../GameTheory/Analysis/TremblingHandTest.lean) | opt-in | Alternative refinement predicates are not conflated. |
| Model deterministic repeated play, public-signal monitoring and rank, discounting, triggers, PPE, and uniform equilibrium | [`GameTheory/Repeated.lean`](../GameTheory/Repeated.lean), [`GameTheory/Tests/MonitoringRank.lean`](../GameTheory/Tests/MonitoringRank.lean), [`GameTheory/Tests/MonitoringEquilibrium.lean`](../GameTheory/Tests/MonitoringEquilibrium.lean), [`GameTheory/Tests/RepeatedUniform.lean`](../GameTheory/Tests/RepeatedUniform.lean) | supported | Rank measures one-period signal effects and is tied to the generated one-prefix law; native monitoring still claims no infinite realized-path law. |
| Use finite stochastic games and uniform payoff certificates | [`GameTheory/Stochastic.lean`](../GameTheory/Stochastic.lean), [`GameTheory/Examples/StochasticUniform.lean`](../GameTheory/Examples/StochasticUniform.lean) | opt-in | General uniform existence is not claimed. |
| Use discounted zero-sum and stationary general-sum stochastic values | [`GameTheory/Analysis/Stochastic.lean`](../GameTheory/Analysis/Stochastic.lean) | opt-in | General-sum theorem is a stationary Bellman certificate, not arbitrary history-dependent equilibrium. |

## Languages and mechanisms

| Workflow | Public evidence | Verdict | Limit or next seam |
|---|---|---|---|
| Write deterministic normal-form syntax and compile directly to the static core | [`GameTheory/Languages/NFG.lean`](../GameTheory/Languages/NFG.lean) | supported | No language-specific Nash predicate. |
| Model simultaneous stochastic observation and serialize FOSG to EFG | [`GameTheory/Languages/FOSG.lean`](../GameTheory/Languages/FOSG.lean), [`GameTheory/Languages/EFG.lean`](../GameTheory/Languages/EFG.lean), [`GameTheory/Languages/Bridges/FOSGToEFG.lean`](../GameTheory/Languages/Bridges/FOSGToEFG.lean) | partial | EFG forgets structurally to FOSG; reverse serialization order is explicit; counterfactual/CFR breadth remains open. |
| Compile typed MAIDs while preserving laws and Nash | [`GameTheory/Languages/MAID.lean`](../GameTheory/Languages/MAID.lean), [`GameTheory/Tests/MAID.lean`](../GameTheory/Tests/MAID.lean) | opt-in | Strategic-relevance/requisite analysis, recall, and Kuhn-facing extensions remain open. |
| Model multi-round imperfect monitoring | [`GameTheory/Languages/MultiRound.lean`](../GameTheory/Languages/MultiRound.lean), [`GameTheory/Tests/MultiRoundMonitoring.lean`](../GameTheory/Tests/MultiRoundMonitoring.lean) | opt-in | Generic stagewise-Nash conveniences remain separate. |
| State intrinsic closed-loop systems and select fixed-point solutions | [`GameTheory/Languages/Intrinsic.lean`](../GameTheory/Languages/Intrinsic.lean), [`GameTheory/Tests/IntrinsicSolution.lean`](../GameTheory/Tests/IntrinsicSolution.lean) | opt-in | Strategic ownership, utilities, equilibrium, and compilation need separate gates. |
| Compile Bayesian games through Protocol and transfer Nash | [`GameTheory/Languages/Bayesian/Strategic.lean`](../GameTheory/Languages/Bayesian/Strategic.lean), [`GameTheory/Tests/Bayesian.lean`](../GameTheory/Tests/Bayesian.lean) | opt-in | The language syntax remains solution-concept free; transfer lives in the strategic leaf. |
| Use Bayesian recommendation, truthful mechanisms, and revelation | [`GameTheory/Core/Bayesian.lean`](../GameTheory/Core/Bayesian.lean), [`GameTheory/Mechanism/BayesianIncentives.lean`](../GameTheory/Mechanism/BayesianIncentives.lean), [`GameTheory/Mechanism/Revelation.lean`](../GameTheory/Mechanism/Revelation.lean) | supported | Analytic envelope identities are not part of the stable API. |
| Use auctions, VCG, reserves, combinatorial allocation, and exact knapsack mechanisms | [`GameTheory/Mechanism.lean`](../GameTheory/Mechanism.lean), [`GameTheory/Tests/AuctionSemantics.lean`](../GameTheory/Tests/AuctionSemantics.lean) | opt-in | All-pay support is arithmetic only; the greedy knapsack approximation has no truthfulness claim. |
| Use finite fair division, ordinal matching, and bargaining | [`GameTheory/Mechanism/FairDivision.lean`](../GameTheory/Mechanism/FairDivision.lean), [`GameTheory/Cooperative.lean`](../GameTheory/Cooperative.lean) | opt-in | Cake cutting, matching strategyproofness, and alternative bargaining solutions remain open. |
| Use compositional open-game machinery | none | frontier | Requires a compositional theorem and external semantic comparison before admission. |

The discriminating examples behind these claims are indexed in
[`SupportEvidenceMatrix.md`](SupportEvidenceMatrix.md).
