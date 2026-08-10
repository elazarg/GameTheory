# Support evidence matrix

This index records discriminating, stable evidence for public semantic
predicates and opt-in surfaces. A positive witness alone shows that a type can
be inhabited; a falsifying witness checks that the definition rejects a nearby
bad case; the consumer column shows where the result reaches a shared API or a
downstream theorem.

## Semantic predicates

| Predicate | Positive witness | Falsifying witness | Shared or downstream consumer |
|---|---|---|---|
| Strong Nash | coordinated payoff-one profile in [`Tests/MonitoringEquilibrium.lean`](../GameTheory/Tests/MonitoringEquilibrium.lean) | mutual defection in Prisoner's Dilemma in [`Examples/Classic.lean`](../GameTheory/Examples/Classic.lean) | `IsStrongNash.isNash` and weak Pareto efficiency |
| ESS/NSS and mixed specialization | a resident tied at first order and accepted by the load-bearing ESS second clause; plus a finite-law ESS in [`Tests/Evolutionary.lean`](../GameTheory/Tests/Evolutionary.lean) | a symmetric Nash resident that is neither NSS nor ESS | canonical symmetric pure/mixed Nash bridges |
| Trembling-hand perfection | fully mixed Matching Pennies in [`Analysis/TremblingHandTest.lean`](../GameTheory/Analysis/TremblingHandTest.lean) | weakly dominated Nash profile in the same fixture | perfection-to-mixed-Nash theorem |
| Sequential equilibrium | fully mixed Bayes assessment with nonconstant terminal payoff in [`Analysis/Protocol/EFGTest.lean`](../GameTheory/Analysis/Protocol/EFGTest.lean) | dogmatic-`true` belief paired with a pure-`false` policy in the same fixture | EFG specialization of Protocol rationality and consistency |
| Finite-horizon one-shot optimality | stopping-game first/second decisions at their exact remaining depths in [`Tests/Assessment.lean`](../GameTheory/Tests/Assessment.lean) | both swapped fuel values are rejected and early exit is absorbing | arbitrary-policy comparison and compiled static Nash |
| Imperfect-information subgame perfection | information-set-closed initial root and perfect-information Bellman SPE in [`Tests/SubgameRoots.lean`](../GameTheory/Tests/SubgameRoots.lean) and [`Tests/EFGZermelo.lean`](../GameTheory/Tests/EFGZermelo.lean) | a crossed information-set root is rejected; [`Tests/SubgameOneShot.lean`](../GameTheory/Tests/SubgameOneShot.lean) refutes the tempting local-deviation characterization | canonical whole-policy SPE plus the distinct historywise one-shot theorem |
| Perfect public equilibrium | noisy, branch-dependent coordinated profile in [`Tests/MonitoringEquilibrium.lean`](../GameTheory/Tests/MonitoringEquilibrium.lean) | stationary mismatched profile with a profitable root deviation | bounded one-shot-deviation principle, including off-support histories |
| Repeated uniform equilibrium | stationary Prisoner's Dilemma defection in [`Tests/RepeatedUniform.lean`](../GameTheory/Tests/RepeatedUniform.lean) | stationary cooperation fails the uniform approximation clause at all positive horizons | canonical finite-horizon approximate Nash |
| Stochastic uniform payoff | reachable transient payoffs `1` and `2` with an explicit `2 / horizon` cap in [`Examples/StochasticUniform.lean`](../GameTheory/Examples/StochasticUniform.lean) | constant-one claimed payoff in the zero-payoff control | uniform deviation-cap/payoff equivalence |
| Bayes-correlated equilibrium | Nash-induced recommendation in [`Tests/BayesCorrelated.lean`](../GameTheory/Tests/BayesCorrelated.lean) | mismatching recommendation with a profitable flip deviation | canonical Bayesian outcome-law bridge |
| Bayes plausibility | fully revealing posterior law and its constructed inducing signal in [`Tests/FeasiblePosteriors.lean`](../GameTheory/Tests/FeasiblePosteriors.lean) | biased point-mass posterior law | both directions of the signal/posterior splitting characterization |
| Approachability convergence | a signed Boolean game discharging the nonpositive-orthant B-set condition in [`Tests/Approachability.lean`](../GameTheory/Tests/Approachability.lean) | constant unit payoff against the singleton-zero target in [`Analysis/ApproachabilityTest.lean`](../GameTheory/Analysis/ApproachabilityTest.lean) | response existence, finite-time squared-distance bound, and `blackwell_approaches` |
| Exact and ordinal potential | Rosenthal/mixed-potential witnesses plus an ordinal potential proving Nash in [`Tests/Potential.lean`](../GameTheory/Tests/Potential.lean) | the same scaled fixture is proved not exact; a constant function is rejected on a nonzero congestion deviation | finite Nash existence and canonical potential API |
| Fictitious play | constructed histories plus a two-player path changing forever in [`Tests/FictitiousPlay.lean`](../GameTheory/Tests/FictitiousPlay.lean) and [`Analysis/FictitiousPlayTest.lean`](../GameTheory/Analysis/FictitiousPlayTest.lean) | alternating history violating best response | exact-potential convergence and empirical-limit-to-Nash consumers |
| DSIC / truthfulness | quasilinear, affine-maximizer, VCG, and single-parameter fixtures under `GameTheory/Tests` | reversed allocation and zero-payment profitable misreports | canonical dominant-strategy and Nash compilation surfaces |
| Aumann and approximate agreement | exact full-event agreement plus a `p = 3/4` common-belief event with distinct reports `1/7` and `0` in [`Tests/Agreement.lean`](../GameTheory/Tests/Agreement.lean) | differing revealing/coarse posteriors refute common knowledge of the true singleton | exact `CommonKnowledgeAt` theorem and the Monderer--Samet report bound |
| Auction payment semantics | nonzero report-sensitive fees and balanced payer/subsidy transfers in [`Tests/AuctionSemantics.lean`](../GameTheory/Tests/AuctionSemantics.lean) | fees refute balance, subsidies refute no-positive-transfers, and overcharging refutes nonnegative utility | canonical quasilinear payment predicates |
| Bayesian Nash and revelation | two-player type-matching coordination equilibrium in [`Tests/Revelation.lean`](../GameTheory/Tests/Revelation.lean) | profitable-report controls in the one-player fixture | nondeviator report preservation, truthful direct Nash, and BNE-to-BCE certification |
| Persuasion feasibility | receiver-score maximization in [`Mechanism/InformationDesign.lean`](../GameTheory/Mechanism/InformationDesign.lean) | zero-mass messages are documented as automatic rather than substantive constraints | persuasive-rule and sender-optimal persuasive-rule existence |
| Voting-power indices | majority-game swing counts in [`Tests/Banzhaf.lean`](../GameTheory/Tests/Banzhaf.lean) | Banzhaf and Shapley--Shubik values are numerically separated in the same fixture | normalized swing-count theorem and bundled simple-game Shapley--Shubik API |
| Zermelo backward induction | chance-rooted Bellman profile in [`Tests/EFGZermelo.lean`](../GameTheory/Tests/EFGZermelo.lean) | strict comparisons rule out continue and punish | explicit exit and off-path reward prescriptions plus pure SPE existence |

## Opt-in semantic surfaces

| Surface | Discriminating stable evidence | Downstream boundary exercised |
|---|---|---|
| Typed MAID | two players and three sites, with one player owning two distinct decision sites, in [`Tests/MAID.lean`](../GameTheory/Tests/MAID.lean) | owner/site deviation regrouping plus native/compiled law and Nash equivalences |
| Bayesian Protocol compiler | two-player common-bit coordination in [`Tests/Bayesian.lean`](../GameTheory/Tests/Bayesian.lean) | arbitrary policy/plan updates are transported through the generic strategic leaf | direct/protocol expected-utility and Nash equivalence |
| FOSG and multi-round monitoring | hidden opponent actions, remembered own actions, compiled play, and a nonzero external history value in [`Tests/MultiRoundMonitoring.lean`](../GameTheory/Tests/MultiRoundMonitoring.lean) | canonical Protocol/FOSG compiler and external value fold |
| Intrinsic solution | selected fixed point is the identity and distinguishes agents in [`Tests/IntrinsicSolution.lean`](../GameTheory/Tests/IntrinsicSolution.lean) | stable intrinsic solution selector |
| Stochastic uniformity | both successor states have positive support while the payoff tests vary independently in [`Examples/StochasticUniform.lean`](../GameTheory/Examples/StochasticUniform.lean) | perfect-monitoring horizon compiler and payoff-level uniformity |
