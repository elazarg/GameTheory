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
| Mixed ESS and NSS | pure-`true` resident against every finite-law mutant in [`Tests/Evolutionary.lean`](../GameTheory/Tests/Evolutionary.lean) | pure-`false` resident loses the first stability inequality in the same fixture | canonical symmetric mixed Nash bridge |
| Trembling-hand perfection | fully mixed Matching Pennies in [`Analysis/TremblingHandTest.lean`](../GameTheory/Analysis/TremblingHandTest.lean) | weakly dominated Nash profile in the same fixture | perfection-to-mixed-Nash theorem |
| Sequential equilibrium | fully mixed Bayes assessment with nonconstant terminal payoff in [`Analysis/Protocol/EFGTest.lean`](../GameTheory/Analysis/Protocol/EFGTest.lean) | dogmatic-`true` belief paired with a pure-`false` policy in the same fixture | EFG specialization of Protocol rationality and consistency |
| Perfect public equilibrium | noisy, branch-dependent coordinated profile in [`Tests/MonitoringEquilibrium.lean`](../GameTheory/Tests/MonitoringEquilibrium.lean) | stationary mismatched profile with a profitable root deviation | bounded one-shot-deviation principle, including off-support histories |
| Repeated uniform equilibrium | stationary Prisoner's Dilemma defection in [`Tests/RepeatedUniform.lean`](../GameTheory/Tests/RepeatedUniform.lean) | stationary cooperation fails the uniform approximation clause at all positive horizons | canonical finite-horizon approximate Nash |
| Stochastic uniform payoff | zero payoff over a nondegenerate transition in [`Examples/StochasticUniform.lean`](../GameTheory/Examples/StochasticUniform.lean) | constant-one claimed payoff over the same process | uniform deviation-cap/payoff equivalence |
| Bayes-correlated equilibrium | Nash-induced recommendation in [`Tests/BayesCorrelated.lean`](../GameTheory/Tests/BayesCorrelated.lean) | mismatching recommendation with a profitable flip deviation | canonical Bayesian outcome-law bridge |
| Bayes plausibility | fully revealing posterior law in [`Tests/FeasiblePosteriors.lean`](../GameTheory/Tests/FeasiblePosteriors.lean) | biased point-mass posterior law | signal/posterior factorization in `Mechanism.PosteriorSignals` |
| Approachability convergence | alternating-environment regret matching in [`Analysis/ApproachabilityTest.lean`](../GameTheory/Analysis/ApproachabilityTest.lean) | constant unit payoff against the singleton-zero target | game-free Blackwell response and finite-time bound |
| Exact potential | Rosenthal and mixed-potential witnesses in [`Tests/Congestion.lean`](../GameTheory/Tests/Congestion.lean) and [`Tests/MixedPotential.lean`](../GameTheory/Tests/MixedPotential.lean) | constant function rejected on a nonzero congestion deviation | finite Nash existence and canonical potential API |
| Fictitious play | constructed and explicit histories in [`Tests/FictitiousPlay.lean`](../GameTheory/Tests/FictitiousPlay.lean) | alternating history violating best response | exact-potential convergence consumer |
| DSIC / truthfulness | quasilinear, affine-maximizer, VCG, and single-parameter fixtures under `GameTheory/Tests` | reversed allocation and zero-payment profitable misreports | canonical dominant-strategy and Nash compilation surfaces |
| Aumann agreement | common knowledge of the full Boolean event in [`Tests/Agreement.lean`](../GameTheory/Tests/Agreement.lean) | differing revealing/coarse posteriors refute common knowledge of the true singleton | `aumann_full_agreement_of_commonKnowledgeAt` |
| Zermelo backward induction | chance-rooted Bellman profile in [`Tests/EFGZermelo.lean`](../GameTheory/Tests/EFGZermelo.lean) | strict comparisons rule out continue and punish | explicit exit and off-path reward prescriptions plus pure SPE existence |

## Opt-in semantic surfaces

| Surface | Discriminating stable evidence | Downstream boundary exercised |
|---|---|---|
| Typed MAID | distinct native policies induce distinct native and compiled laws in [`Tests/MAID.lean`](../GameTheory/Tests/MAID.lean) | native/compiled law and Nash equivalences |
| FOSG and multi-round monitoring | hidden opponent actions, remembered own actions, compiled play, and a nonzero external history value in [`Tests/MultiRoundMonitoring.lean`](../GameTheory/Tests/MultiRoundMonitoring.lean) | canonical Protocol/FOSG compiler and external value fold |
| Intrinsic solution | selected fixed point is the identity and distinguishes agents in [`Tests/IntrinsicSolution.lean`](../GameTheory/Tests/IntrinsicSolution.lean) | stable intrinsic solution selector |
| Stochastic uniformity | both successor states have positive support while the payoff tests vary independently in [`Examples/StochasticUniform.lean`](../GameTheory/Examples/StochasticUniform.lean) | perfect-monitoring horizon compiler and payoff-level uniformity |
