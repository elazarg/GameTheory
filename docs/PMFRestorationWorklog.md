# PMF restoration delivery record

The implementation replaces the finite-support semantic default with ordinary
Mathlib PMFs. [D62](decisions/D62-general-pmf-restoration.md) records the durable
decision; [the design](PMFRestorationDesign.md) states the acceptance criteria.
Original hypotheses, failed attempts, measurements, and outcomes are preserved
in [EXP-122–141](ExperimentLog.md). This record summarizes integrated coverage
and the remaining acceptance work.

## Current acceptance status

The unrestricted library build passes all 4,209 jobs without warnings. All 282
public modules, original tests and experiments, public lint, and architecture
checks pass. The parallel FinDist carrier and algebra have been removed.
D62 and the P0–P4 restoration gates are accepted.

## Semantic coverage

| Area | Integrated result | Evidence |
| --- | --- | --- |
| Probability mathematics | Native PMF products, conditioning, support-dependent bind, guarded expectation, Fubini, convergence, and measure bridges; no second distribution algebra | EXP-122/123; PMFExtensions, PMFProbabilityLemmas, PMFProductAlgebra |
| Static games | Canonical form, mixed/joint laws, Nash/CE/CCE, full deviation quantifiers, and actual-law expected utility | EXP-124; PMFStaticGate |
| Sequential games | Typed dependent histories, first-arrival Bayes normalization on variable-depth antichains, whole-policy deviations, strong sequential consistency, and certified-horizon independence | EXP-124/125; PMFSequentialGate; PMFSequentialTest |
| Finite existence | Finite-strategy Nash permits infinite outcome support; finite sequential existence retains its original insufficient-fuel refutation | EXP-128; PMFExistenceTest; SequentialExistenceBoundaryTest |
| Policy realization | Discrete predrawing has actual finite-site premises; ordinary measures support forward, reverse, and hybrid realization without a global finite site cover | EXP-126/127/136; PMFProductGate; PMFPolicyMeasureReverseGate |
| Bayesian and strategic transfer | General priors and local posterior values; arbitrary-mixture transfer requires integration of every actual target deviation | EXP-130/131; PMFBayesianGate; PMFTransferGate |
| Rationalizability | Joint payoff integration is explicit; rowwise and columnwise integration alone do not justify Fubini | EXP-132; PMFRationalizabilityGate |
| Repeated and monitored games | Stage integration and discounted-series summability are distinct; finite-average Nash samples the actual finite stage family | EXP-133/134; PMFRepeatedGate; PMFMonitoringGate; PMFUniformGate |
| Epistemic theory | Arbitrary set-based knowledge, infinite-support posteriors, exact/quantitative agreement, and explicit null-cell boundaries | EXP-135; PMFEpistemicGate |
| Evolutionary stability | Actual encounter comparisons; numerical ESS/NSS and small-invasion characterizations; divergent-mutant refutation | EXP-137; PMFEvolutionaryGate |
| Stochastic games | Arbitrary-state Bellman semantics over the actual joint-action/next-state law; finite-state assumptions local to existence | EXP-138; PMFStochasticBellmanGate |
| Mechanisms | Actual net-payoff and message-weighted-score integration; general posterior splitting; undefined alternatives refute optimality | EXP-139; PMFMechanismGate |
| MAID | Arbitrary-value native/compiled PMF laws and Nash equivalence; local finite-value premises for finite-BN graphical results | EXP-140; PMFMAIDGate; all 47 original experimental MAID clients |
| Infinite paths | Existing Ionescu–Tulcea construction and canonical chronological marginals without ambient-history countability | EXP-141; PMFInfinitePlayGate |

The preservation review covered original concrete values and negative controls,
not just declaration names. In particular it retained the finite sequential
horizon counterexample, backward-evaluation refutations, MAID's `3/2` versus `2`
deviation, the stochastic path payoff `1/4`, and history-dependent policy
improvement from `1/2` to `1`. The Kuhn finite-support fixture now states its
per-player support finiteness explicitly, because PMF alone does not encode it.
The Bayesian learning client retains its exact initial regrets, saddle gap,
regret convergence, and canonical approximate-Nash conclusions.

## Validation completed

- Explicit public-module closure: 3,941 jobs. Public lint-scope rebuild after
  the additive Bayesian typed-step law: 3,942 jobs; `lake lint` passes.
- Whole-public signature review: no authored public type names a project-private
  constant. Ten generated equation/helper matches were reviewed. The later
  Bayesian typed-step addition also passes its signature and axiom check.
  Newly introduced integration helpers used in public fixture types are also
  exposed and documented; the original control statements are unchanged.
- Phase-3 source and deep reachability audit: all expected counters pass.
- Phase-2 deep audit: all 350 symbol probes and all 89 deep counters match
  expected values. The final source audit also passes, with 39 named experiment
  owners, 319 raw-weight tokens inside them, and no remaining `toPMF` conversion.
- Unrestricted `lake build`: 4,209 jobs. All three source architecture audits
  pass `-VerifyExpected`; the release-version check passes for Lean 4.34.0.
  After fixture-signature and whitespace cleanup, the combined library, Math,
  and LintAll build passes 4,211 jobs; `lake lint` also passes.
- All 47 experimental MAID modules: 3,180 jobs; all six FOSG serialization and
  transfer clients: 3,036 jobs; all eight stochastic path clients: 3,120 jobs.
- SequentialClientAdequacy: 3,119 jobs, retaining whole-policy optimality and
  its mismatched-policy refutation.
- BayesianZeroSumLearningTest: 3,135 jobs, preserving its original controls.
- Tests.SubgamePerfect: 3,025 jobs, retaining whole-policy optimality from the
  root and the profitable off-path deviation. ApproximateEquilibriumTransport:
  3,016 jobs, retaining exact payoff conjugacy and the failed Nash transport.
- EXP-141's nine stochastic path clients: 3,121 jobs, including an explicitly
  uncountable ambient-history consumer.
- The 28-target compact/probability regression batch: 3,750 jobs. Its first
  combined run exposed an ExecutionLaws failure despite an earlier individual
  report; the repaired group passes. Its subsequent source-style cleanup passes
  the 3,101-job ExecutionLaws target.
- Source checks find no legacy FinDist references, placeholders, custom axioms,
  unauthorized raw-weight owners, forbidden imports, or duplicate equilibrium
  definitions. The final expected-value source checks pass.

Commands and experiment-specific axiom checks are recorded in ExperimentLog.
Runtime logs and restart checkpoints are local, ignored artifacts under
`ephemeral/`; they are not part of the public API or architecture decision.

## Scope boundary

This completes the general discrete restoration and the controlled policy/path
measure extensions in the named experiments. It does not assert infinite-space
equilibrium existence, a universal measurable-game framework, or path-coherence
theorems without their separate measurable-event assumptions.

The work uses one shared checkout with disjoint source ownership. Compiler
processes are serialized to avoid output-artifact races; source work remains
parallel. No worktrees, dependency-tree edits, compatibility aliases, or
parallel game semantics are introduced.
