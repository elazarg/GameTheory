# VegasCore extension recovery

Recover the reusable theorem families from `../VegasCore/GameTheoryExtensions`
into their canonical GameTheory owners, one validated slice per checkpoint.
Do not introduce an extension compatibility surface or a second definition of
an existing semantic concept. Preserve upstream attribution in `NOTICE`.

| Order | Slice | Status and evidence | Next obligation |
|---|---|---|---|
| 1 | Proportional Bayes transport | Supported: `Analysis.Protocol.BeliefTransport` scales site mass, cancels the multiplier in Bayes beliefs, and derives raw positive mass. Exact transport specializes the proportional theorem. Only finite movers are assumed; history carriers are arbitrary. The tremble reach-ratio consumer and existing restriction-extension consumer compile warning-free. | Passage and restriction-extension delivery is covered below. |
| 2 | Depth-free action restrictions | Supported: canonical restriction-belief, completion and extension APIs use terminal passage, with depth parameters removed and only `Finite` target histories. The asynchronous hidden-decision consumer refutes common depth and preserves terminal play under extension. Structural ancestor existence moves to `Protocol.History`; restriction passage lemmas live in `Protocol.RestrictionExecution`. Event-level conditional domination reuses the existing scalar ratio bound. Full build, lint and architecture audit pass. | Additional restriction consumers remain dependency-gated. |
| 3 | Total variation and approximate transport | Supported mathematical slice: the existing half-L1 `statisticalDistance` moves to a dedicated PMF module and equals the uniform event-gap bound. Arbitrary-carrier observation contraction, expected kernel error, support-local payoff-range bounds, domination and discrete convergence are proved. Canonical incentive and continuation contexts bound deviation gain without a new equilibrium predicate. Sample tests and concrete pseudo-Nash transfer improve their constants by two. Full build, lint and architecture audit pass. | Copied-site sequential-limit primitives and the unbounded-source/unequal-depth target consumer are supported; weighted component/copy integration remains below. |
| 4 | Information-abstraction criteria | Protected-law and fixed-payoff slices supported: supported fact recovery transparently specializes Mathlib `Function.FactorsThrough`; conditional averaging preserves arbitrary response laws. Perfect reporting and preservation of all informed reporting laws are equivalent to fact recovery. Guarded terminal-decision optimality specializes canonical contexts, and optimal retained-law sets coincide without finite carriers, finite-support priors or bounded utilities. Consumers cover an erased supported bit, an unreachable merge and infinite carriers. `Protocol.DecisionPayoff` characterizes fixed-payoff preservation by common maximizing actions on supported fibers; a support-local utility bound replaces finite prior support. Only optimum existence and fixed-payoff necessity need finite actions. Universal reporting-utility preservation is equivalent to supported fact recovery for finite facts. | Sequential decision consumers accompany component completion. |
| 5 | Sanction feasibility and synthesis | Supported: independent rational signed-slope inference is sound, complete and minimal against all nonnegative real solutions. Canonical comparison bridges use additional collection risk. Explicit finite tables characterize eventual deterrence, without a finite ambient row type. Sound observable alarms attain exactly the mass outside admitted observations. Sequential rationality specializes the actual continuation context with only finite movers. | Executable monitor construction remains consumer-gated; component integration is covered below. |
| 6 | Component completion with independent or shared mixture weights | Static, passage and consistent-completion slices supported: canonical stochastic strategy substitution, existence of component mixtures with independent or shared weights for arbitrary underlying strategies/outcomes with integrable component plays, weighted approximate member bounds with arbitrary action carriers, and actual-passage Bayes conditioning with only finite movers, consistent assessment completion with independent or shared weights, and an unequal-depth full-menu sequential-equilibrium consumer. Free-agent completion now specializes the component theorem. Uniform whole-policy gain bounds remove finite histories and a uniform horizon; the unbounded countdown consumer compiles. Local copied-site transfer and common subsequence extraction use terminal continuations; source gain mixtures permit infinite source histories. Observed-law matching uses independent distance stability. | Copied-site completion with shared mixture weights is supported with explicit local certificates. Nonconstant comparison certificates for shared mixture weights and sequential decision consumers remain. |

Validation for the first slice:

```text
lake build GameTheory.Analysis.Protocol.BeliefTransport
lake build GameTheory.Analysis.Protocol.BeliefTransportTest
lake build GameTheory.Analysis.Protocol.RestrictionExtensionTest
```

The first consumer build exposed an identity-map simplification mismatch; an
explicit `change` and `PMF.map_id` resolve it without a transparency option.

Validation for the second slice:

```text
lake build GameTheory.Math.Probability.Domination GameTheory.Protocol.RestrictionExecution
lake build GameTheory.Analysis.Protocol.RestrictionBeliefs
lake build GameTheory.Analysis.Protocol.RestrictionExtensionTest GameTheory.Analysis.Protocol.BeliefTransportTest
$env:LEAN_NUM_THREADS = '2'
lake build GameTheory GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
```

Both existing and unequal-depth consumers compile warning-free. No new module,
parallel equilibrium definition, or compatibility alias is introduced.
The full build completed all 4,556 jobs; lint passed and the architecture audit
reported `VERIFIED=1`. Ancestor existence, conditional domination, restriction
belief convergence, consistent completion, sequential extension and the
asynchronous consumer depend only on the standard Lean axioms.

The initial unrestricted integration build exhausted memory while a sibling
repository also built. Limiting this repository's build to two Lean threads
completed the same target without changing proofs or dependencies.

The third slice keeps generic mathematics in
`Math.Probability.StatisticalDistance` and
`Math.Probability.StatisticalDistanceStability`. The latter connects distance to
the existing pointwise-convergence and domination APIs. These modules import no
game semantics, sample-test machinery, analytic fixed points or machine library.
The source extension's separate event-bound predicate is unnecessary: the
existing distance has exactly that characterization.

The independent-sample bound now follows from stochastic kernel composition,
replacing its specialized expectation induction. Acceptance tests in `[0, 1]`
lose at most one distance per sample; tests in `[-1, 1]` retain the sharp factor
two. This lowers mean-test advantage from `4m` to `2m` and improves the concrete
ideal-to-real pseudo-Nash transfer accordingly. The mean bound allows radius
zero. Local continuation transport only bounds possible gains; sequential
consistency and the limit argument remain separate obligations.

Narrow validation for the third slice:

```text
lake build GameTheory.Math.Probability.StatisticalDistanceStability
lake build GameTheory.Math.Probability.Indistinguishability
lake build GameTheory.Math.Probability.StatisticalCloseness
lake build GameTheory.Analysis.IncentiveSimulation GameTheory.Core.PseudoNashTolerance GameTheory.Analysis.Protocol.Incentives
lake build GameTheory GameTheory.LintAll
lake build GameTheory.Math.Probability.StatisticalDistance GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
```

The full integration completed all 4,558 jobs, including existing pseudo-Nash,
hybrid and restriction-extension consumers. The audit prompted removal of a
direct equality transport from the zero-distance proof and explicit ownership
registration of both new PMF modules. The final leaf and lint-scope build
completed 4,199 jobs; lint passed and the audit reported `VERIFIED=1` with no
transport or unowned mass arithmetic. Event equivalence, support-local range,
kernel error, convergence equivalence, independent samples, incentive gain,
continuation gain and sharpened pseudo-Nash transfer use only standard axioms.

The fourth slice first separates probability-law abstraction from utility
comparisons. `Math.Probability.ObservationAbstraction` contains the generic
laws and supported factorization; `Protocol.ContextTransport` transports the
existing guarded optimality through law coverage. `Protocol.DecisionExperiment`
uses this context over whole response policies. There is no separate Bayesian
equilibrium predicate that silently excludes undefined alternatives. Every
compared alternative retains its expectation-existence obligation, and the
transport covers finite or infinite extended values.

The decision modules now live at `Protocol.DecisionExperiment`,
`Protocol.DecisionPayoff`, and `Protocol.DecisionExperimentTest`; they require
no project Analysis dependency. The validation commands below retain the
module paths used at the original checkpoints.

Narrow validation:

```text
lake build GameTheory.Protocol.ContextTransport
lake build GameTheory.Math.Probability.ObservationAbstraction
lake build GameTheory.Analysis.DecisionExperimentTest
lake build GameTheory GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
```

The necessity argument uses reporting laws rather than numerical reporting
values, eliminating finiteness and decidable-equality assumptions. The erased-bit
consumer refutes law matching for every randomized policy; the unreachable
merge checks that only prior-supported states matter. The infinite-carrier
consumer quantifies over arbitrary priors and utilities on `Bool × ℕ` with
natural-number actions.

The protected-law checkpoint completed all 4,562 integration jobs, lint passed
and the architecture audit reported `VERIFIED=1`. Reporting-law necessity,
universal reporting-law preservation, guarded context coverage, optimal-law
correspondence and the hostile consumers use only standard Lean axioms.

The fixed-payoff checkpoint uses whole-policy guarded context optimality throughout.
`fullInformation_optimal_iff` and its support characterization permit infinite
actions and priors. A policy differing at one supported state proves necessity
by strict expectation improvement, without finite sums or atom arithmetic.
`exists_optimal` only needs a finite nonempty action menu and a utility bound on
prior-supported states. It maximizes each observation fiber's pure-action score;
`Math.Probability.ExpectationCommutation` supplies integrable Fubini on arbitrary
carriers. The existing correlation-interaction consumer now specializes that
lemma rather than repeating the swap-and-tower argument.

`preserves_fixed_payoff_iff_commonMaximizer` is one-way law preservation:
every coarse optimum has an informed match. It does not equate the complete
optimal-law sets. The differing-reward control erases a payoff-relevant bit
while both states prefer the same action; the constant-payoff control exhibits
an informed optimal reporting law that no coarse policy matches. The universal
optimality criterion uses finite reporting actions to prove necessity, with no
finite-state or finite-prior assumption. Atomic reporting values and finite
support expectation sums are independent probability lemmas.

Fixed-payoff validation:

```text
lake build GameTheory.Math.Probability.ExpectationAtoms GameTheory.Math.Probability.ExpectationCommutation GameTheory.Math.Probability.Interaction
lake build GameTheory.Analysis.DecisionExperimentTest
lake build GameTheory GameTheory.LintAll
lake build GameTheory.Analysis.DecisionExperimentTest GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
```

The integration build completed 4,565 jobs. The final consumer and lint-scope
build completed 4,206 jobs; lint passed and the audit reported `VERIFIED=1`.
Reporting atom arithmetic lives in its probability owner, explicitly registered
with the mass-ownership audit; the analytic decision module contains none.
Commutation, full-information/support optimality, finite-menu existence,
fixed-payoff classification, universal-utility necessity and both hostile
controls depend only on the standard Lean axioms.

The sanction checkpoint separates the executable finite rational table from
real correctness. `Math.ScalarInequalities.candidate` is the maximum of zero
and the required ratios from positive slopes; `infer` checks it against every
row. Any nonnegative real solution bounds that candidate below, and reducing
to it preserves all negative-slope upper bounds. Rejection therefore means
no nonnegative real solution exists for this fixed table. Returned values are
least even among real solutions. The checker uses explicit `Finset` rows and
no classical choice or finite-carrier conversion. Its tests cover empty rows,
fractional lower and upper bounds, conflicting signed rows, zero-slope profit,
and negative-only rows; runtime evaluation also returns the fractional result.

Generic real tables characterize eventual feasibility without requiring the
ambient index carrier to be finite. `Analysis.Enforcement` specializes the
result to additional collection probabilities. `Math.Probability.EventPenalty`,
`SoundDetection` and `MonitoredPenalty` own the independent probability and
expected-charge mathematics; canonical comparison bridges remain in Analysis.
The original Boolean payoff calculation via a finite sum simplifies to the
generic event-penalty theorem. Sound alarms are constrained on the full admitted
observation set, which may include the supports of every permitted strategy.
The exact observable criterion assumes automatic collection on an alarm.

`Analysis.Protocol.Sanctions` establishes local sequential rationality from
whole-deviation bounds at the actual assessment continuation laws. It needs
only finite movers, includes collection under the prescribed plan, and does
not construct a monitor or consistent beliefs. Shared mixture preservation
moves to the canonical incentive-comparison owner and replaces finite mixture
support with integrability of the two mixed laws.

Validation:

```text
lake build GameTheory.Math.ScalarInequalitiesCorrectness GameTheory.Math.ScalarInequalitiesTest
lake build GameTheory.Math.Probability.EventPenalty GameTheory.Math.Probability.SoundDetection GameTheory.Math.Probability.MonitoredPenalty
lake build GameTheory.Analysis.EnforcementSynthesis GameTheory.Analysis.ObservableEnforcement GameTheory.Analysis.Protocol.Sanctions
lake build GameTheory.Analysis.EnforcementTest
lake build GameTheory GameTheory.LintAll
lake build GameTheory.Analysis.EnforcementTest GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
```

All 4,576 integration jobs completed. Lint caught one missing alarm-definition
docstring; after adding it, the final 4,215-job consumer/lint-scope build passed
and lint passed. The architecture audit reported `VERIFIED=1`, with PMF mass
arithmetic explicitly owned by its probability and analytic bridge modules.
Soundness, exact rejection, real minimality, eventual feasibility, the incentive
bridge, observable deterrence, the sequential adapter and the mixed controls
use only standard Lean axioms. Hostile consumers verify partial randomized
detection, inevitable-charge cancellation, full-admission obstruction and
mixtures over infinite index carriers.

The component checkpoint defines stochastic strategy substitution once in
`Core.StrategySubstitution`, as a transparent specialization of canonical game
forms. Its mixed play flattens independent component draws and commutes with
canonical profile updates. `Analysis.ComponentCompletion` uses finite Nash for
individual component mixtures and the existing local-choice fixed point for
shared mixture weights. Finite underlying strategies or outcomes are unnecessary:
only utilities under each component profile's actual play law must be integrable.
Continuous importance weights are evaluated at the incumbent profile; group
comparisons sum unilateral member gains, not a simultaneous joint deviation.

The source's dependent casts disappear by updating the group profile before
selecting a member's coordinate. Independent-component existence specializes
finite Nash directly instead of going through existence with shared mixture weights.
`Math.Probability.AggregateComparison` only needs the aggregate comparison at the
common near-best action, permits an aggregate tolerance and nonnegative member
weights, and removes finite-action assumptions in favor of integrability of the
compared means. Unit weights recover the cardinality-times-error bound.
Zero weights do not certify individual rationality. A conflicting-preference
control proves that aggregate optimality alone leaves a profitable member deviation;
the positive consumer uses infinite actions. The game consumers use infinite
natural-number strategies and profile outcomes with globally unbounded utility.

`Analysis.Protocol.PassageBayes` conditions the actual encountered-ancestor law
and stochastic readouts on passage, with only finite movers. The antichain
certificate ensures unique encountered information history. The unequal-depth
consumer simultaneously refutes a common depth and proves the conditioning law.

Validation:

```text
lake build GameTheory.Analysis.ComponentCompletion GameTheory.Math.Probability.AggregateComparisonTest
lake build GameTheory.Analysis.ComponentCompletionTest GameTheory.Analysis.Protocol.PassageBayes
lake build GameTheory GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
```

The integration build completed 4,583 jobs and the architecture audit reported
`VERIFIED=1`, with no new equality transports or unowned mass arithmetic.
Substitution, mixture existence with independent or shared weights, weighted member bounds,
conflicting-preference and infinite-carrier controls, and unequal-depth passage
use only the standard Lean axioms.

The consistent-completion checkpoint adds
`Analysis.Protocol.ComponentCompletion`. Fully supported time-varying components
admit simultaneous shared mixture weights and a common subsequence of fully mixed Bayes
assessments. The limit is sequentially consistent; each convergent component
menu retains its mixture representation. A vanishing member-gain error gives
optimality among that menu's mixtures. Independent agents have exact zero error;
shared mixture weight aggregate optimality alone does not establish member rationality.

The existing free-agent completion theorem now specializes this construction,
removing its separate fixed-point, assessment extraction and gain-limit proof.
Its public statement is unchanged. A full-menu trembling-component consumer
proves sequential-equilibrium existence at the unequal-depth hidden-decision
site. Finite histories remain required by the canonical played-agent enumeration;
the passage-law owner itself still needs only finite movers.

One scoped transparency option addresses Lean's stricter implicit-transparency
check in the aggregate gain rewrite. Ordinary matching failures use explicit law
and value equalities instead. No dependent casts, alternate equilibrium
predicate or new trust assumption is introduced.

Validation:

```text
lake build GameTheory.Analysis.Protocol.AgentCompletion GameTheory.Analysis.Protocol.ComponentCompletionTest
lake build GameTheory GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
lake env lean .codex/scratch/ComponentCompletionAxioms.lean
```

All 4,585 integration jobs passed, including restriction completion and
extension consumers. Lint passed, the architecture audit reported `VERIFIED=1`,
and completion with shared weights, independent completion and free-agent completion plus the unequal-depth
consumer use only the standard Lean axioms. Copied-site approximate simulation
and sequential decision consumers remain the next obligations.

The uniform-policy prerequisite generalizes
`GameTheoryExtensions.Analysis.Protocol.UniformPolicyLimit` to actual terminal
continuations. A fixed site's whole-policy gains have one nonnegative bound
that vanishes along any assessment sequence converging to a rational limit.
Only the deviating player needs countably many actual sites and finite menus.
Finitely many of its sites yield one common bound across those sites. Histories,
the player carrier, other action carriers and unused information values may be
infinite. Terminal-only utility bounds replace finite-history bounds, and the
proof uses well-founded termination rather than a uniform fuel or clock.
Neither recall nor Bayes consistency is required.

The unbounded random-countdown consumer has real-valued raw information states,
no uniform horizon and a nonconstant terminal reward. Every sequence converging
to one of its rational assessments has the asserted uniform regret control;
the sequence need not itself be optimal, fully mixed or Bayesian.

Validation:

```text
lake build GameTheory.Analysis.Protocol.UniformPolicyLimit
lake build GameTheory.Analysis.Protocol.UniformPolicyLimitTest
lake build GameTheory GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
lake env lean .codex/scratch/UniformPolicyLimitAxioms.lean
```

All 4,587 integration jobs passed, lint passed and the architecture audit
reported `VERIFIED=1`. Both uniform bounds and the infinite-history consumer
use only standard Lean axioms. Copied-site transfer remains separate: uniform
source regret does not alone establish target consistency or local comparisons.

The copied-site prerequisite introduces `Analysis.Protocol.LocalSimulationLimit`.
At a consistent finite-history target limit, copied-site gains may be bounded
by vanishing errors while remaining sites are certified directly at the limit.
Errors may depend on player, information site and local law; pointwise error
convergence suffices. Decision recall upgrades limiting single-site optimality
to canonical whole-policy sequential rationality. The approximating assessments
need not be rational or Bayesian when their consistent limit is already given.
A separate existence theorem extracts one common sequential-equilibrium
subsequence from fully mixed Bayes approximants with local gain bounds, assuming
countable players for the existing assessment-compactness interface.

Original-source whole-policy gain mixtures supply the target bounds using
uniform source regret. Source players need finite menus at finitely many actual
sites, with well-founded play and terminal-only bounded utility; source histories
and unused information values may be infinite, and no uniform source horizon is
required. Mixtures may vary with perturbation, copied site and local lottery.
The source and target may have different payoff functions: the required gain
comparison explicitly accounts for that difference. No new optimality predicate,
profile transport, or filtered class of integrable alternatives is introduced.

The observed-terminal-law theorem uses strategy convergence alone, permits different source and target player types, and is independent of rationality and consistency.
It specializes a generic PMF stability lemma: two converging sequences whose
statistical distance vanishes share their limit on arbitrary outcome carriers.
A support-local absolute expectation bound likewise lives in the canonical
probability owner, and simplifies the existing uniform-regret proof.

The cross-protocol consumer uses the actual unbounded random-countdown source
and the unequal-depth hidden-decision target. It proves transfer conditional on
explicit gain-comparison certificates; it does not manufacture a simulation.
The other controls retain arbitrary natural-number noise in a shrinking point-
mass perturbation and allow globally unbounded values outside a law's support.
Weighted-component/copy integration and sequential decision criteria remain
separate obligations.

Validation:

```text
lake build GameTheory.Math.Probability.Expectation
lake build GameTheory.Math.Probability.StatisticalDistanceStability GameTheory.Analysis.Protocol.UniformPolicyLimit
lake build GameTheory.Analysis.Protocol.LocalSimulationLimit
lake build GameTheory GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
lake env lean .codex/scratch/LocalSimulationLimitAxioms.lean
```

The initial full integration and the final strengthened-law build both passed
all 4,589 jobs. Lint passed and the architecture audit reported `VERIFIED=1`.
The support-local expectation bound, distance-limit equality, copied-site gain
limit, source-mixture transfer, local-bound existence, terminal-law matching and
all three controls use only standard Lean axioms. The new module is included in
the explicit lint driver; no probability representation-ownership expansion is
needed because its implementation uses the existing canonical probability APIs.

Copied-site completion with shared mixture weights now composes canonical completion with shared mixture weights
and local gain limits in `Analysis.Protocol.CopiedSiteCompletion`.
Its certificate producer receives the assembled strategy laws, full mixing,
Bayes consistency and aggregate optimality. It must supply vanishing
copied-site gains and individual free-member component gains. Converging free
menus must span every local lottery. The conclusion retains assembled shared mixture
weights, the common assessment subsequence, sequential equilibrium and free-site
mixture representations. Shared mixture weights alone assert no observed-law equality.

The unequal-depth consumer puts all played agents in one weight-sharing group of full profiles.
Projected trembling profile components converge to pure projections, and lifting
a local lottery through canonical profile replacement proves menu spanning.
An arbitrary free/copied classification exercises both proof branches with
constant terminal utility. This checks composition and menu coverage; it does
not construct a nonconstant-payoff simulation certificate.
Validation:

```text
lake build GameTheory.Analysis.Protocol.CopiedSiteCompletion
lake env lean GameTheory/Analysis/Protocol/CopiedSiteCompletionTest.lean
lake build GameTheory GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
lake env lean .codex/scratch/CopiedSiteCompletionAxioms.lean
```

The full integration build passed all 4,591 jobs, lint passed and the
architecture audit reported `VERIFIED=1`. Both the completion theorem and
shared mixture weight control use only standard Lean axioms. The new public module is
included in the explicit lint driver. No new probability representation owner
or transparency option is required.
`Analysis.Protocol.LocalDeviationBounds` recovers the local comparisons needed
to construct certificates. A pure-choice gain bound covers every lottery.
Adding reference weight `epsilon` costs at most
`epsilon * (upper - lower)`, sharpening the source absolute-bound estimate.
Only terminal utility values need lie in that interval; nonterminal values
are unrestricted. Approximate member optimality among full-menu trembling
components then bounds every local gain by the member error plus this cost.
The results use canonical terminal continuation contexts and require neither
Bayesian beliefs nor assessment rationality.

The unequal-depth component consumer now obtains equilibrium through explicit
vanishing copied-site gains, rather than menu optimality at the limit. It
accepts arbitrary terminal utilities in `[0,1]`. Concrete specializations retain
the hidden-bit payoff and strictly reward action `true`: actual legal terminal
histories certify rewards one and zero. Independent member completion supplies
the zero member error. Construction of nonconstant shared mixture weight member bounds,
source simulation comparisons and sequential decision consumers remains pending.
Validation:

```text
lake build GameTheory.Analysis.Protocol.LocalDeviationBounds
lake env lean GameTheory/Analysis/Protocol/ComponentCompletionTest.lean
lake build GameTheory GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
lake env lean .codex/scratch/LocalDeviationBoundsAxioms.lean
```

All 4,592 integration jobs passed, lint passed and the architecture audit
reported `VERIFIED=1`. The three local-bound theorems and all three component
consumer theorems use only standard Lean axioms. The public module is imported
by the explicit lint driver; no new representation owner or transparency option
is needed.
The general API now names shared mixture weights explicitly. Groups tie policy
parameters across decision agents; they do not impose common component laws,
correlated random draws, blockchain structure or information protection.
Aggregate optimality still compares sums of unilateral gains, with separate
member certificates required for sequential rationality. Static completion,
consistent assessment completion and copied-site completion use the same
terminology. The independent probability owner is `Math.Probability.AggregateComparison`.
Old theorem names and the former module path have been removed without aliases;
all in-repository consumers and the lint driver use the current API.
Validation:

```text
lake build GameTheory.Analysis.ComponentCompletion GameTheory.Math.Probability.AggregateComparisonTest
lake build GameTheory GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
lake env lean .codex/scratch/SharedMixtureWeightsAxioms.lean
```

The full integration build passed all 4,592 jobs, lint passed and the
architecture audit reported `VERIFIED=1`. Renamed static completion,
consistent assessment completion, copied-site completion, the concrete shared
weight consumer and the weighted aggregate bound use only standard Lean axioms.
The renamed probability module is included in the lint driver; generated
artifacts of the deleted module and its fixture have been removed.