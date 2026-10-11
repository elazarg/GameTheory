# VegasCore extension recovery

Recover the reusable theorem families from `../VegasCore/GameTheoryExtensions`
into their canonical GameTheory owners, one validated slice per checkpoint.
Do not introduce an extension compatibility surface or a second definition of
an existing semantic concept. Preserve upstream attribution in `NOTICE`.

| Order | Slice | Status and evidence | Next obligation |
|---|---|---|---|
| 1 | Proportional Bayes transport | Supported: `Analysis.Protocol.BeliefTransport` scales site mass, cancels the multiplier in Bayes beliefs, and derives raw positive mass. Exact transport specializes the proportional theorem. Only finite movers are assumed; history carriers are arbitrary. The tremble reach-ratio consumer and existing restriction-extension consumer compile warning-free. | Terminal passage transport. |
| 2 | Depth-free action restrictions | Supported: canonical restriction-belief, completion and extension APIs use terminal passage, with depth parameters removed and only `Finite` target histories. The asynchronous hidden-decision consumer refutes common depth and preserves terminal play under extension. Structural ancestor existence moves to `Protocol.History`; restriction passage lemmas live in `Protocol.RestrictionExecution`. Event-level conditional domination reuses the existing scalar ratio bound. Full build, lint and architecture audit pass. | Statistical-distance calculus and approximate transport. |
| 3 | Total variation and approximate transport | Supported mathematical slice: the existing half-L1 `statisticalDistance` moves to a dedicated PMF module and equals the uniform event-gap bound. Arbitrary-carrier observation contraction, expected kernel error, support-local payoff-range bounds, domination and discrete convergence are proved. Canonical incentive and continuation contexts bound deviation gain without a new equilibrium predicate. Sample tests and concrete pseudo-Nash transfer improve their constants by two. Full build, lint and architecture audit pass. | Information abstraction next. Copied-site sequential-limit consumers accompany component completion. |
| 4 | Information-abstraction criteria | Protected-law and fixed-payoff slices supported: supported fact recovery transparently specializes Mathlib `Function.FactorsThrough`; conditional averaging preserves arbitrary response laws. Perfect reporting and preservation of all informed reporting laws are equivalent to fact recovery. Guarded terminal-decision optimality specializes canonical contexts, and optimal retained-law sets coincide without finite carriers, finite-support priors or bounded utilities. Consumers cover an erased supported bit, an unreachable merge and infinite carriers. `Analysis.DecisionPayoff` characterizes fixed-payoff preservation by common maximizing actions on supported fibers; a support-local utility bound replaces finite prior support. Only optimum existence and fixed-payoff necessity need finite actions. Universal reporting-utility preservation is equivalent to supported fact recovery for finite facts. | Sequential decision consumers accompany component completion. |
| 5 | Sanction feasibility and synthesis | Supported: independent rational signed-slope inference is sound, complete and minimal against all nonnegative real solutions. Canonical comparison bridges use additional collection risk. Explicit finite tables characterize eventual deterrence, without a finite ambient row type. Sound observable alarms attain exactly the mass outside admitted observations. Sequential rationality specializes the actual continuation context with only finite movers. | Component and pooled-agent completion next. |
| 6 | Component and pooled-agent completion | Static and passage slice supported: canonical stochastic strategy substitution, finite component-menu and pooled best-response existence for arbitrary underlying strategies/outcomes with integrable component plays, weighted approximate member bounds with arbitrary action carriers, and actual-passage Bayes conditioning with only finite movers. | Consistent pooled/component completion and copied-site sequential-limit consumers. |

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
existing guarded optimality through law coverage. `Analysis.DecisionExperiment`
uses this context over whole response policies. There is no separate Bayesian
equilibrium predicate that silently excludes undefined alternatives. Every
compared alternative retains its expectation-existence obligation, and the
transport covers finite or infinite extended values.

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
shared pool weights. Finite underlying strategies or outcomes are unnecessary:
only utilities under each component profile's actual play law must be integrable.
Continuous importance weights are evaluated at the incumbent profile; pool
comparisons sum unilateral member gains, not a simultaneous joint deviation.

The source's dependent casts disappear by updating the pool profile before
selecting a member's coordinate. Independent-component existence specializes
finite Nash directly instead of going through pooled existence.
`Math.Probability.PooledOptimality` only needs the aggregate comparison at the
common near-best action, permits an aggregate tolerance and nonnegative member
weights, and removes finite-action assumptions in favor of integrability of the
compared means. Unit weights recover the cardinality-times-error bound.
Zero weights do not certify individual rationality. A conflicting-preference
control proves that pooled optimality alone leaves a profitable member deviation;
the positive consumer uses infinite actions. The game consumers use infinite
natural-number strategies and profile outcomes with globally unbounded utility.

`Analysis.Protocol.PassageBayes` conditions the actual encountered-ancestor law
and stochastic readouts on passage, with only finite movers. The antichain
certificate ensures unique encountered information history. The unequal-depth
consumer simultaneously refutes a common depth and proves the conditioning law.

Validation:

```text
lake build GameTheory.Analysis.ComponentCompletion GameTheory.Math.Probability.PooledOptimalityTest
lake build GameTheory.Analysis.ComponentCompletionTest GameTheory.Analysis.Protocol.PassageBayes
lake build GameTheory GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
```

The integration build completed 4,583 jobs and the architecture audit reported
`VERIFIED=1`, with no new equality transports or unowned mass arithmetic.
Substitution, individual and pooled mixture existence, weighted member bounds,
conflicting-preference and infinite-carrier controls, and unequal-depth passage
use only the standard Lean axioms.
