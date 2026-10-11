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
| 5 | Sanction feasibility and synthesis | Planned: incremental collection comparisons and rational least-deposit checker. | Separate executable finite checking from real correctness; signed coefficients where useful. |
| 6 | Component and pooled-agent completion | Planned: generalize prescribed/free agent completion. | Component-mixture optimality, pooled-member conditions and sequential consumers. |

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
