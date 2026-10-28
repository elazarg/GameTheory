# D75: single-parameter integration extends the canonical mechanism

- **Status:** adopted
- **Date:** 2026-10-28
- **Experiment:** EXP-169

## Question and competing designs

The stable single-parameter algebra already has canonical DSIC, a payment
sandwich, and allocation monotonicity. Its analytic continuation could use
direct own-report slices and general scalar integration lemmas, adopt
MathEconLib's bundled scalar-choice problem, or wait for a measurable-game core.

Adopt direct slices. No additional economic data or incentive definition is
needed. `SingleParameterMechanism.OwnAllocation` is the existing scalar slice,
and `IsDSIC` remains the canonical quasilinear incentive predicate. Scalar
integration is an operation on an existing mechanism, not a new game semantics.

## Representative slice and kill conditions

EXP-169 tests signed, globally unbounded identity quantities with quadratic
payments; a discontinuous allocation taking values -1 and 3 with nonzero
baseline charges; and two-player payments depending on an opponent's report.
The wrong zero-payment rule has monotone allocation but fails the new DSIC
characterization. Atomic and diffuse type laws consume the expected-payment
identity; mapped arbitrary natural-number laws require no finite support.

Reject the direct design if it needs stored probability/analytic capabilities,
a duplicate DSIC predicate, allocation probabilities restricted to `[0,1]`, or
continuous-game semantics merely to integrate a scalar payment. None occurs.

## Measurements and mathematical reuse

The semantic extension adds zero structures or definitions. One topology-free
slice-monotonicity theorem extends the existing mechanism leaf. Independent
mathematics lives in `Math.Envelope` and `Math.Probability.TailIntegral`;
`Analysis.SingleParameter` is their economic consumer. The latter is an
explicit import and is also exported by the analytic umbrella. Neither
`Mechanism` nor the lightweight `GameTheory` umbrella imports it back.

Mathlib's convex continuity theorem and fundamental theorem off a countable
set replace the bundled bounds and Lipschitz infrastructure in the external
proof. The derivative argument adapts MathEconLib at the revision recorded in
[the comparison](../MathEconLibComparison.md), retaining attribution.
The tail identity is a direct Fubini proof for signed interval-integrable
functions under finite measures. It needs no chosen density, atomlessness,
nonnegative allocation, or globally measurable integrand hypothesis.

## Consequences and limits

Canonical DSIC now yields utility and payment integral identities and payment
uniqueness after fixing one baseline charge. Monotonicity plus the payment
formula characterizes DSIC against every real report; monotone allocation is
equivalent to the existing existential implementability predicate.

Finite interval support supplies actual-law payment integrability. A scalar
probability measure gives the tail-weighted expected-payment identity; the
PMF theorem uses the existing measure/expectation bridge and permits infinite
support. Opponents' reports are held fixed in these statements. Integrating
over opponents, interim/BIC envelopes, revenue equivalence, optimal auction
design, and unrestricted type laws remain separate results.

[D76](D76-interim-envelope-revenue.md) subsequently delivers the independent
discrete interim and realized-revenue chain through the same owner, preserving
the distinction between interval-wide incentives and supported-type BNE.

## Validation

Focused builds and the integration audit are recorded in EXP-169.
