# M-BAYES: single-parameter and Myerson theory

Title: Single-parameter payment algebra and the Myerson Analysis boundary
Family ID: M-BAYES
Pinned roots: `GameTheory/Mechanism/Bayesian/Myerson.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `fea13d4`
Canonical destination: `GameTheory.Mechanism.SingleParameterMechanism`;
envelope theory deferred to a one-way Analysis consumer
Domain contract / decision: D4, D5, D8, D9, D11; EXP-066/D33
Owner: Post-architecture Wave 2 / mature Bayesian-mechanism recovery
Status: partial but fully classified; 38/38 declarations reviewed, with 19
adapted in the stable algebraic leaf and 19 deferred to the Analysis envelope gate
Last verified: 2026-08-08

The source file combines two materially different layers.  Payment-difference
bounds, allocation monotonicity, zero normalization, and implementability are
ordered-ring consequences of canonical DSIC and need no calculus.  The Myerson
payment formula, its sufficiency and uniqueness, and the derivative route from
DSIC require interval integration, continuity, measure theory, or calculus.
The successor keeps the first layer stable and records the second as a named
one-way Analysis obligation rather than importing Analysis into Mechanism.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Mechanism/Bayesian/Myerson.lean` | `SingleParameterMechanism` | structure | adapt | `GameTheory.Mechanism.SingleParameterMechanism` | focused build; quadratic hostile fixture | Uses the canonical single-parameter report signature and stores no capabilities. |
| same | `toSCFWithPayments` | def | adapt | `SingleParameterMechanism.toQuasiLinearMechanism` | D33 integration | Produces the sole quasilinear owner rather than the retired predecessor type. |
| same | `utility` | def | adapt | `SingleParameterMechanism.utility` | strict truthful/deviation values | Same linear value less payment convention. |
| same | `IsDSIC` | def | adapt | `SingleParameterMechanism.IsDSIC` | canonical IC compilation | Transparent specialization, not a second incentive predicate. |
| same | `toSCFWithPayments_utility` | theorem | adapt | `SingleParameterMechanism.toQuasiLinearMechanism_trueUtility` | focused build | Definitional utility bridge. |
| same | `isDSIC_iff` | theorem | adapt | `SingleParameterMechanism.isDSIC_iff` | quadratic proof and negative control | Proves equivalence between canonical fixed-opponent IC and the familiar truthful-profile form. |
| same | `AllocationIsMonotone` | def | adapt | `SingleParameterMechanism.AllocationIsMonotone` | focused build | Uses canonical `Profile.update`. |
| same | `IsMonotone` | def | adapt | `SingleParameterMechanism.IsMonotone` | identity-allocation witness | Transparent specialization to the stored allocation. |
| same | `allocationDiff` | abbrev | adapt | `SingleParameterMechanism.allocationDiff` | numerical payment sandwich | Canonical update replaces the raw function update. |
| same | `paymentDiff` | abbrev | adapt | `SingleParameterMechanism.paymentDiff` | numerical payment sandwich | Same orientation as the predecessor. |
| same | `payment_difference_le_of_isDSIC` | theorem | adapt | same name | focused build | Upper payment-difference bound from canonical DSIC. |
| same | `payment_difference_ge_of_isDSIC` | theorem | adapt | same name | focused build | Opposite IC constraint supplies the lower bound. |
| same | `payment_sandwich` | theorem | adapt | same name | hostile specialization | Standard two-sided single-parameter payment bound. |
| same | `payment_difference_bound` | theorem | adapt | same name | focused build | Same bound with the replacement-oriented difference. |
| same | `isMonotone_of_isDSIC` | theorem | adapt | same name | identity-allocation witness; axiom audit | DSIC implies own-report allocation monotonicity. |
| same | `OwnAllocation` | abbrev | adapt | `SingleParameterMechanism.OwnAllocation` | stable Analysis-facing interface | The one-variable slice itself needs no topology or measure theory. |
| same | `IsEnvelopeIntegrable` | def | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | source import audit | Its statement uses interval integrability and volume. |
| same | `isEnvelopeIntegrable_of_isMonotone` | theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | monotone-integral dependency | Requires Mathlib measure/integration theory. |
| same | `OwnAllocationContinuous` | def | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | source import audit | Continuity belongs in the one-way Analysis consumer. |
| same | `isEnvelopeIntegrable_of_continuous` | theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | source import audit | Converts topology to interval integrability. |
| same | `ZeroNormalized` | def | adapt | `SingleParameterMechanism.ZeroNormalized` | focused build | Algebraic payment normalization stays stable. |
| same | `HasEnvelopeDerivative` | def | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | derivative dependency | The stable mechanism leaf exposes no calculus predicate. |
| same | `slope_bounds_of_isDSIC` | private theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | source import audit | Private slope machinery is recovered only with its derivative consumer. |
| same | `hasEnvelopeDerivative_of_isDSIC_of_continuous` | theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | topology/calculus dependency | DSIC-to-envelope derivative remains a named analytic theorem. |
| same | `endpoint_mul_le_integral` | private theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | source import audit | Private integration bound. |
| same | `integral_le_endpoint_mul` | private theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | source import audit | Private integration bound. |
| same | `myersonPayment` | def | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | interval-integral formula | The definition itself contains an interval integral. |
| same | `withMyersonPayment` | def | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | depends on analytic payment | Constructor follows the analytic definition. |
| same | `myersonPayment_zeroNormalized` | theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | analytic constructor dependency | Kept with the payment formula it simplifies. |
| same | `withMyersonPayment_hasEnvelopeDerivative_of_continuous` | theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | fundamental-calculus dependency | Requires interval-integral differentiation. |
| same | `payment_eq_myersonPayment_of_zeroNormalized_of_hasEnvelopeDerivative` | theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | fundamental-calculus dependency | Payment identity from the envelope derivative. |
| same | `payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized` | theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | derivative and continuity dependency | Exact zero-normalized DSIC payment identity. |
| same | `payment_formula_of_isDSIC_of_zeroNormalized` | theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | interval-integral conclusion | Expanded payment identity. |
| same | `withMyersonPayment_isDSIC_of_isMonotone` | theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | endpoint integral bounds | Analytic sufficiency direction. |
| same | `IsImplementable` | def | adapt | `SingleParameterMechanism.IsImplementable` | quadratic witness | Existential payment vocabulary is algebraic and stable. |
| same | `isMonotone_of_isImplementable` | theorem | adapt | `SingleParameterMechanism.allocationIsMonotone_of_isImplementable` | focused build | Reuses the stable DSIC-to-monotonicity theorem. |
| same | `isImplementable_of_isMonotone` | theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | Myerson payment construction | The converse needs the analytic payment. |
| same | `existsUnique_zeroNormalized_payment_of_isMonotone` | theorem | deferred | D11 / `Analysis.Mechanism.Myerson` envelope gate | full envelope theorem | Existence and uniqueness remain the flagship analytic conclusion. |

## Validation

```text
lake build GameTheory.Mechanism.SingleParameter GameTheory.Tests.SingleParameter GameTheory.Mechanism
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -SkipReachability
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
lake build
```

For a one-player identity allocation, the hostile mechanism charges half the
square of the report.  Completing the square proves canonical DSIC for every
real true type and report; at type two, truthful utility is two while report
zero gives zero.  The payment sandwich is nontrivial and the identity
allocation is implementable and monotone.  With the same allocation but zero
payments, type two profits strictly by reporting three, giving the negative
control.

The 200-nonblank-line stable leaf and 46-nonblank-line fixture build through
the opt-in Mechanism root in 1,752 jobs; the full build completes warning-free
in 3,457 jobs.  Phase 2 structural and exact coverage audits report
`VERIFIED=1`, with 1,969 pinned declarations now accounted for.  Sampled
flagship axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
The Mechanism root exposes the single-parameter owner and payment sandwich,
while the main umbrella continues to reject them.
