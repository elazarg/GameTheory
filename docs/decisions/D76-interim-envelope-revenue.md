# D76: fixed-law interim incentives and realized revenue

- **Status:** adopted
- **Date:** 2026-10-28
- **Experiment:** EXP-170

## Question and competing designs

Interim payment analysis needs expected allocation and expected payment under
an opponents' law. The choices were an averaging operation returning the
existing single-parameter mechanism, a separate interim-game structure, or a
new pointwise incentive predicate called BIC. EXP-170 validates the first option
using ordinary `IsMaxOn` for the declared type/report interval and canonical
Nash for the actual Bayesian game.

## Ownership and mathematical dependencies

`SingleParameterMechanism.averageOpponents` is one operation on the canonical
owner. It averages allocation and payment after overwriting the sampled own
report. Its law is fixed across true types; it is an independent-types interim
construction, not a substitute for correlated conditional beliefs. Utility
decomposition requests integrability of the actual allocation/payment slices.

The discrete `SingleParameter.Independent` leaf proves the prior resampling
and expectation towers. Actual joint payoff integrability supplies the marginal
integrability guards. `SingleParameter.Bayesian` turns supported-type optimality
against all real reports into truthful Nash of the existing compiled Bayesian
form. No new game, preference, or equilibrium predicate is introduced.

`Math.Envelope` now handles supporting inequalities only on a closed interval,
including its endpoints. It derives monotonicity and local Lipschitz continuity
and specializes back to the global theorem. This removes the global theorem's
redundant monotonicity premise. `Analysis.SingleParameter` supplies interval
payment identity and uniqueness; `Analysis.RevenueEquivalence` applies these to
the averaged mechanism and connects them to realized receipts.

## Scope and kill conditions

Interval-wide optimality includes null types. Supported-type BNE does not
imply this stronger condition, and an interval payment formula cannot be
inferred merely from a discrete prior. For the BNE bridge all real reports are
admissible; the interval envelope and revenue theorem compare reports in the
declared interval. The public statements keep these quantifiers separate.

Revenue equivalence assumes independent type laws, interval-supported own
types, integrable allocation/payment slices on the interval, interval-wide
interim optimality, matching interim allocations, matching lowest-type utility,
and integrable actual joint payments. Its conclusion compares expectations of
the actual sums of payments. No allocation-efficiency or density assumption is
used, and no single-good feasibility claim follows from signed quantities.

Reject the design if it infers interval optimality at null types from BNE,
changes beliefs while treating them as a fixed opponents' law, permits
undefined realized receipts through totalized integration, or needs duplicate
semantic owners. Correlated-belief envelopes and general measurable-type BNE
remain separate work.

## Validation

The positive consumer has expected actual receipts 2 for both mechanisms,
while receipts at the all-two profile are 4 versus 12. The scaled mechanism
fails DSIC and satisfies canonical truthful BNE. Null-type BNE coexists with
failure of interval incentives and payment recovery. The correlated control
identifies both supported conditional laws as the actual posteriors, then
refutes the fixed-belief envelope conclusion when those beliefs vary.
No kill condition fired. Exact commands and integration results are in EXP-170.
