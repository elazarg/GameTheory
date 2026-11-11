# D79: ordinal response uses guarded comparisons and finite-range ranks

- **Status:** adopted for the response-to-existence slice.
- **Date:** 2026-11-11
- **Experiment:** EXP-174

## Question and alternatives

Can response dynamics and strict Nash shed expected utility without changing
their numerical meaning? Compare distinct-deviation strictness alone with
strictness plus incumbent self-comparison. For existence, compare a new
ordinal-potential structure with direct hypotheses on an improvement rank.

Choose the guarded relation definitions and direct rank theorems. No new
problem, preference, potential, or certificate structure is needed.

## What the evidence decides

Strict Nash requires each player to accept the incumbent law and strictly
prefer it to every genuine unilateral replacement. The incumbent comparison
is essential when a strategy carrier is a singleton: the alternative-only
clause is vacuous even for a relation rejecting every law. The fixture proves
both that vacuity and failure of guarded strict Nash.

Improvement is the strict part of the same law preference, applied to the
target and source laws of one canonical profile update. The expected-utility
characterizations recover the original predicates exactly, including
definedness of all compared extended expectations and their possibly infinite
values. Strict Nash implies ordinary Nash without assuming reflexivity or
totality globally; approximate numerical Nash then follows through that theorem.

Failure of weak-form Nash yields a strict improving step only when the
incumbent and each unilateral alternative are comparable. Equality of laws
supplies a partial-preference counterexample: Nash fails while no strict
improvement exists. Local comparability is therefore explicit on the
termination theorem. It imposes no preference laws on unrelated outcome laws,
which matters when those laws have undefined expected utility.

A finite-range rank strictly increasing along improvement steps makes their
reverse relation well-founded. Only a preorder on rank values is needed.
Combining this fact with local comparability gives weak acyclicity, then Nash
existence for nonempty profiles. Finiteness is required of the rank range,
not of profiles. The existing countably infinite strategy fixture traverses
this generic proof; numerical potential and congestion consumers still compile.

The possibility-based fixture ranks lotteries by whether true is possible.
A fair lottery is equivalent to sure true, while sure false is strictly worse.
A proved contradiction with expectation linearity rules out every real
expected-utility representation of this relation. Its strict Nash, improving
edge, and natural-number rank consume the generalized API.

## Ownership and cost

Response owns strict Nash, improving steps, weak acyclicity, their guarded
numerical characterizations, and well-foundedness-to-weak-acyclicity.
Potential owns the finite-range rank consequences and the existing numerical
exact/ordinal certificates. The latter retain their integrability assumptions
and specialize the generic existence and termination arguments.

The added rank helpers have separate consumers: numerical well-foundedness,
nonnumeric weak acyclicity, and numerical finite-range existence. Existing
response definitions are generalized in place; there is no parallel engine.
The alternative-only strictness candidate is machine-refuted, so its shorter
syntax does not justify admission. A new bundled potential candidate was not
implemented: direct hypotheses already serve the existing numerical and
nonnumeric consumers, and no missing reusable operation justified a record. No timing or cold-cost advantage is claimed,
and no bundled abstraction is admitted on amortized client-size arguments.

## Validation and limits

Baseline: `4d2bb891`; implementation checkpoint: `3678492f`.
Focused strict builds cover ExpectedUtility, Response, Approximate, Potential,
Tests.Potential, and Congestion.Rosenthal. The source audit passes. The full
integration result is recorded in EXP-174 and the delivery ledger; raw output
is ignored `.codex/scratch/exp174/integration-audit.log`.

This does not generalize the numerical exact/ordinal-potential certificates,
properness, ESS, or arbitrary arena representations. It does not identify
absence of strict improvement with weak Nash for incomparable alternatives,
nor replace the canonical local law-linear deviation schemes. Item 03 must
separately investigate closure under binary, finite, and arbitrary PMF mixtures.

Full validation passed: `python scripts/audit.py` completed the default strict
build (3,872 jobs), complete validation build (4,762 jobs), public lint,
cached authored diagnostic checks, and transitive standard-axiom checking.
