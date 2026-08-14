# D53: Assemble same-depth Bayesian sites into complete-plan learning

- **Status:** adopted for the explicit two-player, two-type Bayesian slice
- **Date:** 2026-08-11
- **Experiment ID:** EXP-091

## Decision

Validate multi-site usefulness with an explicit schedule before freezing a
general dynamics API. For a common-prior two-player Bayesian Protocol, keep one
canonical D46 regret matcher at each positive-probability acting site, update
all four coordinates from one shared behavioral profile, and assemble their
independent laws into one law over complete legal contingent choices.

Apply D50 to complete contingent deviations, not merely to isolated local
actions. Both players' bounds must concern the same plan-profile round law, so
D51 can produce the canonical empirical-marginal `IsεNash` certificate.

## Hostile evidence

The common fair Boolean type gives each player two acting sites, each with
counterfactual reach exactly `1/2`. Matching pennies makes every branch
interactive and payoff-relevant. The explicit recurrence is proved equal to
all four canonical D46 averages, and direct Protocol evaluation identifies
their local counterfactual utilities with prior-weighted matching-pennies
response values.

The complete-choice matrix payoff is exactly the direct Bayesian game's
ex-ante expected utility. D50 controls every fixed complete contingent plan;
D51 then yields approximate mixed Nash for the empirical plan marginals with
tolerance tending to zero. At round zero the complete-plan saddle gap is
exactly `2`.

The experiment also narrowed its original prediction. Under arbitrary
fallbacks, matching pennies need not give both players a strict improvement at
the same type. It does guarantee that at least one player moves at every type,
which is proved. This is the appropriate nonconstant control for an
interactive zero-sum game; requiring four simultaneous strict improvements
would select a separable surrogate instead of testing the intended seam.

## Rejected alternatives and kill conditions

No site has zero mass or irrelevant payoff. The local vectors are evaluated
under the actual shared profile, the player bounds use one round law, and no
regret limit or root decomposition is assumed. The implementation consumes
D50 and D51 directly and defines no second runner, regret, equilibrium, or
generic coupled-state hierarchy.

Direct full-plan regret matching was rejected because it bypasses Protocol
counterfactual analysis. A public schedule abstraction was deferred because a
single same-depth four-site witness does not yet determine the invariants for
unequal depths or arbitrary behavioral replacements.

## Scope and next gate

D53 establishes a useful multi-site workflow: actual Protocol updates produce
one law over complete Bayesian contingent choices and a canonical empirical
Nash guarantee. It is deliberately an explicit test-level scheduler.

Reusable finite schedule synthesis, arbitrary behavioral replacement regret,
and unequal-depth information fibers remain separate architecture gates.

## Validation

- `lake build GameTheory.Analysis.Protocol.BayesianZeroSumLearningTest`
- `lake build GameTheory.Analysis`
- `lake build GameTheory`
- `scripts/phase2-audit.ps1 -VerifyExpected`
- `scripts/phase3-audit.ps1 -VerifyExpected`

The hostile leaf completes a warm build of 2,452 jobs in about 8.7 seconds.
The cached Analysis aggregate completes 3,211 jobs in 3.4 seconds and the
stable package gate completes 3,596 jobs in 3.3 seconds. Both fast audits
report `VERIFIED=1`. Deep reachability was not run.
