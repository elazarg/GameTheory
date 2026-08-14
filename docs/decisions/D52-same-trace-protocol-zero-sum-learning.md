# D52: Assemble two Protocol learners on one zero-sum trace

- **Status:** adopted for the explicit simultaneous one-shot Protocol slice
- **Date:** 2026-08-11
- **Experiment ID:** EXP-090

## Decision

Validate the dynamic composition of D50 and D51 before introducing a general
coupled-learning API. In the existing two-player simultaneous FOSG/Protocol,
run one canonical local counterfactual regret-matching process per player and
assemble their round laws into one `FinDist` over joint pure profiles. Both
players' external-regret identities must concern that same law. Time-average
it once, derive both empirical marginals from it, and feed their uniform
regret bounds directly to D51's canonical `IsεNash` theorem.

The hostile slice remains a test-level assembly. It freezes no universal
learner state, scheduler, exploitability wrapper, or second equilibrium
semantics. The only new reusable matrix theorem is expectation affinity for a
separable payoff `rowValue i - colValue j`.

## Hostile evidence

The regret-matching fallback is deliberately arbitrary. For each Boolean
player, the fixture defines the other action as a strict improvement worth
exactly one. Thus neither the carrier nor a fortunate fallback can trivialize
the run. At round zero each player's canonical external regret for that action
is exactly `1`, and D51 gives a shared-law saddle gap of exactly `2`.

After the first observation, each learned law has strictly positive expected
score whereas its fallback point mass has score zero, so both laws are proved
to change. For every later round, the row and column canonical external
regrets of the same joint law are exactly the two local D50 gains. Their
positive-part time averages converge to zero; finite sums make the bounds
uniform over deviations. D51 then constructs the canonical approximate mixed
Nash profile of the empirical marginals, with tolerance tending to zero.

## Rejected alternatives and kill conditions

Reject unrelated status-quo laws for the two players, an equilibrium or
constant trajectory, a singleton player carrier, assumed regret bounds,
zero-only controls, failure to consume D50 or D51 directly, and any second
Protocol runner, regret, or equilibrium definition. None fired.

A generic coupled learner abstraction was also rejected at this gate: the
experiment establishes the semantic composition point but does not yet expose
the scheduling invariants needed beyond one-shot single-site players.

## Scope and next gate

This decision establishes a useful end-to-end Protocol learning workflow for
one explicit finite simultaneous zero-sum game. It is stronger than static
definition coverage: actual local updates produce one shared empirical law
and a canonical Nash certificate with vanishing tolerance.

It does not synthesize finite schedules for arbitrary Protocols, compare
against arbitrary behavioral replacements, or handle unequal-depth
information fibers. The next architecture gate should use a genuinely
multi-site two-player Protocol to test the reusable scheduling contract before
any public dynamics API is frozen.

## Validation

- `lake build GameTheory.Analysis.ZeroSumLearning`
- `lake build GameTheory.Analysis.Protocol.CounterfactualZeroSumLearningTest`
- `lake build GameTheory.Analysis.Protocol GameTheory.Analysis`
- `lake build GameTheory`
- `scripts/phase2-audit.ps1 -VerifyExpected`
- `scripts/phase3-audit.ps1 -VerifyExpected`

The hostile leaf completes a warm build in about 8.2 seconds and the Analysis
aggregate in about 8.0 seconds. The stable package gate completes 3,595 jobs in
10.5 seconds. Both fast audits report `VERIFIED=1`. Deep reachability was not
run.
