# D64: terminal play is the only semantics of sequential rationality

- **Status:** adopted
- **Date:** 2026-09-29
- **Evidence:** [EXP-149](../ExperimentLog.md)

## Decision

Sequential rationality and sequential equilibrium are defined on terminal
play only. `continuationContext certificate` scores a whole replacement policy
by the terminal law of play from the belief, `IsSequentiallyRational` is
optimality in those contexts at every decision site, and
`IsSequentialEquilibrium` adds Kreps-Wilson consistency. The EFG predicate
specializes it. There is no fuel-indexed rationality or equilibrium predicate.

The terminal law is certified by well-foundedness of the successor relation on
histories, not on states. State well-foundedness implies it, and so does a
bounded horizon, which does not imply state well-foundedness because it
permits unreachable cycles. Finite histories supply the certificate.

A continuation context is formed from a continuation runner, the law of the
outcome of play from a history under a profile. The terminal context is one
instance. Play cut off after a fixed number of steps is another,
`truncatedContinuationContext`, kept as a finite-prefix quantity: it
drives the finite existence proof's continuity and one-shot arguments, and a
bounded horizon identifies it with the terminal context. Statements whose
proof never uses the meaning of the continuation are stated over an
arbitrary runner; the preservation criteria for sequential rationality and
sequential equilibrium are such statements.

## Alternatives and mathematical limits

Keeping the fuel predicate primary (D63) left finite existence, the EFG
predicate, and the preservation criteria stated on a predicate that is
sequential rationality only at a sufficient horizon; with less fuel it is
rationality in the truncated game, which can have no equilibrium where the
game does (D61's boundary fixture).

Restating every fuel statement through the horizon identification alone would
add a certificate to the preservation criteria, which hold without one. Stating
them over an arbitrary runner keeps them hypothesis-free and shows they do not
depend on how continuation is computed.

The limit theorems for rationality at arbitrary fuel are not kept. Their
conclusion below the horizon concerns the truncated game. The terminal limit
theorem assumes convergence only at decision sites and bounds only on terminal
payoffs, and needs a history certificate. A runner-generic limit theorem would
need a continuity hypothesis on the runner and has no consumer.

Counterfactual regret and the Bayes continuation value remain horizon-indexed;
this decision does not cover them.

## Admission and rejection criteria

No theorem about sequential rationality or equilibrium may gain a hypothesis:
finite existence must hold with finite histories alone, and the preservation
criteria without a certificate. The truncation boundary must remain
expressible and refuted. The tightness-based existence criterion must stay free
of the fixed-point theorem.

## Evidence and result

Finite existence under decision recall now needs no horizon hypothesis. The
EFG consumers' horizon is proved and their equilibria restate on terminal
play. The boundary fixture has a sequential equilibrium and no assessment
rational against two-step truncation. The preservation criteria hold for
arbitrary source and target runners. These results support the decision.
