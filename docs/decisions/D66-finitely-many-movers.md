# D66: behavioral joint laws need finitely many movers, not finitely many players

- **Status:** adopted
- **Date:** 2026-10-01
- **Evidence:** [EXP-157](../ExperimentLog.md)

## Decision

A behavioral profile's joint law after a history is the independent draw of
every player's local choice. Players who need not move have exactly one legal
choice, so their local laws are point masses. The joint law is therefore
`finitaryProduct` over the players who must move: it draws those coordinates
independently and fixes every other coordinate at its unique choice.

Execution protocols carry this capability as the proposition-valued class
`ExecutionProtocol.FiniteMovers`: at every state only finitely many players are
active. Finitely many players supply it by instance, and
`FiniteMovers.of_subsingleton` supplies it for protocols with at most one mover
per state, whatever the player set. The class is a capability on operations and
theorems, never a field of the protocol.

`behavioralJoint_eq_independentProduct` identifies the new joint law with the
independent product over all players when the player set is finite, so
finite-player proofs keep their original shape.

## Alternatives and mathematical limits

An independent product of PMFs over an arbitrary index exists as a PMF exactly
when all but countably many factors are point masses and the remaining ones
concentrate fast enough; a product of infinitely many nondegenerate factors is
nonatomic. Only finitely many movers is the condition that every protocol
consumer can state and check locally. Keeping `[Fintype ι]` on the runner would
exclude every infinite-player sequential game, including those with one mover
per stage.

Mixed profiles, which draw a whole deterministic policy for every player at
once, still need the independent product over all players and keep
`[Fintype ι]`: the Kuhn correspondence, predrawing, strategic realization, and
policy measures. So do counterfactual reach and the results built on its
player-by-player factorization (counterfactual regret, the one-shot deviation
principle, extensive-form perfection, existence). Restating counterfactual
reach as a product over movers would lift those; it is not part of this
decision.

## Admission and rejection criteria

No protocol structure may store the capability. A theorem may take
`[E.FiniteMovers]` only if its proof never reads the joint law as a product
over every player. Finite-player users must not need new arguments.

## Evidence and result

The behavioral runner, history path mass, history events, behavioral
assessments and Bayes beliefs, behavioral continuations and mixtures, terminal
behavioral play, and most sequential-rationality and sequential-equilibrium
declarations compile with `[E.FiniteMovers]`; every
finite-player consumer compiles unchanged. A cascade protocol with the player
set `ℕ` and one mover per stage runs genuinely random behavioral play, which no
finite-player hypothesis admits. These results support the decision.
