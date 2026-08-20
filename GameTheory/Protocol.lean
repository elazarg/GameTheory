/-
# `GameTheory.Protocol`

The sequential layer: how a game is *played*, as opposed to what its outcome
law is.

An `ExecutionProtocol` carries states, legality, chance, and a run law over
finite-support distributions; `Trace` records histories as data, which is what
makes uniqueness of history a real property rather than a vacuous one.
`History` runs the protocol along those histories, which is what a player
choosing from what it has seen requires, and proves the state law is that law's
pushforward. `Randomized` lets the answer at a history be a law rather than a
single action, with deterministic play as the point-mass case. `Information`
keeps a policy's domain to what its owner can see, by typing rather than by a
side condition, and is where a player's randomness is placed either at each
information state or once over whole policies. `Assessment` packages a typed
choice and continuation as a context; its finite-horizon history context
identifies sequential rationality with information-local one-shot optimality.
`Backward` supplies the well-founded recursion and proves it computes the same
value as the fuelled runner.
`Zermelo` adds the finite-choice perfect-information optimization construction
on that same history semantics, yielding a pure subgame-perfect profile without
introducing a second evaluator.
`Strategic` compiles both state-indexed protocol policies and information-local
pure and behavioral policies into static `GameForm`s. The ordinary mixed
extension of the information-local pure form is exactly the existing mixed
history runner, so compilation introduces no parallel evaluator.
`PolicyMeasure` gives an unbounded behavioral policy its ordinary product
probability law over total pure policies. Its finite marginals reconnect to
the executable predraws, so the same law realizes every covered finite prefix,
including behavioral unilateral replacements, and their summable discounted
consequences. Regularity is operation-local to the standard countable-product
topological hypotheses.
`BehavioralAssessment` pairs local randomization with history-supported beliefs
at reached decision sites, states finite Bayes consistency without importing
topology, and forms continuation contexts from whole replacement policies.
`SubgamePerfect` lifts well-founded backward value to complete histories and
separates textbook subgame perfection over information-set-closed roots from
the stronger historywise continuation predicate.  The latter is equivalent to
information-local one-shot optimality under the same no-revisit condition used
by the behavioral/mixed representation theorem.

`Tree` is the derived finite-first presentation. It is faithful only where no
two players move at once, so it is a convenience for single-mover games rather
than an alternative semantics.
-/

import GameTheory.Protocol.Execution
import GameTheory.Protocol.Tree
import GameTheory.Protocol.Extraction
import GameTheory.Protocol.History
import GameTheory.Protocol.Randomized
import GameTheory.Protocol.Backward
import GameTheory.Protocol.Information
import GameTheory.Protocol.Assessment
import GameTheory.Protocol.SubgamePerfect
import GameTheory.Protocol.Zermelo
import GameTheory.Protocol.Strategic
import GameTheory.Protocol.PolicyMeasure
import GameTheory.Protocol.BehavioralAssessment
