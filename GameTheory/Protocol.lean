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
`Strategic` compiles both state-indexed protocol policies and information-local
pure and behavioral policies into static `GameForm`s. The ordinary mixed
extension of the information-local pure form is exactly the existing mixed
history runner, so compilation introduces no parallel evaluator.
`BehavioralAssessment` pairs local randomization with history-supported
beliefs and states finite Bayes consistency without importing topology.

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
import GameTheory.Protocol.Strategic
import GameTheory.Protocol.BehavioralAssessment
