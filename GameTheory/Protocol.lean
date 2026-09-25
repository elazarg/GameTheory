/-
# `GameTheory.Protocol`

The sequential layer: how a game is *played*, as opposed to what its outcome
law is.

An `ExecutionProtocol` carries states, legality, chance, and a run law over
ordinary PMFs; `Trace` records histories as data, which is what
makes uniqueness of history a real property rather than a vacuous one.
`History` runs the protocol along those histories, which is what a player
choosing from what it has seen requires, and proves the state law is that law's
pushforward. `Randomized` lets the answer at a history be a law rather than a
single action, with deterministic play as the point-mass case. `Information`
keeps a policy's domain to what its owner can see, by typing rather than by a
side condition, and is where a player's randomness is placed either at each
information state or once over whole policies. `Assessment` packages a typed
choice and continuation as a context. `InformationOneShot` proves when local
optimality implies whole-policy optimality. `Backward` constructs a terminal
law by well-founded recursion, evaluates it under an integration certificate,
and proves agreement with a runner whose horizon is sufficient for termination.
`Zermelo` adds the finite-choice perfect-information optimization construction
on that same history semantics, yielding a pure subgame-perfect profile without
introducing a second evaluator.
`Strategic` compiles both state-indexed protocol policies and information-local
pure and behavioral policies into static `GameForm`s. The ordinary mixed
extension of the information-local pure form is exactly the existing mixed
history runner, so compilation introduces no parallel evaluator.
`PolicyMeasure` gives an unbounded behavioral policy its ordinary product
probability law over total pure policies. Under the no-revisit condition, the
same measure realizes every bounded behavioral run, including unilateral
replacements and guarded summable discounted consequences. Forward realization
needs no finite site cover; reverse and hybrid results retain their stated
coverage and regularity premises. Measurability remains operation-local.
`BehavioralAssessment` pairs local randomization with history-supported beliefs
at reached decision sites and forms continuation contexts from whole replacement
policies. `BehavioralBayes` normalizes the reach masses of information-history
antichains without importing the project's analytic equilibrium layer.
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
import GameTheory.Protocol.StateKernel
import GameTheory.Protocol.ContinuationLaw
import GameTheory.Protocol.Backward
import GameTheory.Protocol.Information
import GameTheory.Protocol.SingleMover
import GameTheory.Protocol.Predraw
import GameTheory.Protocol.Assessment
import GameTheory.Protocol.SubgamePerfect
import GameTheory.Protocol.Zermelo
import GameTheory.Protocol.Strategic
import GameTheory.Protocol.Continuation
import GameTheory.Protocol.BehavioralContinuation
import GameTheory.Protocol.PolicyMeasure
import GameTheory.Protocol.BehavioralAssessment
import GameTheory.Protocol.BehavioralMixture
