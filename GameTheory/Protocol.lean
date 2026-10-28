module

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
information state or once over whole policies. `OwnPlayRecall` refines any
information model to its coarsest perfect-recall refinement. `Assessment` packages a typed
choice and continuation as a context. `InformationOneShot` proves when local
optimality implies whole-policy optimality. `Backward` constructs a terminal
law by well-founded recursion, evaluates it under an integration certificate,
and proves agreement with a runner whose horizon is sufficient for termination.
`RandomizedBackward` retains complete histories and allows randomized choices;
`HistoryBackward` specializes this terminal law to pure history-dependent play.
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
`DecisionRecall` asks recall only where a player can act, which suffices
wherever recall is used at decisions.
`BehavioralAssessment` pairs local randomization with history-supported beliefs
at reached decision sites and forms continuation contexts from whole replacement
policies. `BehavioralBayes` normalizes the reach masses of information-history
antichains without importing the project's analytic equilibrium layer.
`BehavioralTerminal` scores those contexts by terminal play whenever histories
are well-founded, with integration required on each actual comparison law;
this is the semantics of sequential rationality. Play cut off after a fixed
number of steps agrees with it under a sufficient horizon.
`SubgamePerfect` separates textbook subgame perfection over information-set-closed roots from
the stronger historywise continuation predicate.  The latter is equivalent to
information-local one-shot optimality under the same no-revisit condition used
by the behavioral/mixed representation theorem.

`Tree` is the derived finite-first presentation. It is faithful only where no
two players move at once, so it is a convenience for single-mover games rather
than an alternative semantics.
-/

public import GameTheory.Protocol.Execution
public import GameTheory.Protocol.Tree
public import GameTheory.Protocol.Extraction
public import GameTheory.Protocol.History
public import GameTheory.Protocol.Randomized
public import GameTheory.Protocol.StateKernel
public import GameTheory.Protocol.ContinuationLaw
public import GameTheory.Protocol.Backward
public import GameTheory.Protocol.RandomizedBackward
public import GameTheory.Protocol.HistoryBackward
public import GameTheory.Protocol.Information
public import GameTheory.Protocol.OwnPlayRecall
public import GameTheory.Protocol.SingleMover
public import GameTheory.Protocol.Predraw
public import GameTheory.Protocol.Assessment
public import GameTheory.Protocol.SubgamePerfect
public import GameTheory.Protocol.Zermelo
public import GameTheory.Protocol.Strategic
public import GameTheory.Protocol.Continuation
public import GameTheory.Protocol.BehavioralContinuation
public import GameTheory.Protocol.PolicyMeasure
public import GameTheory.Protocol.BehavioralAssessment
public import GameTheory.Protocol.DecisionRecall
public import GameTheory.Protocol.BehavioralTerminal
public import GameTheory.Protocol.WeakPBE
public import GameTheory.Protocol.BehavioralMixture

@[expose] public section
