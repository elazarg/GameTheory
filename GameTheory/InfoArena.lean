import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import GameTheory.Probability
import GameTheory.KernelGame

namespace GameTheory

universe u v w

/-- Who controls a state. -/
inductive Turn (ι : Type) where
  | terminal
  | chance
  | player (i : ι)
  deriving DecidableEq

/-- A stochastic transition system with imperfect information,
    where actions are indexed by information sets (so measurability is by construction). -/
structure InfoArena (ι : Type) where
  State : Type v
  root    : State

  -- control / turn structure
  turn    : State → Turn ι

  -- terminal outcomes
  Outcome : Type w
  outcome : {s : State} → turn s = .terminal → Outcome
  utility : Outcome → Payoff ι

  -- information sets per player
  InfoSet : ι → Type v
  info    : ∀ {s i}, turn s = .player i → InfoSet i

  -- actions live at information sets
  Act     : ∀ i, InfoSet i → Type v

  -- transitions
  next    : ∀ {s i}, (hs : turn s = .player i) → Act i (info hs) → State
  chanceK : ∀ {s}, turn s = .chance → PMF State

namespace InfoArena

/-- A behavioral strategy for player `i`: a distribution over actions at each info set. -/
def BehavioralStrategy {ι : Type} (A : InfoArena ι) (i : ι) :=
  ∀ I : A.InfoSet i, PMF (A.Act i I)

/-- A behavioral strategy profile. -/
abbrev BehavioralProfile {ι : Type} (A : InfoArena ι) :=
  ∀ i : ι, BehavioralStrategy A i

/-- A pure strategy for player `i`. -/
def PureStrategy {ι : Type} (A : InfoArena ι) (i : ι) :=
  ∀ I : A.InfoSet i, A.Act i I

/-- A pure strategy profile. -/
abbrev PureProfile {ι : Type} (A : InfoArena ι) :=
  ∀ i : ι, PureStrategy A i

/-- The *process semantics*: given a behavioral profile, you get a distribution on outcomes.
    (Define by recursion/induction on reachable states, or by a kernel over histories.)
    This is the exact abstraction boundary you want for Kuhn. -/
noncomputable def outcomePMF {ι : Type} (A : InfoArena ι) :
    BehavioralProfile A → PMF A.Outcome :=
by
  -- left intentionally abstract: implement using your chosen notion of reachability / unfolding
  classical
  exact fun _σ => by
    -- placeholder so it elaborates; replace with the real definition
    classical
    exact PMF.pure (A.outcome (s := A.root) (by
      -- this proof is generally false; you will replace this whole definition
      -- with a real evaluator. Kept only as a type-correct stub.
      sorry))

/-- The kernel form of the same semantics (handy to align with KernelGame). -/
noncomputable def outcomeKernel {ι : Type} (A : InfoArena ι) :
    Kernel (BehavioralProfile A) A.Outcome :=
by
  classical
  -- A Kernel is just a function `α → PMF β` in your setup (I’m assuming),
  -- so this is the same as `outcomePMF`.
  exact fun σ => A.outcomePMF σ

/-- The induced KernelGame at the same abstraction level as your `KernelGame` core. -/
noncomputable def toKernelGame {ι : Type} [DecidableEq ι] (A : InfoArena ι) :
    KernelGame ι where
  Strategy := fun i => BehavioralStrategy A i
  Outcome := A.Outcome
  utility := A.utility
  outcomeKernel := A.outcomeKernel

end InfoArena

end GameTheory
