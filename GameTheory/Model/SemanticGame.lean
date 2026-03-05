import Math.Probability
import GameTheory.Model.FiniteRecall
import GameTheory.Core.KernelGame

/-!
# GameTheory.Model.SemanticGame

Canonical semantic game object:
- finite-run transition semantics (`step`, `init`)
- profile-indexed outcome distribution
- utility as payoff functional on outcomes

This is the GT-facing layer that consumes `Semantics` primitives while staying
agnostic to concrete game languages (NFG/EFG/MAID/Protocol).
-/

namespace GameTheory

open Math.Probability

structure SemanticGame (ι : Type) where
  Label : Type
  State : Type
  Outcome : Type
  Strategy : ι → Type
  init : State
  step : Label → State → State → Prop
  outcomeKernel : Kernel (∀ i, Strategy i) Outcome
  utility : Outcome → Payoff ι

namespace SemanticGame

variable {ι : Type}

abbrev Profile (G : SemanticGame ι) := ∀ i, G.Strategy i

noncomputable def toKernelGame (G : SemanticGame ι) : KernelGame ι where
  Strategy := G.Strategy
  Outcome := G.Outcome
  utility := G.utility
  outcomeKernel := G.outcomeKernel

/-- Canonical embedding of a distribution-only kernel game into semantic form.
The transition component is intentionally trivial; language compilers may provide
richer `step`/`State` semantics when needed. -/
noncomputable def ofKernelGame (G : KernelGame ι) : SemanticGame ι where
  Label := PUnit
  State := PUnit
  Outcome := G.Outcome
  Strategy := G.Strategy
  init := PUnit.unit
  step := fun _ _ _ => True
  outcomeKernel := G.outcomeKernel
  utility := G.utility

@[simp] theorem toKernelGame_ofKernelGame (G : KernelGame ι) :
    (ofKernelGame G).toKernelGame = G := by
  cases G
  rfl

/-- Semantic finite-trace perfect recall schema for `G` under explicit local
information/projection interfaces. -/
def PerfectRecall
    (G : SemanticGame ι)
    (TraceView : ι → Type)
    (infoEq : (i : ι) → G.State → G.State → Prop)
    (project : (i : ι) → List G.Label → TraceView i) : Prop :=
  Model.FiniteRecall.PerfectRecall G.step G.init TraceView infoEq project

/-- Bounded finite-trace perfect recall schema for `G`. -/
def PerfectRecallUpTo
    (k : Nat)
    (G : SemanticGame ι)
    (TraceView : ι → Type)
    (infoEq : (i : ι) → G.State → G.State → Prop)
    (project : (i : ι) → List G.Label → TraceView i) : Prop :=
  Model.FiniteRecall.PerfectRecallUpTo k G.step G.init TraceView infoEq project

end SemanticGame

end GameTheory
