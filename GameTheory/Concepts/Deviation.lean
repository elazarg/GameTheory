import GameTheory.Concepts.SolutionConcepts

/-!
# GameTheory.Concepts.Deviation

Minimal first-class deviation operators for kernel games.

This file introduces profile-transformers (`Deviation`) and canonical unilateral
deviation constructors, with small algebraic lemmas for reuse.
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- A deviation is a profile transformer. -/
abbrev Deviation (G : KernelGame ι) : Type _ := Profile G → Profile G

/-- Unilateral deviation induced by a recommendation-dependent map. -/
def unilateralDeviation (G : KernelGame ι) [DecidableEq ι] (who : ι)
    (dev : G.Strategy who → G.Strategy who) : Deviation G :=
  fun σ => Function.update σ who (dev (σ who))

/-- Unilateral deviation to a fixed strategy. -/
def constantDeviation (G : KernelGame ι) [DecidableEq ι] (who : ι)
    (s' : G.Strategy who) : Deviation G :=
  fun σ => Function.update σ who s'

/-- Player-`who` EU after applying a deviation to `σ`. -/
noncomputable def euAfterDeviation (G : KernelGame ι) (who : ι)
    (d : Deviation G) (σ : Profile G) : ℝ :=
  G.eu (d σ) who

@[simp] theorem unilateralDeviation_apply (G : KernelGame ι) [DecidableEq ι] (who : ι)
    (dev : G.Strategy who → G.Strategy who) (σ : Profile G) :
    unilateralDeviation G who dev σ = Function.update σ who (dev (σ who)) := rfl

@[simp] theorem constantDeviation_apply (G : KernelGame ι) [DecidableEq ι] (who : ι)
    (s' : G.Strategy who) (σ : Profile G) :
    constantDeviation G who s' σ = Function.update σ who s' := rfl

@[simp] theorem euAfterDeviation_unilateral (G : KernelGame ι) [DecidableEq ι] (who : ι)
    (dev : G.Strategy who → G.Strategy who) (σ : Profile G) :
    G.euAfterDeviation who (G.unilateralDeviation who dev) σ =
      G.eu (Function.update σ who (dev (σ who))) who := rfl

@[simp] theorem euAfterDeviation_constant (G : KernelGame ι) [DecidableEq ι] (who : ι)
    (s' : G.Strategy who) (σ : Profile G) :
    G.euAfterDeviation who (G.constantDeviation who s') σ =
      G.eu (Function.update σ who s') who := rfl

end KernelGame

end GameTheory
