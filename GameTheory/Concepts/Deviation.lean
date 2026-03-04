import GameTheory.Core.KernelGame

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
noncomputable def unilateralDeviation (G : KernelGame ι) (who : ι)
    [DecidableEq ι]
    (dev : G.Strategy who → G.Strategy who) : Deviation G :=
  fun σ => Function.update σ who (dev (σ who))

/-- Unilateral deviation to a fixed strategy. -/
noncomputable def constantDeviation (G : KernelGame ι) (who : ι)
    [DecidableEq ι]
    (s' : G.Strategy who) : Deviation G :=
  fun σ => Function.update σ who s'

/-- Player-`who` EU after applying a deviation to `σ`. -/
noncomputable def euAfterDeviation (G : KernelGame ι) (who : ι)
    (d : Deviation G) (σ : Profile G) : ℝ :=
  G.eu (d σ) who

/-- Push a profile distribution through an arbitrary profile deviation map. -/
noncomputable def deviationDistribution (G : KernelGame ι)
    (μ : PMF (Profile G)) (d : Deviation G) : PMF (Profile G) :=
  μ.bind (fun σ => PMF.pure (d σ))

/-- Push through a unilateral recommendation-dependent deviation. -/
noncomputable def unilateralDeviationDistribution (G : KernelGame ι)
    [DecidableEq ι]
    (μ : PMF (Profile G)) (who : ι)
    (dev : G.Strategy who → G.Strategy who) : PMF (Profile G) :=
  G.deviationDistribution μ (G.unilateralDeviation who dev)

/-- Push through a unilateral constant deviation. -/
noncomputable def constantDeviationDistribution (G : KernelGame ι)
    [DecidableEq ι]
    (μ : PMF (Profile G)) (who : ι) (s' : G.Strategy who) : PMF (Profile G) :=
  G.deviationDistribution μ (G.constantDeviation who s')

@[simp] theorem deviationDistribution_apply (G : KernelGame ι)
    (μ : PMF (Profile G)) (d : Deviation G) :
    G.deviationDistribution μ d = μ.bind (fun σ => PMF.pure (d σ)) := rfl

@[simp] theorem deviationDistribution_id (G : KernelGame ι) (μ : PMF (Profile G)) :
    G.deviationDistribution μ _root_.id = μ := by
  simp [deviationDistribution]

end KernelGame

end GameTheory
