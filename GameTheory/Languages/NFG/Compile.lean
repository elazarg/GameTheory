import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Constructions

import GameTheory.Languages.NFG.Syntax
import GameTheory.Core.KernelGame
import GameTheory.Core.GameMorphism
import Math.Probability
import Math.PMFProduct
import GameTheory.Concepts.SolutionConcepts

/-!
# NFG → KernelGame Bridge

Provides:
- `toKernelGame` — bridge to `KernelGame`
- `toKernelGame_outcomeKernel`, `toKernelGame_udist` — bridge equations
- `IsNashPure_iff_kernelGame`, `IsDominant_iff_kernelGame` — bridge theorems
- `MixedProfile`, `toMixedKernelGame`, `IsNashMixed` — mixed strategy Nash
-/

namespace NFG
open Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type} [∀ i, Fintype (A i)]

/-! ## NFG → KernelGame bridge -/

/-- NFG as a kernel-based game. Preserves `Outcome` and `utility`;
    the outcome kernel is the deterministic lift of `outcome`. -/
noncomputable def NFGGame.toKernelGame (G : NFGGame ι A) :
    GameTheory.KernelGame ι where
  Strategy := A
  Outcome := G.Outcome
  utility := G.utility
  outcomeKernel := fun σ => PMF.pure (G.outcome σ)

/-- Outcome-kernel equation for the NFG → KernelGame bridge. -/
@[simp] theorem NFGGame.toKernelGame_outcomeKernel (G : NFGGame ι A) (s : StrategyProfile A) :
    G.toKernelGame.outcomeKernel s = PMF.pure (G.outcome s) := rfl

/-- Pure Nash in NFG is equivalent to Nash in the kernel game. -/
theorem IsNashPure_iff_kernelGame (G : NFGGame ι A) (s : StrategyProfile A) :
    IsNashPure G s ↔ G.toKernelGame.IsNash s := by
  simp only [IsNashPure, GameTheory.KernelGame.IsNash, GameTheory.KernelGame.eu,
      NFGGame.toKernelGame, Math.Probability.expect_pure, deviate]

/-- Dominance in NFG is equivalent to dominance in the kernel game. -/
theorem IsDominant_iff_kernelGame (G : NFGGame ι A) (i : ι) (a : A i) :
    IsDominant G i a ↔ G.toKernelGame.IsDominant i a := by
  simp only [IsDominant, GameTheory.KernelGame.IsDominant, GameTheory.KernelGame.eu,
      NFGGame.toKernelGame, Math.Probability.expect_pure, deviate]

/-- The joint utility distribution of a pure NFG is a point mass. -/
@[simp] theorem NFGGame.toKernelGame_udist (G : NFGGame ι A) (s : StrategyProfile A) :
    G.toKernelGame.udist s = PMF.pure (G.utility (G.outcome s)) := by
  simp [GameTheory.KernelGame.udist, NFGGame.toKernelGame]

/-! ## Mixed strategies -/

/-- A mixed strategy profile: each player independently randomizes over actions. -/
abbrev MixedProfile (A : ι → Type) [∀ i, Fintype (A i)] := ∀ i, PMF (A i)

/-- NFG as a kernel-based game with mixed strategies.
    The outcome kernel maps independent per-player PMFs to a joint distribution
    over pure action profiles via the product PMF construction. -/
noncomputable def NFGGame.toMixedKernelGame
    (G : NFGGame ι A) : GameTheory.KernelGame ι where
  Strategy := fun i => PMF (A i)
  Outcome := G.Outcome
  utility := G.utility
  outcomeKernel := fun σ => (pmfPi σ).bind (fun s => PMF.pure (G.outcome s))

/-- A mixed Nash equilibrium: no player can improve expected payoff by
    changing their marginal distribution. -/
def IsNashMixed (G : NFGGame ι A)
    (σ : MixedProfile A) : Prop :=
  G.toMixedKernelGame.IsNash σ

/-- The pure NFG kernel game embeds into the mixed NFG kernel game: each
pure strategy maps to its Dirac PMF, outcomes are preserved on the nose,
and utilities agree. Built via the `Morphism.ofOutcomeEmbedding` recipe. -/
noncomputable def NFGGame.toMixed_morphism (G : NFGGame ι A) :
    GameTheory.KernelGame.Morphism G.toKernelGame G.toMixedKernelGame :=
  GameTheory.KernelGame.Morphism.ofOutcomeEmbedding
    (stratMap := fun _i s => PMF.pure s)
    (embed := _root_.id)
    (h_outcome := fun σ => by
      change (pmfPi (A := A) (fun i => PMF.pure (σ i))).bind (fun s => PMF.pure (G.outcome s))
        = (PMF.pure (G.outcome σ)).map _root_.id
      rw [pmfPi_pure, PMF.pure_bind, PMF.pure_map]
      rfl)
    (h_util := fun _ω => rfl)

end NFG
