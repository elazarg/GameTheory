/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Foundations.GameMorphism
import GameTheory.Core.GameProperties

/-!
# Welfare Concepts under Game Isomorphism

Expected-utility game isomorphisms preserve Pareto comparisons, Pareto
efficiency, individual rationality, and profile-by-profile social welfare.
-/

namespace GameTheory
namespace KernelGame
namespace EUGameIsomorphism

variable {ι : Type} {G H : KernelGame ι}

/-- Pareto dominance is invariant under expected-utility relabeling. -/
theorem paretoDominates_iff (e : EUGameIsomorphism G H) (σ τ : Profile G) :
    G.ParetoDominates σ τ ↔
      H.ParetoDominates (e.profileEquiv σ) (e.profileEquiv τ) := by
  unfold KernelGame.ParetoDominates
  constructor
  · rintro ⟨hweak, i, hstrict⟩
    refine ⟨fun j => ?_, i, ?_⟩
    · rw [e.eu_profileEquiv, e.eu_profileEquiv]
      exact hweak j
    · rw [e.eu_profileEquiv, e.eu_profileEquiv]
      exact hstrict
  · rintro ⟨hweak, i, hstrict⟩
    refine ⟨fun j => ?_, i, ?_⟩
    · have hj := hweak j
      rw [e.eu_profileEquiv, e.eu_profileEquiv] at hj
      exact hj
    · rw [e.eu_profileEquiv, e.eu_profileEquiv] at hstrict
      exact hstrict

/-- Pareto efficiency is invariant under expected-utility relabeling. -/
theorem isParetoEfficient_iff (e : EUGameIsomorphism G H) (σ : Profile G) :
    G.IsParetoEfficient σ ↔ H.IsParetoEfficient (e.profileEquiv σ) := by
  unfold KernelGame.IsParetoEfficient
  constructor
  · intro h ⟨τ, hτ⟩
    apply h
    refine ⟨e.profileEquiv.symm τ, ?_⟩
    apply (e.paretoDominates_iff (e.profileEquiv.symm τ) σ).mpr
    simpa using hτ
  · intro h ⟨τ, hτ⟩
    apply h
    exact ⟨e.profileEquiv τ, (e.paretoDominates_iff τ σ).mp hτ⟩

/-- Individual rationality transports with the same reservation-utility
vector because player identities are unchanged. -/
theorem isIndividuallyRational_iff (e : EUGameIsomorphism G H)
    (r : ι → ℝ) (σ : Profile G) :
    G.IsIndividuallyRational r σ ↔
      H.IsIndividuallyRational r (e.profileEquiv σ) := by
  unfold KernelGame.IsIndividuallyRational
  constructor <;> intro h i
  · rw [e.eu_profileEquiv]
    exact h i
  · have hi := h i
    rw [e.eu_profileEquiv] at hi
    exact hi

/-- Social welfare is preserved profile-by-profile. -/
theorem socialWelfare_eq [Fintype ι] (e : EUGameIsomorphism G H)
    (σ : Profile G) :
    G.socialWelfare σ = H.socialWelfare (e.profileEquiv σ) := by
  unfold KernelGame.socialWelfare
  apply Finset.sum_congr rfl
  intro who _
  exact (e.eu_preserved σ who).symm

end EUGameIsomorphism
end KernelGame
end GameTheory
