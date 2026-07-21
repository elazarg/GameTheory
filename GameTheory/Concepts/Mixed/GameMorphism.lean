/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.Foundations.GameMorphism

/-!
# Game Morphisms and Independent Mixed Extension

Independent mixed extension transports utility-distribution-preserving game
morphisms by pushing each player's mixed strategy through the underlying
strategy map.  Isomorphism transport is the bijective specialization.
-/

noncomputable section

namespace GameTheory
namespace KernelGame

open Math.PMFProduct

variable {ι : Type} {G H K : KernelGame ι}

/-- A utility-distribution-preserving strategy map lifts through independent
mixed extension by pushforward of each player's probability mass function. -/
noncomputable def Morphism.mixedExtension [Fintype ι] (f : Morphism G H) :
    Morphism G.mixedExtension H.mixedExtension where
  stratMap who μ := μ.map (f.stratMap who)
  udist_preserved := by
    intro σ
    rw [H.mixedExtension_udist, G.mixedExtension_udist, pmfPi_map_bind]
    apply Math.ProbabilityMassFunction.bind_congr_on_support
    intro profile _
    exact f.udist_preserved profile

@[simp]
theorem Morphism.mixedExtension_stratMap [Fintype ι]
    (f : Morphism G H) (who : ι) (μ : PMF (G.Strategy who)) :
    f.mixedExtension.stratMap who μ = μ.map (f.stratMap who) :=
  rfl

@[simp]
theorem Morphism.mixedExtension_id [Fintype ι] :
    (Morphism.id G).mixedExtension = Morphism.id G.mixedExtension := by
  apply Morphism.ext
  intro who μ
  exact PMF.map_id μ

theorem Morphism.mixedExtension_comp [Fintype ι]
    (g : Morphism H K) (f : Morphism G H) :
    (Morphism.comp g f).mixedExtension =
      Morphism.comp g.mixedExtension f.mixedExtension := by
  apply Morphism.ext
  intro who μ
  exact (PMF.map_comp (f.stratMap who) μ (g.stratMap who)).symm

/-- Utility-distribution-preserving game isomorphisms lift through independent
mixed extension.  No boundedness or outcome-finiteness assumption is needed. -/
noncomputable def GameIsomorphism.mixedExtension [Fintype ι]
    (e : GameIsomorphism G H) :
    GameIsomorphism G.mixedExtension H.mixedExtension where
  stratEquiv who :=
    Math.ProbabilityMassFunction.mapEquiv (e.stratEquiv who)
  udist_preserved := e.toMorphism.mixedExtension.udist_preserved

@[simp]
theorem GameIsomorphism.mixedExtension_stratEquiv_apply [Fintype ι]
    (e : GameIsomorphism G H) (who : ι) (μ : PMF (G.Strategy who)) :
    e.mixedExtension.stratEquiv who μ = μ.map (e.stratEquiv who) :=
  rfl

@[simp]
theorem GameIsomorphism.mixedExtension_id [Fintype ι] :
    (GameIsomorphism.id G).mixedExtension =
      GameIsomorphism.id G.mixedExtension := by
  apply GameIsomorphism.ext
  intro who μ
  exact PMF.map_id μ

theorem GameIsomorphism.mixedExtension_comp [Fintype ι]
    (g : GameIsomorphism H K) (e : GameIsomorphism G H) :
    (GameIsomorphism.comp g e).mixedExtension =
      GameIsomorphism.comp g.mixedExtension e.mixedExtension := by
  apply GameIsomorphism.ext
  intro who μ
  exact (PMF.map_comp (e.stratEquiv who) μ (g.stratEquiv who)).symm

@[simp]
theorem GameIsomorphism.mixedExtension_symm [Fintype ι]
    (e : GameIsomorphism G H) :
    e.symm.mixedExtension = e.mixedExtension.symm := by
  apply GameIsomorphism.ext
  intro who μ
  rfl

open Classical in
/-- Relabeling pure strategies preserves Nash equilibrium after independent
mixed extension. -/
theorem GameIsomorphism.mixedExtension_isNash_iff [Fintype ι]
    (e : GameIsomorphism G H) (σ : Profile G.mixedExtension) :
    G.mixedExtension.IsNash σ ↔
      H.mixedExtension.IsNash
        (e.mixedExtension.toEUGameIsomorphism.profileEquiv σ) :=
  e.mixedExtension.toEUGameIsomorphism.nash_iff σ

open Classical in
/-- Isomorphic games have equivalent existence of Nash equilibrium after
independent mixed extension. -/
theorem GameIsomorphism.mixedExtension_exists_isNash_iff [Fintype ι]
    (e : GameIsomorphism G H) :
    (∃ σ : Profile G.mixedExtension, G.mixedExtension.IsNash σ) ↔
      ∃ τ : Profile H.mixedExtension, H.mixedExtension.IsNash τ := by
  let E := e.mixedExtension.toEUGameIsomorphism
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨E.profileEquiv σ, (E.nash_iff σ).mp hσ⟩
  · rintro ⟨τ, hτ⟩
    let σ := E.profileEquiv.symm τ
    refine ⟨σ, (E.nash_iff σ).mpr ?_⟩
    simpa [σ] using hτ

end KernelGame
end GameTheory
