/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Foundations.GameMorphism
import GameTheory.Core.GameProperties
import GameTheory.Concepts.Welfare.PriceOfAnarchy
import Math.Reindex

/-!
# Welfare Concepts under Game Isomorphism

Expected-utility game isomorphisms preserve Pareto comparisons, Pareto
efficiency, individual rationality, and profile-by-profile social welfare.
They also preserve optimal welfare, finite best/worst Nash welfare, and the
resulting prices of anarchy and stability.
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

/-- Optimal welfare is invariant under profile relabeling. No finiteness of
the profile space is needed. -/
theorem optimalWelfare_eq [Fintype ι] (e : EUGameIsomorphism G H) :
    G.optimalWelfare = H.optimalWelfare := by
  unfold KernelGame.optimalWelfare
  calc
    (⨆ σ : Profile G, G.socialWelfare σ) =
        ⨆ σ : Profile G, H.socialWelfare (e.profileEquiv σ) := by
      apply iSup_congr
      intro σ
      exact e.socialWelfare_eq σ
    _ = ⨆ τ : Profile H, H.socialWelfare τ :=
      Math.Reindex.iSup_comp_equiv e.profileEquiv _

/-- Best Nash welfare is invariant under game isomorphism. A target Nash
existence witness and target finiteness instance are both derived from the
source. -/
theorem bestNashWelfare_eq [Fintype ι] [DecidableEq ι] [Finite (Profile G)]
    (e : EUGameIsomorphism G H) (hN : ∃ σ : Profile G, G.IsNash σ) :
    letI : Finite (Profile H) := Finite.of_equiv (Profile G) e.profileEquiv
    G.bestNashWelfare hN =
      H.bestNashWelfare ((e.exists_isNash_iff).mp hN) := by
  classical
  letI : Finite (Profile H) := Finite.of_equiv (Profile G) e.profileEquiv
  let hNH : ∃ τ : Profile H, H.IsNash τ := (e.exists_isNash_iff).mp hN
  calc
    G.bestNashWelfare hN =
        ⨆ σ : {σ : Profile G // G.IsNash σ}, G.socialWelfare σ :=
      G.bestNashWelfare_eq_iSup hN
    _ = ⨆ σ : {σ : Profile G // G.IsNash σ},
          H.socialWelfare (e.nashProfileEquiv σ) := by
      apply iSup_congr
      intro σ
      exact e.socialWelfare_eq σ
    _ = ⨆ τ : {τ : Profile H // H.IsNash τ}, H.socialWelfare τ :=
      Math.Reindex.iSup_comp_equiv e.nashProfileEquiv
        (fun τ : {τ : Profile H // H.IsNash τ} => H.socialWelfare τ)
    _ = H.bestNashWelfare hNH := (H.bestNashWelfare_eq_iSup hNH).symm

/-- Worst Nash welfare is invariant under game isomorphism, with the target
witness and finiteness instance transported internally. -/
theorem worstNashWelfare_eq [Fintype ι] [DecidableEq ι] [Finite (Profile G)]
    (e : EUGameIsomorphism G H) (hN : ∃ σ : Profile G, G.IsNash σ) :
    letI : Finite (Profile H) := Finite.of_equiv (Profile G) e.profileEquiv
    G.worstNashWelfare hN =
      H.worstNashWelfare ((e.exists_isNash_iff).mp hN) := by
  classical
  letI : Finite (Profile H) := Finite.of_equiv (Profile G) e.profileEquiv
  let hNH : ∃ τ : Profile H, H.IsNash τ := (e.exists_isNash_iff).mp hN
  calc
    G.worstNashWelfare hN =
        ⨅ σ : {σ : Profile G // G.IsNash σ}, G.socialWelfare σ :=
      G.worstNashWelfare_eq_iInf hN
    _ = ⨅ σ : {σ : Profile G // G.IsNash σ},
          H.socialWelfare (e.nashProfileEquiv σ) := by
      apply iInf_congr
      intro σ
      exact e.socialWelfare_eq σ
    _ = ⨅ τ : {τ : Profile H // H.IsNash τ}, H.socialWelfare τ :=
      Math.Reindex.iInf_comp_equiv e.nashProfileEquiv
        (fun τ : {τ : Profile H // H.IsNash τ} => H.socialWelfare τ)
    _ = H.worstNashWelfare hNH := (H.worstNashWelfare_eq_iInf hNH).symm

/-- Price of anarchy is invariant under expected-utility game isomorphism. -/
theorem priceOfAnarchy_eq [Fintype ι] [DecidableEq ι] [Finite (Profile G)]
    (e : EUGameIsomorphism G H) (hN : ∃ σ : Profile G, G.IsNash σ) :
    letI : Finite (Profile H) := Finite.of_equiv (Profile G) e.profileEquiv
    G.priceOfAnarchy hN =
      H.priceOfAnarchy ((e.exists_isNash_iff).mp hN) := by
  classical
  letI : Finite (Profile H) := Finite.of_equiv (Profile G) e.profileEquiv
  unfold KernelGame.priceOfAnarchy
  rw [e.optimalWelfare_eq, e.worstNashWelfare_eq hN]

/-- Price of stability is invariant under expected-utility game isomorphism. -/
theorem priceOfStability_eq [Fintype ι] [DecidableEq ι] [Finite (Profile G)]
    (e : EUGameIsomorphism G H) (hN : ∃ σ : Profile G, G.IsNash σ) :
    letI : Finite (Profile H) := Finite.of_equiv (Profile G) e.profileEquiv
    G.priceOfStability hN =
      H.priceOfStability ((e.exists_isNash_iff).mp hN) := by
  classical
  letI : Finite (Profile H) := Finite.of_equiv (Profile G) e.profileEquiv
  unfold KernelGame.priceOfStability
  rw [e.optimalWelfare_eq, e.bestNashWelfare_eq hN]

end EUGameIsomorphism
end KernelGame
end GameTheory
