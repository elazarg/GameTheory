/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.GameMorphism
import GameTheory.Concepts.Equilibrium.SolutionConcepts

/-!
# Solution-Concept Corollaries for Game Morphisms

The morphism structures live in `GameTheory.Core.GameMorphism`. This file adds
Nash, dominance, best-response, and (weak/strict) dominates transport
theorems, which depend on solution concepts.

Every `EUGameIsomorphism` corollary here (`nash_iff`, `dominant_iff`,
`isBestResponse_iff`, `weaklyDominates_iff`, `strictlyDominates_iff`,
`isStrictNash_iff`, `isStrictDominant_iff`) reduces to a single fact,
`eu_update_preserved` (updating one player's strategy commutes with the
isomorphism), composed with generic quantifier reindexing along the
per-player bijection `e.stratEquiv who` and the induced profile bijection
`e.profileEquiv`. No solution concept keeps a bespoke transfer argument.
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

private theorem map_profile_update [DecidableEq ι]
    {A B : ι → Type*} (f : ∀ i, A i → B i)
    (σ : ∀ i, A i) (who : ι) (s' : A who) :
    (fun i => f i (Function.update σ who s' i)) =
      Function.update (fun i => f i (σ i)) who (f who s') := by
  funext j
  simpa using
    (Function.apply_update (f := f) (g := σ) (i := who) (v := s') (j := j))

/-- EU corollary: if a morphism preserves EU values, Nash pulls back. -/
theorem EUMorphism.nash_of_nash [DecidableEq ι]
    {G H : KernelGame ι} (f : EUMorphism G H)
    {σ : Profile G}
    (hN : H.IsNash (fun i => f.stratMap i (σ i))) :
    G.IsNash σ := by
  intro who s'
  have h := hN who (f.stratMap who s')
  have h1 := f.eu_preserved σ who
  have h2 : H.eu (Function.update (fun i => f.stratMap i (σ i)) who (f.stratMap who s')) who =
      G.eu (Function.update σ who s') who := by
    simpa [map_profile_update (f := f.stratMap) σ who s'] using
      f.eu_preserved (Function.update σ who s') who
  linarith

namespace EUGameIsomorphism

variable {G H : KernelGame ι}

/-- The profile-level bijection induced by an isomorphism's per-player
strategy equivalences. -/
noncomputable def profileEquiv (e : EUGameIsomorphism G H) : Profile G ≃ Profile H :=
  Equiv.piCongrRight e.stratEquiv

@[simp] theorem profileEquiv_apply (e : EUGameIsomorphism G H) (σ : Profile G) (i : ι) :
    e.profileEquiv σ i = e.stratEquiv i (σ i) := rfl

@[simp] theorem profileEquiv_symm_apply (e : EUGameIsomorphism G H)
    (τ : Profile H) (i : ι) :
    e.profileEquiv.symm τ i = (e.stratEquiv i).symm (τ i) := rfl

/-- Expected utility is preserved at the bundled profile equivalence. -/
@[simp] theorem eu_profileEquiv (e : EUGameIsomorphism G H)
    (σ : Profile G) (who : ι) :
    H.eu (e.profileEquiv σ) who = G.eu σ who :=
  e.eu_preserved σ who

@[simp] theorem profileEquiv_id (G : KernelGame ι) :
    (EUGameIsomorphism.id G).profileEquiv = Equiv.refl (Profile G) := by
  apply Equiv.ext
  intro σ
  rfl

@[simp] theorem profileEquiv_symm (e : EUGameIsomorphism G H) :
    e.symm.profileEquiv = e.profileEquiv.symm := by
  apply Equiv.ext
  intro σ
  rfl

theorem profileEquiv_comp {K : KernelGame ι}
    (g : EUGameIsomorphism H K) (e : EUGameIsomorphism G H) :
    (EUGameIsomorphism.comp g e).profileEquiv =
      e.profileEquiv.trans g.profileEquiv := by
  apply Equiv.ext
  intro σ
  rfl

/-- Relabeling a profile commutes with a unilateral strategy update. -/
@[simp] theorem profileEquiv_update [DecidableEq ι]
    (e : EUGameIsomorphism G H) (σ : Profile G) (who : ι)
    (s : G.Strategy who) :
    e.profileEquiv (Function.update σ who s) =
      Function.update (e.profileEquiv σ) who (e.stratEquiv who s) := by
  funext j
  rcases eq_or_ne j who with rfl | hne
  · simp
  · simp [Function.update_of_ne hne]

/-- Inverse profile relabeling also commutes with unilateral updates. -/
@[simp] theorem profileEquiv_symm_update [DecidableEq ι]
    (e : EUGameIsomorphism G H) (τ : Profile H) (who : ι)
    (s : H.Strategy who) :
    e.profileEquiv.symm (Function.update τ who s) =
      Function.update (e.profileEquiv.symm τ) who ((e.stratEquiv who).symm s) := by
  have h := e.symm.profileEquiv_update τ who s
  change e.profileEquiv.symm (Function.update τ who s) =
    Function.update (e.profileEquiv.symm τ) who ((e.stratEquiv who).symm s) at h
  exact h

/-- Reindex profile-dependent data along a game isomorphism. This is an
equivalence, not merely a forward transport operation. -/
noncomputable def profileFunctionEquiv {α : Sort*}
    (e : EUGameIsomorphism G H) :
    (Profile G → α) ≃ (Profile H → α) :=
  e.profileEquiv.arrowCongr (Equiv.refl α)

@[simp] theorem profileFunctionEquiv_apply {α : Sort*}
    (e : EUGameIsomorphism G H) (f : Profile G → α) (τ : Profile H) :
    e.profileFunctionEquiv f τ = f (e.profileEquiv.symm τ) := rfl

@[simp] theorem profileFunctionEquiv_apply_profileEquiv {α : Sort*}
    (e : EUGameIsomorphism G H) (f : Profile G → α) (σ : Profile G) :
    e.profileFunctionEquiv f (e.profileEquiv σ) = f σ := by
  simp

@[simp] theorem profileFunctionEquiv_apply_update [DecidableEq ι] {α : Sort*}
    (e : EUGameIsomorphism G H) (f : Profile G → α) (σ : Profile G)
    (who : ι) (s : G.Strategy who) :
    e.profileFunctionEquiv f
        (Function.update (e.profileEquiv σ) who (e.stratEquiv who s)) =
      f (Function.update σ who s) := by
  rw [← profileEquiv_update, profileFunctionEquiv_apply_profileEquiv]

@[simp] theorem profileFunctionEquiv_id {α : Sort*} (G : KernelGame ι) :
    EUGameIsomorphism.profileFunctionEquiv (α := α) (EUGameIsomorphism.id G) =
      Equiv.refl (Profile G → α) := by
  rw [profileFunctionEquiv, profileEquiv_id]
  rfl

@[simp] theorem profileFunctionEquiv_symm {α : Sort*}
    (e : EUGameIsomorphism G H) :
    EUGameIsomorphism.profileFunctionEquiv (α := α) e.symm =
      e.profileFunctionEquiv.symm := by
  rw [profileFunctionEquiv, profileEquiv_symm]
  change e.profileEquiv.symm.arrowCongr (Equiv.refl α) =
    (e.profileEquiv.arrowCongr (Equiv.refl α)).symm
  rw [Equiv.arrowCongr_symm]
  rfl

theorem profileFunctionEquiv_comp {K : KernelGame ι} {α : Sort*}
    (g : EUGameIsomorphism H K) (e : EUGameIsomorphism G H) :
    EUGameIsomorphism.profileFunctionEquiv (α := α) (EUGameIsomorphism.comp g e) =
      e.profileFunctionEquiv.trans g.profileFunctionEquiv := by
  rw [profileFunctionEquiv, profileEquiv_comp]
  change (e.profileEquiv.trans g.profileEquiv).arrowCongr (Equiv.refl α) =
    (e.profileEquiv.arrowCongr (Equiv.refl α)).trans
      (g.profileEquiv.arrowCongr (Equiv.refl α))
  rw [← Equiv.arrowCongr_trans]
  rfl

/-- **The atomic fact underlying every solution-concept transport in this
file.** Updating a single player's strategy commutes with the isomorphism:
the EU of a target profile obtained by updating the realized source profile
at `who` to the realized strategy `e.stratEquiv who s` equals the EU of the
corresponding source update. Nash, dominance, best response, and their
strict/weak variants are all `∀`-shaped statements built from exactly this
comparison, so every corollary below reduces to this one lemma plus
reindexing the relevant quantifiers along `e.stratEquiv who` (strategies) or
`e.profileEquiv` (profiles). -/
theorem eu_update_preserved [DecidableEq ι] (e : EUGameIsomorphism G H)
    (σ : Profile G) (who : ι) (s : G.Strategy who) :
    H.eu (Function.update (e.profileEquiv σ) who (e.stratEquiv who s)) who =
      G.eu (Function.update σ who s) who := by
  rw [← e.profileEquiv_update]
  exact e.eu_preserved (Function.update σ who s) who

/-- EU corollary: best response is preserved in both directions. Every
target-side alternative `s'' : H.Strategy who` is matched by the source-side
alternative `(e.stratEquiv who).symm s''`, and the comparison itself is
`eu_update_preserved` applied at `s` and at that alternative. -/
theorem isBestResponse_iff [DecidableEq ι] (e : EUGameIsomorphism G H)
    (who : ι) (σ : Profile G) (s : G.Strategy who) :
    G.IsBestResponse who σ s ↔
      H.IsBestResponse who (e.profileEquiv σ) (e.stratEquiv who s) := by
  unfold KernelGame.IsBestResponse
  refine (e.stratEquiv who).forall_congr' (fun s'' => ?_)
  rw [← e.eu_update_preserved σ who s,
    ← e.eu_update_preserved σ who ((e.stratEquiv who).symm s'')]
  simp

/-- EU corollary: Nash is preserved in both directions. `IsNash σ` says every
player's own move is already a best response to it, so at each player this is
`eu_update_preserved` applied both at the player's current move (to rewrite
the "no deviation" baseline) and at the candidate alternative. -/
theorem nash_iff [DecidableEq ι] (e : EUGameIsomorphism G H) (σ : Profile G) :
    G.IsNash σ ↔ H.IsNash (e.profileEquiv σ) := by
  unfold KernelGame.IsNash
  refine forall_congr' fun who => (e.stratEquiv who).forall_congr' fun s'' => ?_
  have hcur : H.eu (e.profileEquiv σ) who = G.eu σ who := by
    have h := e.eu_update_preserved σ who (σ who)
    rwa [← profileEquiv_apply, Function.update_eq_self, Function.update_eq_self] at h
  rw [hcur, ← e.eu_update_preserved σ who ((e.stratEquiv who).symm s'')]
  simp

/-- EU corollary: dominance is preserved in both directions. `IsDominant who
s` universally quantifies over both the ambient profile and the alternative,
so this reindexes profiles along `e.profileEquiv` and, at each profile,
strategies along `e.stratEquiv who`. -/
theorem dominant_iff [DecidableEq ι] (e : EUGameIsomorphism G H)
    (who : ι) (s : G.Strategy who) :
    G.IsDominant who s ↔ H.IsDominant who (e.stratEquiv who s) := by
  unfold KernelGame.IsDominant
  refine e.profileEquiv.forall_congr' fun τ => (e.stratEquiv who).forall_congr' fun s'' => ?_
  rw [← e.eu_update_preserved (e.profileEquiv.symm τ) who s,
    ← e.eu_update_preserved (e.profileEquiv.symm τ) who ((e.stratEquiv who).symm s'')]
  simp

/-- EU corollary: weak dominance is preserved in both directions. Unlike
`IsDominant`, the alternative strategy `t` is fixed rather than universally
quantified, so only the ambient profile needs reindexing, along
`e.profileEquiv`. -/
theorem weaklyDominates_iff [DecidableEq ι] (e : EUGameIsomorphism G H)
    (who : ι) (s t : G.Strategy who) :
    G.WeaklyDominates who s t ↔
      H.WeaklyDominates who (e.stratEquiv who s) (e.stratEquiv who t) := by
  unfold KernelGame.WeaklyDominates
  refine e.profileEquiv.forall_congr' (fun τ => ?_)
  rw [← e.eu_update_preserved (e.profileEquiv.symm τ) who s,
    ← e.eu_update_preserved (e.profileEquiv.symm τ) who t]
  simp

/-- EU corollary: strict dominance is preserved in both directions, the
strict analogue of `weaklyDominates_iff`. -/
theorem strictlyDominates_iff [DecidableEq ι] (e : EUGameIsomorphism G H)
    (who : ι) (s t : G.Strategy who) :
    G.StrictlyDominates who s t ↔
      H.StrictlyDominates who (e.stratEquiv who s) (e.stratEquiv who t) := by
  unfold KernelGame.StrictlyDominates
  refine e.profileEquiv.forall_congr' (fun τ => ?_)
  rw [← e.eu_update_preserved (e.profileEquiv.symm τ) who s,
    ← e.eu_update_preserved (e.profileEquiv.symm τ) who t]
  simp

/-- EU corollary: strict Nash is preserved in both directions. The extra
`s'' ≠ σ who` side condition transfers along the bijection `e.stratEquiv who`
via its injectivity. -/
theorem isStrictNash_iff [DecidableEq ι] (e : EUGameIsomorphism G H) (σ : Profile G) :
    G.IsStrictNash σ ↔ H.IsStrictNash (e.profileEquiv σ) := by
  unfold KernelGame.IsStrictNash
  refine forall_congr' fun who => (e.stratEquiv who).forall_congr' fun s'' => ?_
  have hne : ((e.stratEquiv who).symm s'' ≠ σ who) ↔ (s'' ≠ e.profileEquiv σ who) := by
    simp [profileEquiv_apply, Equiv.symm_apply_eq]
  rw [hne]
  refine imp_congr_right (fun _ => ?_)
  have hcur : H.eu (e.profileEquiv σ) who = G.eu σ who := by
    have h := e.eu_update_preserved σ who (σ who)
    rwa [← profileEquiv_apply, Function.update_eq_self, Function.update_eq_self] at h
  rw [hcur, ← e.eu_update_preserved σ who ((e.stratEquiv who).symm s'')]
  simp

/-- EU corollary: strict dominance (as a strategy property) is preserved in
both directions, the strict analogue of `dominant_iff`. -/
theorem isStrictDominant_iff [DecidableEq ι] (e : EUGameIsomorphism G H)
    (who : ι) (s : G.Strategy who) :
    G.IsStrictDominant who s ↔ H.IsStrictDominant who (e.stratEquiv who s) := by
  unfold KernelGame.IsStrictDominant
  refine e.profileEquiv.forall_congr' fun τ => (e.stratEquiv who).forall_congr' fun s'' => ?_
  have hne : ((e.stratEquiv who).symm s'' ≠ s) ↔ (s'' ≠ e.stratEquiv who s) := by
    simp [Equiv.symm_apply_eq]
  rw [hne]
  refine imp_congr_right (fun _ => ?_)
  rw [← e.eu_update_preserved (e.profileEquiv.symm τ) who s,
    ← e.eu_update_preserved (e.profileEquiv.symm τ) who ((e.stratEquiv who).symm s'')]
  simp

end EUGameIsomorphism

end KernelGame

end GameTheory
