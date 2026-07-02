/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Cooperative.MatchingSymmetry
import Mathlib.Data.Fintype.Card

/-!
# Perfect stable matchings in balanced acceptable markets

In a balanced finite two-sided matching market where every cross-side pair is
mutually acceptable, stability forces every agent on both sides to be matched.
-/

namespace GameTheory

namespace MatchingMarket

variable {α β : Type} [Fintype α] [Fintype β] (M : MatchingMarket α β)

/-- If a balanced matching leaves an `α`-agent unmatched, it must leave some
`β`-agent unmatched. -/
theorem exists_unmatched_right_of_unmatched_left
    {μ : α → Option β} (hcard : Fintype.card α = Fintype.card β)
    {a₀ : α} (ha₀ : μ a₀ = none) :
    ∃ b : β, ∀ a : α, μ a ≠ some b := by
  classical
  by_contra h
  push Not at h
  let g : β → α := fun b => Classical.choose (h b)
  have hg : ∀ b : β, μ (g b) = some b := fun b => Classical.choose_spec (h b)
  have hginj : Function.Injective g := by
    intro b₁ b₂ hb
    have hμeq : μ (g b₁) = μ (g b₂) := congrArg μ hb
    rw [hg b₁, hg b₂] at hμeq
    exact Option.some.inj hμeq
  have hnotSurj : ¬ Function.Surjective g := by
    intro hsurj
    obtain ⟨b, hb⟩ := hsurj a₀
    have hcontr := hg b
    rw [hb, ha₀] at hcontr
    contradiction
  have hlt := Fintype.card_lt_of_injective_not_surjective g hginj hnotSurj
  omega

/-- If a balanced matching leaves a `β`-agent unmatched, it must leave some
`α`-agent unmatched. -/
theorem exists_unmatched_left_of_unmatched_right
    {μ : α → Option β} (hμ : IsMatching μ)
    (hcard : Fintype.card α = Fintype.card β) {b₀ : β}
    (hb₀ : ∀ a : α, μ a ≠ some b₀) :
    ∃ a : α, μ a = none := by
  classical
  by_contra h
  push Not at h
  have hsome : ∀ a : α, ∃ b : β, μ a = some b := by
    intro a
    cases hμa : μ a with
    | none => exact False.elim ((h a) hμa)
    | some b => exact ⟨b, rfl⟩
  let f : α → β := fun a => Classical.choose (hsome a)
  have hf : ∀ a : α, μ a = some (f a) := fun a => Classical.choose_spec (hsome a)
  have hfinj : Function.Injective f := by
    intro a₁ a₂ hab
    exact hμ a₁ a₂ (f a₁) (hf a₁) (by rw [hab, hf a₂])
  have hnotSurj : ¬ Function.Surjective f := by
    intro hsurj
    obtain ⟨a, ha⟩ := hsurj b₀
    exact hb₀ a (by rw [hf a, ha])
  have hlt := Fintype.card_lt_of_injective_not_surjective f hfinj hnotSurj
  omega

omit [Fintype α] [Fintype β] in
/-- A stable matching cannot leave a mutually acceptable pair unmatched on both
sides. -/
theorem not_unmatched_acceptable_pair_of_stable
    {μ : α → Option β} (hstable : M.IsStable μ)
    {a : α} {b : β} (ha : μ a = none) (hb : ∀ a' : α, μ a' ≠ some b)
    (hA : M.reserveA a < M.prefA a b) (hB : M.reserveB b < M.prefB b a) :
    False := by
  apply hstable.2.2
  exact ⟨a, b, by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b' hb'
      rw [ha] at hb'
      contradiction
    · intro _
      exact hA
    · intro a' ha'
      exact False.elim (hb a' ha')
    · intro _
      exact hB⟩

omit [Fintype α] [Fintype β] in
/-- Opposed preferences, `α`-side version. If `a` strictly prefers `b` to his
partner `b'` in a stable matching, and `b` is matched to `a'`, then `b` strictly
prefers `a'` to `a`. -/
theorem opposed_preferences
    {μ : α → Option β} (hstable : M.IsStable μ)
    {a a' : α} {b b' : β}
    (hBinj : Function.Injective (M.prefB b))
    (hμa : μ a = some b') (hapref : M.prefA a b' < M.prefA a b)
    (hμb : μ a' = some b) :
    M.prefB b a < M.prefB b a' := by
  by_contra hnot
  have hane : a ≠ a' := by
    intro heq
    subst heq
    rw [hμa] at hμb
    have hbb : b' = b := Option.some.inj hμb
    rw [hbb] at hapref
    exact (lt_irrefl _ hapref)
  have hbpref : M.prefB b a' < M.prefB b a := by
    have hle : M.prefB b a' ≤ M.prefB b a := le_of_not_gt hnot
    refine lt_of_le_of_ne hle ?_
    intro heq
    exact hane (hBinj heq).symm
  apply hstable.2.2
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · intro b'' hb''
    have hb'' : b'' = b' := by
      rw [hμa] at hb''
      exact (Option.some.inj hb'').symm
    rw [hb'']
    exact hapref
  · intro ha_none
    rw [hμa] at ha_none
    contradiction
  · intro a'' ha''
    have ha''eq : a'' = a' := hstable.1 a'' a' b ha'' hμb
    rw [ha''eq]
    exact hbpref
  · intro hb_none
    exact False.elim (hb_none a' hμb)

omit [Fintype α] [Fintype β] in
/-- Opposed preferences, `β`-side version. If `b` strictly prefers `a` to her
partner `a'` in a stable matching, and `a` is matched to `b'`, then `a` strictly
prefers `b'` to `b`. -/
theorem opposed_preferences_women
    {μ : α → Option β} (hstable : M.IsStable μ)
    {a a' : α} {b b' : β}
    (hAinj : Function.Injective (M.prefA a))
    (hμb : μ a' = some b) (hbpref : M.prefB b a' < M.prefB b a)
    (hμa : μ a = some b') :
    M.prefA a b < M.prefA a b' := by
  simpa using
    M.swap.opposed_preferences (M.inverseMatching_isStable hstable) hAinj
      ((inverseMatching_eq_some_iff hstable.1).2 hμb) hbpref
      ((inverseMatching_eq_some_iff hstable.1).2 hμa)

/-- In a balanced market where every cross-side pair is mutually acceptable, any
stable matching is perfect: every agent on both sides is matched. -/
theorem stable_matching_perfect
    {μ : α → Option β} (hstable : M.IsStable μ)
    (hcard : Fintype.card α = Fintype.card β)
    (hA : ∀ a b, M.reserveA a < M.prefA a b)
    (hB : ∀ b a, M.reserveB b < M.prefB b a) :
    (∀ a : α, ∃ b : β, μ a = some b) ∧
      (∀ b : β, ∃ a : α, μ a = some b) := by
  constructor
  · intro a
    cases hμa : μ a with
    | some b => exact ⟨b, rfl⟩
    | none =>
        obtain ⟨b, hb⟩ :=
          exists_unmatched_right_of_unmatched_left (μ := μ) hcard hμa
        exact False.elim
          (M.not_unmatched_acceptable_pair_of_stable hstable hμa hb (hA a b) (hB b a))
  · intro b
    by_contra hbmatched
    push Not at hbmatched
    obtain ⟨a, ha⟩ :=
      exists_unmatched_left_of_unmatched_right (μ := μ) hstable.1 hcard hbmatched
    exact M.not_unmatched_acceptable_pair_of_stable hstable ha hbmatched (hA a b) (hB b a)

/-- The `β`-partner of an `α`-agent in a perfect stable matching. -/
noncomputable def rightPartner
    {μ : α → Option β} (hstable : M.IsStable μ)
    (hcard : Fintype.card α = Fintype.card β)
    (hA : ∀ a b, M.reserveA a < M.prefA a b)
    (hB : ∀ b a, M.reserveB b < M.prefB b a) (a : α) : β :=
  Classical.choose ((M.stable_matching_perfect hstable hcard hA hB).1 a)

/-- The `α`-partner of a `β`-agent in a perfect stable matching. -/
noncomputable def leftPartner
    {μ : α → Option β} (hstable : M.IsStable μ)
    (hcard : Fintype.card α = Fintype.card β)
    (hA : ∀ a b, M.reserveA a < M.prefA a b)
    (hB : ∀ b a, M.reserveB b < M.prefB b a) (b : β) : α :=
  Classical.choose ((M.stable_matching_perfect hstable hcard hA hB).2 b)

theorem match_rightPartner
    {μ : α → Option β} (hstable : M.IsStable μ)
    (hcard : Fintype.card α = Fintype.card β)
    (hA : ∀ a b, M.reserveA a < M.prefA a b)
    (hB : ∀ b a, M.reserveB b < M.prefB b a) (a : α) :
    μ a = some (M.rightPartner hstable hcard hA hB a) :=
  Classical.choose_spec ((M.stable_matching_perfect hstable hcard hA hB).1 a)

theorem match_leftPartner
    {μ : α → Option β} (hstable : M.IsStable μ)
    (hcard : Fintype.card α = Fintype.card β)
    (hA : ∀ a b, M.reserveA a < M.prefA a b)
    (hB : ∀ b a, M.reserveB b < M.prefB b a) (b : β) :
    μ (M.leftPartner hstable hcard hA hB b) = some b :=
  Classical.choose_spec ((M.stable_matching_perfect hstable hcard hA hB).2 b)

/-- The extracted partner maps of a perfect stable matching are inverse to one
another. -/
theorem rightPartner_eq_iff_leftPartner_eq
    {μ : α → Option β} (hstable : M.IsStable μ)
    (hcard : Fintype.card α = Fintype.card β)
    (hA : ∀ a b, M.reserveA a < M.prefA a b)
    (hB : ∀ b a, M.reserveB b < M.prefB b a) {a : α} {b : β} :
    M.rightPartner hstable hcard hA hB a = b ↔
      M.leftPartner hstable hcard hA hB b = a := by
  constructor
  · intro h
    have h₁ : μ a = some b := by
      rw [← h]
      exact M.match_rightPartner hstable hcard hA hB a
    have h₂ : μ (M.leftPartner hstable hcard hA hB b) = some b :=
      M.match_leftPartner hstable hcard hA hB b
    exact hstable.1 (M.leftPartner hstable hcard hA hB b) a b h₂ h₁
  · intro h
    have h₁ : μ a = some b := by
      rw [← h]
      exact M.match_leftPartner hstable hcard hA hB b
    have h₂ : μ a = some (M.rightPartner hstable hcard hA hB a) :=
      M.match_rightPartner hstable hcard hA hB a
    exact (Option.some.inj (h₁.symm.trans h₂)).symm

end MatchingMarket

end GameTheory
