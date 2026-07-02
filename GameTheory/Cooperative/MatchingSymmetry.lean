/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Cooperative.Matching

/-!
# Side symmetry for two-sided matching markets

This file packages the operation that swaps the two sides of a matching market
and inverts an `Option`-encoded matching.
-/

namespace GameTheory

namespace MatchingMarket

variable {α β : Type}

/-- Swap the two sides of a matching market. -/
def swap (M : MatchingMarket α β) : MatchingMarket β α where
  prefA := M.prefB
  prefB := M.prefA
  reserveA := M.reserveB
  reserveB := M.reserveA

@[simp] theorem swap_swap (M : MatchingMarket α β) : M.swap.swap = M := rfl

@[simp] theorem swap_prefA (M : MatchingMarket α β) (b : β) (a : α) :
    M.swap.prefA b a = M.prefB b a := rfl

@[simp] theorem swap_prefB (M : MatchingMarket α β) (a : α) (b : β) :
    M.swap.prefB a b = M.prefA a b := rfl

@[simp] theorem swap_reserveA (M : MatchingMarket α β) (b : β) :
    M.swap.reserveA b = M.reserveB b := rfl

@[simp] theorem swap_reserveB (M : MatchingMarket α β) (a : α) :
    M.swap.reserveB a = M.reserveA a := rfl

/-- Invert an `Option`-encoded matching, choosing the unique preimage when it
exists. The useful equivalence with the original matching requires
`IsMatching`. -/
noncomputable def inverseMatching (μ : α → Option β) : β → Option α :=
  by
    classical
    exact fun b =>
      if h : ∃ a, μ a = some b then
        some (Classical.choose h)
      else
        none

theorem inverseMatching_eq_some_iff {μ : α → Option β} (hμ : IsMatching μ)
    {a : α} {b : β} :
    inverseMatching μ b = some a ↔ μ a = some b := by
  classical
  constructor
  · intro h
    unfold inverseMatching at h
    split_ifs at h with hmatched
    · have hchoose := Classical.choose_spec hmatched
      have ha : Classical.choose hmatched = a := Option.some.inj h
      simpa [ha] using hchoose
  · intro h
    unfold inverseMatching
    split_ifs with hmatched
    · have hchoose := Classical.choose_spec hmatched
      have ha : Classical.choose hmatched = a := hμ (Classical.choose hmatched) a b hchoose h
      simp [ha]
    · exact False.elim (hmatched ⟨a, h⟩)

theorem inverseMatching_none_iff {μ : α → Option β} {b : β} :
    inverseMatching μ b = none ↔ ∀ a, μ a ≠ some b := by
  classical
  constructor
  · intro h a ha
    unfold inverseMatching at h
    split_ifs at h with hmatched
    exact hmatched ⟨a, ha⟩
  · intro h
    unfold inverseMatching
    split_ifs with hmatched
    · exact False.elim (h (Classical.choose hmatched) (Classical.choose_spec hmatched))
    · rfl

theorem matching_none_iff_inverse_ne_some {μ : α → Option β} (hμ : IsMatching μ)
    {a : α} :
    μ a = none ↔ ∀ b, inverseMatching μ b ≠ some a := by
  constructor
  · intro ha b hinv
    have hmatch := (inverseMatching_eq_some_iff hμ).1 hinv
    rw [ha] at hmatch
    contradiction
  · intro h
    cases hμa : μ a with
    | none => rfl
    | some b =>
        exact False.elim (h b ((inverseMatching_eq_some_iff hμ).2 hμa))

theorem inverseMatching_isMatching {μ : α → Option β} (hμ : IsMatching μ) :
    IsMatching (inverseMatching μ) := by
  intro b₁ b₂ a h₁ h₂
  have hμ₁ : μ a = some b₁ := (inverseMatching_eq_some_iff hμ).1 h₁
  have hμ₂ : μ a = some b₂ := (inverseMatching_eq_some_iff hμ).1 h₂
  exact Option.some.inj (hμ₁.symm.trans hμ₂)

theorem swap_isBlockingPair_iff (M : MatchingMarket α β)
    {μ : α → Option β} (hμ : IsMatching μ) {a : α} {b : β} :
    M.swap.IsBlockingPair (inverseMatching μ) b a ↔ M.IsBlockingPair μ a b := by
  constructor
  · intro hblock
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b' hb'
      exact hblock.2.2.1 b' ((inverseMatching_eq_some_iff hμ).2 hb')
    · intro ha
      exact hblock.2.2.2 (by
        intro b' hinv
        have hb' : μ a = some b' := (inverseMatching_eq_some_iff hμ).1 hinv
        rw [ha] at hb'
        contradiction)
    · intro a' ha'
      exact hblock.1 a' ((inverseMatching_eq_some_iff hμ).2 ha')
    · intro hb
      exact hblock.2.1 ((inverseMatching_none_iff).2 hb)
  · intro hblock
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a' ha'
      exact hblock.2.2.1 a' ((inverseMatching_eq_some_iff hμ).1 ha')
    · intro hb
      exact hblock.2.2.2 ((inverseMatching_none_iff).1 hb)
    · intro b' hb'
      exact hblock.1 b' ((inverseMatching_eq_some_iff hμ).1 hb')
    · intro ha
      exact hblock.2.1 ((matching_none_iff_inverse_ne_some hμ).2 ha)

theorem inverseMatching_isStable (M : MatchingMarket α β)
    {μ : α → Option β} (hstable : M.IsStable μ) :
    M.swap.IsStable (inverseMatching μ) := by
  refine ⟨inverseMatching_isMatching hstable.1, ?_, ?_⟩
  · intro b a hba
    have hab : μ a = some b := (inverseMatching_eq_some_iff hstable.1).1 hba
    have hir := hstable.2.1 a b hab
    exact ⟨hir.2, hir.1⟩
  · rintro ⟨b, a, hblock⟩
    apply hstable.2.2
    exact ⟨a, b, (M.swap_isBlockingPair_iff hstable.1).1 hblock⟩

theorem swap_isStable_iff (M : MatchingMarket α β)
    {μ : α → Option β} (hμ : IsMatching μ) :
    M.swap.IsStable (inverseMatching μ) ↔ M.IsStable μ := by
  constructor
  · intro hstable
    refine ⟨hμ, ?_, ?_⟩
    · intro a b hab
      have hba : inverseMatching μ b = some a := (inverseMatching_eq_some_iff hμ).2 hab
      have hir := hstable.2.1 b a hba
      exact ⟨hir.2, hir.1⟩
    · rintro ⟨a, b, hblock⟩
      apply hstable.2.2
      exact ⟨b, a, (M.swap_isBlockingPair_iff hμ).2 hblock⟩
  · exact M.inverseMatching_isStable

end MatchingMarket

end GameTheory
