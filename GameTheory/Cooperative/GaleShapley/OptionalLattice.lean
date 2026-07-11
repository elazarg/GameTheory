/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Cooperative.GaleShapley.OptionalOrder
import GameTheory.Cooperative.GaleShapley.RuralHospitals
import GameTheory.Cooperative.GaleShapley.Perfect

/-!
# Optional-market stable-matching lattice construction

This file extends the stable-matching order beyond balanced complete-acceptability
markets.  Partners are compared as optional partners, with `none` valued at the
agent's reservation value.
-/

namespace GameTheory

namespace MatchingMarket

variable {α β : Type} [Finite α] [Finite β] (M : MatchingMarket α β)

noncomputable local instance : Fintype α := Fintype.ofFinite α
noncomputable local instance : Fintype β := Fintype.ofFinite β

noncomputable local instance {γ : Type} [Fintype γ] (P : γ → Prop) : Fintype {x // P x} :=
  Fintype.ofFinite _

section Join

variable {μ ν : α → Option β}
variable (hμ : M.IsStable μ) (hν : M.IsStable ν)
variable (hAinj : ∀ a, Function.Injective (M.prefA a))
variable (hBinj : ∀ b, Function.Injective (M.prefB b))
variable (hAne : ∀ a b, M.reserveA a ≠ M.prefA a b)
variable (hBne : ∀ b a, M.reserveB b ≠ M.prefB b a)

/-- The better optional `β`-partner for an `α`-agent across two stable matchings. -/
noncomputable def optionalJoinPartner (a : α) : Option β :=
  if M.prefAOption a (ν a) ≤ M.prefAOption a (μ a) then
    μ a
  else
    ν a

/-- The matching candidate induced by optional pointwise `α`-side improvement. -/
noncomputable def optionalStableJoin : α → Option β :=
  fun a => M.optionalJoinPartner (μ := μ) (ν := ν) a

omit [Finite α] [Finite β] in
theorem optionalStableJoin_apply (a : α) :
    M.optionalStableJoin (μ := μ) (ν := ν) a = M.optionalJoinPartner (μ := μ) (ν := ν) a :=
  rfl

omit [Finite α] [Finite β] in
theorem optionalJoinPartner_eq_left_or_right (a : α) :
    M.optionalJoinPartner (μ := μ) (ν := ν) a = μ a ∨
      M.optionalJoinPartner (μ := μ) (ν := ν) a = ν a := by
  unfold optionalJoinPartner
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Finite α] [Finite β] in
theorem optionalJoinPartner_some_source {a : α} {b : β}
    (h : M.optionalJoinPartner (μ := μ) (ν := ν) a = some b) :
    μ a = some b ∨ ν a = some b := by
  rcases M.optionalJoinPartner_eq_left_or_right (μ := μ) (ν := ν) a with hleft | hright
  · exact Or.inl (hleft.symm.trans h)
  · exact Or.inr (hright.symm.trans h)

omit [Finite α] [Finite β] in
theorem pref_leftOption_le_optionalJoin (a : α) :
    M.prefAOption a (μ a) ≤
      M.prefAOption a (M.optionalJoinPartner (μ := μ) (ν := ν) a) := by
  unfold optionalJoinPartner
  split_ifs with hle
  · rfl
  · exact le_of_lt (lt_of_not_ge hle)

omit [Finite α] [Finite β] in
theorem pref_rightOption_le_optionalJoin (a : α) :
    M.prefAOption a (ν a) ≤
      M.prefAOption a (M.optionalJoinPartner (μ := μ) (ν := ν) a) := by
  unfold optionalJoinPartner
  split_ifs with hle
  · exact hle
  · rfl

omit [Finite α] [Finite β] in
private theorem pref_other_lt_optionalJoin_of_join_left {a : α}
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hAne : ∀ a b, M.reserveA a ≠ M.prefA a b)
    (hjoin : M.optionalJoinPartner (μ := μ) (ν := ν) a = μ a)
    (hne : ν a ≠ μ a) :
    M.prefAOption a (ν a) < M.prefAOption a (μ a) := by
  unfold optionalJoinPartner at hjoin
  split_ifs at hjoin with hle
  · refine lt_of_le_of_ne hle ?_
    intro heq
    exact hne (M.prefAOption_injective hAinj hAne a heq)
  · exact False.elim (hne hjoin)

omit [Finite α] [Finite β] in
private theorem pref_other_lt_optionalJoin_of_join_right {a : α}
    (hjoin : M.optionalJoinPartner (μ := μ) (ν := ν) a = ν a)
    (hne : μ a ≠ ν a) :
    M.prefAOption a (μ a) < M.prefAOption a (ν a) := by
  unfold optionalJoinPartner at hjoin
  split_ifs at hjoin with hle
  · exact False.elim (hne hjoin)
  · exact lt_of_not_ge hle

include hμ hν hAinj hBinj hAne hBne

private theorem matchedA_iff_between_stable (a : α) :
    MatchedA μ a ↔ MatchedA ν a := by
  calc
    MatchedA μ a ↔ MatchedA M.daMatching a :=
      M.stable_matchedA_iff_daMatchedA hAinj hBinj hAne hBne hμ a
    _ ↔ MatchedA ν a :=
      (M.stable_matchedA_iff_daMatchedA hAinj hBinj hAne hBne hν a).symm

private theorem matchedB_iff_between_stable (b : β) :
    MatchedB μ b ↔ MatchedB ν b := by
  calc
    MatchedB μ b ↔ MatchedB M.daMatching b :=
      M.stable_matchedB_iff_daMatchedB hAinj hBinj hAne hBne hμ b
    _ ↔ MatchedB ν b :=
      (M.stable_matchedB_iff_daMatchedB hAinj hBinj hAne hBne hν b).symm

theorem optionalStableJoin_matchedA_iff_left (a : α) :
    MatchedA (M.optionalStableJoin (μ := μ) (ν := ν)) a ↔ MatchedA μ a := by
  constructor
  · rintro ⟨b, hb⟩
    rw [optionalStableJoin_apply] at hb
    rcases M.optionalJoinPartner_some_source (μ := μ) (ν := ν) hb with hleft | hright
    · exact ⟨b, hleft⟩
    · exact (matchedA_iff_between_stable (M := M) hμ hν hAinj hBinj hAne hBne a).2 ⟨b, hright⟩
  · intro hmatched
    obtain ⟨bμ, hbμ⟩ := hmatched
    obtain ⟨bν, hbν⟩ :=
      (matchedA_iff_between_stable (M := M) hμ hν hAinj hBinj hAne hBne a).1 ⟨bμ, hbμ⟩
    rcases M.optionalJoinPartner_eq_left_or_right (μ := μ) (ν := ν) a with hleft | hright
    · exact ⟨bμ, by simpa [optionalStableJoin] using hleft.trans hbμ⟩
    · exact ⟨bν, by simpa [optionalStableJoin] using hright.trans hbν⟩

private theorem optionalStableJoin_matchedB_subset_left {b : β} :
    MatchedB (M.optionalStableJoin (μ := μ) (ν := ν)) b → MatchedB μ b := by
  rintro ⟨a, ha⟩
  rw [optionalStableJoin_apply] at ha
  rcases M.optionalJoinPartner_some_source (μ := μ) (ν := ν) ha with hleft | hright
  · exact ⟨a, hleft⟩
  · exact (matchedB_iff_between_stable (M := M) hμ hν hAinj hBinj hAne hBne b).2 ⟨a, hright⟩

private theorem optionalStableJoin_source_of_left_matched {a : α} {b : β}
    (hleft : μ a = some b) :
    ∃ bν, ν a = some bν := by
  exact (matchedA_iff_between_stable (M := M) hμ hν hAinj hBinj hAne hBne a).1 ⟨b, hleft⟩

private theorem optionalStableJoin_source_of_right_matched {a : α} {b : β}
    (hright : ν a = some b) :
    ∃ bμ, μ a = some bμ := by
  exact (matchedA_iff_between_stable (M := M) hμ hν hAinj hBinj hAne hBne a).2 ⟨b, hright⟩

theorem optionalStableJoin_isMatching :
    IsMatching (M.optionalStableJoin (μ := μ) (ν := ν)) := by
  intro a₁ a₂ b h₁ h₂
  rw [optionalStableJoin_apply] at h₁ h₂
  rcases M.optionalJoinPartner_some_source (μ := μ) (ν := ν) h₁ with h₁μ | h₁ν <;>
    rcases M.optionalJoinPartner_some_source (μ := μ) (ν := ν) h₂ with h₂μ | h₂ν
  · exact hμ.1 a₁ a₂ b h₁μ h₂μ
  · by_cases hν₁ : ν a₁ = some b
    · exact hν.1 a₁ a₂ b hν₁ h₂ν
    by_cases hμ₂ : μ a₂ = some b
    · exact hμ.1 a₁ a₂ b h₁μ hμ₂
    obtain ⟨bν₁, hbν₁⟩ := M.optionalStableJoin_source_of_left_matched
      hμ hν hAinj hBinj hAne hBne h₁μ
    obtain ⟨bμ₂, hbμ₂⟩ := M.optionalStableJoin_source_of_right_matched
      hμ hν hAinj hBinj hAne hBne h₂ν
    have hjoin₁ : M.optionalJoinPartner (μ := μ) (ν := ν) a₁ = μ a₁ := h₁.trans h₁μ.symm
    have hjoin₂ : M.optionalJoinPartner (μ := μ) (ν := ν) a₂ = ν a₂ := h₂.trans h₂ν.symm
    have hp₁opt : M.prefAOption a₁ (ν a₁) < M.prefAOption a₁ (μ a₁) :=
      M.pref_other_lt_optionalJoin_of_join_left (μ := μ) (ν := ν) hAinj hAne hjoin₁
        (fun h => hν₁ (h.trans h₁μ))
    have hp₂opt : M.prefAOption a₂ (μ a₂) < M.prefAOption a₂ (ν a₂) :=
      M.pref_other_lt_optionalJoin_of_join_right (μ := μ) (ν := ν) hjoin₂
        (fun h => hμ₂ (h.trans h₂ν))
    have hp₁ : M.prefA a₁ bν₁ < M.prefA a₁ b := by
      simpa [prefAOption, hbν₁, h₁μ] using hp₁opt
    have hp₂ : M.prefA a₂ bμ₂ < M.prefA a₂ b := by
      simpa [prefAOption, hbμ₂, h₂ν] using hp₂opt
    have hb_pref₁ : M.prefB b a₁ < M.prefB b a₂ :=
      M.opposed_preferences hν (hBinj b) hbν₁ hp₁ h₂ν
    have hb_pref₂ : M.prefB b a₂ < M.prefB b a₁ :=
      M.opposed_preferences hμ (hBinj b) hbμ₂ hp₂ h₁μ
    exact False.elim ((lt_asymm hb_pref₁) hb_pref₂)
  · by_cases hμ₁ : μ a₁ = some b
    · exact hμ.1 a₁ a₂ b hμ₁ h₂μ
    by_cases hν₂ : ν a₂ = some b
    · exact hν.1 a₁ a₂ b h₁ν hν₂
    obtain ⟨bμ₁, hbμ₁⟩ := M.optionalStableJoin_source_of_right_matched
      hμ hν hAinj hBinj hAne hBne h₁ν
    obtain ⟨bν₂, hbν₂⟩ := M.optionalStableJoin_source_of_left_matched
      hμ hν hAinj hBinj hAne hBne h₂μ
    have hjoin₁ : M.optionalJoinPartner (μ := μ) (ν := ν) a₁ = ν a₁ := h₁.trans h₁ν.symm
    have hjoin₂ : M.optionalJoinPartner (μ := μ) (ν := ν) a₂ = μ a₂ := h₂.trans h₂μ.symm
    have hp₁opt : M.prefAOption a₁ (μ a₁) < M.prefAOption a₁ (ν a₁) :=
      M.pref_other_lt_optionalJoin_of_join_right (μ := μ) (ν := ν) hjoin₁
        (fun h => hμ₁ (h.trans h₁ν))
    have hp₂opt : M.prefAOption a₂ (ν a₂) < M.prefAOption a₂ (μ a₂) :=
      M.pref_other_lt_optionalJoin_of_join_left (μ := μ) (ν := ν) hAinj hAne hjoin₂
        (fun h => hν₂ (h.trans h₂μ))
    have hp₁ : M.prefA a₁ bμ₁ < M.prefA a₁ b := by
      simpa [prefAOption, hbμ₁, h₁ν] using hp₁opt
    have hp₂ : M.prefA a₂ bν₂ < M.prefA a₂ b := by
      simpa [prefAOption, hbν₂, h₂μ] using hp₂opt
    have hb_pref₁ : M.prefB b a₁ < M.prefB b a₂ :=
      M.opposed_preferences hμ (hBinj b) hbμ₁ hp₁ h₂μ
    have hb_pref₂ : M.prefB b a₂ < M.prefB b a₁ :=
      M.opposed_preferences hν (hBinj b) hbν₂ hp₂ h₁ν
    exact False.elim ((lt_asymm hb_pref₁) hb_pref₂)
  · exact hν.1 a₁ a₂ b h₁ν h₂ν

private theorem optionalStableJoin_matchedB_left_of_left {b : β}
    (hmatch : IsMatching (M.optionalStableJoin (μ := μ) (ν := ν))) :
    MatchedB μ b → MatchedB (M.optionalStableJoin (μ := μ) (ν := ν)) b := by
  intro hb
  exact Math.subtype_of_card_eq_of_imp
    (α := β)
    (p := fun b => MatchedB (M.optionalStableJoin (μ := μ) (ν := ν)) b)
    (q := fun b => MatchedB μ b)
    (fun b hbj => M.optionalStableJoin_matchedB_subset_left hμ hν hAinj hBinj hAne hBne hbj)
    (by
      calc
        Fintype.card {x : β // MatchedB (M.optionalStableJoin (μ := μ) (ν := ν)) x}
            = Fintype.card {x : α // MatchedA (M.optionalStableJoin (μ := μ) (ν := ν)) x} :=
              (Matched.card_matchedA_eq_card_matchedB hmatch).symm
        _ = Fintype.card {x : α // MatchedA μ x} := by
              apply Fintype.card_congr
              exact Equiv.subtypeEquivRight
                (fun a => M.optionalStableJoin_matchedA_iff_left hμ hν hAinj hBinj hAne hBne a)
        _ = Fintype.card {x : β // MatchedB μ x} :=
              Matched.card_matchedA_eq_card_matchedB hμ.1)
    hb

omit [Finite α] [Finite β] hμ hν hAinj hBinj hAne hBne in
private theorem optionalJoin_pref_lt_of_blocks
    {a : α} {b : β}
    (hblock : M.IsBlockingPair (M.optionalStableJoin (μ := μ) (ν := ν)) a b) :
    M.prefAOption a (M.optionalJoinPartner (μ := μ) (ν := ν) a) < M.prefA a b := by
  cases hjoin : M.optionalJoinPartner (μ := μ) (ν := ν) a with
  | none =>
      exact hblock.2.1 (by simp [optionalStableJoin, hjoin])
  | some b' =>
      exact hblock.1 b' (by simp [optionalStableJoin, hjoin])

theorem optionalStableJoin_isStable :
    M.IsStable (M.optionalStableJoin (μ := μ) (ν := ν)) := by
  have hmatch : IsMatching (M.optionalStableJoin (μ := μ) (ν := ν)) :=
    M.optionalStableJoin_isMatching hμ hν hAinj hBinj hAne hBne
  refine ⟨hmatch, ?_, ?_⟩
  · intro a b hab
    rw [optionalStableJoin_apply] at hab
    rcases M.optionalJoinPartner_some_source (μ := μ) (ν := ν) hab with hleft | hright
    · exact hμ.2.1 a b hleft
    · exact hν.2.1 a b hright
  · rintro ⟨a, b, hblock⟩
    have hjoin_pref :
        M.prefAOption a (M.optionalJoinPartner (μ := μ) (ν := ν) a) < M.prefA a b :=
      M.optionalJoin_pref_lt_of_blocks (μ := μ) (ν := ν) hblock
    have hμ_pref_opt : M.prefAOption a (μ a) < M.prefA a b :=
      lt_of_le_of_lt (M.pref_leftOption_le_optionalJoin (μ := μ) (ν := ν) a) hjoin_pref
    have hν_pref_opt : M.prefAOption a (ν a) < M.prefA a b :=
      lt_of_le_of_lt (M.pref_rightOption_le_optionalJoin (μ := μ) (ν := ν) a) hjoin_pref
    have hbμmatched : MatchedB μ b := by
      by_contra hbμ
      have hbν : ¬ MatchedB ν b := by
        intro hbν
        exact hbμ ((matchedB_iff_between_stable (M := M) hμ hν hAinj hBinj hAne hBne b).2 hbν)
      have hbjoin : ∀ a', M.optionalStableJoin (μ := μ) (ν := ν) a' ≠ some b := by
        intro a' ha'
        rw [optionalStableJoin_apply] at ha'
        rcases M.optionalJoinPartner_some_source (μ := μ) (ν := ν) ha' with hleft | hright
        · exact hbμ ⟨a', hleft⟩
        · exact hbν ⟨a', hright⟩
      have hb_reserve : M.reserveB b < M.prefB b a := hblock.2.2.2 hbjoin
      apply hμ.2.2
      refine ⟨a, b, ?_, ?_, ?_, ?_⟩
      · intro b' hb'
        have : M.prefA a b' < M.prefA a b := by
          simpa [prefAOption, hb'] using hμ_pref_opt
        exact this
      · intro ha
        exact (by simpa [prefAOption, ha] using hμ_pref_opt)
      · intro a' ha'
        exact False.elim (hbμ ⟨a', ha'⟩)
      · intro _; exact hb_reserve
    have hbνmatched : MatchedB ν b :=
      (matchedB_iff_between_stable (M := M) hμ hν hAinj hBinj hAne hBne b).1 hbμmatched
    obtain ⟨aj, hjb⟩ :=
      M.optionalStableJoin_matchedB_left_of_left hμ hν hAinj hBinj hAne hBne hmatch hbμmatched
    have hb_blocks : M.prefB b aj < M.prefB b a := hblock.2.2.1 aj hjb
    rw [optionalStableJoin_apply] at hjb
    rcases M.optionalJoinPartner_some_source (μ := μ) (ν := ν) hjb with hjμ | hjν
    · apply hμ.2.2
      refine ⟨a, b, ?_, ?_, ?_, ?_⟩
      · intro b' hb'
        simpa [prefAOption, hb'] using hμ_pref_opt
      · intro ha
        simpa [prefAOption, ha] using hμ_pref_opt
      · intro a' ha'
        have ha' : a' = aj := hμ.1 a' aj b ha' hjμ
        rw [ha']
        exact hb_blocks
      · intro hbnone
        exact False.elim (hbnone aj hjμ)
    · apply hν.2.2
      refine ⟨a, b, ?_, ?_, ?_, ?_⟩
      · intro b' hb'
        simpa [prefAOption, hb'] using hν_pref_opt
      · intro ha
        simpa [prefAOption, ha] using hν_pref_opt
      · intro a' ha'
        have ha' : a' = aj := hν.1 a' aj b ha' hjν
        rw [ha']
        exact hb_blocks
      · intro hbnone
        exact False.elim (hbnone aj hjν)

end Join

namespace OptionalOrder

variable (hAinj : ∀ a, Function.Injective (M.prefA a))
variable (hBinj : ∀ b, Function.Injective (M.prefB b))
variable (hAne : ∀ a b, M.reserveA a ≠ M.prefA a b)
variable (hBne : ∀ b a, M.reserveB b ≠ M.prefB b a)

/-- A bundled stable matching, inverted as a stable matching of the swapped
market. -/
noncomputable def inverseStable (μ : M.StableMatching) : M.swap.StableMatching :=
  ⟨inverseMatching μ, M.inverseMatching_isStable μ.2⟩

omit [Finite α] [Finite β] in
theorem inverse_inverse_apply (μ : M.StableMatching) (a : α) :
    inverseMatching (inverseMatching μ) a = μ a := by
  cases hμa : μ a with
  | some b =>
      exact (inverseMatching_eq_some_iff (inverseMatching_isMatching μ.2.1)).2
        ((inverseMatching_eq_some_iff μ.2.1).2 hμa)
  | none =>
      apply (Option.eq_none_iff_forall_not_mem).2
      intro b hb
      have hinv : inverseMatching μ b = some a :=
        (inverseMatching_eq_some_iff (inverseMatching_isMatching μ.2.1)).1 hb
      exact (matching_none_iff_inverse_ne_some μ.2.1).1 hμa b hinv

include hAinj hBinj hAne hBne

/-- Stable matching preferences polarize: if every `α`-agent weakly prefers `ν`
to `μ`, then every `β`-agent weakly prefers the inverse of `μ` to the inverse of
`ν`. -/
theorem swap_menLe_of_menLe {μ ν : M.StableMatching}
    (hμν : menLe M μ ν) :
    menLe M.swap (inverseStable M ν) (inverseStable M μ) := by
  intro b
  by_contra hnot
  have hlt :
      M.prefBOption b (inverseMatching μ b) <
        M.prefBOption b (inverseMatching ν b) :=
    lt_of_not_ge hnot
  cases hνb : inverseMatching ν b with
  | none =>
      cases hμb : inverseMatching μ b with
      | none =>
          simp [prefBOption, hνb, hμb] at hlt
      | some aμ =>
          have hμab : μ aμ = some b := (inverseMatching_eq_some_iff μ.2.1).1 hμb
          have hir := μ.2.2.1 aμ b hμab
          exact not_lt_of_ge hir.2 (by simpa [prefBOption, hνb, hμb] using hlt)
  | some aν =>
      have hνab : ν aν = some b := (inverseMatching_eq_some_iff ν.2.1).1 hνb
      cases hμb : inverseMatching μ b with
      | none =>
          have hbν : MatchedB ν b := ⟨aν, hνab⟩
          have hbμ : MatchedB μ b :=
            (M.stable_matchedB_iff_daMatchedB hAinj hBinj hAne hBne μ.2 b).2
              ((M.stable_matchedB_iff_daMatchedB hAinj hBinj hAne hBne ν.2 b).1 hbν)
          obtain ⟨aμ, hμab⟩ := hbμ
          exact (inverseMatching_none_iff).1 hμb aμ hμab
      | some aμ =>
          have hμab : μ aμ = some b := (inverseMatching_eq_some_iff μ.2.1).1 hμb
          have hbworse : M.prefB b aμ < M.prefB b aν := by
            simpa [prefBOption, hνb, hμb] using hlt
          have haνμmatched : MatchedA μ aν :=
            (M.stable_matchedA_iff_daMatchedA hAinj hBinj hAne hBne μ.2 aν).2
              ((M.stable_matchedA_iff_daMatchedA hAinj hBinj hAne hBne ν.2 aν).1
                ⟨b, hνab⟩)
          obtain ⟨bμ, haνμ⟩ := haνμmatched
          have hmen := hμν aν
          have hpref_le : M.prefA aν bμ ≤ M.prefA aν b := by
            simpa [prefAOption, haνμ, hνab] using hmen
          have hbμ_ne : bμ ≠ b := by
            intro hb
            have haeq : aμ = aν := μ.2.1 aμ aν b hμab (hb ▸ haνμ)
            subst haeq
            exact lt_irrefl _ hbworse
          have hpref : M.prefA aν bμ < M.prefA aν b := by
            refine lt_of_le_of_ne hpref_le ?_
            intro heq
            exact hbμ_ne (hAinj aν heq)
          have hb_pref : M.prefB b aν < M.prefB b aμ :=
            M.opposed_preferences μ.2 (hBinj b) haνμ hpref hμab
          exact False.elim ((lt_asymm hb_pref) hbworse)

/-- The optional-market join of two bundled stable matchings. -/
noncomputable def join (μ ν : M.StableMatching) : M.StableMatching :=
  ⟨M.optionalStableJoin (μ := μ) (ν := ν),
    M.optionalStableJoin_isStable μ.2 ν.2 hAinj hBinj hAne hBne⟩

theorem join_apply (μ ν : M.StableMatching) (a : α) :
    join M hAinj hBinj hAne hBne μ ν a =
      M.optionalJoinPartner (μ := μ) (ν := ν) a :=
  rfl

theorem le_join_left (μ ν : M.StableMatching) :
    menLe M μ (join M hAinj hBinj hAne hBne μ ν) := by
  intro a
  exact M.pref_leftOption_le_optionalJoin (μ := μ) (ν := ν) a

theorem le_join_right (μ ν : M.StableMatching) :
    menLe M ν (join M hAinj hBinj hAne hBne μ ν) := by
  intro a
  exact M.pref_rightOption_le_optionalJoin (μ := μ) (ν := ν) a

theorem join_le {μ ν η : M.StableMatching}
    (hμη : menLe M μ η) (hνη : menLe M ν η) :
    menLe M (join M hAinj hBinj hAne hBne μ ν) η := by
  intro a
  rcases M.optionalJoinPartner_eq_left_or_right (μ := μ) (ν := ν) a with hleft | hright
  · rw [join_apply, hleft]
    exact hμη a
  · rw [join_apply, hright]
    exact hνη a

/-- The optional-market meet of two bundled stable matchings, defined by applying
the optional join construction in the swapped market and inverting back. -/
noncomputable def meet (μ ν : M.StableMatching) : M.StableMatching :=
  let μ' : M.swap.StableMatching := inverseStable M μ
  let ν' : M.swap.StableMatching := inverseStable M ν
  let join' : M.swap.StableMatching := join M.swap hBinj hAinj hBne hAne μ' ν'
  ⟨inverseMatching join', M.swap.inverseMatching_isStable join'.2⟩

theorem meet_le_left (μ ν : M.StableMatching) :
    menLe M (meet M hAinj hBinj hAne hBne μ ν) μ := by
  let μ' : M.swap.StableMatching := inverseStable M μ
  let ν' : M.swap.StableMatching := inverseStable M ν
  let join' : M.swap.StableMatching := join M.swap hBinj hAinj hBne hAne μ' ν'
  have hjoin : menLe M.swap μ' join' :=
    le_join_left M.swap hBinj hAinj hBne hAne μ' ν'
  have hpol : menLe M.swap.swap (inverseStable M.swap join') (inverseStable M.swap μ') :=
    swap_menLe_of_menLe M.swap hBinj hAinj hBne hAne hjoin
  intro a
  simpa [meet, μ', ν', join', inverseStable, inverse_inverse_apply M μ a] using hpol a

theorem meet_le_right (μ ν : M.StableMatching) :
    menLe M (meet M hAinj hBinj hAne hBne μ ν) ν := by
  let μ' : M.swap.StableMatching := inverseStable M μ
  let ν' : M.swap.StableMatching := inverseStable M ν
  let join' : M.swap.StableMatching := join M.swap hBinj hAinj hBne hAne μ' ν'
  have hjoin : menLe M.swap ν' join' :=
    le_join_right M.swap hBinj hAinj hBne hAne μ' ν'
  have hpol : menLe M.swap.swap (inverseStable M.swap join') (inverseStable M.swap ν') :=
    swap_menLe_of_menLe M.swap hBinj hAinj hBne hAne hjoin
  intro a
  simpa [meet, μ', ν', join', inverseStable, inverse_inverse_apply M ν a] using hpol a

theorem le_meet {η μ ν : M.StableMatching}
    (hημ : menLe M η μ) (hην : menLe M η ν) :
    menLe M η (meet M hAinj hBinj hAne hBne μ ν) := by
  let μ' : M.swap.StableMatching := inverseStable M μ
  let ν' : M.swap.StableMatching := inverseStable M ν
  let η' : M.swap.StableMatching := inverseStable M η
  let join' : M.swap.StableMatching := join M.swap hBinj hAinj hBne hAne μ' ν'
  have hμη : menLe M.swap μ' η' :=
    swap_menLe_of_menLe M hAinj hBinj hAne hBne hημ
  have hνη : menLe M.swap ν' η' :=
    swap_menLe_of_menLe M hAinj hBinj hAne hBne hην
  have hjoin : menLe M.swap join' η' :=
    join_le M.swap hBinj hAinj hBne hAne hμη hνη
  have hpol : menLe M.swap.swap (inverseStable M.swap η') (inverseStable M.swap join') :=
    swap_menLe_of_menLe M.swap hBinj hAinj hBne hAne hjoin
  intro a
  simpa [meet, μ', ν', η', join', inverseStable, inverse_inverse_apply M η a] using hpol a

/-- The optional-market stable matchings form a join-semilattice in the `α`-side
order. -/
@[reducible]
noncomputable def semilatticeSup : SemilatticeSup M.StableMatching where
  le := menLe M
  lt := fun μ ν => menLe M μ ν ∧ ¬ menLe M ν μ
  le_refl := menLe_refl M
  le_trans := fun _ _ _ => menLe_trans M
  le_antisymm := fun _ _ => menLe_antisymm M hAinj hAne
  sup := join M hAinj hBinj hAne hBne
  le_sup_left := le_join_left M hAinj hBinj hAne hBne
  le_sup_right := le_join_right M hAinj hBinj hAne hBne
  sup_le := fun _ _ _ => join_le M hAinj hBinj hAne hBne

/-- The optional-market stable matchings form a lattice in the `α`-side order. -/
@[reducible]
noncomputable def lattice : Lattice M.StableMatching where
  le := menLe M
  lt := fun μ ν => menLe M μ ν ∧ ¬ menLe M ν μ
  le_refl := menLe_refl M
  le_trans := fun _ _ _ => menLe_trans M
  le_antisymm := fun _ _ => menLe_antisymm M hAinj hAne
  sup := join M hAinj hBinj hAne hBne
  le_sup_left := le_join_left M hAinj hBinj hAne hBne
  le_sup_right := le_join_right M hAinj hBinj hAne hBne
  sup_le := fun _ _ _ => join_le M hAinj hBinj hAne hBne
  inf := meet M hAinj hBinj hAne hBne
  inf_le_left := meet_le_left M hAinj hBinj hAne hBne
  inf_le_right := meet_le_right M hAinj hBinj hAne hBne
  le_inf := fun _ _ _ => le_meet M hAinj hBinj hAne hBne

end OptionalOrder

end MatchingMarket

end GameTheory


