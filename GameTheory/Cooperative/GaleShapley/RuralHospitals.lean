/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Cooperative.GaleShapley
import Math.Fintype

/-!
# Matched-agent invariance for stable matchings

This file proves the matched-set part of the rural-hospitals theorem for the
outside-option matching model.  Under strict preferences and no indifference with
the outside option, every stable matching matches exactly the same agents as
men-proposing deferred acceptance.
-/

namespace GameTheory

namespace MatchingMarket

variable {α β : Type} [Fintype α] [Fintype β] (M : MatchingMarket α β)

noncomputable local instance {γ : Type} [Fintype γ] (P : γ → Prop) : Fintype {x // P x} :=
  Fintype.ofFinite _

/-- The `α`-agents matched by a matching. -/
def MatchedA (μ : α → Option β) (a : α) : Prop :=
  ∃ b, μ a = some b

/-- The `β`-agents matched by a matching. -/
def MatchedB (μ : α → Option β) (b : β) : Prop :=
  ∃ a, μ a = some b

namespace Matched

variable {M} {μ ν : α → Option β}

/-- A matching pairs the subtype of matched `α`-agents with the subtype of matched
`β`-agents. -/
noncomputable def equiv (hμ : IsMatching μ) :
    {a : α // MatchedA μ a} ≃ {b : β // MatchedB μ b} where
  toFun a :=
    ⟨Classical.choose a.2, ⟨a.1, Classical.choose_spec a.2⟩⟩
  invFun b :=
    ⟨Classical.choose b.2, ⟨b.1, Classical.choose_spec b.2⟩⟩
  left_inv a := by
    apply Subtype.ext
    have hright :
        μ (Classical.choose
          (show MatchedB μ (Classical.choose a.2) from
            ⟨a.1, Classical.choose_spec a.2⟩)) = some (Classical.choose a.2) :=
      Classical.choose_spec
        (show MatchedB μ (Classical.choose a.2) from
          ⟨a.1, Classical.choose_spec a.2⟩)
    exact hμ _ _ _ hright (Classical.choose_spec a.2)
  right_inv b := by
    apply Subtype.ext
    have hleft :
        μ (Classical.choose b.2) =
          some (Classical.choose
            (show MatchedA μ (Classical.choose b.2) from
              ⟨b.1, Classical.choose_spec b.2⟩)) :=
      Classical.choose_spec
        (show MatchedA μ (Classical.choose b.2) from
          ⟨b.1, Classical.choose_spec b.2⟩)
    exact Option.some.inj (hleft.symm.trans (Classical.choose_spec b.2))

theorem card_matchedA_eq_card_matchedB (hμ : IsMatching μ) :
    Fintype.card {a : α // MatchedA μ a} =
      Fintype.card {b : β // MatchedB μ b} :=
  Fintype.card_congr (equiv hμ)

end Matched

section RuralHospitals

variable (hAinj : ∀ a, Function.Injective (M.prefA a))
variable (hBinj : ∀ b, Function.Injective (M.prefB b))
variable (hAne : ∀ a b, M.reserveA a ≠ M.prefA a b)
variable (hBne : ∀ b a, M.reserveB b ≠ M.prefB b a)

include hAinj hBinj hAne hBne

omit hBne in
private theorem stable_matchedA_subset_daMatchedA {μ : α → Option β}
    (hμstable : M.IsStable μ) {a : α} :
    MatchedA μ a → MatchedA M.daMatching a := by
  rintro ⟨b, hb⟩
  obtain ⟨bda, hbda, _hle⟩ :=
    M.daMatching_man_optimal hAinj hBinj hAne hμstable hb
  exact ⟨bda, hbda⟩

private theorem daMatchedB_subset_stable_matchedB {μ : α → Option β}
    (hμstable : M.IsStable μ) {b : β} :
    MatchedB M.daMatching b → MatchedB μ b := by
  rintro ⟨a, ha⟩
  exact M.daMatching_woman_matched_in_stable hAinj hBinj hAne hBne hμstable ha

private theorem card_stable_matchedA_eq_card_daMatchedA {μ : α → Option β}
    (hμstable : M.IsStable μ) :
    Fintype.card {a : α // MatchedA μ a} =
      Fintype.card {a : α // MatchedA M.daMatching a} := by
  classical
  have hle_forward :
    Fintype.card {a : α // MatchedA μ a} ≤
        Fintype.card {a : α // MatchedA M.daMatching a} :=
    Fintype.card_subtype_mono _ _
      (fun a ha => M.stable_matchedA_subset_daMatchedA hAinj hBinj hAne hμstable (a := a) ha)
  have hle_backward :
      Fintype.card {a : α // MatchedA M.daMatching a} ≤
        Fintype.card {a : α // MatchedA μ a} := by
    calc
      Fintype.card {a : α // MatchedA M.daMatching a}
          = Fintype.card {b : β // MatchedB M.daMatching b} :=
            Matched.card_matchedA_eq_card_matchedB
              (M.daMatching_isStable hAinj hBinj).1
      _ ≤ Fintype.card {b : β // MatchedB μ b} :=
            Fintype.card_subtype_mono _ _
              (fun b hb =>
                M.daMatchedB_subset_stable_matchedB hAinj hBinj hAne hBne hμstable (b := b) hb)
      _ = Fintype.card {a : α // MatchedA μ a} :=
            (Matched.card_matchedA_eq_card_matchedB hμstable.1).symm
  exact le_antisymm hle_forward hle_backward

private theorem card_stable_matchedB_eq_card_daMatchedB {μ : α → Option β}
    (hμstable : M.IsStable μ) :
    Fintype.card {b : β // MatchedB μ b} =
      Fintype.card {b : β // MatchedB M.daMatching b} := by
  calc
    Fintype.card {b : β // MatchedB μ b}
        = Fintype.card {a : α // MatchedA μ a} :=
          (Matched.card_matchedA_eq_card_matchedB hμstable.1).symm
    _ = Fintype.card {a : α // MatchedA M.daMatching a} :=
          M.card_stable_matchedA_eq_card_daMatchedA hAinj hBinj hAne hBne hμstable
    _ = Fintype.card {b : β // MatchedB M.daMatching b} :=
          Matched.card_matchedA_eq_card_matchedB
            (M.daMatching_isStable hAinj hBinj).1

/-- Rural-hospitals matched-set invariance on the proposing side: an `α`-agent is
matched in a stable matching iff he is matched by men-proposing deferred
acceptance. -/
theorem stable_matchedA_iff_daMatchedA {μ : α → Option β}
    (hμstable : M.IsStable μ) (a : α) :
    MatchedA μ a ↔ MatchedA M.daMatching a := by
  constructor
  · exact M.stable_matchedA_subset_daMatchedA hAinj hBinj hAne hμstable
  · intro hda
    exact Math.subtype_of_card_eq_of_imp
      (fun a ha => M.stable_matchedA_subset_daMatchedA hAinj hBinj hAne hμstable (a := a) ha)
      (M.card_stable_matchedA_eq_card_daMatchedA hAinj hBinj hAne hBne hμstable) hda

/-- Rural-hospitals matched-set invariance on the receiving side: a `β`-agent is
matched in a stable matching iff she is matched by men-proposing deferred
acceptance. -/
theorem stable_matchedB_iff_daMatchedB {μ : α → Option β}
    (hμstable : M.IsStable μ) (b : β) :
    MatchedB μ b ↔ MatchedB M.daMatching b := by
  constructor
  · intro hμ
    exact Math.subtype_of_card_eq_of_imp
      (fun b hb =>
        M.daMatchedB_subset_stable_matchedB hAinj hBinj hAne hBne hμstable (b := b) hb)
      (M.card_stable_matchedB_eq_card_daMatchedB hAinj hBinj hAne hBne hμstable).symm
      hμ
  · exact M.daMatchedB_subset_stable_matchedB hAinj hBinj hAne hBne hμstable

end RuralHospitals

end MatchingMarket

end GameTheory
