/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.SurvivalWeightedObstruction

/-!
# Positive-part action of survival-weighted blocks

A survival-weighted block acts on a nonnegative scalar resource by transporting
the resource through survival, subtracting the selected raw charge, and
truncating at zero:

```text
block • debt = max 0 (block.survival * debt - block.charge[channel]).
```

Chronological block concatenation acts by function composition.  The exact
accounting identity separates loss of future reach from immediate charge
consumption.  This module is independent of games; literal terminal-debt
prefixing is one client of the action.
-/

noncomputable section

namespace Math
namespace SurvivalWeightedObstruction
namespace Block

variable {κ : Type*}

/-- Scalar obstacle normalization underlying the block action. -/
theorem max_add_sub_max_eq_posPart_sub_posPart
    (quitValue continueValue transported : ℝ) (htransported : 0 ≤ transported) :
    max quitValue (continueValue + transported) -
        max quitValue continueValue =
      max 0 (transported - max 0 (quitValue - continueValue)) := by
  by_cases hquit : quitValue ≤ continueValue
  · have hquitTransported : quitValue ≤ continueValue + transported := by
      linarith
    rw [max_eq_right hquit, max_eq_right hquitTransported,
      max_eq_left (sub_nonpos.mpr hquit)]
    simp [max_eq_right htransported]
  · have hcontinue : continueValue ≤ quitValue := le_of_not_ge hquit
    rw [max_eq_left hcontinue,
      max_eq_right (sub_nonneg.mpr hcontinue)]
    by_cases htransportedQuit : quitValue ≤ continueValue + transported
    · rw [max_eq_right htransportedQuit,
        max_eq_right (by linarith : 0 ≤ transported - (quitValue - continueValue))]
      ring
    · have hnegative : transported - (quitValue - continueValue) ≤ 0 := by
        linarith
      rw [max_eq_left (le_of_not_ge htransportedQuit), max_eq_left hnegative]
      ring

/-- Positive-part action of one block at a selected charge channel. -/
def act (block : Block κ) (channel : κ) (debt : ℝ) : ℝ :=
  max 0 (block.survival * debt - block.charge.value channel)

theorem act_nonneg (block : Block κ) (channel : κ) (debt : ℝ) :
    0 ≤ block.act channel debt :=
  le_max_left _ _

theorem act_identity_of_nonneg (channel : κ) {debt : ℝ}
    (hdebt : 0 ≤ debt) :
    (identity : Block κ).act channel debt = debt := by
  simp [act, max_eq_right hdebt]

/-- Chronological concatenation acts by composition: the later block acts on
terminal debt first, and the earlier block acts on the result. -/
theorem act_concat (earlier later : Block κ) (channel : κ) (debt : ℝ) :
    (concat earlier later).act channel debt =
      earlier.act channel (later.act channel debt) := by
  have ha := earlier.charge.nonneg channel
  have hc := earlier.survival_nonneg
  simp only [act, concat_survival, concat_charge_value]
  by_cases hinner : later.survival * debt ≤ later.charge.value channel
  · have hinnerNonpos :
        later.survival * debt - later.charge.value channel ≤ 0 := by
      linarith
    rw [max_eq_left hinnerNonpos]
    have hleftNonpos :
        earlier.survival * later.survival * debt -
            (earlier.charge.value channel +
              earlier.survival * later.charge.value channel) ≤ 0 := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hc hinnerNonpos]
    have hrightNonpos :
        earlier.survival * 0 - earlier.charge.value channel ≤ 0 := by
      linarith
    rw [max_eq_left hleftNonpos, max_eq_left hrightNonpos]
  · have hinnerNonneg :
        0 ≤ later.survival * debt - later.charge.value channel := by
      linarith
    rw [max_eq_right hinnerNonneg]
    congr 1
    ring

/-- The amount consumed from survived debt is the smaller of survived debt
and the block charge. -/
theorem survival_mul_debt_sub_act_eq_min
    (block : Block κ) (channel : κ) {debt : ℝ} (hdebt : 0 ≤ debt) :
    block.survival * debt - block.act channel debt =
      min (block.survival * debt) (block.charge.value channel) := by
  have hsurvived : 0 ≤ block.survival * debt :=
    mul_nonneg block.survival_nonneg hdebt
  have hcharge := block.charge.nonneg channel
  unfold act
  by_cases hle : block.survival * debt ≤ block.charge.value channel
  · rw [max_eq_left (sub_nonpos.mpr hle), min_eq_left hle]
    ring
  · have hchargeLe : block.charge.value channel ≤ block.survival * debt :=
      le_of_not_ge hle
    rw [max_eq_right (sub_nonneg.mpr hchargeLe), min_eq_right hchargeLe]
    ring

/-- Exact utilization accounting: total debt loss is killed future debt plus
the charge actually consumed from the surviving part. -/
theorem debt_sub_act_eq_killed_add_min
    (block : Block κ) (channel : κ) {debt : ℝ} (hdebt : 0 ≤ debt) :
    debt - block.act channel debt =
      (1 - block.survival) * debt +
        min (block.survival * debt) (block.charge.value channel) := by
  rw [← survival_mul_debt_sub_act_eq_min block channel hdebt]
  ring

theorem act_le_survival_mul_debt
    (block : Block κ) (channel : κ) {debt : ℝ} (hdebt : 0 ≤ debt) :
    block.act channel debt ≤ block.survival * debt := by
  have haccount := survival_mul_debt_sub_act_eq_min block channel hdebt
  have hmin : 0 ≤
      min (block.survival * debt) (block.charge.value channel) :=
    le_min (mul_nonneg block.survival_nonneg hdebt)
      (block.charge.nonneg channel)
  linarith

theorem act_le_debt
    (block : Block κ) (channel : κ) {debt : ℝ} (hdebt : 0 ≤ debt) :
    block.act channel debt ≤ debt := by
  exact (act_le_survival_mul_debt block channel hdebt).trans
    (mul_le_of_le_one_left hdebt block.survival_le_one)

/-- Zero debt after the block is exactly the obstacle inequality. -/
theorem act_eq_zero_iff
    (block : Block κ) (channel : κ) (debt : ℝ) :
    block.act channel debt = 0 ↔
      block.survival * debt ≤ block.charge.value channel := by
  unfold act
  constructor
  · intro hzero
    by_contra hnot
    have hpos : 0 < block.survival * debt - block.charge.value channel := by
      linarith
    rw [max_eq_right hpos.le] at hzero
    linarith
  · intro hle
    rw [max_eq_left (sub_nonpos.mpr hle)]

/-- A positive debt is preserved exactly only on the unit-survival,
zero-charge face. -/
theorem act_eq_self_iff_of_pos
    (block : Block κ) (channel : κ) {debt : ℝ} (hdebt : 0 < debt) :
    block.act channel debt = debt ↔
      block.survival = 1 ∧ block.charge.value channel = 0 := by
  constructor
  · intro heq
    have haccount := debt_sub_act_eq_killed_add_min
      block channel hdebt.le
    rw [heq, sub_self] at haccount
    have hkilled : 0 ≤ (1 - block.survival) * debt :=
      mul_nonneg (sub_nonneg.mpr block.survival_le_one) hdebt.le
    have hmin : 0 ≤
        min (block.survival * debt) (block.charge.value channel) :=
      le_min (mul_nonneg block.survival_nonneg hdebt.le)
        (block.charge.nonneg channel)
    have hsurvival : block.survival = 1 := by
      have : (1 - block.survival) * debt = 0 := by linarith
      rcases mul_eq_zero.mp this with hsurvival | hdebtZero
      · linarith
      · exact False.elim (ne_of_gt hdebt hdebtZero)
    have hcharge : block.charge.value channel = 0 := by
      rw [hsurvival, one_mul] at haccount
      have hminZero : min debt (block.charge.value channel) = 0 := by
        linarith
      by_cases hle : debt ≤ block.charge.value channel
      · rw [min_eq_left hle] at hminZero
        linarith
      · rw [min_eq_right (le_of_not_ge hle)] at hminZero
        exact hminZero
    exact ⟨hsurvival, hcharge⟩
  · rintro ⟨hsurvival, hcharge⟩
    unfold act
    rw [hsurvival, hcharge, one_mul, sub_zero, max_eq_right hdebt.le]

/-- Positive output removes the truncation and gives exact conservation. -/
theorem survival_mul_debt_eq_act_add_charge_of_act_pos
    (block : Block κ) (channel : κ) (debt : ℝ)
    (hpositive : 0 < block.act channel debt) :
    block.survival * debt =
      block.act channel debt + block.charge.value channel := by
  unfold act at hpositive ⊢
  have hargument :
      0 < block.survival * debt - block.charge.value channel := by
    by_contra hnot
    rw [max_eq_left (by linarith)] at hpositive
    linarith
  rw [max_eq_right hargument.le]
  ring

/-- Division-free rigidity from a small debt drop: a positive debt forces
the killed-survival contribution to be small. -/
theorem killed_mul_lowerDebt_le_of_debt_sub_act_le
    (block : Block κ) (channel : κ) {debt lower error : ℝ}
    (hdebt : lower ≤ debt) (hlower : 0 ≤ lower)
    (hdrop : debt - block.act channel debt ≤ error) :
    (1 - block.survival) * lower ≤ error := by
  have hdebtNonneg := hlower.trans hdebt
  have haccount := debt_sub_act_eq_killed_add_min
    block channel hdebtNonneg
  have hkilledNonneg : 0 ≤ 1 - block.survival :=
    sub_nonneg.mpr block.survival_le_one
  have hlowerKilled :
      (1 - block.survival) * lower ≤
        (1 - block.survival) * debt :=
    mul_le_mul_of_nonneg_left hdebt hkilledNonneg
  have hmin : 0 ≤
      min (block.survival * debt) (block.charge.value channel) :=
    le_min (mul_nonneg block.survival_nonneg hdebtNonneg)
      (block.charge.nonneg channel)
  linarith

/-- If survived debt exceeds the permitted drop, the whole selected charge is
bounded by that drop. -/
theorem charge_le_of_debt_sub_act_le_of_error_lt_survived
    (block : Block κ) (channel : κ) {debt error : ℝ}
    (hdebt : 0 ≤ debt)
    (hdrop : debt - block.act channel debt ≤ error)
    (hstrict : error < block.survival * debt) :
    block.charge.value channel ≤ error := by
  have haccount := debt_sub_act_eq_killed_add_min block channel hdebt
  have hkilled : 0 ≤ (1 - block.survival) * debt :=
    mul_nonneg (sub_nonneg.mpr block.survival_le_one) hdebt
  have hminLe :
      min (block.survival * debt) (block.charge.value channel) ≤ error := by
    linarith
  by_cases hcharge : block.charge.value channel ≤ block.survival * debt
  · rw [min_eq_right hcharge] at hminLe
    exact hminLe
  · rw [min_eq_left (le_of_not_ge hcharge)] at hminLe
    linarith

/-! ## Finite words -/

/-- Chronological concatenation of a finite block word. -/
def concatList : List (Block κ) → Block κ
  | [] => identity
  | block :: blocks => concat block (concatList blocks)

@[simp]
theorem concatList_nil : concatList ([] : List (Block κ)) = identity := rfl

@[simp]
theorem concatList_cons (block : Block κ) (blocks : List (Block κ)) :
    concatList (block :: blocks) = concat block (concatList blocks) := rfl

/-- A finite block word acts by the corresponding finite composition. -/
theorem act_concatList
    (blocks : List (Block κ)) (channel : κ) {debt : ℝ}
    (hdebt : 0 ≤ debt) :
    (concatList blocks).act channel debt =
      List.foldr (fun block carried => block.act channel carried) debt blocks := by
  induction blocks with
  | nil => exact act_identity_of_nonneg channel hdebt
  | cons block blocks ih =>
      simp only [concatList_cons, act_concat, List.foldr_cons, ih]

/-- A positive folded debt gives exact aggregate conservation. -/
theorem concatList_survival_mul_debt_eq_act_add_charge_of_pos
    (blocks : List (Block κ)) (channel : κ) (debt : ℝ)
    (hpositive : 0 < (concatList blocks).act channel debt) :
    (concatList blocks).survival * debt =
      (concatList blocks).act channel debt +
        (concatList blocks).charge.value channel :=
  survival_mul_debt_eq_act_add_charge_of_act_pos
    (concatList blocks) channel debt hpositive

end Block
end SurvivalWeightedObstruction
end Math
