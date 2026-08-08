/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Tactic

/-!
# Compact recurrence need not beat a vanishing contraction charge

Periodic closing of a marked segment has error proportional to

`endpoint seam / opponent-contraction gap`.

Compactness makes endpoint seams small in absolute terms, but it does not
make them small relative to a contraction gap which may vanish along the
selected sequence.  This file records the elementary scalar regression

`z n = 1/(n+1)`, `q n = 1/(n+1)^3`.

The states converge in a compact interval and every charge is positive, yet
for every strict pair `a < b`, the return seam is at least half of the charge
at `a`.  Thus no subsequence selection based on compactness alone can produce
`|z a - z b| = o(q a)`.
-/

noncomputable section

namespace GameTheory

namespace QuittingVanishingChargeRecurrenceNoGo

/-- A bounded convergent scalar state sequence. -/
def state (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- A positive charge which vanishes faster than adjacent state seams. -/
def charge (n : ℕ) : ℝ := 1 / (((n : ℝ) + 1) ^ 3)

theorem state_pos (n : ℕ) : 0 < state n := by
  unfold state
  positivity

theorem state_le_one (n : ℕ) : state n ≤ 1 := by
  unfold state
  have hn : 1 ≤ (n : ℝ) + 1 := by norm_num
  exact (div_le_one (by positivity)).2 hn

theorem charge_pos (n : ℕ) : 0 < charge n := by
  unfold charge
  positivity

/-- The state sequence is strictly decreasing. -/
theorem state_strictAnti : StrictAnti state := by
  intro a b hab
  unfold state
  have habCast : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have habReal : (a : ℝ) + 1 < (b : ℝ) + 1 := by
    linarith
  exact one_div_lt_one_div_of_lt (by positivity) habReal

/-- Every strict return seam is at least half the charge at its source. -/
theorem half_charge_le_returnSeam {a b : ℕ} (hab : a < b) :
    charge a / 2 ≤ |state a - state b| := by
  let A : ℝ := (a : ℝ) + 1
  let B : ℝ := (b : ℝ) + 1
  have hA : 1 ≤ A := by
    dsimp only [A]
    norm_num
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hAB : A < B := by
    dsimp only [A, B]
    have habCast : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    linarith
  have hBpos : 0 < B := hApos.trans hAB
  have hgap : 1 ≤ B - A := by
    dsimp only [A, B]
    have habCast : (a : ℝ) + 1 ≤ (b : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.2 hab)
    linarith
  have halgebra : B ≤ 2 * A ^ 2 * (B - A) := by
    have hAminus : 0 ≤ A - 1 := sub_nonneg.mpr hA
    have hfactor : 0 ≤ (2 * A + 1) * (A - 1) :=
      mul_nonneg (by positivity) hAminus
    have hgapNonneg : 0 ≤ B - A - 1 := sub_nonneg.mpr hgap
    have hcoefficient : 0 ≤ 2 * A ^ 2 - 1 := by nlinarith
    have hextra : 0 ≤ (B - A - 1) * (2 * A ^ 2 - 1) :=
      mul_nonneg hgapNonneg hcoefficient
    nlinarith
  have hstateDiff : 0 ≤ state a - state b :=
    sub_nonneg.mpr (state_strictAnti hab).le
  rw [abs_of_nonneg hstateDiff]
  change (1 / A ^ 3) / 2 ≤ 1 / A - 1 / B
  rw [div_div]
  have hleftDen : 0 < A ^ 3 * 2 := by positivity
  rw [div_le_iff₀ hleftDen]
  have hidentity :
      (1 / A - 1 / B) * (A ^ 3 * 2) =
        (2 * A ^ 2 / B) * (B - A) := by
    field_simp
  rw [hidentity]
  have hBden : 0 < B := hBpos
  rw [div_mul_eq_mul_div, le_div_iff₀ hBden]
  nlinarith

/-- In particular, no strict pair attains a seam smaller than one quarter of
its source charge. -/
theorem no_quarter_relativeReturn :
    ¬ ∃ a b : ℕ, a < b ∧ |state a - state b| < charge a / 4 := by
  rintro ⟨a, b, hab, hsmall⟩
  have hlower := half_charge_le_returnSeam hab
  have hcharge := charge_pos a
  linarith

end QuittingVanishingChargeRecurrenceNoGo

end GameTheory
