/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ProbabilityMassFunction

/-!
# Coordinate tests for finite PMFs

Centered signed coordinate observables that separate distinct finite
probability mass functions.
-/

noncomputable section

namespace Math
namespace Probability

/-- One member of the fixed signed-coordinate test family for a baseline PMF.
The Boolean chooses the positive or negative orientation. -/
noncomputable def pmfCoordinateTestScore {Ω : Type}
    [DecidableEq Ω] (baseline : PMF Ω) (t : Ω) (positive : Bool)
    (x : Ω) : ℝ :=
  (if positive then 1 else -1) *
    ((Pi.single t (1 : ℝ) : Ω → ℝ) x - (baseline t).toReal)

/-- Expected signed-coordinate score under an arbitrary comparison PMF. -/
theorem expect_pmfCoordinateTestScore {Ω : Type}
    [Finite Ω] [DecidableEq Ω] (baseline comparison : PMF Ω)
    (t : Ω) (positive : Bool) :
    expect comparison (pmfCoordinateTestScore baseline t positive) =
      (if positive then 1 else -1) *
        ((comparison t).toReal - (baseline t).toReal) := by
  unfold pmfCoordinateTestScore
  rw [expect_const_mul, expect_sub, expect_pi_single, expect_const]

/-- Every fixed coordinate test is centered under the baseline PMF. -/
theorem expect_pmfCoordinateTestScore_baseline {Ω : Type}
    [Finite Ω] [DecidableEq Ω] (baseline : PMF Ω)
    (t : Ω) (positive : Bool) :
    expect baseline (pmfCoordinateTestScore baseline t positive) = 0 := by
  rw [expect_pmfCoordinateTestScore]
  ring

/-- Every fixed coordinate-test increment has absolute value at most one. -/
theorem abs_pmfCoordinateTestScore_le_one {Ω : Type}
    [DecidableEq Ω] (baseline : PMF Ω)
    (t : Ω) (positive : Bool) (x : Ω) :
    |pmfCoordinateTestScore baseline t positive x| ≤ 1 := by
  have hmass_nonneg : 0 ≤ (baseline t).toReal :=
    ENNReal.toReal_nonneg
  have hmass_le_one : (baseline t).toReal ≤ 1 := by
    have h :=
      (ENNReal.toReal_le_toReal
        (PMF.apply_ne_top baseline t) ENNReal.one_ne_top).2
          (baseline.coe_le_one t)
    simpa using h
  unfold pmfCoordinateTestScore
  rw [abs_mul]
  have horientation :
      |if positive then (1 : ℝ) else -1| = 1 := by
    cases positive <;> norm_num
  rw [horientation, one_mul, Pi.single_apply]
  by_cases hx : x = t
  · rw [if_pos hx, abs_of_nonneg (sub_nonneg.mpr hmass_le_one)]
    linarith
  · rw [if_neg hx, zero_sub, abs_neg, abs_of_nonneg hmass_nonneg]
    exact hmass_le_one

/-- Affine shifting puts every coordinate-test score in the unit interval
consumed by the multiplicative-weights regret theorem. -/
theorem pmfCoordinateTestScore_unitShift_mem_Icc {Ω : Type}
    [DecidableEq Ω] (baseline : PMF Ω)
    (t : Ω) (positive : Bool) (x : Ω) :
    (pmfCoordinateTestScore baseline t positive x + 1) / 2 ∈
      Set.Icc (0 : ℝ) 1 := by
  have hbound :=
    abs_pmfCoordinateTestScore_le_one baseline t positive x
  rw [abs_le] at hbound
  constructor <;> linarith

/-- The fixed finite family containing both signs at every coordinate
separates the baseline PMF from every distinct comparison PMF. -/
theorem exists_pmfCoordinateTestScore_comparison_pos {Ω : Type}
    [Finite Ω] [DecidableEq Ω] (baseline comparison : PMF Ω)
    (hne : baseline ≠ comparison) :
    ∃ t positive,
      0 < expect comparison
        (pmfCoordinateTestScore baseline t positive) := by
  have hcoordinate :
      ∃ t, (baseline t).toReal ≠ (comparison t).toReal := by
    by_contra h
    apply hne
    apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
    intro t
    by_contra ht
    exact h ⟨t, ht⟩
  obtain ⟨t, ht⟩ := hcoordinate
  by_cases hlt : (baseline t).toReal < (comparison t).toReal
  · refine ⟨t, true, ?_⟩
    rw [expect_pmfCoordinateTestScore]
    change 0 < (1 : ℝ) *
      ((comparison t).toReal - (baseline t).toReal)
    nlinarith
  · refine ⟨t, false, ?_⟩
    rw [expect_pmfCoordinateTestScore]
    change 0 < (-1 : ℝ) *
      ((comparison t).toReal - (baseline t).toReal)
    have hreverse : (comparison t).toReal < (baseline t).toReal :=
      lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm ht)
    linarith

/-- Signed surprise of one PMF coordinate, centered at its baseline mass and
oriented toward the comparison PMF. -/
noncomputable def signedPMFCoordinateScore {Ω : Type}
    [DecidableEq Ω] (baseline comparison : PMF Ω) (t x : Ω) : ℝ :=
  (if (baseline t).toReal < (comparison t).toReal then 1 else -1) *
    ((Pi.single t (1 : ℝ) : Ω → ℝ) x - (baseline t).toReal)

/-- The signed coordinate surprise is centered under its baseline PMF. -/
theorem expect_signedPMFCoordinateScore_baseline {Ω : Type}
    [Finite Ω] [DecidableEq Ω] (baseline comparison : PMF Ω) (t : Ω) :
    expect baseline (signedPMFCoordinateScore baseline comparison t) = 0 := by
  unfold signedPMFCoordinateScore
  rw [expect_const_mul, expect_sub, expect_pi_single, expect_const]
  ring

/-- If the selected coordinate masses differ, the oriented surprise has
strictly positive expectation under the comparison PMF. -/
theorem expect_signedPMFCoordinateScore_comparison_pos {Ω : Type}
    [Finite Ω] [DecidableEq Ω] (baseline comparison : PMF Ω) (t : Ω)
    (hne : (baseline t).toReal ≠ (comparison t).toReal) :
    0 < expect comparison
      (signedPMFCoordinateScore baseline comparison t) := by
  unfold signedPMFCoordinateScore
  rw [expect_const_mul, expect_sub, expect_pi_single, expect_const]
  by_cases hlt : (baseline t).toReal < (comparison t).toReal
  · rw [if_pos hlt]
    linarith
  · rw [if_neg hlt]
    have hreverse : (comparison t).toReal < (baseline t).toReal :=
      lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
    linarith

/-- The signed coordinate surprise has absolute value at most one. -/
theorem abs_signedPMFCoordinateScore_le_one {Ω : Type}
    [DecidableEq Ω] (baseline comparison : PMF Ω) (t x : Ω) :
    |signedPMFCoordinateScore baseline comparison t x| ≤ 1 := by
  have hmass_nonneg : 0 ≤ (baseline t).toReal :=
    ENNReal.toReal_nonneg
  have hmass_le_one : (baseline t).toReal ≤ 1 := by
    have h :=
      (ENNReal.toReal_le_toReal
        (PMF.apply_ne_top baseline t) ENNReal.one_ne_top).2
          (baseline.coe_le_one t)
    simpa using h
  unfold signedPMFCoordinateScore
  rw [abs_mul]
  have horientation :
      |if (baseline t).toReal < (comparison t).toReal then
          (1 : ℝ) else -1| = 1 := by
    split <;> norm_num
  rw [horientation, one_mul, Pi.single_apply]
  by_cases hx : x = t
  · rw [if_pos hx, abs_of_nonneg (sub_nonneg.mpr hmass_le_one)]
    linarith
  · rw [if_neg hx, zero_sub, abs_neg, abs_of_nonneg hmass_nonneg]
    exact hmass_le_one

end Probability
end Math
