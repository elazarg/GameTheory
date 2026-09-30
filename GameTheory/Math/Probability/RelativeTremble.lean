/-
# Trembles negligible relative to varying reach

An approximating sequence can make some information events arbitrarily rare.
A positive tremble can still vanish faster than any prescribed positive lower
bound on their reach, without that bound converging, and a fixed number of
trembled decisions then loses negligible mass relative to it.
-/

import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace GameTheory.Math.Probability

open Filter

/-- A strictly positive scale chosen below both unit mass and the supplied
reach bound, with a further vanishing factor. -/
def relativeTremble (reach : ℕ → ℝ) (n : ℕ) : ℝ :=
  min (reach n) 1 / ((n : ℝ) + 1 + 1)

theorem relativeTremble_pos (reach : ℕ → ℝ) (positive : ∀ n, 0 < reach n) (n : ℕ) :
    0 < relativeTremble reach n := by
  unfold relativeTremble
  exact div_pos (lt_min (positive n) zero_lt_one) (by positivity)

theorem relativeTremble_le_rate (reach : ℕ → ℝ) (n : ℕ) :
    relativeTremble reach n ≤ 1 / ((n : ℝ) + 1 + 1) := by
  unfold relativeTremble
  exact div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)

theorem relativeTremble_lt_one (reach : ℕ → ℝ) (n : ℕ) :
    relativeTremble reach n < 1 := by
  apply (relativeTremble_le_rate reach n).trans_lt
  apply (div_lt_one (by positivity)).mpr
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

theorem relativeTremble_div_le_rate (reach : ℕ → ℝ)
    (positive : ∀ n, 0 < reach n) (n : ℕ) :
    relativeTremble reach n / reach n ≤ 1 / ((n : ℝ) + 1 + 1) := by
  apply (div_le_iff₀ (positive n)).mpr
  unfold relativeTremble
  have bound := div_le_div_of_nonneg_right (min_le_left (reach n) 1)
    (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1 + 1)
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using bound

private theorem relativeTremble_rate_tendsto :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1 + 1)) atTop (nhds 0) := by
  have base : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have limit := base.comp
    (Filter.tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using limit

theorem relativeTremble_tendsto (reach : ℕ → ℝ) (positive : ∀ n, 0 < reach n) :
    Tendsto (relativeTremble reach) atTop (nhds 0) :=
  squeeze_zero (fun n => (relativeTremble_pos reach positive n).le)
    (relativeTremble_le_rate reach) relativeTremble_rate_tendsto

/-- The added histories can be made negligible even when the original
information-set mass tends to zero at an arbitrary rate. -/
theorem relativeTremble_div_tendsto (reach : ℕ → ℝ)
    (positive : ∀ n, 0 < reach n) :
    Tendsto (fun n => relativeTremble reach n / reach n) atTop (nhds 0) :=
  squeeze_zero (fun n => div_nonneg (relativeTremble_pos reach positive n).le
    (positive n).le) (relativeTremble_div_le_rate reach positive)
      relativeTremble_rate_tendsto

private theorem power_loss_le (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (atMostOne : epsilon ≤ 1) (steps : Nat) :
    1 - (1 - epsilon) ^ steps ≤ steps * epsilon := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      have factorBound : (1 - epsilon) ^ steps ≤ 1 :=
        pow_le_one₀ (sub_nonneg.mpr atMostOne) (by linarith)
      have extra := mul_le_mul_of_nonneg_right factorBound nonnegative
      rw [pow_succ]
      push_cast
      nlinarith

/-- A fixed finite number of perturbed decisions loses negligible mass
relative to the supplied reach bound, including the conditional normalization. -/
theorem relativeTremble_power_ratio_tendsto (reach : ℕ → ℝ)
    (positive : ∀ n, 0 < reach n) (steps : Nat) :
    Tendsto (fun n => (1 - (1 - relativeTremble reach n) ^ steps) /
      ((1 - relativeTremble reach n) ^ steps * reach n)) atTop (nhds 0) := by
  have factorLimit : Tendsto (fun n => (1 - relativeTremble reach n) ^ steps)
      atTop (nhds 1) := by
    simpa only [sub_zero, one_pow] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub
        (relativeTremble_tendsto reach positive)).pow steps
  have lossLimit : Tendsto (fun n =>
      (1 - (1 - relativeTremble reach n) ^ steps) / reach n) atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      apply div_nonneg _ (positive n).le
      apply sub_nonneg.mpr
      exact pow_le_one₀ (sub_pos.mpr (relativeTremble_lt_one reach n)).le
        (by linarith [relativeTremble_pos reach positive n])
    · intro n
      have loss := power_loss_le (relativeTremble reach n)
        (relativeTremble_pos reach positive n).le (relativeTremble_lt_one reach n).le steps
      exact (div_le_div_of_nonneg_right loss (positive n).le).trans_eq
        (show ((steps : ℝ) * relativeTremble reach n) / reach n =
          (steps : ℝ) * (relativeTremble reach n / reach n) by ring)
    · simpa only [mul_zero] using
        (relativeTremble_div_tendsto reach positive).const_mul (steps : ℝ)
  have quotient := lossLimit.div factorLimit (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun n => ((1 - (1 - relativeTremble reach n) ^ steps) / reach n) /
    ((1 - relativeTremble reach n) ^ steps)) atTop (nhds (0 / (1 : ℝ))) at quotient
  simpa only [div_div, mul_comm, zero_div] using quotient

end GameTheory.Math.Probability
