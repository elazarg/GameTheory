/-
# Why sequential consistency is a limit notion

A sequence of genuinely mixed Boolean laws can converge pointwise to a pure
law. This is the smallest witness that the topology in sequential consistency
does real work: fully mixed approximants need not have a fully mixed limit.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import GameTheory.Analysis.Protocol.Sequential

noncomputable section

namespace GameTheory.Analysis.Protocol.Examples

open Filter GameTheory GameTheory.Math.Probability

/-- A vanishing but strictly positive tremble. -/
def trembleWeight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 2)

theorem trembleWeight_pos (n : ℕ) :
    0 < trembleWeight n := by
  dsimp [trembleWeight]
  exact one_div_pos.mpr
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))

theorem trembleWeight_nonneg (n : ℕ) :
    0 ≤ trembleWeight n :=
  (trembleWeight_pos n).le

theorem trembleWeight_lt_one (n : ℕ) :
    trembleWeight n < 1 := by
  dsimp [trembleWeight]
  apply (div_lt_one
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))).2
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem trembleWeight_le_one (n : ℕ) :
    trembleWeight n ≤ 1 :=
  (trembleWeight_lt_one n).le

/-- Play `true` only with the vanishing tremble probability. -/
def tremblingLaw (n : ℕ) : PMF Bool :=
  mix (trembleWeight n)
    (trembleWeight_nonneg n) (trembleWeight_le_one n)
    (PMF.pure true) (PMF.pure false)

/-- Every approximant genuinely uses both actions. -/
theorem tremblingLaw_fullSupport (n : ℕ) :
    FullSupport (tremblingLaw n) := by
  intro value
  cases value
  · exact mem_support_mix_right _ _ _ (trembleWeight_lt_one n)
      ((PMF.mem_support_pure_iff _ _).mpr rfl)
  · exact mem_support_mix_left _ _ _ (trembleWeight_pos n)
      ((PMF.mem_support_pure_iff _ _).mpr rfl)

theorem trembleWeight_tendsto_zero :
    Tendsto trembleWeight atTop (nhds 0) := by
  have h :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
  convert h using 1
  funext n
  simp [trembleWeight, Function.comp_apply, Nat.cast_add]
  ring

/-- The fully mixed laws converge pointwise to pure `false`. -/
theorem tremblingLaw_tendsto_pureFalse :
    PMFConvergesPointwise tremblingLaw (PMF.pure false) :=
  pmfConvergesPointwise_mix_zero trembleWeight trembleWeight_nonneg
    trembleWeight_le_one trembleWeight_tendsto_zero _ _

/-- The limit itself is not fully mixed. -/
theorem pureFalse_not_fullSupport :
    ¬ FullSupport (PMF.pure false) := by
  intro hfull
  exact (by simp : true ∉ (PMF.pure false).support) (hfull true)

end GameTheory.Analysis.Protocol.Examples
