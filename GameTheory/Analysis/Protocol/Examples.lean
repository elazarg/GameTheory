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
def tremblingLaw (n : ℕ) : FinDist Bool :=
  FinDist.mix (trembleWeight n)
    (trembleWeight_nonneg n) (trembleWeight_le_one n)
    (FinDist.pure true) (FinDist.pure false)

/-- Every approximant genuinely uses both actions. -/
theorem tremblingLaw_fullSupport (n : ℕ) :
    (tremblingLaw n).FullSupport := by
  intro value
  rw [← FinDist.prob_pos_iff]
  rw [tremblingLaw, FinDist.prob_mix]
  cases value
  · rw [FinDist.prob_pure_of_ne (by decide),
      FinDist.prob_pure_self]
    simpa using sub_pos.mpr (trembleWeight_lt_one n)
  · rw [FinDist.prob_pure_self,
      FinDist.prob_pure_of_ne (by decide)]
    simpa using trembleWeight_pos n

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
    FinDistConvergesPointwise tremblingLaw (FinDist.pure false) := by
  intro value
  simp only [tremblingLaw, FinDist.prob_mix]
  cases value
  · simp only [
      FinDist.prob_pure_of_ne (a := false) (b := true) (by decide),
      FinDist.prob_pure_self, mul_zero, zero_add, mul_one]
    simpa using
      (tendsto_const_nhds.sub trembleWeight_tendsto_zero :
        Tendsto (fun n => 1 - trembleWeight n) atTop (nhds (1 - 0)))
  · simp only [FinDist.prob_pure_self,
      FinDist.prob_pure_of_ne (a := true) (b := false) (by decide),
      mul_one, mul_zero, add_zero]
    exact trembleWeight_tendsto_zero

/-- The limit itself is not fully mixed. -/
theorem pureFalse_not_fullSupport :
    ¬ (FinDist.pure false).FullSupport := by
  intro hfull
  exact (by simp : true ∉ (FinDist.pure false).support) (hfull true)

end GameTheory.Analysis.Protocol.Examples
