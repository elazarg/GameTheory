/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.OnlineLearning.AnytimeMultiplicativeWeights
import Math.OnlineLearning.CompletedEpochCalendar
import Math.Probability.SublinearLedger
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Burn-in shifts of the universal logarithmic calendar

A fixed burn-in shift of the universal epoch scale retains positivity and
convergence to zero, so every epoch can be placed inside an arbitrary
punctured neighborhood while keeping the same quadratic calendar.  The
epoch envelope read through that calendar charges the current epoch in full,
which also controls unfinished epochs, and stays sublinear.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology

namespace Math
namespace OnlineLearning

/-- Burn-in shift of the universal logarithmic scale.  This lets every epoch
lie inside an arbitrary punctured analytic neighborhood while retaining the
same quadratic calendar. -/
def shiftedUniversalEpochScale (startEpoch k : ℕ) : ℝ :=
  universalEpochScale (startEpoch + k)

/-- Every fixed burn-in shift retains convergence to zero. -/
theorem tendsto_shiftedUniversalEpochScale (startEpoch : ℕ) :
    Tendsto (shiftedUniversalEpochScale startEpoch)
      atTop (𝓝 0) := by
  apply tendsto_universalEpochScale.comp
  refine tendsto_atTop.2 fun K => ?_
  filter_upwards [eventually_ge_atTop K] with k hk
  omega

/-- Every shifted universal scale is positive. -/
theorem shiftedUniversalEpochScale_pos (startEpoch k : ℕ) :
    0 < shiftedUniversalEpochScale startEpoch k :=
  universalEpochScale_pos _

/-- An epoch envelope read through the quadratic anytime calendar.  The
current epoch is charged in full, so the definition also controls unfinished
epochs. -/
def completedAndCurrentEpochBudget (epochBudget : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (anytimeEpochIndex T), epochBudget k) +
    epochBudget (anytimeEpochIndex T)

private theorem tendsto_localAnytimeEpochIndex :
    Tendsto anytimeEpochIndex atTop atTop := by
  refine tendsto_atTop.2 fun K => ?_
  filter_upwards
    [eventually_ge_atTop (epochStart anytimeEpochLength K)] with t ht
  exact anytimeEpochIndex_ge_of_start_le ht

/-- Any nonnegative per-epoch bill which is little-o of the quadratic epoch
length has a sublinear completed-plus-current calendar budget. -/
theorem completedAndCurrentEpochBudget_sublinear
    (epochBudget : ℕ → ℝ)
    (hnonneg : ∀ k, 0 ≤ epochBudget k)
    (hratio :
      Tendsto
        (fun k : ℕ =>
          epochBudget k / (anytimeEpochLength k : ℝ))
        atTop (𝓝 0)) :
    Probability.IsAsymptoticallySublinear
      (completedAndCurrentEpochBudget epochBudget) := by
  let lengthR : ℕ → ℝ := fun k => (anytimeEpochLength k : ℝ)
  let startR : ℕ → ℝ :=
    fun k => (epochStart anytimeEpochLength k : ℝ)
  have hlength_ne (k : ℕ) : lengthR k = 0 → epochBudget k = 0 := by
    intro hzero
    have : (0 : ℝ) < lengthR k := by
      dsimp only [lengthR]
      simp only [anytimeEpochLength]
      positivity
    exact (ne_of_gt this hzero).elim
  have hbudget_length :
      epochBudget =o[atTop] lengthR := by
    apply
      (Asymptotics.isLittleO_iff_tendsto
        hlength_ne).2
    simpa only [lengthR] using hratio
  have hlength_start :
      lengthR =O[atTop] startR := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨6, eventually_atTop.2 ⟨1, ?_⟩⟩
    intro k hk
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hstart_nonneg : 0 ≤ startR k := by
      dsimp only [startR]
      positivity
    have hlength_nonneg : 0 ≤ lengthR k := by
      dsimp only [lengthR]
      positivity
    rw [Real.norm_of_nonneg hlength_nonneg,
      Real.norm_of_nonneg hstart_nonneg]
    dsimp only [lengthR, startR]
    rw [anytimeEpochStart_cast]
    simp only [anytimeEpochLength]
    push_cast
    have hfactor :
        0 ≤ (k : ℝ) * ((k : ℝ) + 1) := by positivity
    nlinarith [mul_nonneg hfactor (by positivity :
      0 ≤ 2 * (k : ℝ) + 1)]
  have hbudget_start :
      epochBudget =o[atTop] startR :=
    hbudget_length.trans_isBigO hlength_start
  have hstart_sum :
      (fun K : ℕ => ∑ k ∈ Finset.range K, lengthR k) = startR := by
    funext K
    simp only [lengthR, startR, epochStart]
    norm_cast
  have hsum_length :
      Tendsto
        (fun K : ℕ => ∑ k ∈ Finset.range K, lengthR k)
        atTop atTop := by
    rw [hstart_sum]
    apply Filter.tendsto_atTop_mono' atTop
      (f₁ := fun K : ℕ => (K : ℝ))
    · filter_upwards [] with K
      dsimp only [startR]
      exact_mod_cast le_anytimeEpochStart K
    · exact tendsto_natCast_atTop_atTop
  have hsum_budget_start :
      (fun K : ℕ =>
        ∑ k ∈ Finset.range K, epochBudget k) =o[atTop]
          startR := by
    rw [← hstart_sum]
    exact hbudget_length.sum_range
      (fun k => by
        dsimp only [lengthR]
        positivity)
      hsum_length
  have hcompleted_ratio :
      Tendsto
        (fun K : ℕ =>
          (∑ k ∈ Finset.range K, epochBudget k) / startR K)
        atTop (𝓝 0) :=
    hsum_budget_start.tendsto_div_nhds_zero
  have hcurrent_ratio :
      Tendsto
        (fun K : ℕ => epochBudget K / startR K)
        atTop (𝓝 0) :=
    hbudget_start.tendsto_div_nhds_zero
  have hindex_ratio :
      Tendsto
        (fun T : ℕ =>
          ((∑ k ∈ Finset.range (anytimeEpochIndex T),
              epochBudget k) +
            epochBudget (anytimeEpochIndex T)) /
              startR (anytimeEpochIndex T))
        atTop (𝓝 0) := by
    have hratioK :
        Tendsto
          (fun K : ℕ =>
            ((∑ k ∈ Finset.range K, epochBudget k) +
              epochBudget K) / startR K)
          atTop (𝓝 0) := by
      simpa only [add_div, zero_add] using
        hcompleted_ratio.add hcurrent_ratio
    exact hratioK.comp tendsto_localAnytimeEpochIndex
  rw [Probability.isAsymptoticallySublinear_iff_tendsto]
  apply squeeze_zero'
    (g := fun T : ℕ =>
      ((∑ k ∈ Finset.range (anytimeEpochIndex T),
          epochBudget k) +
        epochBudget (anytimeEpochIndex T)) /
          startR (anytimeEpochIndex T))
  · filter_upwards [] with T
    exact mul_nonneg
      (inv_nonneg.mpr (Nat.cast_nonneg T))
      (add_nonneg
        (Finset.sum_nonneg fun k _ => hnonneg k)
        (hnonneg _))
  · filter_upwards
      [eventually_ge_atTop 1,
        (tendsto_localAnytimeEpochIndex.eventually
          (eventually_ge_atTop 1))] with T hT hindex
    have hstart_pos :
        0 < startR (anytimeEpochIndex T) := by
      dsimp only [startR]
      rw [anytimeEpochStart_cast]
      positivity
    have hT_pos : (0 : ℝ) < T := by exact_mod_cast hT
    have hstart_le :
        startR (anytimeEpochIndex T) ≤ (T : ℝ) := by
      dsimp only [startR]
      exact_mod_cast anytimeEpochStart_index_le T
    have hbudget_nonneg :
        0 ≤ completedAndCurrentEpochBudget epochBudget T :=
      add_nonneg
        (Finset.sum_nonneg fun k _ => hnonneg k)
        (hnonneg _)
    rw [show
      (T : ℝ)⁻¹ *
          completedAndCurrentEpochBudget epochBudget T =
        completedAndCurrentEpochBudget epochBudget T / T by
          rw [div_eq_mul_inv, mul_comm]]
    exact div_le_div_of_nonneg_left
      hbudget_nonneg hstart_pos hstart_le
  · simpa only [completedAndCurrentEpochBudget] using hindex_ratio

end OnlineLearning
end Math
