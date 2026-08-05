/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingExceptionalTailFallback
import Math.BonferroniProductBounds

/-!
# The direction-barycenter chart of the vanishing-hazard sphere

Blow up the all-continue corner of the stationary hazard cube: write a hazard
vector as scale times direction, `h = H·ĥ` with `H = ∑ᵢ hᵢ`.  This file
proves the zeroth-order chart of that blow-up, exactly and division-free:

  `|H · v_who − ∑ᵢ hᵢ · r_who({i})| ≤ 6 · M · H²`     for `0 < H ≤ 1/2`,

where `v` is the stationary terminal payoff of the root with hazards `h`.
Thus stationary values factor through the direction simplex (the barycenter
`∑ ĥᵢ · r({i})` of singleton rewards) up to an error linear in the scale.
This is the quantitative content of the fourth stationary regime — hazards
tending to zero while the absorption distribution survives — and the chart in
which the normalized-direction escape and the owner-solo vertex analysis
live.

The proof needs only the Weierstrass product inequality, the partition of the
product law by quitter set, and the landed `absorbingContribution / (1 − m)`
representation of stationary values.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Weierstrass product inequality: `1 - ∑ f ≤ ∏ (1 - f)` for `f ∈ [0,1]`.
The rearranged form of `Math.one_sub_prod_one_sub_le_sum`, the first
Bonferroni bound. -/
private theorem one_sub_sum_le_prod_one_sub
    (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  have h := Math.one_sub_prod_one_sub_le_sum f s h0 h1
  linarith

/-- Sum of the players' stationary one-stage quit hazards. -/
def quittingStationaryTotalHazard (root : ι → PMF Bool) : ℝ :=
  ∑ i, (root i true).toReal

/-- Barycenter of singleton rewards under the normalized stationary hazard
direction.  This definition is intended for positive total hazard; at the
zero-hazard apex its divisions are left at Lean's totalized value. -/
def quittingStationarySingletonDirectionBarycenter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) : Payoff ι :=
  fun who ↦
    ∑ i, ((root i true).toReal / quittingStationaryTotalHazard root) *
      quittingSoloReward reward i who

omit [DecidableEq ι] in
/-- **Direction-barycenter chart.**  For a stationary root with total hazard
`H = ∑ᵢ hᵢ` in `(0, 1/2]`, the hazard-weighted stationary value is the
hazard-weighted barycenter of singleton rewards up to `6·M·H²`. -/
theorem abs_stationaryValue_sub_directionBarycenter_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : ∀ S who, |reward S who| ≤ M)
    (root : ι → PMF Bool) (who : ι)
    (hH0 : 0 < ∑ i, (root i true).toReal)
    (hH : ∑ i, (root i true).toReal ≤ 1 / 2) :
    |(∑ i, (root i true).toReal) *
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who -
      ∑ i, (root i true).toReal * quittingSoloReward reward i who| ≤
      6 * M * (∑ i, (root i true).toReal) ^ 2 := by
  classical
  -- Basic hazard facts.
  set hazard : ι → ℝ := fun i ↦ (root i true).toReal with hhazard
  set H : ℝ := ∑ i, hazard i with hHdef
  have hmarg : ∀ i, (root i false).toReal = 1 - hazard i := by
    intro i
    have hsum := pmf_toReal_sum_one (root i)
    rw [Fintype.sum_bool] at hsum
    linarith
  have hz0 : ∀ i, 0 ≤ hazard i := fun i ↦ ENNReal.toReal_nonneg
  have hz1 : ∀ i, hazard i ≤ 1 := by
    intro i
    have := ENNReal.toReal_nonneg (a := root i false)
    rw [hmarg i] at this
    linarith
  have hne : Nonempty ι := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    rw [hHdef, Finset.univ_eq_empty, Finset.sum_empty] at hH0
    exact lt_irrefl 0 hH0
  obtain ⟨i0⟩ := hne
  have hM0 : 0 ≤ M :=
    le_trans (abs_nonneg _) (hM ⟨{i0}, Finset.singleton_nonempty i0⟩ who)
  -- Product-law probabilities.
  set P : (ι → Bool) → ℝ := fun a ↦ ((pmfPi root) a).toReal with hPdef
  have hPprod : ∀ a, P a = ∏ i, (root i (a i)).toReal := by
    intro a
    change ((pmfPi root) a).toReal = _
    rw [pmfPi_apply, ENNReal.toReal_prod]
  have hPnn : ∀ a, 0 ≤ P a := fun a ↦ ENNReal.toReal_nonneg
  have hPsum : ∑ a : ι → Bool, P a = 1 := pmf_toReal_sum_one (pmfPi root)
  -- The all-continue mass.
  set m : ℝ := quittingStationaryContinueMass root with hmdef
  have hm : m = ∏ i, (1 - hazard i) := by
    change ((pmfPi root) (quittingAllContinueAction : ι → Bool)).toReal = _
    rw [show ((pmfPi root) (quittingAllContinueAction : ι → Bool)).toReal =
        P quittingAllContinueAction from rfl, hPprod]
    exact Finset.prod_congr rfl fun i _ ↦ by
      rw [show quittingAllContinueAction i = false from rfl, hmarg i]
  have hmH : 1 - H ≤ m := by
    rw [hm, hHdef]
    exact one_sub_sum_le_prod_one_sub Finset.univ hazard
      (fun i _ ↦ hz0 i) (fun i _ ↦ hz1 i)
  -- Solo-action probabilities.
  have hPsolo : ∀ i, P (quittingSoloAction i true) =
      hazard i * ∏ j ∈ Finset.univ.erase i, (1 - hazard j) := by
    intro i
    rw [hPprod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · rw [show quittingSoloAction i true i = true from by
        simp [quittingSoloAction]]
    · exact Finset.prod_congr rfl fun j hj ↦ by
        rw [show quittingSoloAction i true j = false from by
          simp [quittingSoloAction,
            Function.update_of_ne (Finset.mem_erase.mp hj).1], hmarg j]
  have hPsoloUp : ∀ i, P (quittingSoloAction i true) ≤ hazard i := by
    intro i
    rw [hPsolo i]
    exact mul_le_of_le_one_right (hz0 i)
      (Finset.prod_le_one (fun j hj ↦ by linarith [hz1 j])
        (fun j hj ↦ by linarith [hz0 j]))
  have hPsoloLow : ∀ i, hazard i * (1 - H) ≤ P (quittingSoloAction i true) := by
    intro i
    rw [hPsolo i]
    have herase : ∑ j ∈ Finset.univ.erase i, hazard j = H - hazard i := by
      have := Finset.add_sum_erase Finset.univ hazard (Finset.mem_univ i)
      rw [hHdef]
      linarith
    have hweier := one_sub_sum_le_prod_one_sub (Finset.univ.erase i) hazard
      (fun j _ ↦ hz0 j) (fun j _ ↦ hz1 j)
    rw [herase] at hweier
    have hmono : 1 - H ≤ 1 - (H - hazard i) := by linarith [hz0 i]
    exact mul_le_mul_of_nonneg_left (le_trans hmono hweier) (hz0 i)
  -- The partition of the action space.
  set solos : Finset (ι → Bool) :=
    Finset.univ.image (fun i ↦ quittingSoloAction i true) with hsolosdef
  have hinj : ∀ x ∈ (Finset.univ : Finset ι), ∀ y ∈ (Finset.univ : Finset ι),
      quittingSoloAction x true = quittingSoloAction y true → x = y := by
    intro x _ y _ hxy
    by_contra hne'
    have hx := congrFun hxy y
    rw [show quittingSoloAction x true y = false from by
        simp [quittingSoloAction, Function.update_of_ne (Ne.symm hne')],
      show quittingSoloAction y true y = true from by
        simp [quittingSoloAction]] at hx
    exact Bool.false_ne_true hx
  have hallContNotSolo : quittingAllContinueAction ∉ solos := by
    intro hmem
    obtain ⟨i, -, heq⟩ := Finset.mem_image.mp hmem
    have := congrFun heq i
    rw [show quittingSoloAction i true i = true from by
      simp [quittingSoloAction]] at this
    exact Bool.false_ne_true this.symm
  set core : Finset (ι → Bool) := insert quittingAllContinueAction solos
    with hcoredef
  have hsumSolosP : ∑ a ∈ solos, P a =
      ∑ i, P (quittingSoloAction i true) := by
    exact Finset.sum_image hinj
  have hsumCoreP : ∑ a ∈ core, P a =
      m + ∑ i, P (quittingSoloAction i true) := by
    rw [Finset.sum_insert hallContNotSolo, hsumSolosP]
    rfl
  have hcoreSub : core ⊆ Finset.univ := Finset.subset_univ core
  have hsdiffP : ∑ a ∈ Finset.univ \ core, P a =
      1 - (m + ∑ i, P (quittingSoloAction i true)) := by
    have htotal := Finset.sum_sdiff (f := P) hcoreSub
    rw [hsumCoreP, hPsum] at htotal
    linarith
  have hsdiffPnn : 0 ≤ ∑ a ∈ Finset.univ \ core, P a :=
    Finset.sum_nonneg fun a _ ↦ hPnn a
  -- Aggregate solo-mass bounds.
  have hSoloSumUp : ∑ i, P (quittingSoloAction i true) ≤ H := by
    rw [hHdef]
    exact Finset.sum_le_sum fun i _ ↦ hPsoloUp i
  have hSoloSumLow : H * (1 - H) ≤ ∑ i, P (quittingSoloAction i true) := by
    calc H * (1 - H) = ∑ i, hazard i * (1 - H) := by
          rw [hHdef, Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦ hPsoloLow i
  have hD_low : H * (1 - H) ≤ 1 - m := by linarith
  have hD_up : 1 - m ≤ H := by linarith
  have hDpos : 0 < 1 - m :=
    lt_of_lt_of_le (mul_pos hH0 (by linarith)) hD_low
  have hquit : m < 1 := by linarith
  -- Absorbing contribution split.
  set payoffAt : (ι → Bool) → ℝ :=
    fun a ↦ quittingRootPayoff reward (0 : Payoff ι) a who with hpayoffdef
  have hpayoffBound : ∀ a, |payoffAt a| ≤ M := by
    intro a
    exact abs_quittingRootPayoff_le reward (0 : Payoff ι) hM
      (fun k ↦ by simpa using hM0) a who
  have hpayoffSolo : ∀ i, payoffAt (quittingSoloAction i true) =
      quittingSoloReward reward i who := by
    intro i
    change quittingRootPayoff reward (0 : Payoff ι)
      (quittingSoloAction i true) who = _
    unfold quittingRootPayoff quittingSoloReward
    simp
  have hpayoffContinue : payoffAt quittingAllContinueAction = 0 := by
    change quittingRootPayoff reward (0 : Payoff ι)
      quittingAllContinueAction who = 0
    unfold quittingRootPayoff
    rw [dif_neg]
    · rfl
    · simp [quittingQuitters, quittingAllContinueAction]
  set A : ℝ := quittingRootAbsorbingContribution reward root who with hAdef
  have hA : A = ∑ a : ι → Bool, P a * payoffAt a := by
    change quittingRootAbsorbingContribution reward root who = _
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    exact expect_eq_sum (pmfPi root) _
  have hAsplit : A =
      (∑ i, P (quittingSoloAction i true) * quittingSoloReward reward i who) +
        ∑ a ∈ Finset.univ \ core, P a * payoffAt a := by
    rw [hA, ← Finset.sum_sdiff (f := fun a ↦ P a * payoffAt a) hcoreSub,
      add_comm]
    congr 1
    rw [Finset.sum_insert hallContNotSolo, hpayoffContinue, mul_zero,
      zero_add]
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hpayoffSolo i]
  -- The two H² errors.
  have hRemainder : |∑ a ∈ Finset.univ \ core, P a * payoffAt a| ≤
      M * H ^ 2 := by
    calc |∑ a ∈ Finset.univ \ core, P a * payoffAt a| ≤
        ∑ a ∈ Finset.univ \ core, |P a * payoffAt a| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Finset.univ \ core, P a * M := by
          refine Finset.sum_le_sum fun a _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (hPnn a)]
          exact mul_le_mul_of_nonneg_left (hpayoffBound a) (hPnn a)
      _ = (∑ a ∈ Finset.univ \ core, P a) * M := by
          rw [Finset.sum_mul]
      _ ≤ H ^ 2 * M := by
          refine mul_le_mul_of_nonneg_right ?_ hM0
          rw [hsdiffP]
          nlinarith
      _ = M * H ^ 2 := by ring
  have hSoloApprox :
      |(∑ i, P (quittingSoloAction i true) * quittingSoloReward reward i who) -
        ∑ i, hazard i * quittingSoloReward reward i who| ≤ M * H ^ 2 := by
    have hsr : ∀ i, |quittingSoloReward reward i who| ≤ M := by
      intro i
      exact hM ⟨{i}, Finset.singleton_nonempty i⟩ who
    calc |(∑ i, P (quittingSoloAction i true) *
            quittingSoloReward reward i who) -
          ∑ i, hazard i * quittingSoloReward reward i who| =
        |∑ i, (P (quittingSoloAction i true) - hazard i) *
            quittingSoloReward reward i who| := by
          rw [← Finset.sum_sub_distrib]
          congr 1
          exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ ≤ ∑ i, |(P (quittingSoloAction i true) - hazard i) *
            quittingSoloReward reward i who| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (hazard i - P (quittingSoloAction i true)) * M := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [abs_mul, abs_of_nonpos (by linarith [hPsoloUp i]), neg_sub]
          exact mul_le_mul (le_refl _) (hsr i) (abs_nonneg _)
            (by linarith [hPsoloUp i])
      _ = (H - ∑ i, P (quittingSoloAction i true)) * M := by
          rw [← Finset.sum_mul, Finset.sum_sub_distrib, hHdef]
      _ ≤ H ^ 2 * M := by
          refine mul_le_mul_of_nonneg_right ?_ hM0
          nlinarith
      _ = M * H ^ 2 := by ring
  have hAclose : |A - ∑ i, hazard i * quittingSoloReward reward i who| ≤
      2 * M * H ^ 2 := by
    rw [hAsplit]
    calc |((∑ i, P (quittingSoloAction i true) *
            quittingSoloReward reward i who) +
          ∑ a ∈ Finset.univ \ core, P a * payoffAt a) -
          ∑ i, hazard i * quittingSoloReward reward i who| ≤
        |(∑ i, P (quittingSoloAction i true) *
            quittingSoloReward reward i who) -
          ∑ i, hazard i * quittingSoloReward reward i who| +
          |∑ a ∈ Finset.univ \ core, P a * payoffAt a| := by
          rw [add_sub_right_comm]
          exact abs_add_le _ _
      _ ≤ M * H ^ 2 + M * H ^ 2 := add_le_add hSoloApprox hRemainder
      _ = 2 * M * H ^ 2 := by ring
  -- Assemble through the division representation of the stationary value.
  set S : ℝ := ∑ i, hazard i * quittingSoloReward reward i who with hSdef
  have hSbound : |S| ≤ M * H := by
    calc |∑ i, hazard i * quittingSoloReward reward i who| ≤
        ∑ i, |hazard i * quittingSoloReward reward i who| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, hazard i * M := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (hz0 i)]
          exact mul_le_mul_of_nonneg_left
            (hM ⟨{i}, Finset.singleton_nonempty i⟩ who) (hz0 i)
      _ = H * M := by rw [← Finset.sum_mul, hHdef]
      _ = M * H := by ring
  have hvalue : quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) who = A / (1 - m) := by
    exact quittingTerminalPayoff_stationary_eq_absorbingContribution_div
      reward root who hquit
  rw [hvalue]
  have hexpand : H * (A / (1 - m)) - S = (H * A - S * (1 - m)) / (1 - m) := by
    field_simp
  rw [hexpand, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
  have hkey : H * A - S * (1 - m) = H * (A - S) + S * (H - (1 - m)) := by
    ring
  have hHD2 : H - (1 - m) ≤ H ^ 2 := by nlinarith
  have hHD0 : 0 ≤ H - (1 - m) := by linarith
  calc |H * A - S * (1 - m)| = |H * (A - S) + S * (H - (1 - m))| := by
        rw [hkey]
    _ ≤ |H * (A - S)| + |S * (H - (1 - m))| := abs_add_le _ _
    _ = H * |A - S| + |S| * (H - (1 - m)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt hH0),
          abs_of_nonneg hHD0]
    _ ≤ H * (2 * M * H ^ 2) + (M * H) * H ^ 2 := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left (by simpa [hSdef] using hAclose)
            (le_of_lt hH0)
        · exact mul_le_mul hSbound hHD2 hHD0 (by positivity)
    _ = 3 * M * H ^ 3 := by ring
    _ ≤ 6 * M * H ^ 2 * (1 - m) := by
        have hcube : 0 ≤ M * H ^ 3 * (1 - 2 * H) :=
          mul_nonneg (mul_nonneg hM0 (le_of_lt (pow_pos hH0 3)))
            (by linarith)
        have hstep : 6 * M * H ^ 2 * (H * (1 - H)) ≤
            6 * M * H ^ 2 * (1 - m) :=
          mul_le_mul_of_nonneg_left hD_low
            (mul_nonneg (mul_nonneg (by norm_num) hM0) (sq_nonneg H))
        nlinarith [hcube, hstep]

omit [DecidableEq ι] in
/-- Normalized direction chart: the stationary payoff is within
`6·M·H` of the singleton-reward barycenter of its hazard direction. -/
theorem abs_stationaryPayoff_sub_singletonDirectionBarycenter_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : ∀ S who, |reward S who| ≤ M)
    (root : ι → PMF Bool) (who : ι)
    (hH0 : 0 < quittingStationaryTotalHazard root)
    (hH : quittingStationaryTotalHazard root ≤ 1 / 2) :
    |quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who -
        quittingStationarySingletonDirectionBarycenter reward root who| ≤
      6 * M * quittingStationaryTotalHazard root := by
  classical
  let H := quittingStationaryTotalHazard root
  let S := ∑ i, (root i true).toReal *
    quittingSoloReward reward i who
  have hmain :
      |H * quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who - S| ≤
        6 * M * H ^ 2 := by
    simpa [H, S, quittingStationaryTotalHazard] using
      abs_stationaryValue_sub_directionBarycenter_le
        reward hM root who hH0 hH
  have hHne : H ≠ 0 := ne_of_gt hH0
  have hbary :
      quittingStationarySingletonDirectionBarycenter reward root who =
        S / H := by
    unfold quittingStationarySingletonDirectionBarycenter
    dsimp only [S, H]
    calc
      (∑ i, ((root i true).toReal /
          quittingStationaryTotalHazard root) *
            quittingSoloReward reward i who) =
          ∑ i, ((root i true).toReal *
            quittingSoloReward reward i who) /
              quittingStationaryTotalHazard root := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, (root i true).toReal *
          quittingSoloReward reward i who) /
            quittingStationaryTotalHazard root := by
        rw [Finset.sum_div]
  rw [hbary]
  have hexpand :
      quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who - S / H =
        (H * quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who - S) / H := by
    field_simp [hHne]
  rw [hexpand, abs_div, abs_of_pos hH0]
  apply (div_le_iff₀ hH0).2
  calc
    |H * quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who - S| ≤
        6 * M * H ^ 2 := hmain
    _ = (6 * M * H) * H := by ring

end GameTheory
