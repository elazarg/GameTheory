/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CapDebtBellmanReduction
import UniformEquilibrium.Quitting.Boundary.Repair.SureSetOwnerRepair
import UniformEquilibrium.Quitting.Classification.LCP.Normalization
import UniformEquilibrium.Quitting.Circulation.SingletonFlowMesh

/-!
# Finite positive-hazard approximants to an ideal singleton block

This file begins the carrier bridge for the three-core lasso. It computes one
exact positive-hazard semantic step. No ideal limit is postulated.
-/

noncomputable section

namespace GameTheory
namespace IdealSingletonBlockApproximation

open Math.Probability Math.PMFProduct
open Filter
open QuittingSureSetOwnerRepair
open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Only `owner` may quit, with probability `p`. -/
def singletonHazardRoot (owner : ι) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ι → PMF Bool :=
  quittingSureSetOwnerRoot ∅ owner p hp0 hp1

/-- Own-singleton payoff. -/
def ownSingleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) : ℝ :=
  reward (quittingProjectiveSingletonTerminal who) who

/-- Cap clearance above the own-singleton payoff. -/
def capClearance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (who : ι) : ℝ :=
  cap who - ownSingleton reward who

/-- Pair-collision surplus above the receiver's own singleton. -/
def pairSurplus
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) : ℝ :=
  reward ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who -
    ownSingleton reward who

/-! ## Scalar recurrence of one nonowner clearance -/

/-- One nonowner clearance update with Continue probability `β`. -/
def scalarClearanceStep (β A M t : ℝ) : ℝ :=
  max ((1 - β) * A) (β * t + (1 - β) * M)

/-- Repetition of the same singleton microstep. -/
def scalarClearanceIter (β A M t : ℝ) (n : ℕ) : ℝ :=
  (scalarClearanceStep β A M)^[n] t

@[simp] theorem scalarClearanceIter_zero (β A M t : ℝ) :
    scalarClearanceIter β A M t 0 = t := rfl

@[simp] theorem scalarClearanceIter_succ (β A M t : ℝ) (n : ℕ) :
    scalarClearanceIter β A M t (n + 1) =
      scalarClearanceStep β A M (scalarClearanceIter β A M t n) := by
  simp [scalarClearanceIter, Function.iterate_succ_apply']

/-- The unreflected affine orbit is a lower bound for the max recursion. -/
theorem affine_le_scalarClearanceIter
    {β A M t : ℝ} (hβ0 : 0 ≤ β) (n : ℕ) :
    β ^ n * t + (1 - β ^ n) * M ≤
      scalarClearanceIter β A M t n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [scalarClearanceIter_succ]
      unfold scalarClearanceStep
      apply le_max_of_le_right
      have hscaled := mul_le_mul_of_nonneg_left ih hβ0
      rw [pow_succ]
      nlinarith

/-- After at least one microstep the collision floor itself is a lower
bound. -/
theorem collisionFloor_le_scalarClearanceIter
    (β A M t : ℝ) (n : ℕ) :
    (1 - β) * A ≤ scalarClearanceIter β A M t (n + 1) := by
  rw [scalarClearanceIter_succ]
  exact le_max_left _ _

/-- A uniform upper envelope for the reflected affine recurrence. -/
theorem scalarClearanceIter_le_envelope
    {β A M t : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (n : ℕ) :
    scalarClearanceIter β A M t n ≤
      max (β ^ n * t + (1 - β ^ n) * M)
        ((1 - β) * max A 0 + max 0 ((1 - β ^ n) * M)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [scalarClearanceIter_succ]
      unfold scalarClearanceStep
      apply max_le
      · apply le_max_of_le_right
        exact le_trans
          (mul_le_mul_of_nonneg_left (le_max_left A 0)
            (sub_nonneg.mpr hβ1))
          (le_add_of_nonneg_right (le_max_left 0 _))
      · have hscaled := mul_le_mul_of_nonneg_left ih hβ0
        have hfirst :
            β * (β ^ n * t + (1 - β ^ n) * M) + (1 - β) * M =
              β ^ (n + 1) * t + (1 - β ^ (n + 1)) * M := by
          rw [pow_succ]
          ring
        have hmaxScale :
            β * max (β ^ n * t + (1 - β ^ n) * M)
                ((1 - β) * max A 0 + max 0 ((1 - β ^ n) * M)) +
                (1 - β) * M =
              max
                (β * (β ^ n * t + (1 - β ^ n) * M) + (1 - β) * M)
                (β * ((1 - β) * max A 0 +
                  max 0 ((1 - β ^ n) * M)) + (1 - β) * M) := by
          rw [mul_max_of_nonneg _ _ hβ0, max_add_add_right]
        calc
          β * scalarClearanceIter β A M t n + (1 - β) * M ≤
              β * max (β ^ n * t + (1 - β ^ n) * M)
                  ((1 - β) * max A 0 + max 0 ((1 - β ^ n) * M)) +
                (1 - β) * M := by
                  simpa [add_comm] using
                    (add_le_add_right hscaled ((1 - β) * M))
          _ = max
                (β * (β ^ n * t + (1 - β ^ n) * M) + (1 - β) * M)
                (β * ((1 - β) * max A 0 +
                  max 0 ((1 - β ^ n) * M)) + (1 - β) * M) := hmaxScale
          _ ≤ max (β ^ (n + 1) * t + (1 - β ^ (n + 1)) * M)
                ((1 - β) * max A 0 +
                  max 0 ((1 - β ^ (n + 1)) * M)) := by
            rw [hfirst]
            apply max_le (le_max_left _ _)
            apply le_max_of_le_right
            by_cases hM : 0 ≤ M
            · rw [max_eq_right (mul_nonneg (sub_nonneg.mpr
                  (pow_le_one₀ hβ0 hβ1)) hM),
                max_eq_right (mul_nonneg (sub_nonneg.mpr
                  (pow_le_one₀ hβ0 hβ1)) hM)]
              have hβmax : β * ((1 - β) * max A 0) ≤
                  (1 - β) * max A 0 := by
                nlinarith [mul_nonneg (sub_nonneg.mpr hβ1)
                  (le_max_right A 0)]
              rw [pow_succ]
              nlinarith
            · have hM' : M ≤ 0 := le_of_not_ge hM
              rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos
                  (sub_nonneg.mpr (pow_le_one₀ hβ0 hβ1)) hM'),
                max_eq_left (mul_nonpos_of_nonneg_of_nonpos
                  (sub_nonneg.mpr (pow_le_one₀ hβ0 hβ1)) hM')]
              have hterm : (1 - β) * M ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hβ1) hM'
              have hβmax : β * ((1 - β) * max A 0) ≤
                  (1 - β) * max A 0 := by
                nlinarith [mul_nonneg (sub_nonneg.mpr hβ1)
                  (le_max_right A 0)]
              linarith

/-- Quantitative approximation of the ideal reflected affine block.

If `n` repetitions have total Continue mass `α = β ^ n`, the only
error left by the per-stage collision floor is at most one micro-hazard
times `|A|`. -/
theorem scalarClearanceIter_approx_ideal
    {β α A M t : ℝ} {n : ℕ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hn : 0 < n)
    (hpow : β ^ n = α) (hα0 : 0 ≤ α) (ht0 : 0 ≤ t) :
    |scalarClearanceIter β A M t n -
        max 0 (α * t + (1 - α) * M)| ≤
      (1 - β) * |A| := by
  let u : ℝ := α * t + (1 - α) * M
  let target : ℝ := max 0 u
  let err : ℝ := (1 - β) * |A|
  have herr0 : 0 ≤ err :=
    mul_nonneg (sub_nonneg.mpr hβ1) (abs_nonneg A)
  have hlowAffine : u ≤ scalarClearanceIter β A M t n := by
    simpa [u, hpow] using
      (affine_le_scalarClearanceIter (A := A) (M := M) (t := t) hβ0 n)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hlowFloor : (1 - β) * A ≤
      scalarClearanceIter β A M t (k + 1) :=
    collisionFloor_le_scalarClearanceIter β A M t k
  have htargetLower : target - err ≤
      scalarClearanceIter β A M t (k + 1) := by
    by_cases hu : 0 ≤ u
    · rw [show target = u by simp [target, max_eq_right hu]]
      exact le_trans (sub_le_self _ herr0) hlowAffine
    · have hu' : u ≤ 0 := le_of_not_ge hu
      rw [show target = 0 by simp [target, max_eq_left hu']]
      have habs : -|A| ≤ A := neg_abs_le A
      have := mul_le_mul_of_nonneg_left habs (sub_nonneg.mpr hβ1)
      exact le_trans (by simpa [err] using this) hlowFloor
  have hupperEnvelope := scalarClearanceIter_le_envelope
    (A := A) (M := M) (t := t) hβ0 hβ1 (k + 1)
  rw [hpow] at hupperEnvelope
  have hMpart : max 0 ((1 - α) * M) ≤ target := by
    by_cases hM : 0 ≤ M
    · have hα1 : α ≤ 1 := by
        rw [← hpow]
        exact pow_le_one₀ hβ0 hβ1
      have hbase : (1 - α) * M ≤ u := by
        dsimp [u]
        nlinarith [mul_nonneg hα0 ht0]
      rw [max_eq_right (mul_nonneg (sub_nonneg.mpr hα1) hM)]
      exact le_trans hbase (le_max_right 0 u)
    · have hM' : M ≤ 0 := le_of_not_ge hM
      have hα1 : α ≤ 1 := by
        rw [← hpow]
        exact pow_le_one₀ hβ0 hβ1
      rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr hα1) hM')]
      exact le_max_left 0 u
  have hApart : (1 - β) * max A 0 ≤ err := by
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hβ1)
    exact max_le (le_abs_self A) (abs_nonneg A)
  have htargetUpper : scalarClearanceIter β A M t (k + 1) ≤
      target + err := by
    apply le_trans hupperEnvelope
    apply max_le
    · exact le_trans (le_max_right 0 u) (le_add_of_nonneg_right herr0)
    · exact add_le_add hApart hMpart |>.trans_eq (add_comm err target)
  rw [abs_le]
  constructor <;> dsimp [target, err] at * <;> linarith

/-- A fixed coarse hazard split into `n+1` equal microstages tends to zero. -/
theorem quittingMeshHazard_succ_tendsto_zero
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Tendsto (fun n : ℕ => quittingMeshHazard p (n + 1)) atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n : ℕ => quittingMeshIntensity p / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
    apply ((tendsto_const_div_atTop_nhds_zero_nat
      (quittingMeshIntensity p)).comp (tendsto_add_atTop_nat 1)).congr'
    exact Eventually.of_forall fun n => by simp [Nat.cast_add]
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      quittingMeshHazard_nonneg (n + 1) hp0 hp1.le
  · exact Eventually.of_forall fun n =>
      quittingMeshHazard_le_intensity_div hp1
  · exact hupper

/-- Mesh blocks with fixed total survival converge to the ideal reflected
affine clearance update. -/
theorem scalarClearanceIter_mesh_tendsto_ideal
    {α A M t : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (ht0 : 0 ≤ t) :
    Tendsto
      (fun n : ℕ =>
        let β := 1 - quittingMeshHazard (1 - α) (n + 1)
        scalarClearanceIter β A M t (n + 1))
      atTop (nhds (max 0 (α * t + (1 - α) * M))) := by
  let target : ℝ := max 0 (α * t + (1 - α) * M)
  let hazard : ℕ → ℝ := fun n => quittingMeshHazard (1 - α) (n + 1)
  have hp0 : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have hp1 : 1 - α < 1 := by linarith
  have hhazard : Tendsto hazard atTop (nhds 0) := by
    exact quittingMeshHazard_succ_tendsto_zero hp0 hp1
  have hbound : ∀ n : ℕ,
      |scalarClearanceIter (1 - hazard n) A M t (n + 1) - target| ≤
        hazard n * |A| := by
    intro n
    have hh0 : 0 ≤ hazard n :=
      quittingMeshHazard_nonneg (n + 1) hp0 hp1.le
    have hh1 : hazard n ≤ 1 :=
      quittingMeshHazard_le_one (n + 1) hp1.le
    have hpow : (1 - hazard n) ^ (n + 1) = α := by
      dsimp [hazard]
      simpa using one_sub_quittingMeshHazard_pow hp1.le (Nat.succ_pos n)
    simpa [target] using scalarClearanceIter_approx_ideal
      (sub_nonneg.mpr hh1) (by linarith) (Nat.succ_pos n)
      hpow hα0.le ht0
  have herr : Tendsto (fun n => hazard n * |A|) atTop (nhds 0) := by
    simpa using hhazard.mul_const |A|
  have habs : Tendsto
      (fun n =>
        |scalarClearanceIter (1 - hazard n) A M t (n + 1) - target|)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n => abs_nonneg _
    · exact Eventually.of_forall hbound
    · exact herr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [target, hazard, Real.norm_eq_abs] using habs

theorem quitPayoff_singletonHazardRoot_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (owner : ι) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootQuitPayoff reward cap
        (singletonHazardRoot owner p hp0 hp1) owner =
      ownSingleton reward owner := by
  unfold quittingRootQuitPayoff singletonHazardRoot
  rw [update_sureSetOwnerRoot_owner_true]
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_pureSetRoot]
  have hmass : quittingStationaryContinueMass
      (quittingPureSetRoot (insert owner ∅)) = 0 :=
    stationaryContinueMass_pureSetRoot_of_nonempty
      (Finset.insert_nonempty owner ∅)
  rw [hmass]
  simp [ownSingleton, quittingProjectiveSingletonTerminal]

theorem continuePayoff_singletonHazardRoot_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (owner : ι) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootContinuePayoff reward cap
        (singletonHazardRoot owner p hp0 hp1) owner = cap owner := by
  unfold quittingRootContinuePayoff singletonHazardRoot
  rw [update_sureSetOwnerRoot_owner_false (by simp)]
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_pureSetRoot]
  rw [show quittingStationaryContinueMass (quittingPureSetRoot ∅) = 1 by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    simp [quittingPureSetRoot, quittingSetAction]]
  simp

theorem quitPayoff_singletonHazardRoot_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) {owner who : ι} (hne : who ≠ owner)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootQuitPayoff reward cap
        (singletonHazardRoot owner p hp0 hp1) who =
      ownSingleton reward who + p * pairSurplus reward who owner := by
  unfold quittingRootQuitPayoff singletonHazardRoot
  rw [update_sureSetOwnerRoot_other_true hne]
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  have habs := quittingRootAbsorbingContribution_sureSetOwnerRoot reward
    (T := insert who ∅) (owner := owner) (by simpa using Ne.symm hne)
    p hp0 hp1 who
  rw [habs]
  rw [stationaryContinueMass_sureSetOwnerRoot_of_nonempty
    (Finset.insert_nonempty who ∅) (by simpa using Ne.symm hne)]
  simp [quittingSureSetOwnerValue, pairSurplus, ownSingleton,
    quittingProjectiveSingletonTerminal]
  ring

theorem continuePayoff_singletonHazardRoot_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) {owner who : ι} (hne : who ≠ owner)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootContinuePayoff reward cap
        (singletonHazardRoot owner p hp0 hp1) who =
      (1 - p) * cap who +
        p * reward (quittingProjectiveSingletonTerminal owner) who := by
  unfold quittingRootContinuePayoff singletonHazardRoot
  rw [update_sureSetOwnerRoot_other_false hne]
  simp only [Finset.erase_empty]
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  have habs := quittingRootAbsorbingContribution_sureSetOwnerRoot reward
    (T := ∅) (owner := owner) (by simp) p hp0 hp1 who
  rw [habs]
  rw [stationaryContinueMass_sureSetOwnerRoot_empty]
  simp [quittingSureSetOwnerValue, quittingProjectiveSingletonTerminal]
  ring

/-- Exact one-step cap-clearance recurrence away from the clock owner. -/
theorem capClearance_prefix_singletonHazardRoot_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) {owner who : ι}
    (hne : who ≠ owner) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    capClearance reward
        (quittingTerminalSemanticPrefix reward
          (singletonHazardRoot owner p hp0 hp1) pair).2 who =
      max (p * pairSurplus reward who owner)
        ((1 - p) * capClearance reward pair.2 who +
          p * normalizedSoloMatrix reward who owner) := by
  unfold capClearance quittingTerminalSemanticPrefix
  dsimp only
  rw [quitPayoff_singletonHazardRoot_other reward pair.1 hne,
    continuePayoff_singletonHazardRoot_other reward
      (Function.update pair.1 who (pair.2 who)) hne]
  simp only [Function.update_self]
  unfold pairSurplus ownSingleton
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  unfold quittingProjectiveLCPMatrix
  rw [← max_sub_sub_right]
  congr 1 <;> ring

/-- If the owner's input clearance is nonnegative, its cap is fixed by one
positive-hazard singleton step. -/
theorem capClearance_prefix_singletonHazardRoot_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hclearance : 0 ≤ capClearance reward pair.2 owner) :
    capClearance reward
        (quittingTerminalSemanticPrefix reward
          (singletonHazardRoot owner p hp0 hp1) pair).2 owner =
      capClearance reward pair.2 owner := by
  unfold capClearance quittingTerminalSemanticPrefix
  dsimp only
  rw [quitPayoff_singletonHazardRoot_owner,
    continuePayoff_singletonHazardRoot_owner, max_eq_right]
  · simp
  · simpa [capClearance, ownSingleton, quittingProjectiveSingletonTerminal,
      quittingSingletonTerminal] using hclearance

/-- The semantic prefix map associated with one singleton microstage. -/
def singletonHazardPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QuittingTerminalSemanticPair ι → QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPrefix reward
    (singletonHazardRoot owner p hp0 hp1)

/-- Repeated genuine singleton microstages realize exactly the scalar max
recurrence on every nonowner's cap clearance. -/
theorem capClearance_iterate_singletonHazardPrefix_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) {owner who : ι}
    (hne : who ≠ owner) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) :
    capClearance reward
        (((singletonHazardPrefix reward owner p hp0 hp1)^[n]) pair).2 who =
      scalarClearanceIter (1 - p) (pairSurplus reward who owner)
        (normalizedSoloMatrix reward who owner)
        (capClearance reward pair.2 who) n := by
  induction n with
  | zero => simp [scalarClearanceIter]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change capClearance reward
          (quittingTerminalSemanticPrefix reward
            (singletonHazardRoot owner p hp0 hp1) _).2 who = _
      rw [capClearance_prefix_singletonHazardRoot_other reward _ hne]
      rw [scalarClearanceIter_succ]
      unfold scalarClearanceStep singletonHazardPrefix at *
      rw [ih]
      congr 1 <;> ring

end IdealSingletonBlockApproximation
end GameTheory
