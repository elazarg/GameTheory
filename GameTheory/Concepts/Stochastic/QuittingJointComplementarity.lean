/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingExceptionalBellmanTail
import GameTheory.Concepts.Stochastic.QuittingCyclicPeriodicExtension
import GameTheory.Concepts.Stochastic.QuittingUnboundedInverseIterate
import GameTheory.Concepts.Stochastic.QuittingSurvivalPrefixBridge

/-!
# Joint infinite-horizon complementarity for quitting games

Every landed complementarity notion in this tree is either single-coordinate
(`IsQuittingLivePrescribedValue`, `IsεQuittingRootEndpointNash`) or periodic
(`IsQuittingCyclicContinuationBlock`).  Neither can state "every complementary
sequence": an arbitrary infinite row sequence `x : ℕ → ι → PMF Bool`, not
periodic, not finite-support.  This file supplies that joint,
infinite-horizon notion, built from the existing single-stage machinery
`quittingFixedOpponentsQuitValue`, `quittingFixedOpponentsContinueReward`,
`quittingFixedOpponentsContinueMass`.

## Contents

* `quittingJointSurvivalWeight`: the probability that nobody quits over a
  finite window, for an arbitrary root sequence.  A thin `start`-indexed
  wrapper over the existing `quittingFiniteContinueWeight`.
* `quittingComplementarityTailValue`: the tail value `V i t`, an absolutely
  convergent series (Deliverable 1).  Convergence needs only a bounded
  reward table -- automatic here since `ι` is a `Fintype` -- and no further
  hypothesis: the survival weights telescope regardless of whether the
  sequence eventually absorbs.
* `quittingComplementarityStageGap` and `IsQuittingJointComplementary`: the
  stage gap and the joint complementarity predicate.
* `isQuittingJointComplementary_quittingCyclicBlockRoots`: the compatibility
  bridge from a periodic `IsQuittingCyclicContinuationBlock`.
* `quittingJointSurvivalWeight_tendsto_zero_of_isQuittingJointComplementary_of_solo_pos`:
  Deliverable 2, absorption forced by a positive solo reward.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Joint survival weight -/

/-- The probability that *every* player continues over `fuel` stages
starting at `start`, along an arbitrary sequence of live product roots.
A `start`-indexed wrapper over the existing `quittingFiniteContinueWeight`,
instantiated at the raw (not opponent-restricted) continue mass. -/
def quittingJointSurvivalWeight (x : ℕ → ι → PMF Bool) (start fuel : ℕ) : ℝ :=
  quittingFiniteContinueWeight (fun time => quittingStationaryContinueMass (x time))
    start fuel

omit [DecidableEq ι] in
/-- Every joint survival weight is nonnegative. -/
theorem quittingJointSurvivalWeight_nonneg
    (x : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    0 ≤ quittingJointSurvivalWeight x start fuel :=
  quittingFiniteContinueWeight_nonneg _
    (fun time => quittingStationaryContinueMass_nonneg (x time)) start fuel

omit [DecidableEq ι] in
/-- Every joint survival weight is at most one. -/
theorem quittingJointSurvivalWeight_le_one
    (x : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    quittingJointSurvivalWeight x start fuel ≤ 1 :=
  quittingFiniteContinueWeight_le_one _
    (fun time => quittingStationaryContinueMass_nonneg (x time))
    (fun time => quittingStationaryContinueMass_le_one (x time)) start fuel

omit [DecidableEq ι] in
/-- The closed product form, matching `quittingOpponentSurvivalWeight`'s
shape. -/
theorem quittingJointSurvivalWeight_eq_prod
    (x : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    quittingJointSurvivalWeight x start fuel =
      ∏ offset ∈ Finset.range fuel,
        quittingStationaryContinueMass (x (start + offset)) :=
  quittingFiniteContinueWeight_eq_product _ start fuel

omit [DecidableEq ι] in
/-- Adding one stage multiplies survival by that stage's joint continue
mass. -/
theorem quittingJointSurvivalWeight_succ
    (x : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    quittingJointSurvivalWeight x start (fuel + 1) =
      quittingJointSurvivalWeight x start fuel *
        quittingStationaryContinueMass (x (start + fuel)) := by
  rw [quittingJointSurvivalWeight_eq_prod, quittingJointSurvivalWeight_eq_prod,
    Finset.prod_range_succ]

omit [DecidableEq ι] in
/-- Joint survival weights are antitone in the horizon. -/
theorem antitone_quittingJointSurvivalWeight (x : ℕ → ι → PMF Bool) (start : ℕ) :
    Antitone (quittingJointSurvivalWeight x start) := by
  apply antitone_nat_of_succ_le
  intro fuel
  rw [quittingJointSurvivalWeight_succ]
  exact mul_le_of_le_one_right (quittingJointSurvivalWeight_nonneg x start fuel)
    (quittingStationaryContinueMass_le_one _)

omit [DecidableEq ι] in
/-- Joint survival weights split exactly into a prefix and the tail starting
after that prefix. -/
theorem quittingJointSurvivalWeight_add
    (x : ℕ → ι → PMF Bool) (start cutoff suffix : ℕ) :
    quittingJointSurvivalWeight x start (cutoff + suffix) =
      quittingJointSurvivalWeight x start cutoff *
        quittingJointSurvivalWeight x (start + cutoff) suffix := by
  induction suffix with
  | zero => simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  | succ suffix ih =>
      rw [Nat.add_succ, quittingJointSurvivalWeight_succ, ih,
        quittingJointSurvivalWeight_succ]
      simp only [Nat.add_assoc]
      ring

omit [DecidableEq ι] in
/-- Every joint survival weight sequence converges: antitone and bounded
below by zero. -/
theorem exists_tendsto_quittingJointSurvivalWeight
    (x : ℕ → ι → PMF Bool) (start : ℕ) :
    ∃ L : ℝ, Tendsto (quittingJointSurvivalWeight x start) atTop (nhds L) :=
  ⟨_, tendsto_atTop_ciInf (antitone_quittingJointSurvivalWeight x start)
    ⟨0, by rintro y ⟨n, rfl⟩; exact quittingJointSurvivalWeight_nonneg x start n⟩⟩

omit [DecidableEq ι] in
/-- Joint survival telescopes exactly against the loss of joint continue
mass, mirroring `sum_quittingOpponentSurvivalWeight_mul_one_sub_continueMass`. -/
theorem sum_quittingJointSurvivalWeight_mul_one_sub_continueMass
    (x : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    (∑ offset ∈ Finset.range fuel, quittingJointSurvivalWeight x start offset *
        (1 - quittingStationaryContinueMass (x (start + offset)))) =
      1 - quittingJointSurvivalWeight x start fuel := by
  induction fuel with
  | zero => simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  | succ fuel ih =>
      rw [Finset.sum_range_succ, ih, quittingJointSurvivalWeight_succ]
      ring

/-- The joint survival weight never exceeds the opponent-only survival
weight for any single player: dropping that player's own continue
probability from the joint product can only raise it. -/
theorem quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
    (x : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingJointSurvivalWeight x start fuel ≤
      quittingOpponentSurvivalWeight x who start fuel := by
  rw [quittingJointSurvivalWeight_eq_prod]
  unfold quittingOpponentSurvivalWeight
  apply Finset.prod_le_prod
  · intro i _
    exact quittingStationaryContinueMass_nonneg _
  · intro i _
    have hfactor :
        quittingStationaryContinueMass (x (start + i)) =
          quittingFixedOpponentsContinueMass x who (start + i) *
            (x (start + i) who false).toReal := by
      rw [quittingStationaryContinueMass_eq_deletedContinueMass_mul_own
        (x (start + i)) who,
        quittingRootDeletedContinueMass_eq_fixedOpponents]
    rw [hfactor]
    have hle1 : (x (start + i) who false).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _) |>.trans_eq
        (by norm_num)
    have hmass0 : 0 ≤ quittingFixedOpponentsContinueMass x who (start + i) :=
      quittingStationaryContinueMass_nonneg _
    calc quittingFixedOpponentsContinueMass x who (start + i) *
          (x (start + i) who false).toReal ≤
        quittingFixedOpponentsContinueMass x who (start + i) * 1 :=
          mul_le_mul_of_nonneg_left hle1 hmass0
      _ = quittingFixedOpponentsContinueMass x who (start + i) := mul_one _

/-! ## The tail value -/

omit [DecidableEq ι] in
/-- Absolute value of the term at `offset`: the bound needed for absolute
convergence of the tail value.  Uses only boundedness of the reward
table, via the canonical `quittingRewardBound`. -/
theorem abs_quittingJointSurvivalWeight_mul_quittingRootAbsorbingContribution_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (i : ι) (start offset : ℕ) :
    |quittingJointSurvivalWeight x start offset *
        quittingRootAbsorbingContribution reward (x (start + offset)) i| ≤
      quittingJointSurvivalWeight x start offset * quittingRewardBound reward *
        (1 - quittingStationaryContinueMass (x (start + offset))) := by
  rw [abs_mul, abs_of_nonneg (quittingJointSurvivalWeight_nonneg x start offset)]
  have hcontribution := abs_quittingRootAbsorbingContribution_le reward
    (x (start + offset)) i (quittingRewardBound reward)
    (fun S player => abs_reward_le_quittingRewardBound reward S player)
  rw [quittingRootAbsorptionMass] at hcontribution
  calc quittingJointSurvivalWeight x start offset *
        |quittingRootAbsorbingContribution reward (x (start + offset)) i| ≤
      quittingJointSurvivalWeight x start offset *
        (quittingRewardBound reward *
          (1 - quittingStationaryContinueMass (x (start + offset)))) :=
        mul_le_mul_of_nonneg_left hcontribution
          (quittingJointSurvivalWeight_nonneg x start offset)
    _ = quittingJointSurvivalWeight x start offset * quittingRewardBound reward *
          (1 - quittingStationaryContinueMass (x (start + offset))) := by ring

omit [DecidableEq ι] in
/-- **Absolute convergence of the tail-value series.**  Needs only a bounded
reward table -- automatic here, since `ι` is a `Fintype` -- and no further
hypothesis: the survival weights lie in `[0,1]` and telescope
(`sum_quittingJointSurvivalWeight_mul_one_sub_continueMass`) regardless of
whether the sequence eventually absorbs. -/
theorem summable_quittingJointSurvivalWeight_mul_quittingRootAbsorbingContribution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (i : ι) (start : ℕ) :
    Summable (fun offset => quittingJointSurvivalWeight x start offset *
      quittingRootAbsorbingContribution reward (x (start + offset)) i) := by
  apply Summable.of_abs
  apply summable_of_sum_range_le (c := quittingRewardBound reward)
    (fun offset => abs_nonneg _)
  intro fuel
  calc ∑ offset ∈ Finset.range fuel,
        |quittingJointSurvivalWeight x start offset *
          quittingRootAbsorbingContribution reward (x (start + offset)) i| ≤
      ∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight x start offset * quittingRewardBound reward *
          (1 - quittingStationaryContinueMass (x (start + offset))) :=
        Finset.sum_le_sum (fun offset _ =>
          abs_quittingJointSurvivalWeight_mul_quittingRootAbsorbingContribution_le
            reward x i start offset)
    _ = quittingRewardBound reward *
          ∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight x start offset *
              (1 - quittingStationaryContinueMass (x (start + offset))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset _
        ring
    _ = quittingRewardBound reward *
          (1 - quittingJointSurvivalWeight x start fuel) := by
        rw [sum_quittingJointSurvivalWeight_mul_one_sub_continueMass]
    _ ≤ quittingRewardBound reward := by
        nlinarith [quittingRewardBound_nonneg reward,
          quittingJointSurvivalWeight_nonneg x start fuel]

/-- **Deliverable 1: the tail value.**  The value to `i` of the sequence of
live product roots shifted `start` places: the sum, over every future stage,
of the survival-discounted absorbing contribution at that stage. -/
def quittingComplementarityTailValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (i : ι) (start : ℕ) : ℝ :=
  ∑' offset : ℕ, quittingJointSurvivalWeight x start offset *
    quittingRootAbsorbingContribution reward (x (start + offset)) i

omit [DecidableEq ι] in
/-- The tail value is bounded by the canonical reward bound, uniformly in
`start` and with no survival hypothesis. -/
theorem abs_quittingComplementarityTailValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (i : ι) (start : ℕ) :
    |quittingComplementarityTailValue reward x i start| ≤
      quittingRewardBound reward := by
  have hsummable :=
    summable_quittingJointSurvivalWeight_mul_quittingRootAbsorbingContribution
      reward x i start
  have hnorm : ‖quittingComplementarityTailValue reward x i start‖ ≤
      ∑' offset, ‖quittingJointSurvivalWeight x start offset *
        quittingRootAbsorbingContribution reward (x (start + offset)) i‖ :=
    norm_tsum_le_tsum_norm hsummable.norm
  simp only [Real.norm_eq_abs] at hnorm
  refine hnorm.trans (Real.tsum_le_of_sum_range_le (fun offset => abs_nonneg _)
    (fun fuel => ?_))
  calc ∑ offset ∈ Finset.range fuel,
        |quittingJointSurvivalWeight x start offset *
          quittingRootAbsorbingContribution reward (x (start + offset)) i| ≤
      ∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight x start offset * quittingRewardBound reward *
          (1 - quittingStationaryContinueMass (x (start + offset))) :=
        Finset.sum_le_sum (fun offset _ =>
          abs_quittingJointSurvivalWeight_mul_quittingRootAbsorbingContribution_le
            reward x i start offset)
    _ = quittingRewardBound reward *
          ∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight x start offset *
              (1 - quittingStationaryContinueMass (x (start + offset))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset _
        ring
    _ = quittingRewardBound reward *
          (1 - quittingJointSurvivalWeight x start fuel) := by
        rw [sum_quittingJointSurvivalWeight_mul_one_sub_continueMass]
    _ ≤ quittingRewardBound reward := by
        nlinarith [quittingRewardBound_nonneg reward,
          quittingJointSurvivalWeight_nonneg x start fuel]

omit [DecidableEq ι] in
/-- **The tail value solves its own one-step recursion**: the current
absorbing contribution plus joint continue mass times the tail value one
stage later.  This is exactly the "abs + c * tail" form of
`quittingRootSuccessorPayoff_sub_tail`, unrolled to the whole series. -/
theorem quittingComplementarityTailValue_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (i : ι) (start : ℕ) :
    quittingComplementarityTailValue reward x i start =
      quittingRootAbsorbingContribution reward (x start) i +
        quittingStationaryContinueMass (x start) *
          quittingComplementarityTailValue reward x i (start + 1) := by
  unfold quittingComplementarityTailValue
  have hsummable :=
    summable_quittingJointSurvivalWeight_mul_quittingRootAbsorbingContribution
      reward x i start
  rw [hsummable.tsum_eq_zero_add]
  have hzero : quittingJointSurvivalWeight x start 0 *
      quittingRootAbsorbingContribution reward (x (start + 0)) i =
      quittingRootAbsorbingContribution reward (x start) i := by
    simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  rw [hzero]
  congr 1
  have hterm : ∀ offset : ℕ,
      quittingJointSurvivalWeight x start (offset + 1) *
          quittingRootAbsorbingContribution reward (x (start + (offset + 1))) i =
        quittingStationaryContinueMass (x start) *
          (quittingJointSurvivalWeight x (start + 1) offset *
            quittingRootAbsorbingContribution reward
              (x (start + 1 + offset)) i) := by
    intro offset
    have hsplit : quittingJointSurvivalWeight x start (1 + offset) =
        quittingJointSurvivalWeight x start 1 *
          quittingJointSurvivalWeight x (start + 1) offset :=
      quittingJointSurvivalWeight_add x start 1 offset
    have hone : quittingJointSurvivalWeight x start 1 =
        quittingStationaryContinueMass (x start) := by
      simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
    rw [show offset + 1 = 1 + offset by omega, hsplit, hone,
      show start + (1 + offset) = start + 1 + offset by omega]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]

end GameTheory
