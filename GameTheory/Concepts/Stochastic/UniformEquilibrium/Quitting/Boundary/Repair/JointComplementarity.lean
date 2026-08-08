/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Exceptional.BellmanTail
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Cycles.CyclicPeriodicExtension
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Analytic.UnboundedInverseIterate
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Paths.SurvivalPrefixBridge
import Math.SurvivalProduct

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
* `IsQuittingUpperComplementaryAt` and `IsQuittingLowerComplementaryAt`: the
  minimal one-coordinate, single-clause hypotheses whose conjunction (at one
  coordinate) is exactly `IsQuittingJointComplementary` restricted to that
  coordinate.  `IsQuittingUpperComplementaryAt` alone is strictly weaker and
  is what Deliverable 2 actually consumes, so it also covers unilateral
  best-response tails, one-sided `ε`-equilibria, and non-equilibrium plans.
* `quittingJointSurvivalWeight_tendsto_zero_of_isQuittingUpperComplementaryAt_of_solo_pos`
  and `isCompletelyAbsorbing_of_isQuittingUpperComplementaryAt_of_solo_pos`:
  Deliverable 2, absorption forced by a positive solo reward, from the
  minimal hypothesis.  `..._of_isQuittingJointComplementary_of_solo_pos`
  versions of both are kept as corollaries under the full joint predicate.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

/-! ## A general real-analysis lemma -/

/-- An antitone nonnegative real sequence whose subsequence along multiples
of a fixed positive `N` tends to zero itself tends to zero.  Used to bootstrap
geometric decay of a periodic survival product, checked only every full
period, to decay of the whole sequence. -/
theorem tendsto_zero_of_antitone_nonneg_of_tendsto_zero_along_mul
    (f : ℕ → ℝ) (N : ℕ) (hN : N ≠ 0) (hf0 : ∀ n, 0 ≤ f n) (hanti : Antitone f)
    (hsub : Tendsto (fun n => f (n * N)) atTop (nhds 0)) :
    Tendsto f atTop (nhds 0) := by
  have hdiv : Tendsto (fun n => n / N) atTop atTop := Nat.tendsto_div_const_atTop hN
  have hcomp : Tendsto (fun n => f ((n / N) * N)) atTop (nhds 0) := hsub.comp hdiv
  apply squeeze_zero hf0 (fun n => hanti (Nat.div_mul_le_self n N)) hcomp

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
/-- **Bridge to the canonical survival product.**  `quittingJointSurvivalWeight`
is `Math.survivalProduct` at the stationary continue mass -- see the module
docstring of `Math.SurvivalProduct` for the full census this bridges into. -/
theorem quittingJointSurvivalWeight_eq_survivalProduct
    (x : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    quittingJointSurvivalWeight x start fuel =
      Math.survivalProduct (fun t => quittingStationaryContinueMass (x t)) start fuel :=
  quittingJointSurvivalWeight_eq_prod x start fuel

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

omit [DecidableEq ι] in
/-- If a joint survival weight from `start` has a positive limit, every
finite prefix is at least that limit. -/
theorem le_quittingJointSurvivalWeight_of_tendsto
    (x : ℕ → ι → PMF Bool) (start : ℕ) {L : ℝ}
    (hL : Tendsto (quittingJointSurvivalWeight x start) atTop (nhds L)) (n : ℕ) :
    L ≤ quittingJointSurvivalWeight x start n :=
  le_of_tendsto' (hL.comp (tendsto_add_atTop_nat n))
    (fun m => antitone_quittingJointSurvivalWeight x start (Nat.le_add_left n m))

omit [DecidableEq ι] in
/-- Under a positive limiting joint survival probability, the joint survival
products after a fixed live cutoff converge to the quotient of the global
limit by the surviving prefix. -/
theorem tendsto_quittingJointSurvivalWeight_tail_of_tendsto
    (x : ℕ → ι → PMF Bool) (start : ℕ) {L : ℝ}
    (hL : Tendsto (quittingJointSurvivalWeight x start) atTop (nhds L))
    (hLpos : 0 < L) (n : ℕ) :
    Tendsto (quittingJointSurvivalWeight x (start + n)) atTop
      (nhds (L / quittingJointSurvivalWeight x start n)) := by
  have hprefixNe : quittingJointSurvivalWeight x start n ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hLpos (le_quittingJointSurvivalWeight_of_tendsto x start hL n))
  have hshift : Tendsto (fun fuel => quittingJointSurvivalWeight x start (fuel + n))
      atTop (nhds L) := hL.comp (tendsto_add_atTop_nat n)
  have hquotient := hshift.div_const (quittingJointSurvivalWeight x start n)
  apply hquotient.congr'
  filter_upwards with fuel
  rw [show fuel + n = n + fuel by omega, quittingJointSurvivalWeight_add]
  field_simp

omit [DecidableEq ι] in
/-- The limiting conditional joint tail-survival probabilities converge to
one as the live cutoff goes to infinity. -/
theorem tendsto_quittingJointSurvivalWeight_ratio_one_of_tendsto
    (x : ℕ → ι → PMF Bool) (start : ℕ) {L : ℝ}
    (hL : Tendsto (quittingJointSurvivalWeight x start) atTop (nhds L))
    (hLpos : 0 < L) :
    Tendsto (fun n => L / quittingJointSurvivalWeight x start n) atTop (nhds 1) := by
  have hconst : Tendsto (fun _ : ℕ => L) atTop (nhds L) := tendsto_const_nhds
  have hquotient := hconst.div hL (ne_of_gt hLpos)
  simpa only [Pi.div_def, div_self hLpos.ne'] using hquotient

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
/-- **A sharper tail-value bound, against a known survival limit.**  If the
joint survival weight from `start` tends to `L`, the tail value is bounded
by the reward bound times the *surviving* mass `1 - L`, not merely `1`.
This is what forces the tail value to vanish as `start → ∞` under a
positive survival limit (Deliverable 2). -/
theorem abs_quittingComplementarityTailValue_le_of_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (i : ι) (start : ℕ) {L : ℝ}
    (hL : Tendsto (quittingJointSurvivalWeight x start) atTop (nhds L)) :
    |quittingComplementarityTailValue reward x i start| ≤
      quittingRewardBound reward * (1 - L) := by
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
  have hweightGe : L ≤ quittingJointSurvivalWeight x start fuel :=
    le_of_tendsto' (hL.comp (tendsto_add_atTop_nat fuel))
      (fun m => antitone_quittingJointSurvivalWeight x start (Nat.le_add_left fuel m))
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
    _ ≤ quittingRewardBound reward * (1 - L) := by
        nlinarith [quittingRewardBound_nonneg reward, hweightGe]

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

omit [DecidableEq ι] in
/-- The tail value satisfies the abstract live-prescribed Bellman recursion
already used throughout the codebase, at every coordinate. -/
theorem isQuittingLivePrescribedValue_quittingComplementarityTailValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (i : ι) :
    IsQuittingLivePrescribedValue reward x i
      (quittingComplementarityTailValue reward x i) := by
  intro time
  rw [quittingComplementarityTailValue_eq]
  have hsub := quittingRootSuccessorPayoff_sub_tail reward
    (fun _ => quittingComplementarityTailValue reward x i (time + 1))
    (x time) i
  rw [quittingRootAbsorptionMass] at hsub
  linarith [hsub]

/-! ## Stage gap and joint complementarity -/

/-- **Deliverable 1: the stage gap.**  The fixed-opponents quit value minus
the continuation value that uses the tail value at the next stage. -/
def quittingComplementarityStageGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (i : ι) (time : ℕ) : ℝ :=
  quittingFixedOpponentsQuitValue reward x i time -
    (quittingFixedOpponentsContinueReward reward x i time +
      quittingFixedOpponentsContinueMass x i time *
        quittingComplementarityTailValue reward x i (time + 1))

/-- **Deliverable 1: joint infinite-horizon complementarity.**  At every
time and every player, a positive quit probability forces a nonnegative
stage gap, and a sub-certain quit probability forces a nonpositive stage
gap. -/
def IsQuittingJointComplementary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) : Prop :=
  ∀ time i,
    (0 < (x time i true).toReal →
      0 ≤ quittingComplementarityStageGap reward x i time) ∧
    ((x time i true).toReal < 1 →
      quittingComplementarityStageGap reward x i time ≤ 0)

/-! ## Uniqueness of bounded solutions under vanishing joint survival -/

omit [DecidableEq ι] in
/-- Two bounded solutions of the live-prescribed recursion agree at a
starting time from which the joint survival weight vanishes.  The proof is
the exact one-step contraction `quittingRootSuccessorPayoff_sub`, iterated
and squeezed against the vanishing joint survival weight -- the *joint*
weight, not any single player's opponent-only weight, since both solutions
already agree on the underlying one-step map. -/
theorem eq_of_isQuittingLivePrescribedValue_of_bounded_of_jointSurvival_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (i : ι) (value value' : ℕ → ℝ) (M : ℝ)
    (hvalue : IsQuittingLivePrescribedValue reward x i value)
    (hvalue' : IsQuittingLivePrescribedValue reward x i value')
    (hbound : ∀ time, |value time| ≤ M) (hbound' : ∀ time, |value' time| ≤ M)
    (start : ℕ)
    (hsurvival :
      Tendsto (quittingJointSurvivalWeight x start) atTop (nhds 0)) :
    value start = value' start := by
  have hstep : ∀ time, value time - value' time =
      quittingStationaryContinueMass (x time) *
        (value (time + 1) - value' (time + 1)) := by
    intro time
    calc value time - value' time =
        quittingRootSuccessorPayoff reward (fun _ => value (time + 1)) (x time) i -
          quittingRootSuccessorPayoff reward (fun _ => value' (time + 1))
            (x time) i := by rw [hvalue time, hvalue' time]
      _ = quittingStationaryContinueMass (x time) *
            (value (time + 1) - value' (time + 1)) :=
          quittingRootSuccessorPayoff_sub reward _ _ (x time) i
  have hiterate : ∀ fuel, value start - value' start =
      quittingJointSurvivalWeight x start fuel *
        (value (start + fuel) - value' (start + fuel)) := by
    intro fuel
    induction fuel with
    | zero => simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
    | succ fuel ih =>
        rw [ih, quittingJointSurvivalWeight_succ,
          show start + (fuel + 1) = (start + fuel) + 1 by omega,
          hstep (start + fuel)]
        ring
  have hboundDiff : ∀ fuel,
      |value (start + fuel) - value' (start + fuel)| ≤ 2 * M := by
    intro fuel
    calc |value (start + fuel) - value' (start + fuel)| ≤
        |value (start + fuel)| + |value' (start + fuel)| := abs_sub _ _
      _ ≤ M + M := add_le_add (hbound _) (hbound' _)
      _ = 2 * M := by ring
  have htendsto : Tendsto (fun fuel => quittingJointSurvivalWeight x start fuel *
      (value (start + fuel) - value' (start + fuel))) atTop (nhds 0) := by
    have hmul := hsurvival.mul_const (2 * M)
    simp only [zero_mul] at hmul
    apply squeeze_zero_norm' _ hmul
    filter_upwards with fuel
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (quittingJointSurvivalWeight_nonneg x start fuel)]
    exact mul_le_mul_of_nonneg_left (hboundDiff fuel)
      (quittingJointSurvivalWeight_nonneg x start fuel)
  have hconst : Tendsto (fun _ : ℕ => value start - value' start) atTop
      (nhds (value start - value' start)) := tendsto_const_nhds
  rw [show (fun _ : ℕ => value start - value' start) =
      (fun fuel => quittingJointSurvivalWeight x start fuel *
        (value (start + fuel) - value' (start + fuel))) from funext hiterate] at hconst
  have := tendsto_nhds_unique hconst htendsto
  linarith [this]

/-! ## The compatibility bridge -/

/-- The trivial single-point path anchoring the periodic extension at the
block's own origin: the periodic extension played from stage zero, without
any pre-cutoff chain. -/
def quittingCyclicBlockPath
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1)) :
    QuittingFiniteNashBellmanPath ι 0 :=
  fun _ => block 0

/-- **The periodic extension of a cyclic continuation block, played from
stage zero.**  Repeats `block`'s own roots forever. -/
def quittingCyclicBlockRoots
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1)) :
    ℕ → ι → PMF Bool :=
  quittingCyclicPeriodicRoots 0 (quittingCyclicBlockPath period block) period block

/-- The periodic extension's own displayed value, played from stage zero. -/
def quittingCyclicBlockValue
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (who : ι) : ℕ → ℝ :=
  fun time =>
    quittingCyclicPeriodicValue 0 (quittingCyclicBlockPath period block)
      period block time who

/-- The trivial path anchors correctly at `terminal`: it lies in the
zero-cutoff anchored chain set, with a vacuous edge condition. -/
theorem quittingCyclicBlockPath_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block) :
    quittingCyclicBlockPath period block ∈
      quittingFiniteAnchoredNashBellmanChainSet reward terminal 0 :=
  ⟨fun _ => hblock.1.1 0, hblock.2.1, fun time => time.elim0⟩

/-- The block's self-reproduction seam, needed by every periodic-extension
lemma consumed below. -/
theorem quittingCyclicBlockPath_hcycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block) :
    (block 0).1 = (block (Fin.last (period + 1))).1 :=
  hblock.2.1.trans hblock.1.2.1.symm

/-- The periodic extension's own value satisfies the abstract live-prescribed
recursion, at every player. -/
theorem isQuittingLivePrescribedValue_quittingCyclicBlockValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (who : ι) :
    IsQuittingLivePrescribedValue reward (quittingCyclicBlockRoots period block)
      who (quittingCyclicBlockValue period block who) :=
  isQuittingLivePrescribedValue_quittingCyclicPeriodic 0
    (quittingCyclicBlockPath period block) period block reward
    (fun time => time.elim0) hblock.1.2.2 rfl
    (quittingCyclicBlockPath_hcycle reward terminal period block hblock) who

/-- The periodic extension's own value is exactly endpoint Nash at every
time against its own next value, inherited from the block's edges. -/
theorem isεQuittingRootEndpointNash_quittingCyclicBlockRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (time : ℕ) :
    IsεQuittingRootEndpointNash reward
      (fun who => quittingCyclicBlockValue period block who (time + 1)) 0
      (quittingCyclicBlockRoots period block time) := by
  have hcycle := quittingCyclicBlockPath_hcycle reward terminal period block hblock
  have hvalueSucc := quittingCyclicPeriodicValue_succ_of_le 0
    (quittingCyclicBlockPath period block) period block hcycle time (Nat.zero_le time)
  have hrootEq := quittingCyclicPeriodicRoots_of_le 0
    (quittingCyclicBlockPath period block) period block time (Nat.zero_le time)
  change IsεQuittingRootEndpointNash reward
    (fun who => quittingCyclicPeriodicValue 0 (quittingCyclicBlockPath period block)
      period block (time + 1) who) 0
    (quittingCyclicPeriodicRoots 0 (quittingCyclicBlockPath period block) period block time)
  rw [show (fun who => quittingCyclicPeriodicValue 0
      (quittingCyclicBlockPath period block) period block (time + 1) who) =
      quittingCyclicPeriodicValue 0 (quittingCyclicBlockPath period block) period block
        (time + 1) from rfl,
    hvalueSucc, hrootEq]
  exact (hblock.1.2.2 (quittingCyclicPeriodicStage 0 period time)).2

/-! ### Periodicity forces the joint survival weight to vanish everywhere -/

omit [DecidableEq ι] in
/-- The periodic extension repeats exactly every `period + 1` stages. -/
theorem quittingCyclicBlockRoots_periodic
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1)) (time : ℕ) :
    quittingCyclicBlockRoots period block (time + (period + 1)) =
      quittingCyclicBlockRoots period block time := by
  unfold quittingCyclicBlockRoots
  rw [quittingCyclicPeriodicRoots_of_le 0 (quittingCyclicBlockPath period block) period
      block (time + (period + 1)) (by omega),
    quittingCyclicPeriodicRoots_of_le 0 (quittingCyclicBlockPath period block) period
      block time (Nat.zero_le time)]
  have hstage : quittingCyclicPeriodicStage 0 period (time + (period + 1)) =
      quittingCyclicPeriodicStage 0 period time := by
    apply Fin.ext
    simp only [quittingCyclicPeriodicStage, Nat.sub_zero]
    exact Nat.add_mod_right time (period + 1)
  rw [hstage]

omit [DecidableEq ι] in
/-- Shifting the starting time of a joint survival window by one period
leaves it unchanged. -/
theorem quittingJointSurvivalWeight_quittingCyclicBlockRoots_shift
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (time fuel : ℕ) :
    quittingJointSurvivalWeight (quittingCyclicBlockRoots period block)
        (time + (period + 1)) fuel =
      quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) time fuel := by
  rw [quittingJointSurvivalWeight_eq_prod, quittingJointSurvivalWeight_eq_prod]
  apply Finset.prod_congr rfl
  intro k _
  rw [show time + (period + 1) + k = (time + k) + (period + 1) by ring,
    quittingCyclicBlockRoots_periodic]

omit [DecidableEq ι] in
/-- Shifting the starting time of a joint survival window by a whole number
of periods leaves it unchanged. -/
theorem quittingJointSurvivalWeight_quittingCyclicBlockRoots_shift_mul
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (n time fuel : ℕ) :
    quittingJointSurvivalWeight (quittingCyclicBlockRoots period block)
        (time + n * (period + 1)) fuel =
      quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) time fuel := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show time + (n + 1) * (period + 1) =
          (time + n * (period + 1)) + (period + 1) by ring,
        quittingJointSurvivalWeight_quittingCyclicBlockRoots_shift, ih]

omit [DecidableEq ι] in
/-- The periodic extension plays the block's own roots verbatim at every
stage within the first period. -/
theorem quittingCyclicBlockRoots_of_lt
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (stage : Fin (period + 1)) :
    quittingCyclicBlockRoots period block stage.val =
      quittingRootOfSimplex (block (Fin.castSucc stage)).2 := by
  unfold quittingCyclicBlockRoots
  rw [quittingCyclicPeriodicRoots_of_le 0 (quittingCyclicBlockPath period block) period
    block stage.val (Nat.zero_le _)]
  have hstage : quittingCyclicPeriodicStage 0 period stage.val = stage := by
    apply Fin.ext
    simp only [quittingCyclicPeriodicStage, Nat.sub_zero]
    exact Nat.mod_eq_of_lt stage.isLt
  rw [hstage]

/-- **One full period of the periodic extension already absorbs.**  Repeats
the block's own fence -- some stage has positive absorption mass -- against
the whole cycle. -/
theorem quittingJointSurvivalWeight_quittingCyclicBlockRoots_period_lt_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block) :
    quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) 0 (period + 1) < 1 := by
  obtain ⟨stage, habsorb⟩ := hblock.2.2
  rw [quittingJointSurvivalWeight_eq_prod]
  simp only [Nat.zero_add]
  apply prod_quittingStationaryContinueMass_lt_one_of_absorbing
    (quittingCyclicBlockRoots period block) (period + 1) stage.val stage.isLt
  rwa [quittingCyclicBlockRoots_of_lt]

omit [DecidableEq ι] in
/-- Every whole number of periods geometrically compounds the one-period
survival factor. -/
theorem quittingJointSurvivalWeight_quittingCyclicBlockRoots_mul_period_eq_pow
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1)) (n : ℕ) :
    quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) 0
        (n * (period + 1)) =
      quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) 0
        (period + 1) ^ n := by
  induction n with
  | zero => simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  | succ n ih =>
      have hshift : quittingJointSurvivalWeight (quittingCyclicBlockRoots period block)
          (n * (period + 1)) (period + 1) =
          quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) 0
            (period + 1) := by
        simpa using
          quittingJointSurvivalWeight_quittingCyclicBlockRoots_shift_mul period block n
            0 (period + 1)
      rw [show (n + 1) * (period + 1) = n * (period + 1) + (period + 1) by ring,
        quittingJointSurvivalWeight_add]
      simp only [Nat.zero_add]
      rw [hshift, ih, pow_succ]

/-- **The periodic extension's own joint survival weight, started at zero,
vanishes at infinity.** -/
theorem tendsto_zero_quittingJointSurvivalWeight_quittingCyclicBlockRoots_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block) :
    Tendsto (quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) 0)
      atTop (nhds 0) := by
  have hlt := quittingJointSurvivalWeight_quittingCyclicBlockRoots_period_lt_one
    reward terminal period block hblock
  have h0le := quittingJointSurvivalWeight_nonneg
    (quittingCyclicBlockRoots period block) 0 (period + 1)
  have hsub : Tendsto (fun n => quittingJointSurvivalWeight
      (quittingCyclicBlockRoots period block) 0 (n * (period + 1))) atTop (nhds 0) := by
    simp only [quittingJointSurvivalWeight_quittingCyclicBlockRoots_mul_period_eq_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one h0le hlt
  exact tendsto_zero_of_antitone_nonneg_of_tendsto_zero_along_mul
    (quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) 0) (period + 1)
    (Nat.succ_ne_zero period)
    (quittingJointSurvivalWeight_nonneg (quittingCyclicBlockRoots period block) 0)
    (antitone_quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) 0)
    hsub

/-- **Deliverable-1 supporting fact: the periodic extension of an absorbing
cyclic block absorbs almost surely from every starting time**, not only from
zero.  Splits the window at the next period boundary and falls back on the
zero-anchored decay above. -/
theorem tendsto_zero_quittingJointSurvivalWeight_quittingCyclicBlockRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (t : ℕ) :
    Tendsto (quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) t)
      atTop (nhds 0) := by
  have hzero := tendsto_zero_quittingJointSurvivalWeight_quittingCyclicBlockRoots_zero
    reward terminal period block hblock
  set m := t / (period + 1) + 1 with hm
  set q := m * (period + 1) - t with hq
  have hdm := Nat.div_add_mod t (period + 1)
  have hmlt := Nat.mod_lt t (show 0 < period + 1 by omega)
  have htq : t + q = m * (period + 1) := by
    have : t ≤ m * (period + 1) := by
      simp only [hm]
      nlinarith [hdm, hmlt]
    omega
  have hbound : ∀ fuel, q ≤ fuel →
      quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) t fuel ≤
        quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) 0
          (fuel - q) := by
    intro fuel hfuel
    have hsplit := quittingJointSurvivalWeight_add
      (quittingCyclicBlockRoots period block) t q (fuel - q)
    rw [show q + (fuel - q) = fuel by omega] at hsplit
    have hshift : quittingJointSurvivalWeight (quittingCyclicBlockRoots period block)
        (t + q) (fuel - q) =
        quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) 0
          (fuel - q) := by
      rw [htq]
      simpa using
        quittingJointSurvivalWeight_quittingCyclicBlockRoots_shift_mul period block m
          0 (fuel - q)
    rw [hsplit, hshift]
    calc quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) t q *
          quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) 0
            (fuel - q) ≤
        1 * quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) 0
            (fuel - q) := by
          apply mul_le_mul_of_nonneg_right
            (quittingJointSurvivalWeight_le_one _ t q)
            (quittingJointSurvivalWeight_nonneg _ 0 (fuel - q))
      _ = quittingJointSurvivalWeight (quittingCyclicBlockRoots period block) 0
            (fuel - q) := one_mul _
  have hdivtendsto : Tendsto (fun fuel : ℕ => fuel - q) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b + q, fun n hn => by omega⟩)
  have hrhs : Tendsto (fun fuel => quittingJointSurvivalWeight
      (quittingCyclicBlockRoots period block) 0 (fuel - q)) atTop (nhds 0) :=
    hzero.comp hdivtendsto
  apply squeeze_zero' (Eventually.of_forall
    (fun fuel => quittingJointSurvivalWeight_nonneg
      (quittingCyclicBlockRoots period block) t fuel)) _ hrhs
  filter_upwards [eventually_ge_atTop q] with fuel hfuel
  exact hbound fuel hfuel

/-- The periodic extension's own value is bounded by the canonical reward
bound, inherited from the block's own bounded box. -/
theorem abs_quittingCyclicBlockValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (who : ι) (time : ℕ) :
    |quittingCyclicBlockValue period block who time| ≤ quittingRewardBound reward := by
  unfold quittingCyclicBlockValue
  rw [quittingCyclicPeriodicValue_of_le 0 (quittingCyclicBlockPath period block) period
    block time (Nat.zero_le time)]
  have hbox := hblock.1.1 (Fin.castSucc (quittingCyclicPeriodicStage 0 period time))
  exact abs_le.mpr ⟨hbox.1 who, hbox.2 who⟩

/-- **The compatibility bridge, value part.**  The tail value agrees with
the periodic extension's own displayed value at every time and every
player: both are bounded solutions of the same live-prescribed recursion,
and the periodic extension's joint survival weight vanishes from every
starting time. -/
theorem quittingComplementarityTailValue_eq_quittingCyclicBlockValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (who : ι) (time : ℕ) :
    quittingComplementarityTailValue reward (quittingCyclicBlockRoots period block)
        who time =
      quittingCyclicBlockValue period block who time :=
  eq_of_isQuittingLivePrescribedValue_of_bounded_of_jointSurvival_tendsto_zero
    reward (quittingCyclicBlockRoots period block) who
    (quittingComplementarityTailValue reward (quittingCyclicBlockRoots period block) who)
    (quittingCyclicBlockValue period block who) (quittingRewardBound reward)
    (isQuittingLivePrescribedValue_quittingComplementarityTailValue reward
      (quittingCyclicBlockRoots period block) who)
    (isQuittingLivePrescribedValue_quittingCyclicBlockValue reward terminal period block
      hblock who)
    (fun t => abs_quittingComplementarityTailValue_le reward
      (quittingCyclicBlockRoots period block) who t)
    (fun t => abs_quittingCyclicBlockValue_le reward terminal period block hblock who t)
    time
    (tendsto_zero_quittingJointSurvivalWeight_quittingCyclicBlockRoots reward terminal
      period block hblock time)

/-- **The compatibility bridge.**  A periodic sequence satisfying the
existing cyclic-block predicate satisfies joint complementarity. -/
theorem isQuittingJointComplementary_quittingCyclicBlockRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block) :
    IsQuittingJointComplementary reward (quittingCyclicBlockRoots period block) := by
  intro time i
  have hendpoint := isεQuittingRootEndpointNash_quittingCyclicBlockRoots reward terminal
    period block hblock time i
  have hveq := quittingComplementarityTailValue_eq_quittingCyclicBlockValue reward terminal
    period block hblock i (time + 1)
  have hquit := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
    (quittingCyclicBlockRoots period block) i
    (fun who => quittingCyclicBlockValue period block who (time + 1)) time
  have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents reward
    (quittingCyclicBlockRoots period block) i
    (fun who => quittingCyclicBlockValue period block who (time + 1)) time
  have hgap : quittingComplementarityStageGap reward
      (quittingCyclicBlockRoots period block) i time =
      quittingRootEndpointDifference reward
        (fun who => quittingCyclicBlockValue period block who (time + 1))
        (quittingCyclicBlockRoots period block time) i := by
    unfold quittingComplementarityStageGap quittingRootEndpointDifference
    rw [hveq, hquit, hcontinue]
  rw [hgap]
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (quittingCyclicBlockRoots period block time) i
  set diff := quittingRootEndpointDifference reward
    (fun who => quittingCyclicBlockValue period block who (time + 1))
    (quittingCyclicBlockRoots period block time) i with hdiff
  set quitProb := (quittingCyclicBlockRoots period block time i true).toReal with hqp
  set continueProb := (quittingCyclicBlockRoots period block time i false).toReal with hcp
  constructor
  · intro hpos
    nlinarith [hendpoint.2]
  · intro hlt
    nlinarith [hendpoint.1]

/-! ## Deliverable 2: absorption is forced by a positive solo reward -/

/-- If an opponent-only survival weight from `start` has a positive limit,
every finite prefix is at least that limit. -/
theorem le_quittingOpponentSurvivalWeight_of_tendsto
    (x : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) {L : ℝ}
    (hL : Tendsto (quittingOpponentSurvivalWeight x who start) atTop (nhds L))
    (n : ℕ) :
    L ≤ quittingOpponentSurvivalWeight x who start n :=
  le_of_tendsto' (hL.comp (tendsto_add_atTop_nat n))
    (fun m => antitone_quittingOpponentSurvivalWeight x who start (Nat.le_add_left n m))

/-- **Positive opponent-only survival forces the per-stage opponent continue
mass to one.**  The ratio of consecutive convergent partial products of a
sequence with positive limit tends to one. -/
theorem tendsto_one_quittingFixedOpponentsContinueMass_of_tendsto
    (x : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) {L : ℝ}
    (hL : Tendsto (quittingOpponentSurvivalWeight x who start) atTop (nhds L))
    (hLpos : 0 < L) :
    Tendsto (fun n => quittingFixedOpponentsContinueMass x who (start + n))
      atTop (nhds 1) := by
  have hnum : Tendsto (fun n => quittingOpponentSurvivalWeight x who start (n + 1))
      atTop (nhds L) := hL.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun n => quittingOpponentSurvivalWeight x who start (n + 1) /
      quittingOpponentSurvivalWeight x who start n) atTop (nhds (L / L)) :=
    hnum.div hL (ne_of_gt hLpos)
  rw [div_self (ne_of_gt hLpos)] at hratio
  refine hratio.congr (fun n => ?_)
  have hne : quittingOpponentSurvivalWeight x who start n ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hLpos
      (le_quittingOpponentSurvivalWeight_of_tendsto x who start hL n))
  rw [quittingOpponentSurvivalWeight_succ, mul_comm, mul_div_assoc, div_self hne, mul_one]

/-- **The minimal complementarity hypothesis absorption actually needs.**
Only the sub-certain-quit ("upper") clause of `IsQuittingJointComplementary`'s
two clauses, and only at the single coordinate `i` -- not the positive-quit
clause, and not any other coordinate's clauses at all.  Strictly weaker than
joint complementarity restricted to `i`, so it also covers, e.g., a
unilateral best-response tail for `i` alone, a one-sided `ε`-equilibrium at
`i`, or any non-equilibrium plan that merely never leaves a positive stage
gap at a sub-certain quit for `i` -- none of which satisfy the full joint
predicate. -/
def IsQuittingUpperComplementaryAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (i : ι) : Prop :=
  ∀ time, (x time i true).toReal < 1 →
    quittingComplementarityStageGap reward x i time ≤ 0

/-- The symmetric ("lower") companion of `IsQuittingUpperComplementaryAt`:
the positive-quit clause of `IsQuittingJointComplementary`'s two clauses, at
the single coordinate `i`.  Together, `IsQuittingLowerComplementaryAt reward
x i` and `IsQuittingUpperComplementaryAt reward x i` are exactly
`IsQuittingJointComplementary reward x` restricted to coordinate `i`. -/
def IsQuittingLowerComplementaryAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (i : ι) : Prop :=
  ∀ time, 0 < (x time i true).toReal →
    0 ≤ quittingComplementarityStageGap reward x i time

/-- Joint complementarity, restricted to one coordinate, is at least as
strong as the minimal upper-clause hypothesis above. -/
theorem isQuittingUpperComplementaryAt_of_isQuittingJointComplementary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (hcomplementary : IsQuittingJointComplementary reward x)
    (i : ι) :
    IsQuittingUpperComplementaryAt reward x i :=
  fun time hlt => (hcomplementary time i).2 hlt

/-- Joint complementarity, restricted to one coordinate, is at least as
strong as the lower-clause hypothesis above. -/
theorem isQuittingLowerComplementaryAt_of_isQuittingJointComplementary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (hcomplementary : IsQuittingJointComplementary reward x)
    (i : ι) :
    IsQuittingLowerComplementaryAt reward x i :=
  fun time hpos => (hcomplementary time i).1 hpos

/-- **Deliverable 2: absorption is forced by a positive solo reward, from the
minimal upper-clause hypothesis alone.**  If the sub-certain-quit stage-gap
clause holds at coordinate `i` (`IsQuittingUpperComplementaryAt`) and `i`'s
solo-quit reward is strictly positive, play absorbs almost surely from every
starting time -- no hypothesis at any other coordinate, and no positive-quit
clause at `i` either.

Proof idea: suppose not, from some `t`.  Then the joint survival weight from
`t` has a positive limit `L`, hence so does the coarser opponent-only
survival weight for `i` (joint `≤` opponent, pointwise).  Positive opponent
survival forces the opponent continue mass to one and, through the
exceptional-clock estimates, the quit value to the solo reward and the
continue reward to zero.  It also forces the tail value itself to vanish
(`abs_quittingComplementarityTailValue_le_of_tendsto`, using that positive
survival makes the *surviving* mass bound shrink to zero) -- this is the
step flagged in the design sketch as needing care about the other
coordinates, and it closes because the tail-value bound is against the
*joint* survival limit, which the opponent-only argument shows also tends to
one from `t`.  So the stage gap for `i` tends to the strictly positive solo
reward, and is eventually positive, hence eventually strictly above the
upper clause's threshold.  Since the clause only *forces* a nonpositive gap
when the quit probability is sub-certain, a positive gap there forces `i`'s
quit probability to be exactly one at that stage, so the joint continue mass
there is exactly zero, and the joint survival weight is eventually exactly
zero -- contradicting a positive limit. -/
theorem quittingJointSurvivalWeight_tendsto_zero_of_isQuittingUpperComplementaryAt_of_solo_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (i : ι)
    (hcomplementary : IsQuittingUpperComplementaryAt reward x i)
    (hsolo : 0 < reward (quittingSingletonTerminal i) i) (t : ℕ) :
    Tendsto (quittingJointSurvivalWeight x t) atTop (nhds 0) := by
  obtain ⟨L, hL⟩ := exists_tendsto_quittingJointSurvivalWeight x t
  suffices hLeq : L = 0 by rwa [hLeq] at hL
  by_contra hL0
  have hLnonneg : 0 ≤ L :=
    ge_of_tendsto' hL (fun n => quittingJointSurvivalWeight_nonneg x t n)
  have hLpos : 0 < L := lt_of_le_of_ne hLnonneg (Ne.symm hL0)
  have hLi := tendsto_atTop_ciInf (antitone_quittingOpponentSurvivalWeight x i t)
    (⟨0, by rintro y ⟨n, rfl⟩; exact quittingOpponentSurvivalWeight_nonneg x i t n⟩)
  set Li := ⨅ n, quittingOpponentSurvivalWeight x i t n with hLidef
  have hLLi : L ≤ Li := le_of_tendsto_of_tendsto' hL hLi
    (fun n => quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight x i t n)
  have hLipos : 0 < Li := lt_of_lt_of_le hLpos hLLi
  have hfixedOppTendsto :=
    tendsto_one_quittingFixedOpponentsContinueMass_of_tendsto x i t hLi hLipos
  have hbound0 : (0 : ℝ) ≤ quittingRewardBound reward := quittingRewardBound_nonneg reward
  have hrewardBound : ∀ S, |reward S i| ≤ quittingRewardBound reward :=
    fun S => abs_reward_le_quittingRewardBound reward S i
  have honeMinusTendsto : Tendsto
      (fun n => 1 - quittingFixedOpponentsContinueMass x i (t + n)) atTop (nhds 0) := by
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    simpa using h1.sub hfixedOppTendsto
  have hrhsTendsto : Tendsto (fun n => quittingRewardBound reward *
      (1 - quittingFixedOpponentsContinueMass x i (t + n))) atTop (nhds 0) := by
    simpa using honeMinusTendsto.const_mul (quittingRewardBound reward)
  have hquitTendsto : Tendsto (fun n => quittingFixedOpponentsQuitValue reward x i (t + n))
      atTop (nhds (reward (quittingSingletonTerminal i) i)) := by
    have hdiffTendsto : Tendsto (fun n => quittingFixedOpponentsQuitValue reward x i (t + n) -
        quittingFixedOpponentsContinueMass x i (t + n) *
          reward (quittingSingletonTerminal i) i) atTop (nhds 0) := by
      apply squeeze_zero_norm (fun n => ?_) hrhsTendsto
      rw [Real.norm_eq_abs]
      exact abs_quittingFixedOpponentsQuitValue_sub_continueMass_mul_solo_le reward x i
        (t + n) (quittingRewardBound reward) hbound0 hrewardBound
    have hprodTendsto : Tendsto (fun n => quittingFixedOpponentsContinueMass x i (t + n) *
        reward (quittingSingletonTerminal i) i) atTop
        (nhds (reward (quittingSingletonTerminal i) i)) := by
      simpa using hfixedOppTendsto.mul_const (reward (quittingSingletonTerminal i) i)
    simpa using hdiffTendsto.add hprodTendsto
  have hcontinueTendsto : Tendsto
      (fun n => quittingFixedOpponentsContinueReward reward x i (t + n)) atTop (nhds 0) := by
    apply squeeze_zero_norm (fun n => ?_) hrhsTendsto
    rw [Real.norm_eq_abs]
    exact abs_quittingFixedOpponentsContinueReward_le_hazard reward x i (t + n)
      (quittingRewardBound reward) hbound0 hrewardBound
  have hratioOne := tendsto_quittingJointSurvivalWeight_ratio_one_of_tendsto x t hL hLpos
  have hVtendsto : Tendsto
      (fun n => quittingComplementarityTailValue reward x i (t + n + 1)) atTop (nhds 0) := by
    have hbound : ∀ n, |quittingComplementarityTailValue reward x i (t + n + 1)| ≤
        quittingRewardBound reward * (1 - L / quittingJointSurvivalWeight x t (n + 1)) := by
      intro n
      have hle := abs_quittingComplementarityTailValue_le_of_tendsto reward x i (t + n + 1)
        (tendsto_quittingJointSurvivalWeight_tail_of_tendsto x t hL hLpos (n + 1))
      rwa [show t + n + 1 = t + (n + 1) by ring] at hle
    have hratioOneShift : Tendsto (fun n => L / quittingJointSurvivalWeight x t (n + 1))
        atTop (nhds 1) := hratioOne.comp (tendsto_add_atTop_nat 1)
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - L / quittingJointSurvivalWeight x t (n + 1))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (α := ℕ) (x := (1 : ℝ))).sub hratioOneShift
    have hrhsV : Tendsto (fun n => quittingRewardBound reward *
        (1 - L / quittingJointSurvivalWeight x t (n + 1))) atTop (nhds 0) := by
      simpa using h1.const_mul (quittingRewardBound reward)
    exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hbound n) hrhsV
  have hcontinueMassBounded : Tendsto
      (fun n => quittingFixedOpponentsContinueMass x i (t + n)) atTop (nhds 1) := hfixedOppTendsto
  have hgapTendsto : Tendsto
      (fun n => quittingComplementarityStageGap reward x i (t + n)) atTop
      (nhds (reward (quittingSingletonTerminal i) i)) := by
    have hproduct : Tendsto (fun n => quittingFixedOpponentsContinueMass x i (t + n) *
        quittingComplementarityTailValue reward x i (t + n + 1)) atTop (nhds 0) := by
      have := hcontinueMassBounded.mul hVtendsto
      simpa using this
    have hcombine : Tendsto (fun n => quittingFixedOpponentsQuitValue reward x i (t + n) -
        (quittingFixedOpponentsContinueReward reward x i (t + n) +
          quittingFixedOpponentsContinueMass x i (t + n) *
            quittingComplementarityTailValue reward x i (t + n + 1))) atTop
        (nhds (reward (quittingSingletonTerminal i) i)) := by
      have := hquitTendsto.sub (hcontinueTendsto.add hproduct)
      simpa using this
    simpa [quittingComplementarityStageGap] using hcombine
  obtain ⟨n, hn⟩ := (hgapTendsto.eventually
    (eventually_gt_nhds hsolo)).exists
  have hquitOne : (x (t + n) i true).toReal = 1 := by
    by_contra hne
    have hlt : (x (t + n) i true).toReal < 1 :=
      lt_of_le_of_ne (ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _) |>.trans_eq
        (by norm_num)) hne
    exact absurd (hcomplementary (t + n) hlt) (not_le.mpr hn)
  have hcontinueZero : (x (t + n) i false).toReal = 0 := by
    have hsum := quittingRoot_continueProbability_add_quitProbability (x (t + n)) i
    linarith [hquitOne]
  have hmassZero : quittingStationaryContinueMass (x (t + n)) = 0 := by
    rw [quittingStationaryContinueMass_eq_deletedContinueMass_mul_own (x (t + n)) i,
      hcontinueZero, mul_zero]
  have hweightZero : quittingJointSurvivalWeight x t (n + 1) = 0 := by
    rw [quittingJointSurvivalWeight_succ, hmassZero, mul_zero]
  have hLzero : L = 0 := by
    have hLle := le_quittingJointSurvivalWeight_of_tendsto x t hL (n + 1)
    rw [hweightZero] at hLle
    linarith [hLnonneg]
  exact hL0 hLzero

/-- **Deliverable 2, full joint complementarity.**  Corollary of the minimal
one-coordinate result above, via
`isQuittingUpperComplementaryAt_of_isQuittingJointComplementary`.  Kept so
every existing consumer of the strong hypothesis keeps working unchanged. -/
theorem quittingJointSurvivalWeight_tendsto_zero_of_isQuittingJointComplementary_of_solo_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (hcomplementary : IsQuittingJointComplementary reward x)
    (i : ι) (hsolo : 0 < reward (quittingSingletonTerminal i) i) (t : ℕ) :
    Tendsto (quittingJointSurvivalWeight x t) atTop (nhds 0) :=
  quittingJointSurvivalWeight_tendsto_zero_of_isQuittingUpperComplementaryAt_of_solo_pos
    reward x i (isQuittingUpperComplementaryAt_of_isQuittingJointComplementary reward x
      hcomplementary i) hsolo t

omit [DecidableEq ι] in
/-- The joint survival weight from `t` is exactly the pre-existing
`quittingSurvivalPrefix` of the shifted row sequence. -/
theorem quittingJointSurvivalWeight_eq_quittingSurvivalPrefix
    (x : ℕ → ι → PMF Bool) (t fuel : ℕ) :
    quittingJointSurvivalWeight x t fuel =
      quittingSurvivalPrefix (fun n => x (t + n)) fuel := by
  rw [quittingJointSurvivalWeight_eq_prod, quittingSurvivalPrefix]

/-- **Deliverable 2, restated against the pre-existing complete-absorption
vocabulary, from the minimal upper-clause hypothesis alone.**  Under the
sub-certain-quit stage-gap clause at coordinate `i`
(`IsQuittingUpperComplementaryAt`) and a positive solo reward at `i`, the row
sequence shifted to start at any time `t` is completely absorbing in the
sense of `IsCompletelyAbsorbing`. -/
theorem isCompletelyAbsorbing_of_isQuittingUpperComplementaryAt_of_solo_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (i : ι)
    (hcomplementary : IsQuittingUpperComplementaryAt reward x i)
    (hsolo : 0 < reward (quittingSingletonTerminal i) i) (t : ℕ) :
    IsCompletelyAbsorbing (fun n => x (t + n)) := by
  unfold IsCompletelyAbsorbing
  rw [show quittingSurvivalPrefix (fun n => x (t + n)) =
      quittingJointSurvivalWeight x t from
      funext (fun fuel => (quittingJointSurvivalWeight_eq_quittingSurvivalPrefix x t fuel).symm)]
  exact quittingJointSurvivalWeight_tendsto_zero_of_isQuittingUpperComplementaryAt_of_solo_pos
    reward x i hcomplementary hsolo t

/-- **Deliverable 2, restated against the pre-existing complete-absorption
vocabulary, full joint complementarity.**  Corollary of the minimal
one-coordinate result above.  Kept so every existing consumer of the strong
hypothesis keeps working unchanged. -/
theorem isCompletelyAbsorbing_of_isQuittingJointComplementary_of_solo_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (hcomplementary : IsQuittingJointComplementary reward x)
    (i : ι) (hsolo : 0 < reward (quittingSingletonTerminal i) i) (t : ℕ) :
    IsCompletelyAbsorbing (fun n => x (t + n)) :=
  isCompletelyAbsorbing_of_isQuittingUpperComplementaryAt_of_solo_pos
    reward x i (isQuittingUpperComplementaryAt_of_isQuittingJointComplementary reward x
      hcomplementary i) hsolo t

end GameTheory
