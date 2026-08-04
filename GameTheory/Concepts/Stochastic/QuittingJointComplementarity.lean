/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingExceptionalBellmanTail
import GameTheory.Concepts.Stochastic.QuittingCyclicPeriodicExtension
import GameTheory.Concepts.Stochastic.QuittingUnboundedInverseIterate

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

/-- Every joint survival weight is nonnegative. -/
theorem quittingJointSurvivalWeight_nonneg
    (x : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    0 ≤ quittingJointSurvivalWeight x start fuel :=
  quittingFiniteContinueWeight_nonneg _
    (fun time => quittingStationaryContinueMass_nonneg (x time)) start fuel

/-- Every joint survival weight is at most one. -/
theorem quittingJointSurvivalWeight_le_one
    (x : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    quittingJointSurvivalWeight x start fuel ≤ 1 :=
  quittingFiniteContinueWeight_le_one _
    (fun time => quittingStationaryContinueMass_nonneg (x time))
    (fun time => quittingStationaryContinueMass_le_one (x time)) start fuel

/-- The closed product form, matching `quittingOpponentSurvivalWeight`'s
shape. -/
theorem quittingJointSurvivalWeight_eq_prod
    (x : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    quittingJointSurvivalWeight x start fuel =
      ∏ offset ∈ Finset.range fuel,
        quittingStationaryContinueMass (x (start + offset)) :=
  quittingFiniteContinueWeight_eq_product _ start fuel

/-- Adding one stage multiplies survival by that stage's joint continue
mass. -/
theorem quittingJointSurvivalWeight_succ
    (x : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    quittingJointSurvivalWeight x start (fuel + 1) =
      quittingJointSurvivalWeight x start fuel *
        quittingStationaryContinueMass (x (start + fuel)) := by
  rw [quittingJointSurvivalWeight_eq_prod, quittingJointSurvivalWeight_eq_prod,
    Finset.prod_range_succ]

/-- Joint survival weights are antitone in the horizon. -/
theorem antitone_quittingJointSurvivalWeight (x : ℕ → ι → PMF Bool) (start : ℕ) :
    Antitone (quittingJointSurvivalWeight x start) := by
  apply antitone_nat_of_succ_le
  intro fuel
  rw [quittingJointSurvivalWeight_succ]
  exact mul_le_of_le_one_right (quittingJointSurvivalWeight_nonneg x start fuel)
    (quittingStationaryContinueMass_le_one _)

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

/-- Every joint survival weight sequence converges: antitone and bounded
below by zero. -/
theorem exists_tendsto_quittingJointSurvivalWeight
    (x : ℕ → ι → PMF Bool) (start : ℕ) :
    ∃ L : ℝ, Tendsto (quittingJointSurvivalWeight x start) atTop (nhds L) :=
  ⟨_, tendsto_atTop_ciInf (antitone_quittingJointSurvivalWeight x start)
    ⟨0, by rintro y ⟨n, rfl⟩; exact quittingJointSurvivalWeight_nonneg x start n⟩⟩

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

end GameTheory
