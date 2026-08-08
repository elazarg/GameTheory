/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtMonotonicity

/-!
# Calibration of optimized exact finite dynamic debt

This file completes the finite-dimensional comparison and selection argument
for the two optimized exact-D objectives.  The minimum of the playerwise
maximum and the minimum of the aggregate sum are comparable up to the number
of players, even though their minimizers need not coincide.  Both antitone
minimum sequences converge to their conditional infima.

For the stronger edgewise statement, we expose a prepend operation with an
arbitrary bounded exact Nash--Bellman predecessor.  Prepending a sum minimizer
has total coordinate loss at most the one-step drop of the optimized sum.
This controls every coordinate.  Prepending a max minimizer controls only the
drop of the maximum, and a coordinate attaining the new maximum; a tiny
two-coordinate regression records why no all-coordinate conclusion follows.

No nested selection of minimizers and no compatible infinite path is asserted.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Sum versus maximum -/

/-- On an admissible path, the aggregate exact debt is at most the number of
players times the largest coordinate. -/
theorem quittingFiniteNashBellmanPathAggregateDynamicDebt_le_card_mul_max
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff) :
    quittingFiniteNashBellmanPathAggregateDynamicDebt reward cutoff path ≤
      (Fintype.card ι : ℝ) *
        quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff path := by
  unfold quittingFiniteNashBellmanPathAggregateDynamicDebt
  calc
    (∑ who, quittingFiniteNashBellmanPathDynamicDebt
        reward cutoff path who 0) ≤
      ∑ _who : ι,
        quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff path := by
      exact Finset.sum_le_sum fun who _ ↦
        quittingFiniteNashBellmanPathDynamicDebt_le_max
          reward cutoff path who
    _ = (Fintype.card ι : ℝ) *
        quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff path := by
      simp

/-- The optimized maximum is below the optimized sum.  The proof evaluates
the maximum objective at a sum minimizer. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_le_minDynamicDebt
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff ≤
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer reward cutoff
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer_mem
      reward cutoff
  calc
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff ≤
        quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff path :=
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_le
        reward cutoff path hpath
    _ ≤ quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward cutoff path :=
      quittingFiniteNashBellmanPathMaxDynamicDebt_le_aggregate
        reward cutoff path hpath
    _ = quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward cutoff := rfl

/-- The optimized sum is at most the number of players times the optimized
maximum.  This proof deliberately evaluates the sum objective at a max
minimizer, which need not be the preceding theorem's minimizer. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt_le_card_mul_minMax
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff ≤
      (Fintype.card ι : ℝ) *
        quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
          reward cutoff := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer reward cutoff
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff
  calc
    quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff ≤
        quittingFiniteNashBellmanPathAggregateDynamicDebt
          reward cutoff path :=
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt_le
        reward cutoff path hpath
    _ ≤ (Fintype.card ι : ℝ) *
        quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff path :=
      quittingFiniteNashBellmanPathAggregateDynamicDebt_le_card_mul_max
        reward cutoff path
    _ = (Fintype.card ι : ℝ) *
        quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
          reward cutoff := rfl

/-! ## Convergence to the conditional infima -/

/-- The attained aggregate minima converge to their infimum. -/
theorem tendsto_quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Tendsto
      (quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward)
      atTop
      (nhds (⨅ cutoff : ℕ,
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff)) := by
  apply tendsto_atTop_ciInf
  · exact antitone_nat_of_succ_le fun cutoff ↦
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt_succ_le
        reward cutoff
  · refine ⟨0, ?_⟩
    rintro value ⟨cutoff, rfl⟩
    exact quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt_nonneg
      reward cutoff

/-- The attained min-max debts converge to their infimum. -/
theorem tendsto_quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Tendsto
      (quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward)
      atTop
      (nhds (⨅ cutoff : ℕ,
        quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
          reward cutoff)) := by
  apply tendsto_atTop_ciInf
  · exact antitone_nat_of_succ_le fun cutoff ↦
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_succ_le
        reward cutoff
  · refine ⟨0, ?_⟩
    rintro value ⟨cutoff, rfl⟩
    exact quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_nonneg
      reward cutoff

/-- Successive drops of the aggregate optimum tend to zero. -/
theorem tendsto_minDynamicDebt_sub_succ_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Tendsto (fun cutoff ↦
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff -
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (cutoff + 1)) atTop (nhds 0) := by
  have h := tendsto_quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward
  have hshift := h.comp (tendsto_add_atTop_nat 1)
  simpa using h.sub hshift

/-- Successive drops of the min-max optimum tend to zero. -/
theorem tendsto_minMaxDynamicDebt_sub_succ_zero [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Tendsto (fun cutoff ↦
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff -
        quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
          reward (cutoff + 1)) atTop (nhds 0) := by
  have h := tendsto_quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
    reward
  have hshift := h.comp (tendsto_add_atTop_nat 1)
  simpa using h.sub hshift

/-- Vanishing of the two optimized infima is equivalent. -/
theorem iInf_minDynamicDebt_eq_zero_iff_iInf_minMaxDynamicDebt_eq_zero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (⨅ cutoff : ℕ,
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff) =
        0 ↔
      (⨅ cutoff : ℕ,
        quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
          reward cutoff) = 0 := by
  let sumDebt :=
    quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward
  let maxDebt :=
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward
  have hsum :=
    tendsto_quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward
  have hmax :=
    tendsto_quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward
  have hsumNonneg : 0 ≤ ⨅ cutoff : ℕ, sumDebt cutoff :=
    le_ciInf fun cutoff ↦
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt_nonneg
        reward cutoff
  have hmaxNonneg : 0 ≤ ⨅ cutoff : ℕ, maxDebt cutoff :=
    le_ciInf fun cutoff ↦
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_nonneg
        reward cutoff
  constructor
  · intro hsumZero
    have hlimitLe :
        (⨅ cutoff : ℕ, maxDebt cutoff) ≤
          (⨅ cutoff : ℕ, sumDebt cutoff) := by
      apply le_of_tendsto_of_tendsto hmax hsum
      exact Filter.Eventually.of_forall fun cutoff ↦
        quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_le_minDynamicDebt
          reward cutoff
    apply le_antisymm
    · simpa [sumDebt] using hlimitLe.trans_eq hsumZero
    · exact hmaxNonneg
  · intro hmaxZero
    have hscaled : Tendsto
        (fun cutoff ↦ (Fintype.card ι : ℝ) * maxDebt cutoff)
        atTop
        (nhds ((Fintype.card ι : ℝ) *
          (⨅ cutoff : ℕ, maxDebt cutoff))) :=
      hmax.const_mul (Fintype.card ι : ℝ)
    have hlimitLe :
        (⨅ cutoff : ℕ, sumDebt cutoff) ≤
          (Fintype.card ι : ℝ) *
            (⨅ cutoff : ℕ, maxDebt cutoff) := by
      apply le_of_tendsto_of_tendsto hsum hscaled
      exact Filter.Eventually.of_forall fun cutoff ↦
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt_le_card_mul_minMax
          reward cutoff
    apply le_antisymm
    · rw [hmaxZero, mul_zero] at hlimitLe
      exact hlimitLe
    · exact hsumNonneg

/-! ## Arbitrary bounded predecessor prepend -/

/-- Prepend a supplied point rather than the canonical selected predecessor. -/
def quittingFiniteNashBellmanPathPrependPoint
    (cutoff : ℕ) (predecessor : QuittingNashBellmanPoint ι)
    (path : QuittingFiniteNashBellmanPath ι cutoff) :
    QuittingFiniteNashBellmanPath ι (cutoff + 1) :=
  Fin.cases predecessor path

omit [DecidableEq ι] in
@[simp] theorem quittingFiniteNashBellmanPathPrependPoint_zero
    (cutoff : ℕ) (predecessor : QuittingNashBellmanPoint ι)
    (path : QuittingFiniteNashBellmanPath ι cutoff) :
    quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path 0 =
      predecessor := by
  rfl

omit [DecidableEq ι] in
@[simp] theorem quittingFiniteNashBellmanPathPrependPoint_succ
    (cutoff : ℕ) (predecessor : QuittingNashBellmanPoint ι)
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (time : Fin (cutoff + 1)) :
    quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
        (Fin.succ time) = path time := by
  rfl

/-- Any bounded exact predecessor gives another admissible zero-boundary
chain. -/
theorem quittingFiniteNashBellmanPathPrependPoint_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (predecessor : QuittingNashBellmanPoint ι)
    (hpredecessor : predecessor ∈
      quittingNashBellmanBox (quittingRewardBound reward))
    (hedge : IsQuittingNashBellmanEdge reward predecessor (path 0)) :
    quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (cutoff + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro time
    refine Fin.cases hpredecessor (fun oldTime ↦ ?_) time
    simpa only [quittingFiniteNashBellmanPathPrependPoint_succ] using
      hpath.1 oldTime
  · rw [show Fin.last (cutoff + 1) = Fin.succ (Fin.last cutoff) by rfl,
      quittingFiniteNashBellmanPathPrependPoint_succ]
    exact hpath.2.1
  · intro time
    refine Fin.cases ?_ (fun oldTime ↦ ?_) time
    · change IsQuittingNashBellmanEdge reward predecessor (path 0)
      exact hedge
    · rw [show oldTime.succ.castSucc = Fin.succ oldTime.castSucc by rfl,
        quittingFiniteNashBellmanPathPrependPoint_succ]
      simpa only [quittingFiniteNashBellmanPathPrependPoint_succ] using
        hpath.2.2 oldTime

omit [DecidableEq ι] in
/-- Operational roots shift literally after an arbitrary prepend. -/
theorem quittingFiniteNashBellmanPathRoots_prependPoint_shift
    (cutoff : ℕ) (predecessor : QuittingNashBellmanPoint ι)
    (path : QuittingFiniteNashBellmanPath ι cutoff) (time : ℕ) :
    quittingFiniteNashBellmanPathRoots (cutoff + 1)
        (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path)
        (time + 1) =
      quittingFiniteNashBellmanPathRoots cutoff path time := by
  by_cases htime : time < cutoff
  · simp only [quittingFiniteNashBellmanPathRoots,
      dif_pos (by omega : time + 1 < cutoff + 1), dif_pos htime]
    congr 1
  · rw [quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
        (cutoff + 1)
        (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path)
        (time + 1) (by omega),
      quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
        cutoff path time (not_lt.mp htime)]

omit [DecidableEq ι] in
/-- Displayed values shift literally after an arbitrary prepend. -/
theorem quittingFiniteNashBellmanPathValue_prependPoint_shift
    (cutoff : ℕ) (predecessor : QuittingNashBellmanPoint ι)
    (path : QuittingFiniteNashBellmanPath ι cutoff) (time : ℕ) :
    quittingFiniteNashBellmanPathValue (cutoff + 1)
        (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path)
        (time + 1) =
      quittingFiniteNashBellmanPathValue cutoff path time := by
  unfold quittingFiniteNashBellmanPathValue
  split_ifs with hnew hold
  · have hindex : (⟨time + 1, hnew⟩ : Fin (cutoff + 1 + 1)) =
        Fin.succ (⟨time, hold⟩ : Fin (cutoff + 1)) := by
      rfl
    rw [hindex, quittingFiniteNashBellmanPathPrependPoint_succ]
  · omega
  · omega
  · rfl

/-- Time one of an arbitrary prepend carries exactly the old initial debt. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_prependPoint_tail_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (predecessor : QuittingNashBellmanPoint ι)
    (path : QuittingFiniteNashBellmanPath ι cutoff) (who : ι) :
    quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
        (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path)
        who 1 =
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 := by
  unfold quittingFiniteNashBellmanPathDynamicDebt
  have hshift := quittingFiniteDynamicDebt_shift_one reward
    (quittingFiniteNashBellmanPathRoots cutoff path)
    (quittingFiniteNashBellmanPathRoots (cutoff + 1)
      (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path))
    who
    (fun time ↦ quittingFiniteNashBellmanPathValue cutoff path time who)
    (fun time ↦ quittingFiniteNashBellmanPathValue (cutoff + 1)
      (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path)
      time who)
    (quittingPositiveSingletonDebtCap reward who)
    (quittingFiniteNashBellmanPathRoots_prependPoint_shift
      cutoff predecessor path)
    (fun time ↦ congrFun
      (quittingFiniteNashBellmanPathValue_prependPoint_shift
        cutoff predecessor path time) who)
    0 cutoff
  simpa using hshift

/-- Every coordinate weakly decreases under any bounded exact predecessor. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_prependPoint_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (predecessor : QuittingNashBellmanPoint ι)
    (hpredecessor : predecessor ∈
      quittingNashBellmanBox (quittingRewardBound reward))
    (hedge : IsQuittingNashBellmanEdge reward predecessor (path 0))
    (who : ι) :
    quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
        (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path)
        who 0 ≤
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 := by
  let extended :=
    quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
  have hextended : extended ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (cutoff + 1) :=
    quittingFiniteNashBellmanPathPrependPoint_mem reward cutoff path hpath
      predecessor hpredecessor hedge
  calc
    quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
        extended who 0 ≤
      quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
        extended who 1 :=
      quittingFiniteNashBellmanPathDynamicDebt_le_succ reward (cutoff + 1)
        extended hextended who 0 (by omega)
    _ = quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 :=
      quittingFiniteNashBellmanPathDynamicDebt_prependPoint_tail_eq
        reward cutoff predecessor path who

/-! ## Calibrated losses of selected minimizers -/

/-- Prepending any bounded exact predecessor to the selected sum minimizer
has total coordinate loss at most the drop in the optimized aggregate value. -/
theorem quittingFiniteDynamicDebt_sumMinimizer_prependPoint_calibrated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (predecessor : QuittingNashBellmanPoint ι)
    (hpredecessor : predecessor ∈
      quittingNashBellmanBox (quittingRewardBound reward))
    (hedge : IsQuittingNashBellmanEdge reward predecessor
      (quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
        reward cutoff 0)) :
    let path :=
      quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer reward cutoff
    let extended :=
      quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
    0 ≤ ∑ who,
        (quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 -
          quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
            extended who 0) ∧
      (∑ who,
        (quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 -
          quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
            extended who 0)) ≤
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff -
          quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
            reward (cutoff + 1) := by
  dsimp only
  let path :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer reward cutoff
  let extended :=
    quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer_mem
      reward cutoff
  have hextended : extended ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (cutoff + 1) :=
    quittingFiniteNashBellmanPathPrependPoint_mem reward cutoff path hpath
      predecessor hpredecessor hedge
  have hcoordinate : ∀ who,
      quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
          extended who 0 ≤
        quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 :=
    fun who ↦ quittingFiniteNashBellmanPathDynamicDebt_prependPoint_le
      reward cutoff path hpath predecessor hpredecessor hedge who
  have hnewMinimum :
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (cutoff + 1) ≤
        ∑ who, quittingFiniteNashBellmanPathDynamicDebt
          reward (cutoff + 1) extended who 0 := by
    simpa only [quittingFiniteNashBellmanPathAggregateDynamicDebt] using
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt_le
        reward (cutoff + 1) extended hextended
  constructor
  · exact Finset.sum_nonneg fun who _ ↦ sub_nonneg.mpr (hcoordinate who)
  · rw [Finset.sum_sub_distrib]
    change
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff -
          (∑ who, quittingFiniteNashBellmanPathDynamicDebt
            reward (cutoff + 1) extended who 0) ≤
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff -
          quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
            reward (cutoff + 1)
    exact sub_le_sub_left hnewMinimum _

/-- Consequently every individual coordinate loss of a prepended sum
minimizer is controlled by the optimized sum drop. -/
theorem quittingFiniteDynamicDebt_sumMinimizer_prependPoint_coordinate_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (predecessor : QuittingNashBellmanPoint ι)
    (hpredecessor : predecessor ∈
      quittingNashBellmanBox (quittingRewardBound reward))
    (hedge : IsQuittingNashBellmanEdge reward predecessor
      (quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
        reward cutoff 0)) (who : ι) :
    let path :=
      quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer reward cutoff
    let extended :=
      quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
    0 ≤ quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 -
        quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
          extended who 0 ∧
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 -
          quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
            extended who 0 ≤
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff -
          quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
            reward (cutoff + 1) := by
  dsimp only
  let path :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer reward cutoff
  let extended :=
    quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer_mem
      reward cutoff
  have hcoordinate : ∀ player,
      0 ≤ quittingFiniteNashBellmanPathDynamicDebt reward cutoff path player 0 -
        quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
          extended player 0 := fun player ↦ sub_nonneg.mpr
    (quittingFiniteNashBellmanPathDynamicDebt_prependPoint_le
      reward cutoff path hpath predecessor hpredecessor hedge player)
  have hcalibrated :=
    quittingFiniteDynamicDebt_sumMinimizer_prependPoint_calibrated
      reward cutoff predecessor hpredecessor hedge
  refine ⟨hcoordinate who, ?_⟩
  exact (Finset.single_le_sum
      (fun player _ ↦ hcoordinate player) (Finset.mem_univ who)).trans
    hcalibrated.2

/-- For a maximum minimizer, arbitrary prepend controls the maximum loss,
but not all coordinate losses. -/
theorem quittingFiniteDynamicDebt_maxMinimizer_prependPoint_calibrated
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (predecessor : QuittingNashBellmanPoint ι)
    (hpredecessor : predecessor ∈
      quittingNashBellmanBox (quittingRewardBound reward))
    (hedge : IsQuittingNashBellmanEdge reward predecessor
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward cutoff 0)) :
    let path :=
      quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward cutoff
    let extended :=
      quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
    0 ≤ quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
          reward cutoff -
        quittingFiniteNashBellmanPathMaxDynamicDebt
          reward (cutoff + 1) extended ∧
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff -
          quittingFiniteNashBellmanPathMaxDynamicDebt
            reward (cutoff + 1) extended ≤
        quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff -
          quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
            reward (cutoff + 1) := by
  dsimp only
  let path :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer reward cutoff
  let extended :=
    quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff
  have hextended : extended ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (cutoff + 1) :=
    quittingFiniteNashBellmanPathPrependPoint_mem reward cutoff path hpath
      predecessor hpredecessor hedge
  have hcoordinate : ∀ who,
      quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
          extended who 0 ≤
        quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 :=
    fun who ↦ quittingFiniteNashBellmanPathDynamicDebt_prependPoint_le
      reward cutoff path hpath predecessor hpredecessor hedge who
  have hmaxLe :
      quittingFiniteNashBellmanPathMaxDynamicDebt reward (cutoff + 1)
          extended ≤
        quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff path := by
    unfold quittingFiniteNashBellmanPathMaxDynamicDebt
    exact Finset.sup'_le Finset.univ_nonempty _ fun who _ ↦
      (hcoordinate who).trans
        (quittingFiniteNashBellmanPathDynamicDebt_le_max
          reward cutoff path who)
  have hnewMinimum :
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
          reward (cutoff + 1) ≤
        quittingFiniteNashBellmanPathMaxDynamicDebt
          reward (cutoff + 1) extended :=
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_le
      reward (cutoff + 1) extended hextended
  constructor
  · exact sub_nonneg.mpr hmaxLe
  · exact sub_le_sub_left hnewMinimum _

/-- A coordinate attaining the *new* maximum inherits the maximum-loss
calibration.  No claim is made for the remaining coordinates. -/
theorem quittingFiniteDynamicDebt_maxMinimizer_prependPoint_argmax_loss_le
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (predecessor : QuittingNashBellmanPoint ι)
    (hpredecessor : predecessor ∈
      quittingNashBellmanBox (quittingRewardBound reward))
    (hedge : IsQuittingNashBellmanEdge reward predecessor
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward cutoff 0)) (who : ι)
    (hattains :
      quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
          (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor
            (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
              reward cutoff)) who 0 =
        quittingFiniteNashBellmanPathMaxDynamicDebt reward (cutoff + 1)
          (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor
            (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
              reward cutoff))) :
    let path :=
      quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward cutoff
    let extended :=
      quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
    0 ≤ quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 -
        quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
          extended who 0 ∧
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 -
          quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
            extended who 0 ≤
        quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff -
          quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
            reward (cutoff + 1) := by
  dsimp only
  let path :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer reward cutoff
  let extended :=
    quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff
  have hcoordinate :=
    quittingFiniteNashBellmanPathDynamicDebt_prependPoint_le
      reward cutoff path hpath predecessor hpredecessor hedge who
  have holdLe := quittingFiniteNashBellmanPathDynamicDebt_le_max
    reward cutoff path who
  have hmaxCalibrated :=
    quittingFiniteDynamicDebt_maxMinimizer_prependPoint_calibrated
      reward cutoff predecessor hpredecessor hedge
  refine ⟨sub_nonneg.mpr hcoordinate, ?_⟩
  calc
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 -
        quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
          extended who 0 ≤
      quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff path -
        quittingFiniteNashBellmanPathMaxDynamicDebt reward (cutoff + 1)
          extended := by
        rw [hattains]
        exact sub_le_sub_right holdLe _
    _ ≤ quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
          reward cutoff -
        quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
          reward (cutoff + 1) := hmaxCalibrated.2

/-! ## The maximum-loss logical fence -/

/-- Old and new debt vectors for the elementary two-coordinate maximum
counterexample. -/
def maxLossFenceOld : Bool → ℝ := fun _ ↦ 1

def maxLossFenceNew : Bool → ℝ := fun who ↦ if who then 0 else 1

/-- Coordinatewise decrease and equality of maxima do not force every
coordinate loss to be small: the `true` coordinate loses exactly one. -/
theorem maxLossFence :
    (∀ who, maxLossFenceNew who ≤ maxLossFenceOld who) ∧
      Finset.univ.sup' Finset.univ_nonempty maxLossFenceOld =
        Finset.univ.sup' Finset.univ_nonempty maxLossFenceNew ∧
      maxLossFenceOld true - maxLossFenceNew true = 1 := by
  have hcoordinate : ∀ who,
      maxLossFenceNew who ≤ maxLossFenceOld who := by
    intro who
    cases who <;> norm_num [maxLossFenceOld, maxLossFenceNew]
  refine ⟨hcoordinate, ?_, ?_⟩
  · apply le_antisymm
    · apply Finset.sup'_le
      intro who _
      cases who
      · exact Finset.le_sup' maxLossFenceNew (Finset.mem_univ false)
      · calc
          maxLossFenceOld true = maxLossFenceNew false := by
            norm_num [maxLossFenceOld, maxLossFenceNew]
          _ ≤ Finset.univ.sup' Finset.univ_nonempty maxLossFenceNew :=
            Finset.le_sup' maxLossFenceNew (Finset.mem_univ false)
    · exact Finset.sup'_le Finset.univ_nonempty _ fun who _ ↦
        (hcoordinate who).trans
          (Finset.le_sup' maxLossFenceOld (Finset.mem_univ who))
  · norm_num [maxLossFenceOld, maxLossFenceNew]

end GameTheory
