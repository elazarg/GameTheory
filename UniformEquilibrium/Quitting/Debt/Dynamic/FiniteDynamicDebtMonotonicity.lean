/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtOptimizer
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanDebtMonotonicity

/-!
# Monotonicity of optimized exact finite-chain dynamic debt

Prepending an exact Nash--Bellman predecessor adds one genuine exact-D edge
before a finite zero-boundary chain.  The time-one suffix is literally the
old root and value sequence, including their all-Continue/zero extensions.
Exact dynamic debt cannot increase when pulled backwards across the new
edge.  Consequently both the aggregate and literal playerwise-maximum
objectives weakly decrease under prepending, and their attained minima are
antitone in the cutoff.

This resolves a selection issue but not the existence problem.  Independently
chosen minimizers need not be nested: to compare successive minimum values,
one prepends a predecessor to the old minimizer and uses it merely as a
competitor at the new cutoff.  No assertion that the decreasing minimum
converges to zero is made here.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The literal shifted suffix -/

/-- The whole operational root sequence after time one in the prepended
chain is the old sequence.  This includes both all-Continue tails. -/
theorem quittingFiniteNashBellmanPathRoots_prepend_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) :
    quittingFiniteNashBellmanPathRoots (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
        (time + 1) =
      quittingFiniteNashBellmanPathRoots cutoff path time := by
  by_cases htime : time < cutoff
  · exact quittingFiniteNashBellmanPathRoots_prepend_succ
      reward cutoff path hpath time htime
  · rw [quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
        (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
        (time + 1) (by omega),
      quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
        cutoff path time (not_lt.mp htime)]

/-- The whole displayed value sequence after time one in the prepended
chain is the old sequence, including both zero extensions. -/
theorem quittingFiniteNashBellmanPathValue_prepend_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) :
    quittingFiniteNashBellmanPathValue (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
        (time + 1) =
      quittingFiniteNashBellmanPathValue cutoff path time := by
  unfold quittingFiniteNashBellmanPathValue
  split_ifs with hnew hold
  · have hindex : (⟨time + 1, hnew⟩ : Fin (cutoff + 1 + 1)) =
        Fin.succ (⟨time, hold⟩ : Fin (cutoff + 1)) := by
      rfl
    rw [hindex, quittingFiniteNashBellmanPathPrepend_succ]
  · omega
  · omega
  · rfl

/-! ## Shift invariance of the finite exact recursion -/

/-- Shifting both the root and prescribed-value sequences by one leaves a
finite exact-debt recursion unchanged. -/
theorem quittingFiniteDynamicDebt_shift_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (oldRoots newRoots : ℕ → ι → PMF Bool) (who : ι)
    (oldPrescribed newPrescribed : ℕ → ℝ)
    (terminalDebt : ℝ)
    (hroots : ∀ time, newRoots (time + 1) = oldRoots time)
    (hprescribed : ∀ time,
      newPrescribed (time + 1) = oldPrescribed time)
    (start fuel : ℕ) :
    quittingFiniteDynamicDebt reward newRoots who newPrescribed terminalDebt
        (start + 1) fuel =
      quittingFiniteDynamicDebt reward oldRoots who oldPrescribed terminalDebt
        start fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [quittingFiniteDynamicDebt_succ,
        quittingFiniteDynamicDebt_succ]
      rw [hprescribed start, hprescribed (start + 1), ih (start + 1)]
      unfold quittingFixedOpponentsQuitValue
        quittingFixedOpponentsContinueReward
        quittingFixedOpponentsContinueMass
      rw [hroots start]

/-- The exact dynamic debt at time one of a prepended chain is exactly the
old chain's initial exact dynamic debt. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_prepend_tail_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) :
    quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
        who 1 =
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 := by
  unfold quittingFiniteNashBellmanPathDynamicDebt
  have hshift := quittingFiniteDynamicDebt_shift_one reward
    (quittingFiniteNashBellmanPathRoots cutoff path)
    (quittingFiniteNashBellmanPathRoots (cutoff + 1)
      (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath))
    who
    (fun time ↦ quittingFiniteNashBellmanPathValue cutoff path time who)
    (fun time ↦ quittingFiniteNashBellmanPathValue (cutoff + 1)
      (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
      time who)
    (quittingPositiveSingletonDebtCap reward who)
    (quittingFiniteNashBellmanPathRoots_prepend_shift
      reward cutoff path hpath)
    (fun time ↦ congrFun
      (quittingFiniteNashBellmanPathValue_prepend_shift
        reward cutoff path hpath time) who)
    0 cutoff
  simpa using hshift

/-! ## Coordinatewise and scalar monotonicity -/

/-- Along any displayed pre-terminal exact Nash--Bellman edge, exact dynamic
debt is weakly smaller at the current point than at its successor. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_le_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) (time : ℕ) (htime : time < cutoff) :
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who time ≤
      quittingFiniteNashBellmanPathDynamicDebt
        reward cutoff path who (time + 1) := by
  let current := quittingFiniteNashBellmanPathDynamicDebtPoint
    reward cutoff path time
  let successor := quittingFiniteNashBellmanPathDynamicDebtPoint
    reward cutoff path (time + 1)
  have hedge : IsQuittingDynamicDebtEdge reward current successor :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_edge
      reward cutoff path hpath time htime
  have hsuccessor : successor ∈ quittingDebtBox reward :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
      reward cutoff path hpath (time + 1)
  have hle := quittingDynamicDebtUpdate_le_successor reward current successor
    hedge.1 hsuccessor.2.1 who
  rw [← hedge.2 who] at hle
  simpa [current, successor,
    quittingFiniteNashBellmanPathDynamicDebtPoint,
    Nat.le_of_lt htime, Nat.succ_le_iff.mpr htime] using hle

/-- Prepending a predecessor weakly lowers every player's initial exact
dynamic debt. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_prepend_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) :
    quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
        who 0 ≤
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 := by
  have hnewMem := quittingFiniteNashBellmanPathPrepend_mem
    reward cutoff path hpath
  calc
    quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
        who 0 ≤
      quittingFiniteNashBellmanPathDynamicDebt reward (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
        who 1 :=
      quittingFiniteNashBellmanPathDynamicDebt_le_succ reward (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
        hnewMem who 0 (by omega)
    _ = quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 :=
      quittingFiniteNashBellmanPathDynamicDebt_prepend_tail_eq
        reward cutoff path hpath who

/-- Aggregate exact dynamic debt weakly decreases under predecessor
prepending. -/
theorem quittingFiniteNashBellmanPathAggregateDynamicDebt_prepend_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteNashBellmanPathAggregateDynamicDebt reward (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath) ≤
      quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward cutoff path := by
  unfold quittingFiniteNashBellmanPathAggregateDynamicDebt
  exact Finset.sum_le_sum fun who _ ↦
    quittingFiniteNashBellmanPathDynamicDebt_prepend_le
      reward cutoff path hpath who

/-- The literal maximum exact dynamic debt weakly decreases under
predecessor prepending. -/
theorem quittingFiniteNashBellmanPathMaxDynamicDebt_prepend_le [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteNashBellmanPathMaxDynamicDebt reward (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath) ≤
      quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff path := by
  unfold quittingFiniteNashBellmanPathMaxDynamicDebt
  exact Finset.sup'_le Finset.univ_nonempty _ fun who _ ↦
    (quittingFiniteNashBellmanPathDynamicDebt_prepend_le
      reward cutoff path hpath who).trans
      (quittingFiniteNashBellmanPathDynamicDebt_le_max
        reward cutoff path who)

/-! ## Antitonicity of the attained minima -/

/-- The attained minimum aggregate exact dynamic debt is antitone in the
finite cutoff.  The selected minimizers themselves need not be nested. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt_succ_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (cutoff + 1) ≤
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer reward cutoff
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer_mem
      reward cutoff
  exact (quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt_le
      reward (cutoff + 1)
      (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
      (quittingFiniteNashBellmanPathPrepend_mem
        reward cutoff path hpath)).trans
    (quittingFiniteNashBellmanPathAggregateDynamicDebt_prepend_le
      reward cutoff path hpath)

/-- The attained minimum playerwise maximum exact dynamic debt is antitone
in the finite cutoff.  No coherent selection of minimizers is required. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_succ_le
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
        reward (cutoff + 1) ≤
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer reward cutoff
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff
  exact (quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_le
      reward (cutoff + 1)
      (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
      (quittingFiniteNashBellmanPathPrepend_mem
        reward cutoff path hpath)).trans
    (quittingFiniteNashBellmanPathMaxDynamicDebt_prepend_le
      reward cutoff path hpath)

end GameTheory
