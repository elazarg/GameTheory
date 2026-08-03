/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteDynamicDebtCompiler
import GameTheory.Concepts.Stochastic.QuittingDynamicDebtProjectiveTail
import GameTheory.Concepts.Stochastic.QuittingNashBellmanClockReduction

/-!
# Exact dynamic debt on finite zero-boundary Nash--Bellman chains

This file puts the corrected exact Bellman debt directly on the compact
finite-chain space.  For a chain of length `K`, player `i`'s initial debt is
`quittingFiniteDynamicDebt` with terminal boundary
`max 0 (r({i})_i)`.  The aggregate objective is their finite sum.

The all-Continue extension of a zero-boundary chain is a genuine prescribed
value sequence.  Its local residual vanishes before the cutoff, which gives
localized nonnegativity and the terminal-cap bound needed to place every
backward debt state in `quittingDebtBox`.  Consecutive annotated states are
literal `IsQuittingDynamicDebtEdge`s.

No claim is made that the infimum of the exact-debt objectives is zero, nor
that this finite-chain architecture is dense in all terminal equilibria.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Prescribed-value and residual interface -/

/-- A zero-boundary path's displayed value is zero from the cutoff onward. -/
theorem quittingFiniteNashBellmanPathValue_eq_zero_of_cutoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) (htime : cutoff ≤ time) :
    quittingFiniteNashBellmanPathValue cutoff path time = 0 := by
  rcases htime.eq_or_lt with rfl | hlt
  · exact quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
      reward cutoff path hpath
  · unfold quittingFiniteNashBellmanPathValue
    rw [dif_neg]
    omega

/-- Each scalar coordinate of an admissible finite path is a globally
defined prescribed value for the all-Continue root extension. -/
theorem isQuittingLivePrescribedValue_finiteNashBellmanPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) :
    IsQuittingLivePrescribedValue reward
      (quittingFiniteNashBellmanPathRoots cutoff path) who
      (fun time ↦ quittingFiniteNashBellmanPathValue cutoff path time who) := by
  intro time
  by_cases htime : time < cutoff
  · have hpolicy := congrFun
      (quittingFiniteNashBellmanPathValue_eq_successor
        reward cutoff path hpath time htime) who
    have hcongr := quittingRootExpectedPayoff_continuation_congr
      reward
      (quittingFiniteNashBellmanPathValue cutoff path (time + 1))
      (fun _ ↦ quittingFiniteNashBellmanPathValue cutoff path (time + 1) who)
      (quittingFiniteNashBellmanPathRoots cutoff path time) who rfl
    exact hpolicy.trans hcongr
  · have hcutoff : cutoff ≤ time := not_lt.mp htime
    have hzero := quittingFiniteNashBellmanPathValue_eq_zero_of_cutoff_le
      reward cutoff path hpath time hcutoff
    have hzeroNext := quittingFiniteNashBellmanPathValue_eq_zero_of_cutoff_le
      reward cutoff path hpath (time + 1) (by omega)
    have hroot := quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
      cutoff path time hcutoff
    have hzeroWho := congrFun hzero who
    have hzeroNextWho := congrFun hzeroNext who
    change quittingFiniteNashBellmanPathValue cutoff path time who =
      quittingRootSuccessorPayoff reward
        (fun _ ↦ quittingFiniteNashBellmanPathValue cutoff path (time + 1) who)
        (quittingFiniteNashBellmanPathRoots cutoff path time) who
    rw [hzeroWho, hzeroNextWho, hroot]
    change (0 : ℝ) = quittingRootSuccessorPayoff reward
      (0 : Payoff ι) quittingAllContinueRoot who
    exact (congrFun
      (quittingRootSuccessorPayoff_allContinueRoot_eq
        reward (0 : Payoff ι)) who).symm

set_option maxHeartbeats 800000 in
-- Scalarizing the finite vector path through continuation congruence is costly.
/-- Exact root Nash makes the scalar prescribed Bellman residual vanish at
every pre-terminal time of an admissible path. -/
theorem quittingPrescribedOneStepResidual_finiteNashBellmanPath_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) (time : ℕ) (htime : time < cutoff) :
    quittingPrescribedOneStepResidual reward
      (quittingFiniteNashBellmanPathRoots cutoff path) who
      (fun liveTime ↦
        quittingFiniteNashBellmanPathValue cutoff path liveTime who)
      time = 0 := by
  let roots := quittingFiniteNashBellmanPathRoots cutoff path
  let index : Fin cutoff := ⟨time, htime⟩
  let current := path (Fin.castSucc index)
  let successor := path (Fin.succ index)
  have hedge : IsQuittingNashBellmanEdge reward current successor := by
    exact hpath.2.2 index
  let root := quittingRootOfSimplex current.2
  let quitValue := quittingRootQuitPayoff reward successor.1 root who
  let continueValue := quittingRootContinuePayoff reward successor.1 root who
  have hmax : max quitValue continueValue = current.1 who := by
    apply le_antisymm
    · exact max_le
        (quittingRootQuitPayoff_le_currentValue_of_nashBellmanEdge
          reward current successor hedge who)
        (quittingRootContinuePayoff_le_currentValue_of_nashBellmanEdge
          reward current successor hedge who)
    · exact currentValue_le_max_endpoints_of_nashBellmanEdge
        reward current successor hedge who
  have hroot : roots time = root := by
    simp [roots, root, current, index,
      quittingFiniteNashBellmanPathRoots, htime]
  have hcurrent :
      quittingFiniteNashBellmanPathValue cutoff path time who =
        current.1 who := by
    simp [current, index, quittingFiniteNashBellmanPathValue,
      Nat.lt_succ_of_lt htime]
  have hsuccessor :
      quittingFiniteNashBellmanPathValue cutoff path (time + 1) =
        successor.1 := by
    simp [successor, index, quittingFiniteNashBellmanPathValue,
      Nat.succ_lt_succ htime]
  unfold quittingPrescribedOneStepResidual quittingLiveBellmanValue
  change
    max (quittingFixedOpponentsQuitValue reward roots who time)
        (quittingFixedOpponentsContinueReward reward roots who time +
          quittingFixedOpponentsContinueMass roots who time *
            quittingFiniteNashBellmanPathValue cutoff path (time + 1) who) -
      quittingFiniteNashBellmanPathValue cutoff path time who = 0
  rw [congrFun hsuccessor who]
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward roots who successor.1 time,
    ← quittingRootContinuePayoff_eq_fixedOpponents
      reward roots who successor.1 time,
    hroot, hcurrent]
  exact sub_eq_zero.mpr hmax

/-! ## A localized finite dynamic-debt estimate -/

/-- The usual survival-times-terminal bound only needs zero residual on the
finite interval actually traversed by the recursion. -/
theorem quittingFiniteDynamicDebt_le_survival_mul_terminalDebt_on
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel ≤
        quittingOpponentSurvivalWeight roots who start fuel * terminalDebt := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro _
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      intro hwindow
      have hstart : start < bound := by omega
      have htailWindow : start + 1 + fuel ≤ bound := by omega
      have hstep := quittingFiniteDynamicDebt_succ_le_residual_add
        reward roots who prescribed hprescribed hterminalDebt start fuel
      rw [hresidual start hstart, zero_add] at hstep
      have htail := ih (start + 1) htailWindow
      have hmass : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      have hscaled := mul_le_mul_of_nonneg_left htail hmass
      calc
        quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
            start (fuel + 1) ≤
          quittingFixedOpponentsContinueMass roots who start *
            quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
              (start + 1) fuel := hstep
        _ ≤ quittingFixedOpponentsContinueMass roots who start *
            (quittingOpponentSurvivalWeight roots who (start + 1) fuel *
              terminalDebt) := hscaled
        _ = quittingOpponentSurvivalWeight roots who start (fuel + 1) *
            terminalDebt := by
          rw [show fuel + 1 = 1 + fuel by omega,
            quittingOpponentSurvivalWeight_add]
          simp [quittingOpponentSurvivalWeight]
          ring

/-! ## Exact-D objective and augmented states -/

/-- Playerwise exact dynamic debt at a displayed time, with the remaining
zero-boundary horizon and the singleton-or-Never terminal option. -/
def quittingFiniteNashBellmanPathDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (who : ι) (time : ℕ) : ℝ :=
  quittingFiniteDynamicDebt reward
    (quittingFiniteNashBellmanPathRoots cutoff path) who
    (fun liveTime ↦
      quittingFiniteNashBellmanPathValue cutoff path liveTime who)
    (quittingPositiveSingletonDebtCap reward who)
    time (cutoff - time)

/-- Sum of the players' initial exact dynamic debts.  For finite nonempty
player sets, vanishing of this nonnegative objective is equivalent to
vanishing of the maximum playerwise debt. -/
def quittingFiniteNashBellmanPathAggregateDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff) : ℝ :=
  ∑ who, quittingFiniteNashBellmanPathDynamicDebt
    reward cutoff path who 0

/-- Every displayed exact dynamic debt is nonnegative. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) (time : ℕ) :
    0 ≤ quittingFiniteNashBellmanPathDynamicDebt
      reward cutoff path who time := by
  exact quittingFiniteDynamicDebt_nonneg reward
    (quittingFiniteNashBellmanPathRoots cutoff path) who
    (fun liveTime ↦
      quittingFiniteNashBellmanPathValue cutoff path liveTime who)
    (isQuittingLivePrescribedValue_finiteNashBellmanPath
      reward cutoff path hpath who)
    (le_max_left _ _) time (cutoff - time)

/-- Before or at the cutoff, exact dynamic debt stays within its terminal
singleton cap. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_le_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) (time : ℕ) (htime : time ≤ cutoff) :
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who time ≤
      quittingPositiveSingletonDebtCap reward who := by
  let roots := quittingFiniteNashBellmanPathRoots cutoff path
  let prescribed := fun liveTime ↦
    quittingFiniteNashBellmanPathValue cutoff path liveTime who
  let cap := quittingPositiveSingletonDebtCap reward who
  have hraw := quittingFiniteDynamicDebt_le_survival_mul_terminalDebt_on
    reward roots who prescribed
      (isQuittingLivePrescribedValue_finiteNashBellmanPath
        reward cutoff path hpath who)
      (show 0 ≤ cap from le_max_left _ _) cutoff
      (fun liveTime hliveTime ↦
        quittingPrescribedOneStepResidual_finiteNashBellmanPath_eq_zero
          reward cutoff path hpath who liveTime hliveTime)
      time (cutoff - time) (by omega)
  have hsurvival := quittingOpponentSurvivalWeight_le_one
    roots who time (cutoff - time)
  have hcap0 : 0 ≤ cap := le_max_left _ _
  change quittingFiniteDynamicDebt reward roots who prescribed cap
      time (cutoff - time) ≤ cap
  exact hraw.trans (mul_le_of_le_one_left hcap0 hsurvival)

/-- The exact-D annotation of a finite chain, padded by its terminal state
and terminal debt after the cutoff. -/
def quittingFiniteNashBellmanPathDynamicDebtPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (time : ℕ) : QuittingDebtPoint ι :=
  if htime : time ≤ cutoff then
    (path ⟨time, Nat.lt_succ_of_le htime⟩,
      fun who ↦ quittingFiniteNashBellmanPathDynamicDebt
        reward cutoff path who time)
  else
    (path (Fin.last cutoff), quittingPositiveSingletonDebtCap reward)

/-- Every state of the padded exact-D annotation lies in the common compact
debt box. -/
theorem quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) :
    quittingFiniteNashBellmanPathDynamicDebtPoint reward cutoff path time ∈
      quittingDebtBox reward := by
  unfold quittingFiniteNashBellmanPathDynamicDebtPoint
  split_ifs with htime
  · exact ⟨hpath.1 _,
      ⟨fun who ↦ quittingFiniteNashBellmanPathDynamicDebt_nonneg
          reward cutoff path hpath who time,
        fun who ↦ quittingFiniteNashBellmanPathDynamicDebt_le_cap
          reward cutoff path hpath who time htime⟩⟩
  · exact ⟨hpath.1 (Fin.last cutoff),
      ⟨fun who ↦ le_max_left _ _, fun _ ↦ le_rfl⟩⟩

/-- Consecutive pre-terminal annotations satisfy the literal exact dynamic-
debt recurrence, not merely its multiplicative upper bound. -/
theorem quittingFiniteNashBellmanPathDynamicDebtPoint_edge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) (htime : time < cutoff) :
    IsQuittingDynamicDebtEdge reward
      (quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path time)
      (quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path (time + 1)) := by
  let roots := quittingFiniteNashBellmanPathRoots cutoff path
  let value := quittingFiniteNashBellmanPathValue cutoff path
  let index : Fin cutoff := ⟨time, htime⟩
  let current := path (Fin.castSucc index)
  let successor := path (Fin.succ index)
  have hcurrentPoint :
      quittingFiniteNashBellmanPathDynamicDebtPoint
          reward cutoff path time =
        (current, fun who ↦
          quittingFiniteNashBellmanPathDynamicDebt
            reward cutoff path who time) := by
    simp [quittingFiniteNashBellmanPathDynamicDebtPoint, current, index,
      Nat.le_of_lt htime]
  have hsuccessorPoint :
      quittingFiniteNashBellmanPathDynamicDebtPoint
          reward cutoff path (time + 1) =
        (successor, fun who ↦
          quittingFiniteNashBellmanPathDynamicDebt
            reward cutoff path who (time + 1)) := by
    simp [quittingFiniteNashBellmanPathDynamicDebtPoint, successor, index,
      Nat.succ_le_iff.mpr htime]
  rw [hcurrentPoint, hsuccessorPoint]
  constructor
  · exact hpath.2.2 index
  · intro who
    let nextDebt := quittingFiniteNashBellmanPathDynamicDebt
      reward cutoff path who (time + 1)
    have hremaining : cutoff - time = cutoff - (time + 1) + 1 := by omega
    have hroot : roots time = quittingRootOfSimplex current.2 := by
      simp [roots, current, index,
        quittingFiniteNashBellmanPathRoots, htime]
    have hcurrentValue : value time who = current.1 who := by
      simp [value, current, index, quittingFiniteNashBellmanPathValue,
        Nat.lt_succ_of_lt htime]
    have hsuccessorValue : value (time + 1) = successor.1 := by
      simp [value, successor, index, quittingFiniteNashBellmanPathValue,
        Nat.succ_lt_succ htime]
    have hmass : quittingFixedOpponentsContinueMass roots who time =
        quittingDebtOpponentContinueMass
          (current, fun player ↦
            quittingFiniteNashBellmanPathDynamicDebt
              reward cutoff path player time) who := by
      unfold quittingFixedOpponentsContinueMass
      rw [hroot]
      exact (quittingDebtOpponentContinueMass_eq_stationary
        (current, fun player ↦
          quittingFiniteNashBellmanPathDynamicDebt
            reward cutoff path player time) who).symm
    have hquit : quittingFixedOpponentsQuitValue reward roots who time =
        quittingRootQuitPayoff reward successor.1
          (quittingRootOfSimplex current.2) who := by
      rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward roots who successor.1 time, hroot]
    have hcontinue :
        quittingFixedOpponentsContinueReward reward roots who time +
            quittingFixedOpponentsContinueMass roots who time *
              (value (time + 1) who + nextDebt) =
          quittingRootContinuePayoff reward successor.1
              (quittingRootOfSimplex current.2) who +
            quittingDebtOpponentContinueMass
                (current, fun player ↦
                  quittingFiniteNashBellmanPathDynamicDebt
                    reward cutoff path player time) who * nextDebt := by
      have hbase := quittingRootContinuePayoff_eq_fixedOpponents
        reward roots who successor.1 time
      rw [hroot] at hbase
      rw [congrFun hsuccessorValue who, hbase, hmass]
      ring
    unfold quittingFiniteNashBellmanPathDynamicDebt
    change quittingFiniteDynamicDebt reward roots who (fun liveTime ↦
        value liveTime who) (quittingPositiveSingletonDebtCap reward who)
          time (cutoff - time) = _
    unfold quittingDynamicDebtUpdate
    rw [hremaining, quittingFiniteDynamicDebt_succ]
    change
      max (quittingFixedOpponentsQuitValue reward roots who time)
          (quittingFixedOpponentsContinueReward reward roots who time +
            quittingFixedOpponentsContinueMass roots who time *
              (value (time + 1) who + nextDebt)) - value time who =
        max
            (quittingRootQuitPayoff reward successor.1
              (quittingRootOfSimplex current.2) who)
            (quittingRootContinuePayoff reward successor.1
                (quittingRootOfSimplex current.2) who +
              quittingDebtOpponentContinueMass
                  (current, fun player ↦
                    quittingFiniteNashBellmanPathDynamicDebt
                      reward cutoff path player time) who * nextDebt) -
          current.1 who
    rw [hquit, hcontinue, hcurrentValue]

/-- The aggregate exact-D objective is nonnegative on every admissible
zero-boundary chain. -/
theorem quittingFiniteNashBellmanPathAggregateDynamicDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    0 ≤ quittingFiniteNashBellmanPathAggregateDynamicDebt
      reward cutoff path := by
  unfold quittingFiniteNashBellmanPathAggregateDynamicDebt
  exact Finset.sum_nonneg fun who _ ↦
    quittingFiniteNashBellmanPathDynamicDebt_nonneg
      reward cutoff path hpath who 0

/-- Each initial player debt is bounded by the aggregate exact-D objective. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_le_aggregate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) :
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 ≤
      quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward cutoff path := by
  unfold quittingFiniteNashBellmanPathAggregateDynamicDebt
  exact Finset.single_le_sum
    (fun player _ ↦ quittingFiniteNashBellmanPathDynamicDebt_nonneg
      reward cutoff path hpath player 0)
    (Finset.mem_univ who)

/-- **Exact-D finite-chain criterion.**  Arbitrarily small aggregate exact
dynamic debt on zero-boundary exact Nash--Bellman chains suffices for a
uniform-equilibrium payoff.  This is the positive half of the proposed
decisive question; universal smallness is not asserted. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_finiteNashBellmanPathDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hchains : ∀ ε : ℝ, 0 < ε →
      ∃ cutoff : ℕ, ∃ path : QuittingFiniteNashBellmanPath ι cutoff,
        path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff ∧
        quittingFiniteNashBellmanPathAggregateDynamicDebt
          reward cutoff path ≤ ε) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_finiteDynamicDebtChains
    reward
  intro ε hε
  obtain ⟨cutoff, path, hpath, hdebt⟩ := hchains ε hε
  refine ⟨quittingFiniteNashBellmanPathRoots cutoff path,
    quittingFiniteNashBellmanPathValue cutoff path, cutoff,
    quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
      cutoff path,
    quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
      reward cutoff path hpath,
    quittingFiniteNashBellmanPathValue_eq_successor
      reward cutoff path hpath, ?_⟩
  intro who
  have hplayer :=
    (quittingFiniteNashBellmanPathDynamicDebt_le_aggregate
      reward cutoff path hpath who).trans hdebt
  simpa only [quittingFiniteNashBellmanPathDynamicDebt,
    Nat.zero_sub, Nat.sub_zero, quittingPositiveSingletonDebtCap] using hplayer

end GameTheory
