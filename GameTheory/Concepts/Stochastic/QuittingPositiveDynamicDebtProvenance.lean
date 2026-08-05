/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteDynamicDebtCalibration
import GameTheory.Concepts.Stochastic.QuittingMarkedFenceFirstOpponentAdapter
import GameTheory.Concepts.Potential.MixedPotential

/-!
# Provenance forced by positive exact dynamic debt

This file develops the local, selector-free part of positive-debt
provenance.  Positive exact debt propagates forward through every finite
exact-D edge.  At the last
live edge of a zero-boundary chain it forces a genuine positive-probability
opponent action whose *full simultaneous quitter set* gives the debt owner a
strictly larger payoff when the owner continues than when the owner joins the
same set of quitters.

This is a residual-depth-one terminal packet.  It is not singletonized, does
not choose a new owner, and is not claimed to be a terminal equilibrium or a
finite discharge.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Strict forward propagation -/

/-- Positive current exact debt forces both positive opponent-Continue mass
and positive successor debt. -/
theorem quittingDynamicDebtEdge_pos_propagates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (owner : ι) (hcurrent : 0 < current.2 owner) :
    0 < quittingDebtOpponentContinueMass current owner ∧
      0 < successor.2 owner := by
  have hupper := quittingDynamicDebtUpdate_le_mul reward current successor
    hedge.1 hsuccessor.2.1 owner
  rw [← hedge.2 owner] at hupper
  have hproduct : 0 <
      quittingDebtOpponentContinueMass current owner * successor.2 owner :=
    hcurrent.trans_le hupper
  have hmass0 := quittingDebtOpponentContinueMass_nonneg current owner
  have hnext0 := hsuccessor.2.1 owner
  exact ⟨pos_of_mul_pos_left hproduct hnext0,
    pos_of_mul_pos_right hproduct hmass0⟩

/-! ## Exact terminal-live stopping semantics -/

/-- When the exact debt is positive and every local Bellman residual
vanishes, its uniquely selected stopping alternative is to Continue at every
remaining live date and take the supplied terminal live value.  This is the
recursive, expectation-level form of the exact first-opponent identity. -/
theorem quittingFiniteTerminalNeverHazardValue_eq_prescribed_add_dynamicDebt_of_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (prescribed : ℕ → ℝ) (terminalDebt : ℝ)
    (bound : ℕ) (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots owner prescribed time = 0) :
    ∀ start fuel,
      start + fuel ≤ bound →
      0 < quittingFiniteDynamicDebt reward roots owner prescribed
          terminalDebt start fuel →
      quittingFiniteTerminalHazardValue reward roots owner
          (quittingPureTimeHazard none)
          (prescribed (start + fuel) + terminalDebt) start fuel =
        prescribed start +
          quittingFiniteDynamicDebt reward roots owner prescribed
            terminalDebt start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro _ _
      simp
  | succ fuel ih =>
      intro hwindow hpositive
      let quitValue :=
        quittingFixedOpponentsQuitValue reward roots owner start
      let continueBase :=
        quittingFixedOpponentsContinueReward reward roots owner start +
          quittingFixedOpponentsContinueMass roots owner start *
            prescribed (start + 1)
      let mass := quittingFixedOpponentsContinueMass roots owner start
      let nextDebt := quittingFiniteDynamicDebt reward roots owner prescribed
        terminalDebt (start + 1) fuel
      let augmented :=
        quittingFixedOpponentsContinueReward reward roots owner start +
          quittingFixedOpponentsContinueMass roots owner start *
            (prescribed (start + 1) + nextDebt)
      have hres := hresidual start (by omega)
      unfold quittingPrescribedOneStepResidual quittingLiveBellmanValue at hres
      change max quitValue continueBase - prescribed start = 0 at hres
      have hquit : quitValue ≤ prescribed start := by
        linarith [le_max_left quitValue continueBase]
      have hcontinue : continueBase ≤ prescribed start := by
        linarith [le_max_right quitValue continueBase]
      have haugmented : prescribed start < augmented := by
        by_contra hnot
        have haugmentedLe : augmented ≤
            prescribed start := le_of_not_gt hnot
        have hmaxLe : max quitValue augmented ≤
            prescribed start := max_le hquit haugmentedLe
        rw [quittingFiniteDynamicDebt_succ] at hpositive
        change 0 < max quitValue augmented -
          prescribed start at hpositive
        linarith
      have haugmentedEq : augmented = continueBase + mass * nextDebt := by
        dsimp only [augmented, continueBase, mass]
        ring
      have hproduct : 0 < mass * nextDebt := by
        have haugmented' := haugmented
        rw [haugmentedEq] at haugmented'
        linarith
      have hmass : 0 ≤ mass :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) owner (PMF.pure false))
      have hnext : 0 < nextDebt :=
        pos_of_mul_pos_right hproduct hmass
      have hchoose : quitValue ≤ augmented :=
        hquit.trans (le_of_lt haugmented)
      have htail := ih (start + 1) (by omega) hnext
      rw [quittingFiniteTerminalHazardValue]
      simp only [quittingPureTimeHazard_none, PMF.pure_apply,
        if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
        if_true, ENNReal.toReal_one, zero_mul, one_mul, zero_add]
      rw [show start + (fuel + 1) = start + 1 + fuel by omega, htail]
      rw [quittingFiniteDynamicDebt_succ]
      change augmented = prescribed start +
        (max quitValue augmented - prescribed start)
      rw [max_eq_right hchoose]
      ring

/-- Positive debt at one displayed time of an admissible finite chain
propagates to every later displayed time, including the terminal debt cap. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_pos_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (owner : ι) (start : ℕ)
    (hstart : 0 < quittingFiniteNashBellmanPathDynamicDebt
      reward cutoff path owner start) :
    ∀ time, start ≤ time → time ≤ cutoff →
      0 < quittingFiniteNashBellmanPathDynamicDebt
        reward cutoff path owner time := by
  intro time hstartTime htime
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hstartTime
  induction offset with
  | zero => simpa
  | succ offset ih =>
      have hprevious : start + offset ≤ cutoff := by omega
      have ih := ih (by omega) hprevious
      let time := start + offset
      have htimeLt : time < cutoff := by omega
      let current := quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path time
      let successor := quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path (time + 1)
      have hedge : IsQuittingDynamicDebtEdge reward current successor :=
        quittingFiniteNashBellmanPathDynamicDebtPoint_edge
          reward cutoff path hpath time htimeLt
      have hsuccessor : successor ∈ quittingDebtBox reward :=
        quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
          reward cutoff path hpath (time + 1)
      have hcurrentPoint : current.2 owner =
          quittingFiniteNashBellmanPathDynamicDebt
            reward cutoff path owner time := by
        simp [current, quittingFiniteNashBellmanPathDynamicDebtPoint,
          Nat.le_of_lt htimeLt]
      have hsuccessorPoint : successor.2 owner =
          quittingFiniteNashBellmanPathDynamicDebt
            reward cutoff path owner (time + 1) := by
        simp [successor, quittingFiniteNashBellmanPathDynamicDebtPoint,
          Nat.succ_le_iff.mpr htimeLt]
      have hpropagates := quittingDynamicDebtEdge_pos_propagates
        reward current successor hsuccessor hedge owner
          (by simpa [hcurrentPoint] using ih)
      simpa [hsuccessorPoint, time, Nat.add_assoc] using hpropagates.2

/-- Exact debt at an earlier displayed date is bounded by opponent survival
to a later date times the later debt.  This is the multiplicative link that
turns a last-edge product atom into a raw first-opponent atom measured from
the original root. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_le_survival_mul_later
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (owner : ι) (start later : ℕ)
    (hstartLater : start ≤ later) (hlater : later ≤ cutoff) :
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path owner start ≤
      quittingOpponentSurvivalWeight
          (quittingFiniteNashBellmanPathRoots cutoff path) owner start
          (later - start) *
        quittingFiniteNashBellmanPathDynamicDebt
          reward cutoff path owner later := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hstartLater
  simp only [Nat.add_sub_cancel_left]
  induction offset with
  | zero =>
      simp [quittingOpponentSurvivalWeight]
  | succ offset ih =>
      have hprevious : start + offset ≤ cutoff := by omega
      have ih := ih (by omega) hprevious
      let time := start + offset
      let current := quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path time
      let successor := quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path (time + 1)
      have htime : time < cutoff := by omega
      have hedge : IsQuittingDynamicDebtEdge reward current successor :=
        quittingFiniteNashBellmanPathDynamicDebtPoint_edge
          reward cutoff path hpath time htime
      have hsuccessor : successor ∈ quittingDebtBox reward :=
        quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
          reward cutoff path hpath (time + 1)
      have hstep := quittingDynamicDebtUpdate_le_mul reward current successor
        hedge.1 hsuccessor.2.1 owner
      rw [← hedge.2 owner] at hstep
      have hcurrentPoint : current.2 owner =
          quittingFiniteNashBellmanPathDynamicDebt
            reward cutoff path owner time := by
        simp [current, quittingFiniteNashBellmanPathDynamicDebtPoint,
          Nat.le_of_lt htime]
      have hsuccessorPoint : successor.2 owner =
          quittingFiniteNashBellmanPathDynamicDebt
            reward cutoff path owner (time + 1) := by
        simp [successor, quittingFiniteNashBellmanPathDynamicDebtPoint,
          Nat.succ_le_iff.mpr htime]
      have hroot : quittingRootOfSimplex current.1.2 =
          quittingFiniteNashBellmanPathRoots cutoff path time := by
        simp [current, quittingFiniteNashBellmanPathDynamicDebtPoint,
          quittingFiniteNashBellmanPathRoots, Nat.le_of_lt htime, htime]
      have hmass : quittingDebtOpponentContinueMass current owner =
          quittingFixedOpponentsContinueMass
            (quittingFiniteNashBellmanPathRoots cutoff path) owner time := by
        rw [quittingDebtOpponentContinueMass_eq_stationary]
        rw [hroot]
        rfl
      rw [hcurrentPoint, hsuccessorPoint, hmass] at hstep
      have hsurvival : 0 ≤ quittingOpponentSurvivalWeight
          (quittingFiniteNashBellmanPathRoots cutoff path) owner start offset :=
        quittingOpponentSurvivalWeight_nonneg _ owner start offset
      calc
        quittingFiniteNashBellmanPathDynamicDebt
            reward cutoff path owner start ≤
          quittingOpponentSurvivalWeight
              (quittingFiniteNashBellmanPathRoots cutoff path) owner start
              offset *
            quittingFiniteNashBellmanPathDynamicDebt
              reward cutoff path owner time := by
                simpa [time] using ih
        _ ≤ quittingOpponentSurvivalWeight
              (quittingFiniteNashBellmanPathRoots cutoff path) owner start
              offset *
            (quittingFixedOpponentsContinueMass
                (quittingFiniteNashBellmanPathRoots cutoff path) owner time *
              quittingFiniteNashBellmanPathDynamicDebt
                reward cutoff path owner (time + 1)) :=
          mul_le_mul_of_nonneg_left hstep hsurvival
        _ = quittingOpponentSurvivalWeight
              (quittingFiniteNashBellmanPathRoots cutoff path) owner start
              (offset + 1) *
            quittingFiniteNashBellmanPathDynamicDebt
              reward cutoff path owner (start + (offset + 1)) := by
          rw [quittingOpponentSurvivalWeight_succ]
          simp only [time]
          ring_nf

/-- Positive debt at any live date implies a strictly positive singleton
quitting reward for the same owner. -/
theorem positiveSingletonReward_of_finiteDynamicDebt_pos_at
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (owner : ι) (start : ℕ) (hstart : start ≤ cutoff) (hpositive :
      0 < quittingFiniteNashBellmanPathDynamicDebt
        reward cutoff path owner start) :
    0 < reward (quittingSingletonTerminal owner) owner := by
  have hterminal := quittingFiniteNashBellmanPathDynamicDebt_pos_of_le
    reward cutoff path hpath owner start hpositive cutoff hstart le_rfl
  unfold quittingFiniteNashBellmanPathDynamicDebt at hterminal
  simp only [Nat.sub_self, quittingFiniteDynamicDebt_zero] at hterminal
  unfold quittingPositiveSingletonDebtCap at hterminal
  by_cases hreward : reward (quittingSingletonTerminal owner) owner ≤ 0
  · rw [max_eq_left hreward] at hterminal
    exact (lt_irrefl 0 hterminal).elim
  · exact lt_of_not_ge hreward

/-- Root specialization of
`positiveSingletonReward_of_finiteDynamicDebt_pos_at`. -/
theorem positiveSingletonReward_of_finiteDynamicDebt_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (owner : ι) (hpositive :
      0 < quittingFiniteNashBellmanPathDynamicDebt
        reward cutoff path owner 0) :
    0 < reward (quittingSingletonTerminal owner) owner :=
  positiveSingletonReward_of_finiteDynamicDebt_pos_at
    reward cutoff path hpath owner 0 (Nat.zero_le cutoff) hpositive

/-- **Positive-debt terminal-solo provenance.**  The probability that every
opponent continues from `start` to the zero boundary is at least current
exact debt divided by the owner's positive singleton reward.  This is the
quantitative terminal atom of the first-opponent identity; it uses no atom
selection and has no dependence on the number of players. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_div_singleton_le_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (owner : ι) (start : ℕ) (hstart : start ≤ cutoff)
    (hpositive : 0 < quittingFiniteNashBellmanPathDynamicDebt
      reward cutoff path owner start) :
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path owner start /
        reward (quittingSingletonTerminal owner) owner ≤
      quittingOpponentSurvivalWeight
        (quittingFiniteNashBellmanPathRoots cutoff path) owner start
          (cutoff - start) := by
  let roots := quittingFiniteNashBellmanPathRoots cutoff path
  let prescribed := fun liveTime ↦
    quittingFiniteNashBellmanPathValue cutoff path liveTime owner
  let singleton := reward (quittingSingletonTerminal owner) owner
  let cap := quittingPositiveSingletonDebtCap reward owner
  have hsingleton : 0 < singleton := by
    exact positiveSingletonReward_of_finiteDynamicDebt_pos_at
      reward cutoff path hpath owner start hstart hpositive
  have hcap : cap = singleton := by
    exact max_eq_right (le_of_lt hsingleton)
  have hraw := quittingFiniteDynamicDebt_le_survival_mul_terminalDebt_on
    reward roots owner prescribed
      (isQuittingLivePrescribedValue_finiteNashBellmanPath
        reward cutoff path hpath owner)
      (show 0 ≤ cap from le_max_left _ _) cutoff
      (fun liveTime hliveTime ↦
        quittingPrescribedOneStepResidual_finiteNashBellmanPath_eq_zero
          reward cutoff path hpath owner liveTime hliveTime)
      start (cutoff - start) (by omega)
  change quittingFiniteNashBellmanPathDynamicDebt
      reward cutoff path owner start ≤
    quittingOpponentSurvivalWeight roots owner start (cutoff - start) * cap
      at hraw
  rw [hcap] at hraw
  exact (div_le_iff₀ hsingleton).2 hraw

/-- Positive exact debt therefore gives strictly positive terminal-live
mass for the owner's deterministic terminal-solo witness. -/
theorem quittingOpponentSurvivalWeight_pos_of_finiteDynamicDebt_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (owner : ι) (start : ℕ) (hstart : start ≤ cutoff)
    (hpositive : 0 < quittingFiniteNashBellmanPathDynamicDebt
      reward cutoff path owner start) :
    0 < quittingOpponentSurvivalWeight
      (quittingFiniteNashBellmanPathRoots cutoff path) owner start
        (cutoff - start) := by
  have hsingleton := positiveSingletonReward_of_finiteDynamicDebt_pos_at
    reward cutoff path hpath owner start hstart hpositive
  have hlower :=
    quittingFiniteNashBellmanPathDynamicDebt_div_singleton_le_survival
      reward cutoff path hpath owner start hstart hpositive
  have hratio : 0 <
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff path owner start /
        reward (quittingSingletonTerminal owner) owner :=
    div_pos hpositive hsingleton
  exact hratio.trans_le hlower

/-- On a zero-boundary Nash--Bellman chain, positive exact debt is attained
by the concrete deviation that Continues throughout and takes the singleton
terminal option if every opponent has also continued. -/
theorem quittingFiniteNashBellmanPath_neverHazardValue_eq_value_add_dynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (owner : ι) (start : ℕ) (hstart : start ≤ cutoff)
    (hpositive : 0 < quittingFiniteNashBellmanPathDynamicDebt
      reward cutoff path owner start) :
    quittingFiniteTerminalHazardValue reward
        (quittingFiniteNashBellmanPathRoots cutoff path) owner
        (quittingPureTimeHazard none)
        (quittingPositiveSingletonDebtCap reward owner)
        start (cutoff - start) =
      quittingFiniteNashBellmanPathValue cutoff path start owner +
        quittingFiniteNashBellmanPathDynamicDebt
          reward cutoff path owner start := by
  let roots := quittingFiniteNashBellmanPathRoots cutoff path
  let prescribed := fun liveTime ↦
    quittingFiniteNashBellmanPathValue cutoff path liveTime owner
  let cap := quittingPositiveSingletonDebtCap reward owner
  have hexact :=
    quittingFiniteTerminalNeverHazardValue_eq_prescribed_add_dynamicDebt_of_pos
      reward roots owner prescribed cap
      cutoff (fun liveTime hliveTime ↦
        quittingPrescribedOneStepResidual_finiteNashBellmanPath_eq_zero
          reward cutoff path hpath owner liveTime hliveTime)
      start (cutoff - start) (by omega) hpositive
  have hterminal : prescribed (start + (cutoff - start)) = 0 := by
    rw [Nat.add_sub_of_le hstart]
    exact congrFun
      (quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
        reward cutoff path hpath) owner
  rw [hterminal, zero_add] at hexact
  exact hexact

/-! ## A one-stage full-set terminal advantage -/

/-- Against an opponent action, compare continuing with the singleton
terminal option to joining the same simultaneous quitter set.  The action is
sampled with the owner forced to Continue. -/
def quittingTerminalOpponentAdvantage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (action : ι → Bool) : ℝ :=
  quittingRootPayoff reward
      (fun _ ↦ reward (quittingSingletonTerminal owner) owner)
      action owner -
    quittingRootPayoff reward (0 : Payoff ι)
      (Function.update action owner true) owner

/-- The expectation of the full-set advantage is exactly the augmented
Continue endpoint minus the Quit endpoint. -/
theorem expect_terminalOpponentAdvantage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) :
    expect (pmfPi (Function.update root owner (PMF.pure false)))
        (quittingTerminalOpponentAdvantage reward owner) =
      quittingRootContinuePayoff reward
          (fun _ ↦ reward (quittingSingletonTerminal owner) owner)
          root owner -
        quittingRootQuitPayoff reward (0 : Payoff ι) root owner := by
  unfold quittingTerminalOpponentAdvantage quittingRootContinuePayoff
    quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_sub]
  congr 1
  have hpure := KernelGame.expect_pmfPi_update_pure
    (Function.update root owner (PMF.pure false)) owner true
    (fun action ↦ quittingRootPayoff reward (0 : Payoff ι) action owner)
  simpa using hpure.symm

/-- Updating a forced-continuing owner's action to Quit inserts exactly that
owner into the full simultaneous quitter set. -/
theorem quittingQuitters_update_true_of_apply_false
    (action : ι → Bool) (owner : ι) :
    quittingQuitters (Function.update action owner true) =
      insert owner (quittingQuitters action) := by
  ext player
  by_cases hplayer : player = owner
  · subst player
    simp [quittingQuitters]
  · simp [quittingQuitters, hplayer]

/-- A positive expected full-set advantage contains a genuine positive-mass
action with positive advantage. -/
theorem exists_terminalOpponentAdvantage_atom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hpositive : 0 <
      quittingRootContinuePayoff reward
          (fun _ ↦ reward (quittingSingletonTerminal owner) owner)
          root owner -
        quittingRootQuitPayoff reward (0 : Payoff ι) root owner) :
    ∃ action : ι → Bool,
      0 < ((pmfPi (Function.update root owner (PMF.pure false))) action).toReal ∧
      0 < quittingTerminalOpponentAdvantage reward owner action := by
  let distribution :=
    pmfPi (Function.update root owner (PMF.pure false))
  have hexpect :
      0 < expect distribution
        (quittingTerminalOpponentAdvantage reward owner) := by
    rw [expect_terminalOpponentAdvantage]
    exact hpositive
  rw [expect_eq_sum] at hexpect
  by_contra hno
  push Not at hno
  have hsumNonpos :
      (∑ action : ι → Bool,
        (distribution action).toReal *
          quittingTerminalOpponentAdvantage reward owner action) ≤ 0 := by
    apply Finset.sum_nonpos
    intro action _
    by_cases hmass : (distribution action).toReal = 0
    · simp [hmass]
    · have hmassPos : 0 < (distribution action).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hmass)
      have hadvantage := hno action hmassPos
      exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
        hadvantage
  exact (not_lt_of_ge hsumNonpos hexpect)

/-! ## Quantitative residual-depth-one packet -/

/-- At a one-step zero boundary, positive exact debt is bounded by the
expected full-set advantage of continuing against the realized opponent set
rather than joining it. -/
theorem quittingFiniteDynamicDebt_one_le_expect_terminalOpponentAdvantage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (prescribed : ℕ → ℝ) (start : ℕ)
    (hterminal : prescribed (start + 1) = 0)
    (hresidual : quittingPrescribedOneStepResidual
      reward roots owner prescribed start = 0)
    (hpositive : 0 < quittingFiniteDynamicDebt reward roots owner prescribed
      (reward (quittingSingletonTerminal owner) owner) start 1) :
    quittingFiniteDynamicDebt reward roots owner prescribed
        (reward (quittingSingletonTerminal owner) owner) start 1 ≤
      expect (pmfPi (Function.update (roots start) owner (PMF.pure false)))
        (quittingTerminalOpponentAdvantage reward owner) := by
  let quitValue := quittingFixedOpponentsQuitValue reward roots owner start
  let continueReward :=
    quittingFixedOpponentsContinueReward reward roots owner start
  let mass := quittingFixedOpponentsContinueMass roots owner start
  let singleton := reward (quittingSingletonTerminal owner) owner
  let augmented := continueReward + mass * singleton
  have hres := hresidual
  unfold quittingPrescribedOneStepResidual quittingLiveBellmanValue at hres
  rw [hterminal, mul_zero, add_zero] at hres
  change max quitValue continueReward - prescribed start = 0 at hres
  have hquit : quitValue ≤ prescribed start := by
    linarith [le_max_left quitValue continueReward]
  have haugmented : prescribed start < augmented := by
    by_contra hnot
    have haugmentedLe : augmented ≤ prescribed start := le_of_not_gt hnot
    rw [quittingFiniteDynamicDebt_succ] at hpositive
    simp only [quittingFiniteDynamicDebt_zero, hterminal, zero_add]
      at hpositive
    change 0 < max quitValue augmented - prescribed start at hpositive
    have := max_le hquit haugmentedLe
    linarith
  have hchoose : quitValue ≤ augmented :=
    hquit.trans (le_of_lt haugmented)
  rw [quittingFiniteDynamicDebt_succ]
  simp only [quittingFiniteDynamicDebt_zero, hterminal, zero_add]
  change max quitValue augmented - prescribed start ≤ _
  rw [max_eq_right hchoose, expect_terminalOpponentAdvantage]
  rw [quittingRootContinuePayoff_eq_fixedOpponents
      reward roots owner (fun _ ↦ singleton) start,
    quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward roots owner (0 : Payoff ι) start]
  change augmented - prescribed start ≤
    continueReward + mass * singleton - quitValue
  linarith

/-- Finite pigeonhole form of the depth-one packet.  The selected object is
one complete product action, so its simultaneous quitter set is retained
without singletonization.  No player in that set is promoted to a new debt
owner. -/
theorem exists_terminalOpponentAdvantage_atom_quantitative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) (debt : ℝ)
    (hdebt : debt ≤
      expect (pmfPi (Function.update root owner (PMF.pure false)))
        (quittingTerminalOpponentAdvantage reward owner)) :
    ∃ action : ι → Bool,
      debt ≤ (Fintype.card (ι → Bool) : ℝ) *
        ((pmfPi (Function.update root owner (PMF.pure false))) action).toReal *
          quittingTerminalOpponentAdvantage reward owner action := by
  let distribution := pmfPi (Function.update root owner (PMF.pure false))
  let contribution := fun action : ι → Bool ↦
    (distribution action).toReal *
      quittingTerminalOpponentAdvantage reward owner action
  have huniv : (Finset.univ : Finset (ι → Bool)).Nonempty :=
    Finset.univ_nonempty
  obtain ⟨action, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (ι → Bool)) contribution huniv
  refine ⟨action, hdebt.trans ?_⟩
  rw [expect_eq_sum]
  change (∑ other : ι → Bool, contribution other) ≤ _
  have hsum := Finset.sum_le_card_nsmul
    (Finset.univ : Finset (ι → Bool)) contribution
      (contribution action) (fun other _ ↦ hmax other (Finset.mem_univ other))
  simpa [nsmul_eq_mul, contribution, distribution, mul_assoc] using hsum

/-- A full-set terminal advantage is at most twice the canonical reward
bound.  This estimate does not replace the simultaneous set by singleton
outcomes. -/
theorem quittingTerminalOpponentAdvantage_le_two_mul_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (action : ι → Bool) :
    quittingTerminalOpponentAdvantage reward owner action ≤
      2 * quittingRewardBound reward := by
  let singleton := reward (quittingSingletonTerminal owner) owner
  let before := quittingRootPayoff reward (fun _ ↦ singleton) action owner
  let after := quittingRootPayoff reward (0 : Payoff ι)
    (Function.update action owner true) owner
  have hsingleton : |singleton| ≤ quittingRewardBound reward :=
    abs_reward_le_quittingRewardBound reward
      (quittingSingletonTerminal owner) owner
  have hbefore : |before| ≤ quittingRewardBound reward := by
    exact abs_quittingRootPayoff_le reward (fun _ ↦ singleton)
      (abs_reward_le_quittingRewardBound reward) (fun _ ↦ hsingleton)
      action owner
  have hafter : |after| ≤ quittingRewardBound reward := by
    exact abs_quittingRootPayoff_le reward (0 : Payoff ι)
      (abs_reward_le_quittingRewardBound reward)
      (fun _ ↦ by simpa using quittingRewardBound_nonneg reward)
      (Function.update action owner true) owner
  unfold quittingTerminalOpponentAdvantage
  change before - after ≤ 2 * quittingRewardBound reward
  calc
    before - after ≤ |before - after| := le_abs_self _
    _ ≤ |before| + |after| := abs_sub _ _
    _ ≤ quittingRewardBound reward + quittingRewardBound reward :=
      add_le_add hbefore hafter
    _ = 2 * quittingRewardBound reward := by ring

/-- Quantitative full-action pigeonhole packet.  Positive expected debt
selects one genuine product action with positive raw mass and positive owner
advantage.  Its weighted advantage carries at least a `1 / card` share of
the debt, and its raw mass satisfies the corresponding `2M` estimate. -/
theorem exists_terminalOpponentAdvantage_atom_quantitative_of_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) (debt : ℝ)
    (hpositive : 0 < debt)
    (hdebt : debt ≤
      expect (pmfPi (Function.update root owner (PMF.pure false)))
        (quittingTerminalOpponentAdvantage reward owner)) :
    ∃ action : ι → Bool,
      0 < ((pmfPi (Function.update root owner (PMF.pure false))) action).toReal ∧
      0 < quittingTerminalOpponentAdvantage reward owner action ∧
      debt ≤ (Fintype.card (ι → Bool) : ℝ) *
        ((pmfPi (Function.update root owner (PMF.pure false))) action).toReal *
          quittingTerminalOpponentAdvantage reward owner action ∧
      debt ≤ 2 * quittingRewardBound reward *
        (Fintype.card (ι → Bool) : ℝ) *
          ((pmfPi (Function.update root owner (PMF.pure false))) action).toReal := by
  obtain ⟨action, hweighted⟩ :=
    exists_terminalOpponentAdvantage_atom_quantitative
      reward root owner debt hdebt
  let mass :=
    ((pmfPi (Function.update root owner (PMF.pure false))) action).toReal
  let advantage := quittingTerminalOpponentAdvantage reward owner action
  let card := (Fintype.card (ι → Bool) : ℝ)
  have hcard : 0 < card := by positivity
  have hmass0 : 0 ≤ mass := ENNReal.toReal_nonneg
  have hproduct : 0 < card * mass * advantage :=
    hpositive.trans_le hweighted
  have hcardMass0 : 0 ≤ card * mass :=
    mul_nonneg (le_of_lt hcard) hmass0
  have hadvantage : 0 < advantage :=
    pos_of_mul_pos_right hproduct hcardMass0
  have hcardMass : 0 < card * mass :=
    pos_of_mul_pos_left hproduct (le_of_lt hadvantage)
  have hmass : 0 < mass :=
    pos_of_mul_pos_right hcardMass (le_of_lt hcard)
  have hadvantageBound : advantage ≤ 2 * quittingRewardBound reward :=
    quittingTerminalOpponentAdvantage_le_two_mul_rewardBound
      reward owner action
  have hraw : debt ≤ 2 * quittingRewardBound reward * card * mass := by
    calc
      debt ≤ card * mass * advantage := hweighted
      _ ≤ card * mass * (2 * quittingRewardBound reward) :=
        mul_le_mul_of_nonneg_left hadvantageBound hcardMass0
      _ = 2 * quittingRewardBound reward * card * mass := by ring
  exact ⟨action, hmass, hadvantage, hweighted, hraw⟩

/-- **Residual-depth-one first-opponent packet.**  Positive initial exact
debt on a chain of horizon `last + 1` selects one complete action at the last
live root.  After multiplying by opponent survival from the original root,
the resulting raw first-opponent atom carries a linear (not quadratic) share
of the initial debt.  The conclusion keeps the complete simultaneous action
and makes no new-owner claim. -/
theorem exists_finiteDynamicDebt_lastAtom_quantitative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) (path : QuittingFiniteNashBellmanPath ι (last + 1))
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (last + 1))
    (owner : ι)
    (hpositive : 0 < quittingFiniteNashBellmanPathDynamicDebt
      reward (last + 1) path owner 0) :
    ∃ action : ι → Bool,
      let survival := quittingOpponentSurvivalWeight
        (quittingFiniteNashBellmanPathRoots (last + 1) path) owner 0 last
      let mass := ((pmfPi (Function.update
        (quittingFiniteNashBellmanPathRoots (last + 1) path last)
          owner (PMF.pure false))) action).toReal
      let advantage := quittingTerminalOpponentAdvantage reward owner action
      0 < survival * mass ∧
      0 < advantage ∧
      quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) path owner 0 ≤
        (Fintype.card (ι → Bool) : ℝ) * (survival * mass) * advantage ∧
      quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) path owner 0 ≤
        2 * quittingRewardBound reward *
          (Fintype.card (ι → Bool) : ℝ) * (survival * mass) := by
  let roots := quittingFiniteNashBellmanPathRoots (last + 1) path
  let prescribed := fun liveTime ↦
    quittingFiniteNashBellmanPathValue (last + 1) path liveTime owner
  let singleton := reward (quittingSingletonTerminal owner) owner
  have hlastPositive := quittingFiniteNashBellmanPathDynamicDebt_pos_of_le
    reward (last + 1) path hpath owner 0 hpositive last (by omega) (by omega)
  have hsingleton : 0 < singleton :=
    positiveSingletonReward_of_finiteDynamicDebt_pos_at
      reward (last + 1) path hpath owner last (by omega) hlastPositive
  have hcap : quittingPositiveSingletonDebtCap reward owner = singleton := by
    exact max_eq_right (le_of_lt hsingleton)
  have hterminal : prescribed (last + 1) = 0 := by
    exact congrFun
      (quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
        reward (last + 1) path hpath) owner
  have hresidual : quittingPrescribedOneStepResidual
      reward roots owner prescribed last = 0 := by
    exact quittingPrescribedOneStepResidual_finiteNashBellmanPath_eq_zero
      reward (last + 1) path hpath owner last (by omega)
  have hlastDebtEq :
      quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) path owner last =
        quittingFiniteDynamicDebt reward roots owner prescribed singleton
          last 1 := by
    unfold quittingFiniteNashBellmanPathDynamicDebt
    rw [hcap]
    congr 1
    omega
  have hlastExpectation :
      quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) path owner last ≤
        expect (pmfPi (Function.update (roots last) owner (PMF.pure false)))
          (quittingTerminalOpponentAdvantage reward owner) := by
    rw [hlastDebtEq]
    exact quittingFiniteDynamicDebt_one_le_expect_terminalOpponentAdvantage
      reward roots owner prescribed last hterminal hresidual
        (by simpa [hlastDebtEq] using hlastPositive)
  obtain ⟨action, hmass, hadvantage, hlastWeighted, hlastRaw⟩ :=
    exists_terminalOpponentAdvantage_atom_quantitative_of_pos
      reward (roots last) owner
        (quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) path owner last)
        hlastPositive hlastExpectation
  let survival := quittingOpponentSurvivalWeight roots owner 0 last
  let mass := ((pmfPi (Function.update (roots last) owner
    (PMF.pure false))) action).toReal
  let advantage := quittingTerminalOpponentAdvantage reward owner action
  have hprefixLink :=
    quittingFiniteNashBellmanPathDynamicDebt_le_survival_mul_later
      reward (last + 1) path hpath owner 0 last (by omega) (by omega)
  change quittingFiniteNashBellmanPathDynamicDebt
      reward (last + 1) path owner 0 ≤
    survival * quittingFiniteNashBellmanPathDynamicDebt
      reward (last + 1) path owner last at hprefixLink
  have hlast0 := quittingFiniteNashBellmanPathDynamicDebt_nonneg
    reward (last + 1) path hpath owner last
  have hsurvivalProduct : 0 < survival *
      quittingFiniteNashBellmanPathDynamicDebt
        reward (last + 1) path owner last :=
    hpositive.trans_le hprefixLink
  have hsurvival : 0 < survival :=
    pos_of_mul_pos_left hsurvivalProduct hlast0
  have hscaledWeighted := mul_le_mul_of_nonneg_left hlastWeighted
    (le_of_lt hsurvival)
  have hscaledRaw := mul_le_mul_of_nonneg_left hlastRaw
    (le_of_lt hsurvival)
  refine ⟨action, ?_, hadvantage, ?_, ?_⟩
  · exact mul_pos hsurvival hmass
  · calc
      quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) path owner 0 ≤
        survival * quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) path owner last := hprefixLink
      _ ≤ survival * ((Fintype.card (ι → Bool) : ℝ) * mass *
          advantage) := hscaledWeighted
      _ = (Fintype.card (ι → Bool) : ℝ) * (survival * mass) *
          advantage := by ring
  · calc
      quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) path owner 0 ≤
        survival * quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) path owner last := hprefixLink
      _ ≤ survival * (2 * quittingRewardBound reward *
          (Fintype.card (ι → Bool) : ℝ) * mass) := hscaledRaw
      _ = 2 * quittingRewardBound reward *
          (Fintype.card (ι → Bool) : ℝ) * (survival * mass) := by ring

end GameTheory
