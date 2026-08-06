/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingTargetAnchoredTail
import GameTheory.Concepts.Stochastic.QuittingCertifiedBoundaryReinsertion
import GameTheory.Concepts.Stochastic.QuittingPhaseSwitchProfile
import GameTheory.Concepts.Stochastic.QuittingJointComplementarity

/-!
# Diagonal target-tail reinsertion

This module supplies the semantic and finite-recursion layer of the
player-indexed tail construction.

For every player, retain that player's own payoff from its designated suffix
as one coordinate of a diagonal endpoint.  A finite exact Nash--Bellman prefix
may then be evaluated against an actual suffix rather than a synthetic zero
boundary.  The lemmas below identify the phase-switch payoff with the finite
terminal-boundary recursion, prove exact finite-prefix optimality, and show
how an endpoint mismatch is weighted by survival.

Target closure, exceptional-coordinate selection, and the game-facing
compiler are separated into downstream modules.  No compact-minimizer or
continuity claim over varying anchors is used here.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Closed-tail families and their diagonal endpoint -/

/-- The payoff vector retaining, in coordinate `target`, only that target's
own payoff in its designated suffix. -/
def quittingDiagonalTailEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ι → ℕ → ι → PMF Bool) : Payoff ι :=
  fun target =>
    quittingRootSequenceTerminalValue reward (tail target) target 0

/-- Every diagonal suffix endpoint lies in the canonical reward cube. -/
theorem abs_quittingDiagonalTailEndpoint_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ι → ℕ → ι → PMF Bool) (target : ι) :
    |quittingDiagonalTailEndpoint reward tail target| ≤
      quittingRewardBound reward := by
  exact abs_quittingRootSequenceTerminalValue_le reward (tail target) target 0
    (quittingRewardBound_nonneg reward)
    (abs_reward_le_quittingRewardBound reward)

/-! ## Stationary-cap diagonal endpoints -/

/-- Choose one constant opponent row per player and retain each player's exact
stationary unilateral cap in that player's coordinate. -/
def quittingStationaryCapDiagonalEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (rows : ι → ι → PMF Bool) : Payoff ι :=
  fun target => quittingStationaryUnilateralCap reward (rows target) target

/-- The stationary-cap diagonal endpoint lies in the canonical reward cube.
This uses actual cap attainment rather than continuity of the ratio formula. -/
theorem abs_quittingStationaryCapDiagonalEndpoint_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (rows : ι → ι → PMF Bool) (target : ι) :
    |quittingStationaryCapDiagonalEndpoint reward rows target| ≤
      quittingRewardBound reward := by
  exact abs_quittingStationaryUnilateralCap_le_of_bound
    reward (rows target) target (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)

/-! ## Finite semantic adapters for a prefix and an actual suffix -/

/-- Replacing a root sequence's own coordinate by a supplied hazard and then
using that updated coordinate as the finite hazard is semantically invisible:
the fixed-opponent coefficients ignore the overwritten coordinate. -/
theorem quittingFiniteTerminalHazardValue_rootSequenceUpdate_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (terminalValue : ℝ) :
    ∀ start fuel,
      quittingFiniteTerminalHazardValue reward
          (quittingRootSequenceUpdate roots who hazard) who
          (fun time =>
            quittingRootSequenceUpdate roots who hazard time who)
          terminalValue start fuel =
        quittingFiniteTerminalHazardValue reward roots who hazard
          terminalValue start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [quittingFiniteTerminalHazardValue,
        quittingFiniteTerminalHazardValue, ih (start + 1)]
      simp only [quittingRootSequenceUpdate, Function.update_self]
      unfold quittingFixedOpponentsQuitValue
        quittingFixedOpponentsContinueReward
        quittingFixedOpponentsContinueMass
      simp [quittingRootSequenceUpdate]

/-- Inside the plan window, phase-switch roots give the same finite hazard
value as the plan itself. -/
theorem quittingFiniteTerminalHazardValue_phaseSwitch_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan tail : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    (hazard : ℕ → PMF Bool) (terminalValue : ℝ) :
    ∀ start fuel, start + fuel ≤ switch →
      quittingFiniteTerminalHazardValue reward
          (quittingPhaseSwitchRoots plan tail switch) who hazard
          terminalValue start fuel =
        quittingFiniteTerminalHazardValue reward plan who hazard
          terminalValue start fuel := by
  intro start fuel hwindow
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      have hstart : start < switch := by omega
      have htail : start + 1 + fuel ≤ switch := by omega
      rw [quittingFiniteTerminalHazardValue,
        quittingFiniteTerminalHazardValue,
        ih (start + 1) htail]
      unfold quittingFixedOpponentsQuitValue
        quittingFixedOpponentsContinueReward
        quittingFixedOpponentsContinueMass
      rw [quittingPhaseSwitchRoots_of_lt plan tail hstart]

/-- Following the phase-switch profile itself through its plan window is the
same finite recursion as following the plan's own marginals. -/
theorem quittingFiniteTerminalHazardValue_phaseSwitch_self_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan tail : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    (terminalValue : ℝ) :
    ∀ start fuel, start + fuel ≤ switch →
      quittingFiniteTerminalHazardValue reward
          (quittingPhaseSwitchRoots plan tail switch) who
          (fun time => quittingPhaseSwitchRoots plan tail switch time who)
          terminalValue start fuel =
        quittingFiniteTerminalHazardValue reward plan who
          (fun time => plan time who) terminalValue start fuel := by
  intro start fuel hwindow
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      have hstart : start < switch := by omega
      have htail : start + 1 + fuel ≤ switch := by omega
      rw [quittingFiniteTerminalHazardValue,
        quittingFiniteTerminalHazardValue,
        quittingPhaseSwitchRoots_of_lt plan tail hstart,
        ih (start + 1) htail]
      unfold quittingFixedOpponentsQuitValue
        quittingFixedOpponentsContinueReward
        quittingFixedOpponentsContinueMass
      rw [quittingPhaseSwitchRoots_of_lt plan tail hstart]

/-- An arbitrary unilateral hazard against a phase switch is exactly the
finite plan-prefix hazard recursion with boundary equal to that hazard's
actual suffix payoff. -/
theorem quittingRootSequenceHazardTerminalValue_phaseSwitch_eq_finite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan tail : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingPhaseSwitchRoots plan tail switch) who hazard 0 =
      quittingFiniteTerminalHazardValue reward plan who hazard
        (quittingRootSequenceHazardTerminalValue reward tail who
          (fun offset => hazard (switch + offset)) 0)
        0 switch := by
  let phase := quittingPhaseSwitchRoots plan tail switch
  let updated := quittingRootSequenceUpdate phase who hazard
  let prescribed : ℕ → ℝ := fun time =>
    quittingRootSequenceTerminalValue reward updated who time
  have heval := quittingFiniteTerminalHazardValue_self_eq_prescribed
    reward updated who prescribed
      (fun time =>
        quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff
          reward updated who time) 0 switch
  simp only [Nat.zero_add] at heval
  have hboundary :=
    quittingRootSequenceTerminalValue_update_quittingPhaseSwitchRoots_switch
      reward plan tail switch who hazard
  calc
    quittingRootSequenceHazardTerminalValue reward phase who hazard 0 =
        prescribed 0 := rfl
    _ = quittingFiniteTerminalHazardValue reward updated who
          (fun time => updated time who) (prescribed switch) 0 switch :=
      heval.symm
    _ = quittingFiniteTerminalHazardValue reward phase who hazard
          (prescribed switch) 0 switch :=
      quittingFiniteTerminalHazardValue_rootSequenceUpdate_self
        reward phase who hazard (prescribed switch) 0 switch
    _ = quittingFiniteTerminalHazardValue reward plan who hazard
          (prescribed switch) 0 switch :=
      quittingFiniteTerminalHazardValue_phaseSwitch_prefix
        reward plan tail switch who hazard (prescribed switch) 0 switch
          (by omega)
    _ = quittingFiniteTerminalHazardValue reward plan who hazard
          (quittingRootSequenceHazardTerminalValue reward tail who
            (fun offset => hazard (switch + offset)) 0) 0 switch := by
      rw [show prescribed switch =
          quittingRootSequenceTerminalValue reward updated who switch from rfl,
        hboundary]

/-- The prescribed phase-switch payoff is the finite plan-prefix policy
recursion with boundary equal to the suffix's prescribed payoff. -/
theorem quittingRootSequenceTerminalValue_phaseSwitch_eq_finite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan tail : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι) :
    quittingRootSequenceTerminalValue reward
        (quittingPhaseSwitchRoots plan tail switch) who 0 =
      quittingFiniteTerminalHazardValue reward plan who
        (fun time => plan time who)
        (quittingRootSequenceTerminalValue reward tail who 0)
        0 switch := by
  let phase := quittingPhaseSwitchRoots plan tail switch
  let prescribed : ℕ → ℝ := fun time =>
    quittingRootSequenceTerminalValue reward phase who time
  have heval := quittingFiniteTerminalHazardValue_self_eq_prescribed
    reward phase who prescribed
      (fun time =>
        quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff
          reward phase who time) 0 switch
  simp only [Nat.zero_add] at heval
  have hboundary :=
    quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots_switch
      reward plan tail switch who
  calc
    quittingRootSequenceTerminalValue reward phase who 0 = prescribed 0 := rfl
    _ = quittingFiniteTerminalHazardValue reward phase who
          (fun time => phase time who) (prescribed switch) 0 switch :=
      heval.symm
    _ = quittingFiniteTerminalHazardValue reward plan who
          (fun time => plan time who) (prescribed switch) 0 switch :=
      quittingFiniteTerminalHazardValue_phaseSwitch_self_prefix
        reward plan tail switch who (prescribed switch) 0 switch (by omega)
    _ = quittingFiniteTerminalHazardValue reward plan who
          (fun time => plan time who)
          (quittingRootSequenceTerminalValue reward tail who 0) 0 switch := by
      rw [show prescribed switch =
          quittingRootSequenceTerminalValue reward phase who switch from rfl,
        hboundary]

/-! ## Exact finite-prefix optimality -/

/-- Exact one-root Nash together with policy evaluation bounds both pure
unilateral endpoints by the displayed current value. -/
theorem quittingFinitePrefix_endpointBounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (time : ℕ)
    (hpolicy : value time = quittingRootSuccessorPayoff reward
      (value (time + 1)) (roots time))
    (hnash : IsεQuittingRootNash reward (value (time + 1)) 0
      (roots time)) :
    quittingFixedOpponentsQuitValue reward roots who time ≤ value time who ∧
      quittingFixedOpponentsContinueReward reward roots who time +
          quittingFixedOpponentsContinueMass roots who time *
            value (time + 1) who ≤
        value time who := by
  have hcurrent := congrFun hpolicy who
  have hquitNash := hnash who (PMF.pure true)
  have hcontinueNash := hnash who (PMF.pure false)
  constructor
  · rw [hcurrent,
      ← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward roots who (value (time + 1)) time]
    unfold quittingRootQuitPayoff quittingRootSuccessorPayoff
    simpa only [add_zero] using hquitNash
  · rw [hcurrent,
      ← quittingRootContinuePayoff_eq_fixedOpponents
        reward roots who (value (time + 1)) time]
    unfold quittingRootContinuePayoff quittingRootSuccessorPayoff
    simpa only [add_zero] using hcontinueNash

/-- A nonnegative terminal debt at the end of an exact finite Nash--Bellman
prefix is multiplied by opponent-only survival through the prefix. -/
theorem quittingFiniteTerminalBestResponseValue_le_declared_add_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (cutoff : ℕ) {terminalDebt : ℝ}
    (hterminalDebt : 0 ≤ terminalDebt)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time)) :
    ∀ start fuel, start + fuel ≤ cutoff →
      quittingFiniteTerminalBestResponseValue reward roots who
          (value (start + fuel) who + terminalDebt) start fuel ≤
        value start who +
          quittingOpponentSurvivalWeight roots who start fuel * terminalDebt := by
  intro start fuel hcutoff
  induction fuel generalizing start with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hstart : start < cutoff := by omega
      have htailCutoff : start + 1 + fuel ≤ cutoff := by omega
      have htail := ih (start + 1) htailCutoff
      obtain ⟨hquit, hcontinue⟩ :=
        quittingFinitePrefix_endpointBounds reward roots value who start
          (hpolicy start hstart) (hnash start hstart)
      let mass := quittingFixedOpponentsContinueMass roots who start
      let tailWeight := quittingOpponentSurvivalWeight roots who (start + 1) fuel
      have hmass : 0 ≤ mass :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      have htailWeight : 0 ≤ tailWeight :=
        quittingOpponentSurvivalWeight_nonneg roots who (start + 1) fuel
      have hsurvival :
          quittingOpponentSurvivalWeight roots who start (fuel + 1) =
            mass * tailWeight := by
        simpa only [mass, tailWeight] using
          quittingOpponentSurvivalWeight_shift roots who start fuel
      have hindex : start + (fuel + 1) = start + 1 + fuel := by omega
      rw [quittingFiniteTerminalBestResponseValue, hindex]
      apply max_le
      · calc
          quittingFixedOpponentsQuitValue reward roots who start ≤
              value start who := hquit
          _ ≤ value start who + mass * tailWeight * terminalDebt := by
            exact le_add_of_nonneg_right
              (mul_nonneg (mul_nonneg hmass htailWeight) hterminalDebt)
          _ = value start who +
              quittingOpponentSurvivalWeight roots who start (fuel + 1) *
                terminalDebt := by rw [hsurvival]
      · have hscaled := mul_le_mul_of_nonneg_left htail hmass
        calc
          quittingFixedOpponentsContinueReward reward roots who start +
                mass *
                  quittingFiniteTerminalBestResponseValue reward roots who
                    (value (start + 1 + fuel) who + terminalDebt)
                    (start + 1) fuel ≤
              quittingFixedOpponentsContinueReward reward roots who start +
                mass * (value (start + 1) who + tailWeight * terminalDebt) := by
                  linarith
          _ = (quittingFixedOpponentsContinueReward reward roots who start +
                mass * value (start + 1) who) +
                mass * tailWeight * terminalDebt := by ring
          _ ≤ value start who + mass * tailWeight * terminalDebt := by
            linarith
          _ = value start who +
              quittingOpponentSurvivalWeight roots who start (fuel + 1) *
                terminalDebt := by rw [hsurvival]

/-- Following the prescribed root marginal through an exact policy-evaluation
prefix returns the displayed initial value at the displayed endpoint. -/
theorem quittingFiniteTerminalHazardValue_self_eq_declared
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (cutoff : ℕ)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) :
    ∀ start fuel, start + fuel ≤ cutoff →
      quittingFiniteTerminalHazardValue reward roots who
          (fun time => roots time who) (value (start + fuel) who)
          start fuel = value start who := by
  intro start fuel hcutoff
  induction fuel generalizing start with
  | zero => simp
  | succ fuel ih =>
      have hstart : start < cutoff := by omega
      have htailCutoff : start + 1 + fuel ≤ cutoff := by omega
      have hindex : start + (fuel + 1) = start + 1 + fuel := by omega
      rw [quittingFiniteTerminalHazardValue, hindex,
        ih (start + 1) htailCutoff]
      rw [congrFun (hpolicy start hstart) who,
        quittingRootSuccessorPayoff_eq_endpointMix,
        quittingRootQuitPayoff_eq_fixedOpponentsQuitValue,
        quittingRootContinuePayoff_eq_fixedOpponents]

/-- The finite best-response recursion is monotone in its terminal boundary. -/
theorem quittingFiniteTerminalBestResponseValue_mono_terminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {first second : ℝ} (hterminal : first ≤ second) :
    ∀ start fuel,
      quittingFiniteTerminalBestResponseValue reward roots who first start fuel ≤
        quittingFiniteTerminalBestResponseValue reward roots who second start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => exact hterminal
  | succ fuel ih =>
      rw [quittingFiniteTerminalBestResponseValue,
        quittingFiniteTerminalBestResponseValue]
      have hmass : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      exact max_le_max le_rfl
        (add_le_add_left
          (mul_le_mul_of_nonneg_left (ih (start + 1)) hmass)
          (quittingFixedOpponentsContinueReward reward roots who start))

end GameTheory
