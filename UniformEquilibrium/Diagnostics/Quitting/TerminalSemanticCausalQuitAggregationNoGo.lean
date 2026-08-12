/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCausalQuitAggregation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEndpointDefectPolarity
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingPayoff
import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Stationary cancellation no-go for eventwise Quit accounts

A fair stationary opponent makes the selected player's positive singleton
insertion atom cancel its equally large negative collision atom. The first
two literal reached rows carry any prescribed nonnegative positive-part
account after scaling, while every behavioral deviation of the selected
player has payoff zero.

Thus eventwise positive Quit atoms cannot be aggregated into a profitable
behavioral deviation merely by causal Continue-to-Quit mixing. The exact
finite causal identity uses signed row advantages instead. This is an
architectural no-go, not a closure of the prescribed-atom frontier.
-/

noncomputable section

namespace GameTheory
namespace CausalQuitAggregationCounterexample

open StochasticGame Math.Probability Math.PMFProduct

abbrev Player := Bool
abbrev observer : Player := false
abbrev opponent : Player := true

/-- The observer gains `scale` by quitting alone, loses `scale` in a
collision, and receives zero when only the opponent quits. -/
def reward (scale : ℝ) :
    {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who =>
    if who = observer then
      if terminal.val = {observer} then scale
      else if terminal.val = {opponent} then 0
      else -scale
    else 0

def fairCoin : PMF Bool :=
  quittingHazardCoin (1 / 2) (by norm_num) (by norm_num)

def root : Player → PMF Bool := fun who =>
  if who = observer then PMF.pure false else fairCoin

def profile (scale : ℝ) : (quittingGame (reward scale)).BehaviorProfile :=
  quittingStationaryProfile (reward scale) root

@[simp] theorem fairCoin_true_toReal : (fairCoin true).toReal = 1 / 2 := by
  simp [fairCoin]

@[simp] theorem fairCoin_false_toReal : (fairCoin false).toReal = 1 / 2 := by
  simp [fairCoin]
  norm_num

theorem root_observer : root observer = PMF.pure false := by
  rfl

theorem root_opponent : root opponent = fairCoin := by
  rfl

/-- The literal continuation payoff is zero at every shifted row. -/
theorem terminalPayoff_observer_eq_zero (scale : ℝ) :
    quittingTerminalPayoff (reward scale) (profile scale) observer = 0 := by
  rw [profile, quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
  · unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_bool]
    simp [expect_eq_sum, root, fairCoin, reward, observer, opponent,
      quittingRootPayoff, quittingQuitters, Finset.ext_iff,
      quittingStationaryContinueMass, quittingAllContinueAction]
  · simp [root, fairCoin, quittingStationaryContinueMass,
      quittingAllContinueAction]

theorem fixedOpponentsQuitValue_observer_eq_zero (scale : ℝ) :
    quittingStationaryFixedOpponentsQuitValue (reward scale) root observer =
      0 := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp [expect_eq_sum, root, fairCoin, reward, observer, opponent,
    quittingRootPayoff, quittingQuitters, Finset.ext_iff]
  have hnonempty :
      ({x ∈ ({true, false} : Finset Bool) | x = false}).Nonempty := by
    exact ⟨false, by simp⟩
  rw [if_pos hnonempty]
  ring

theorem fixedOpponentsContinueReward_observer_eq_zero (scale : ℝ) :
    quittingStationaryFixedOpponentsContinueReward
      (reward scale) root observer = 0 := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp [expect_eq_sum, root, fairCoin, reward, observer, opponent,
    quittingRootPayoff, quittingQuitters, Finset.ext_iff]

theorem fixedOpponentsContinueMass_observer_eq_half :
    quittingStationaryFixedOpponentsContinueMass root observer = 1 / 2 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  simp [root, fairCoin, quittingAllContinueAction]
  norm_num

/-- The observer's full arbitrary-behavior best-response value is zero. -/
theorem bestReplyValue_observer_eq_zero (scale : ℝ) :
    quittingBestReplyValue (reward scale) (profile scale) observer = 0 := by
  rw [profile, quittingBestReplyValue_stationary,
    quittingStationaryUnilateralCap_eq_max_div,
    fixedOpponentsQuitValue_observer_eq_zero,
    fixedOpponentsContinueReward_observer_eq_zero,
    fixedOpponentsContinueMass_observer_eq_half]
  norm_num

theorem pureTimePayoff_observer_eq_zero
    (scale : ℝ) (choice : Option ℕ) :
    quittingTerminalPayoff (reward scale)
        (Function.update (profile scale) observer
          (quittingPureTimeBehaviorStrategy (reward scale) observer choice))
        observer = 0 := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    profile, quittingProfileLiveRoot_stationary,
    quittingRootSequencePureTimeTerminalValue_const]
  · rw [fixedOpponentsQuitValue_observer_eq_zero,
      fixedOpponentsContinueReward_observer_eq_zero,
      fixedOpponentsContinueMass_observer_eq_half]
    cases choice with
    | none => simp [quittingStationaryDeterministicValue,
        quittingStationaryNeverValue]
    | some steps =>
        simp only [quittingStationaryDeterministicValue]
        induction steps with
        | zero => rfl
        | succ steps ih =>
            rw [quittingStationaryPureTimeValue, ih]
            ring
  · rw [fixedOpponentsContinueMass_observer_eq_half]
    norm_num

/-- Every behavioral modification of the observer has exactly the same
payoff, not merely every modification supported on the first two rows. -/
theorem every_observer_deviation_payoff_eq_zero
    (scale : ℝ)
    (deviation : (quittingGame (reward scale)).BehaviorStrategy observer) :
    quittingTerminalPayoff (reward scale)
        (Function.update (profile scale) observer deviation) observer = 0 := by
  rw [quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
    (reward scale) (profile scale) observer deviation (abs_nonneg scale)]
  · have hpure : (fun choice =>
        quittingTerminalPayoff (reward scale)
          (Function.update (profile scale) observer
            (quittingPureTimeBehaviorStrategy (reward scale) observer choice))
          observer) = fun _ => 0 := by
      funext choice
      exact pureTimePayoff_observer_eq_zero scale choice
    rw [hpure, expect_const]
  · intro terminal player
    simp only [reward]
    split_ifs <;> simp

/-- Although the signed Quit advantage is zero, the formal eventwise
positive-part Quit account is `scale / 2`: the favorable opponent-Continue
atom is retained and the equally large collision loss is discarded. -/
theorem sum_quitDirectedAtoms_eq_half_scale
    (scale : ℝ) (hscale : 0 ≤ scale) :
    (∑ coalition ∈ (Finset.univ.erase observer).powerset,
      quittingRootQuitDirectedAtom (reward scale) 0 root observer coalition) =
        scale / 2 := by
  classical
  have hcarrier : (Finset.univ.erase observer).powerset =
      ({∅, {opponent}} : Finset (Finset Player)) := by decide
  rw [hcarrier]
  simp [quittingRootQuitDirectedAtom, quittingOpponentCoalitionMass,
    quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
    root, reward, observer, opponent, fairCoin_true_toReal]
  have hneq : ({false, true} : Finset Bool) ≠ {false} := by decide
  rw [if_neg hneq, max_eq_right (neg_nonpos.mpr hscale)]
  have hbool : ({true, false} : Finset Bool).erase false = {true} := by decide
  rw [hbool]
  simp [fairCoin_false_toReal, max_eq_left hscale]
  ring

/-- **Stationary cancellation obstruction.** The first two reached
positive-part accounts can have any prescribed nonnegative size `kappa`,
while every infinite-horizon behavioral deviation of the observer has zero
payoff. -/
theorem arbitrary_behavior_cancellation_obstruction
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (deviation : (quittingGame (reward (4 * kappa / 3))).BehaviorStrategy
      observer) :
    let scale := 4 * kappa / 3
    (∑ coalition ∈ (Finset.univ.erase observer).powerset,
        quittingRootQuitDirectedAtom (reward scale) 0 root observer coalition) +
      (1 / 2 : ℝ) *
        (∑ coalition ∈ (Finset.univ.erase observer).powerset,
          quittingRootQuitDirectedAtom
            (reward scale) 0 root observer coalition) = kappa ∧
      quittingTerminalPayoff (reward scale)
          (Function.update (profile scale) observer deviation) observer = 0 := by
  dsimp only
  constructor
  · have hscale : 0 ≤ 4 * kappa / 3 := by positivity
    rw [sum_quitDirectedAtoms_eq_half_scale _ hscale]
    ring
  · exact every_observer_deviation_payoff_eq_zero _ deviation

end CausalQuitAggregationCounterexample
end GameTheory
