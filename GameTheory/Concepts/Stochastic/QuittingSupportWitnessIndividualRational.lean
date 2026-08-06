/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSupportWitnessReduction
import GameTheory.Concepts.Stochastic.QuittingStationaryMinMax

/-!
# Individual rationality supplies the support-witness tail

The support-witness compiler in `QuittingSupportWitnessReduction` asks for a
player-indexed closed tail at the selected switch.  That tail is not extra
strategic structure.  The quitting min--max theorem already says that each
player's punishment value is the infimum of stationary unilateral caps, and
every stationary cap is attained by an actual behavioral response.

Consequently, whenever the plan's continuation value at the switch is at
least the selected player's punishment value, any positive slack supplies a
stationary row whose cap lies below the continuation value plus that slack.
Keeping the row's opponents stationary and installing its cap-attaining
response as the player's prescribed behavior gives the required closed tail.

This file replaces the player-indexed tail producer by the ordinary
individual-rationality inequalities at one deterministic switch.  Together
with support-local one-stage witnesses and a genuine own-survival crossing,
those inequalities imply terminal approximate Nash profiles and hence a
uniform-equilibrium payoff at all accuracies.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Root-sequence hazard values depend only on the opponents' coordinates. -/
theorem quittingSupportWitnessHazardTerminalValue_congr_of_opponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : ℕ → ι → PMF Bool} (who : ι)
    (hagree : ∀ time player, player ≠ who →
      first time player = second time player)
    (hazard : ℕ → PMF Bool) (start : ℕ) :
    quittingRootSequenceHazardTerminalValue reward first who hazard start =
      quittingRootSequenceHazardTerminalValue reward second who hazard start := by
  unfold quittingRootSequenceHazardTerminalValue
  apply congrArg
    (fun roots => quittingRootSequenceTerminalValue reward roots who start)
  funext time player
  unfold quittingRootSequenceUpdate
  by_cases hplayer : player = who
  · subst player
    simp
  · simp [Function.update_of_ne hplayer, hagree time player hplayer]

/-- Every stationary opponent row admits a closed tail whose target payoff is
exactly that row's stationary unilateral cap.  The opponents repeat the row;
the target uses an actual cap-attaining behavioral response. -/
theorem exists_quittingSupportWitnessTargetClosedTail_of_stationaryRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (target : ι) :
    ∃ tail : ℕ → ι → PMF Bool,
      IsQuittingTargetClosedTail reward tail target ∧
      quittingRootSequenceTerminalValue reward tail target 0 =
        quittingStationaryUnilateralCap reward root target := by
  obtain ⟨response, hresponse⟩ :=
    exists_quittingTerminalPayoff_update_stationary_eq_cap
      reward root target
  let responseHazard : ℕ → PMF Bool :=
    quittingBehaviorLiveHazard reward response
  let tail : ℕ → ι → PMF Bool :=
    quittingRootSequenceUpdate (fun _ => root) target responseHazard
  have hcollapse :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward (quittingStationaryProfile reward root) target response
  rw [quittingProfileLiveRoot_stationary] at hcollapse
  have hvalue :
      quittingRootSequenceTerminalValue reward tail target 0 =
        quittingStationaryUnilateralCap reward root target := by
    dsimp only [tail]
    change
      quittingRootSequenceHazardTerminalValue reward (fun _ => root)
          target responseHazard 0 =
        quittingStationaryUnilateralCap reward root target
    rw [← hcollapse]
    exact hresponse
  refine ⟨tail, ?_, hvalue⟩
  intro hazard
  have hsame :
      quittingRootSequenceHazardTerminalValue reward tail target hazard 0 =
        quittingRootSequenceHazardTerminalValue reward (fun _ => root)
          target hazard 0 := by
    apply quittingSupportWitnessHazardTerminalValue_congr_of_opponents
    intro time player hplayer
    simp [tail, quittingRootSequenceUpdate,
      Function.update_of_ne hplayer]
  calc
    quittingRootSequenceHazardTerminalValue reward tail target hazard 0 =
        quittingRootSequenceHazardTerminalValue reward (fun _ => root)
          target hazard 0 := hsame
    _ ≤ quittingStationaryUnilateralCap reward root target :=
      quittingRootSequenceHazardTerminalValue_const_le_cap
        reward root target hazard
    _ = quittingRootSequenceTerminalValue reward tail target 0 :=
      hvalue.symm

/-- The stationary-cap infimum can be approximated from above by an actual
row at every positive slack.  Exact attainment is neither assumed nor needed. -/
theorem exists_stationaryRoot_cap_lt_punishmentValue_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : ι) {slack : ℝ} (hslack : 0 < slack) :
    ∃ root : ι → PMF Bool,
      quittingStationaryUnilateralCap reward root target <
        quittingPunishmentValue reward target + slack := by
  rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
  unfold quittingStationaryPunishmentValue
  by_contra hnone
  have hall : ∀ root : ι → PMF Bool,
      (⨅ row : ι → PMF Bool,
          quittingStationaryUnilateralCap reward row target) + slack ≤
        quittingStationaryUnilateralCap reward root target := by
    intro root
    exact le_of_not_gt (fun hroot => hnone ⟨root, hroot⟩)
  have hcollapse :
      (⨅ row : ι → PMF Bool,
          quittingStationaryUnilateralCap reward row target) + slack ≤
        (⨅ row : ι → PMF Bool,
          quittingStationaryUnilateralCap reward row target) :=
    le_ciInf hall
  linarith

/-- Individual rationality at a boundary value supplies a target-closed tail
whose target payoff is within any prescribed positive slack of that boundary. -/
theorem exists_quittingTargetClosedTail_le_of_punishmentValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : ι) (boundary : ℝ) {slack : ℝ}
    (hslack : 0 < slack)
    (hir : quittingPunishmentValue reward target ≤ boundary) :
    ∃ tail : ℕ → ι → PMF Bool,
      IsQuittingTargetClosedTail reward tail target ∧
      quittingRootSequenceTerminalValue reward tail target 0 ≤
        boundary + slack := by
  obtain ⟨root, hroot⟩ :=
    exists_stationaryRoot_cap_lt_punishmentValue_add
      reward target hslack
  obtain ⟨tail, hclosed, hvalue⟩ :=
    exists_quittingSupportWitnessTargetClosedTail_of_stationaryRoot
      reward root target
  refine ⟨tail, hclosed, ?_⟩
  rw [hvalue]
  linarith

/-- The reduced producer: support-local one-stage witnesses, one genuine
own-survival crossing, and individual rationality at the resulting global
switch.  Closed tails are no longer part of the input. -/
def HasQuittingSupportWitnessIndividualRationalPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) : Prop :=
  ∃ (plan : ℕ → ι → PMF Bool)
      (δ ledgerCap threshold continuationSlack : ℝ),
    0 ≤ δ ∧
    0 < ledgerCap ∧
    0 < threshold ∧
    0 < continuationSlack ∧
    δ ≤ ledgerCap * threshold ∧
    IsQuittingRootSequenceSupportApproxNash reward plan δ ∧
    (∃ cutoff, ∃ player,
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard plan player) cutoff ≤ threshold) ∧
    (∀ target : ι,
      quittingPunishmentValue reward target ≤
        quittingRootSequenceTerminalValue reward plan target
          (quittingSupportSurvivalSwitchIndex plan threshold)) ∧
    ledgerCap + 2 * δ + continuationSlack +
        threshold * (7 * quittingRewardBound reward) ≤ ε

/-- Individual-rational support-witness data automatically provide the
player-indexed closed-tail package consumed by the phase-switch compiler. -/
theorem hasQuittingSupportWitnessTailPackage_of_individualRationalPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {ε : ℝ}
    (hpackage :
      HasQuittingSupportWitnessIndividualRationalPackage reward ε) :
    HasQuittingSupportWitnessTailPackage reward ε := by
  obtain ⟨plan, δ, ledgerCap, threshold, continuationSlack,
    hδ, hledgerCap, hthreshold, hcontinuationSlack, hscale,
    hsupport, hexists, hir, herror⟩ := hpackage
  refine ⟨plan, δ, ledgerCap, threshold, continuationSlack,
    hδ, hledgerCap, hthreshold, hcontinuationSlack.le, hscale,
    hsupport, hexists, ?_, herror⟩
  intro target
  exact exists_quittingTargetClosedTail_le_of_punishmentValue_le
    reward target
      (quittingRootSequenceTerminalValue reward plan target
        (quittingSupportSurvivalSwitchIndex plan threshold))
      hcontinuationSlack (hir target)

/-- One individual-rational support-witness package yields a terminal
approximate Nash profile. -/
theorem
    exists_isεAsymptoticNash_of_hasQuittingSupportWitnessIndividualRationalPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {ε : ℝ}
    (hpackage :
      HasQuittingSupportWitnessIndividualRationalPackage reward ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile :=
  exists_isεAsymptoticNash_of_hasQuittingSupportWitnessTailPackage
    reward
      (hasQuittingSupportWitnessTailPackage_of_individualRationalPackage
        reward hpackage)

/-- Individual-rational support-witness packages at every positive tolerance
imply a uniform-equilibrium payoff. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_supportWitnessIndividualRationalPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpackage : ∀ ε : ℝ, 0 < ε →
      HasQuittingSupportWitnessIndividualRationalPackage reward ε) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_supportWitnessTailPackage
    reward fun ε hε =>
      hasQuittingSupportWitnessTailPackage_of_individualRationalPackage
        reward (hpackage ε hε)

end GameTheory
