/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSharedPunishmentThreePlayer
import Mathlib.Probability.Distributions.Uniform

/-!
# Exact shared-punishment price for the cyclic three-player table

For the cyclic table in `QuittingSharedPunishmentThreePlayer`, every individual
punishment floor is `-1`, while every committed shared plan leaves some player
with best-reply value at least `-1/4`.  This file closes the matching upper
bound: the stationary row in which every player quits with probability `1/2`
has best-reply value exactly `-1/4` for every designated player.

Thus the shared excess is exactly `3/4`.  The value is unchanged when the
infimum is restricted to stationary product rows, so stationarity is optimal
for this table despite the positive price of sharing one punishment plan.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace QuittingSharedThreePlayer

/-! ## The remaining stationary coefficients -/

/-- Continuing now has the same immediate absorbing contribution as quitting
now, since this table's payoff to a player depends only on the two opponents. -/
theorem quittingStationaryFixedOpponentsContinueReward_eq
    (root : Player → PMF Bool) (who : Player) :
    quittingStationaryFixedOpponentsContinueReward reward root who =
      -(root (next who) true).toReal *
        (root (other who) false).toReal := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward
    quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [show (fun action =>
      quittingRootPayoff reward (0 : Payoff Player) action who) =
      (fun action =>
        if action (next who) = true ∧ action (other who) = false
          then (-1 : ℝ) else 0) by
    funext action
    exact quittingRootPayoff_eq_badEvent action who]
  rw [expect_pmfPi_badEvent _ (next_ne_other who)]
  simp [next_ne_self who, other_ne_self who]

private theorem prod_player (f : Player → ℝ) :
    ∏ player, f player =
      f Player.a * f Player.b * f Player.c := by
  rw [show (Finset.univ : Finset Player) =
      {Player.a, Player.b, Player.c} by decide]
  simp [mul_assoc]

/-- The opponents survive one stage exactly when both cyclic opponent
coordinates continue. -/
theorem quittingStationaryFixedOpponentsContinueMass_eq
    (root : Player → PMF Bool) (who : Player) :
    quittingStationaryFixedOpponentsContinueMass root who =
      (root (next who) false).toReal *
        (root (other who) false).toReal := by
  cases who <;>
    simp [quittingStationaryFixedOpponentsContinueMass,
      quittingFixedOpponentsContinueMass,
      quittingStationaryContinueMass, quittingAllContinueAction,
      prod_player, next, other, mul_assoc, mul_comm, mul_left_comm]

/-! ## The fair stationary row -/

/-- The fair Boolean marginal. -/
def fairMarginal : PMF Bool := PMF.uniformOfFintype Bool

/-- Every player quits with probability one half. -/
def fairRoot : Player → PMF Bool := fun _ => fairMarginal

@[simp] theorem fairMarginal_apply_toReal (action : Bool) :
    (fairMarginal action).toReal = (1 / 2 : ℝ) := by
  unfold fairMarginal
  rw [PMF.uniformOfFintype_apply]
  have hcard : Fintype.card Bool = 2 := by rfl
  rw [hcard]
  norm_num

@[simp] theorem fairRoot_apply_toReal (who : Player) (action : Bool) :
    (fairRoot who action).toReal = (1 / 2 : ℝ) := by
  simp [fairRoot]

@[simp] theorem fairRoot_quitValue (who : Player) :
    quittingStationaryFixedOpponentsQuitValue reward fairRoot who =
      (-1 / 4 : ℝ) := by
  rw [quittingStationaryFixedOpponentsQuitValue_eq]
  norm_num

@[simp] theorem fairRoot_continueReward (who : Player) :
    quittingStationaryFixedOpponentsContinueReward reward fairRoot who =
      (-1 / 4 : ℝ) := by
  rw [quittingStationaryFixedOpponentsContinueReward_eq]
  norm_num

@[simp] theorem fairRoot_continueMass (who : Player) :
    quittingStationaryFixedOpponentsContinueMass fairRoot who =
      (1 / 4 : ℝ) := by
  rw [quittingStationaryFixedOpponentsContinueMass_eq]
  norm_num

/-- The fair row's selected stationary stopping cap is `-1/4`: quitting now
beats waiting for the opponents' absorption value `-1/3`. -/
@[simp] theorem fairRoot_unilateralCap (who : Player) :
    quittingStationaryUnilateralCap reward fairRoot who =
      (-1 / 4 : ℝ) := by
  rw [quittingStationaryUnilateralCap_eq_max_div,
    fairRoot_quitValue, fairRoot_continueReward, fairRoot_continueMass]
  norm_num

/-- Every designated player has exact best-reply value `-1/4` against the
fair stationary profile. -/
@[simp] theorem fairRoot_bestReplyValue (who : Player) :
    quittingBestReplyValue reward
        (quittingStationaryProfile reward fairRoot) who =
      (-1 / 4 : ℝ) := by
  rw [quittingBestReplyValue_stationary, fairRoot_unilateralCap]

/-! ## Shared gaps and their exact infima -/

/-- Worst excess above the individual punishment floors for one committed
behavior plan. -/
def quittingSharedPunishmentGap
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  max
    (quittingBestReplyValue reward profile Player.a -
      quittingPunishmentValue reward Player.a)
    (max
      (quittingBestReplyValue reward profile Player.b -
        quittingPunishmentValue reward Player.b)
      (quittingBestReplyValue reward profile Player.c -
        quittingPunishmentValue reward Player.c))

/-- Worst excess above the stationary individual floors for one constant row. -/
def quittingSharedStationaryPunishmentGap
    (root : Player → PMF Bool) : ℝ :=
  max
    (quittingStationaryUnilateralCap reward root Player.a -
      quittingStationaryPunishmentValue reward Player.a)
    (max
      (quittingStationaryUnilateralCap reward root Player.b -
        quittingStationaryPunishmentValue reward Player.b)
      (quittingStationaryUnilateralCap reward root Player.c -
        quittingStationaryPunishmentValue reward Player.c))

/-- On stationary profiles the behavior-plan and constant-row gaps coincide. -/
theorem quittingSharedPunishmentGap_stationary
    (root : Player → PMF Bool) :
    quittingSharedPunishmentGap
        (quittingStationaryProfile reward root) =
      quittingSharedStationaryPunishmentGap root := by
  unfold quittingSharedPunishmentGap
    quittingSharedStationaryPunishmentGap
  simp only [quittingBestReplyValue_stationary,
    quittingPunishmentValue_eq_stationaryPunishmentValue]

/-- Every shared behavior plan has worst-player excess at least `3/4`. -/
theorem three_quarters_le_quittingSharedPunishmentGap
    (profile : (quittingGame reward).BehaviorProfile) :
    (3 / 4 : ℝ) ≤ quittingSharedPunishmentGap profile := by
  obtain ⟨who, hwho⟩ :=
    exists_neg_quarter_le_quittingBestReplyValue profile
  have hgap : (3 / 4 : ℝ) ≤
      quittingBestReplyValue reward profile who -
        quittingPunishmentValue reward who := by
    rw [quittingPunishmentValue_eq_neg_one]
    linarith
  unfold quittingSharedPunishmentGap
  cases who with
  | a =>
      exact hgap.trans (le_max_left _ _)
  | b =>
      calc
        (3 / 4 : ℝ) ≤
            quittingBestReplyValue reward profile Player.b -
              quittingPunishmentValue reward Player.b := hgap
        _ ≤ max
            (quittingBestReplyValue reward profile Player.b -
              quittingPunishmentValue reward Player.b)
            (quittingBestReplyValue reward profile Player.c -
              quittingPunishmentValue reward Player.c) := le_max_left _ _
        _ ≤ max
            (quittingBestReplyValue reward profile Player.a -
              quittingPunishmentValue reward Player.a)
            (max
              (quittingBestReplyValue reward profile Player.b -
                quittingPunishmentValue reward Player.b)
              (quittingBestReplyValue reward profile Player.c -
                quittingPunishmentValue reward Player.c)) := le_max_right _ _
  | c =>
      calc
        (3 / 4 : ℝ) ≤
            quittingBestReplyValue reward profile Player.c -
              quittingPunishmentValue reward Player.c := hgap
        _ ≤ max
            (quittingBestReplyValue reward profile Player.b -
              quittingPunishmentValue reward Player.b)
            (quittingBestReplyValue reward profile Player.c -
              quittingPunishmentValue reward Player.c) := le_max_right _ _
        _ ≤ max
            (quittingBestReplyValue reward profile Player.a -
              quittingPunishmentValue reward Player.a)
            (max
              (quittingBestReplyValue reward profile Player.b -
                quittingPunishmentValue reward Player.b)
              (quittingBestReplyValue reward profile Player.c -
                quittingPunishmentValue reward Player.c)) := le_max_right _ _

/-- Every constant row has worst-player excess at least `3/4`. -/
theorem three_quarters_le_quittingSharedStationaryPunishmentGap
    (root : Player → PMF Bool) :
    (3 / 4 : ℝ) ≤ quittingSharedStationaryPunishmentGap root := by
  rw [← quittingSharedPunishmentGap_stationary]
  exact three_quarters_le_quittingSharedPunishmentGap
    (quittingStationaryProfile reward root)

@[simp] theorem fairRoot_sharedPunishmentGap :
    quittingSharedPunishmentGap
        (quittingStationaryProfile reward fairRoot) = (3 / 4 : ℝ) := by
  unfold quittingSharedPunishmentGap
  simp [quittingPunishmentValue_eq_neg_one]
  norm_num

@[simp] theorem fairRoot_sharedStationaryPunishmentGap :
    quittingSharedStationaryPunishmentGap fairRoot = (3 / 4 : ℝ) := by
  rw [← quittingSharedPunishmentGap_stationary]
  exact fairRoot_sharedPunishmentGap

/-- Infimum of the worst-player excess over arbitrary committed behavior
plans. -/
def quittingSharedPunishmentExcess : ℝ :=
  ⨅ profile : (quittingGame reward).BehaviorProfile,
    quittingSharedPunishmentGap profile

/-- Infimum of the worst-player excess over constant product rows. -/
def quittingSharedStationaryPunishmentExcess : ℝ :=
  ⨅ root : Player → PMF Bool,
    quittingSharedStationaryPunishmentGap root

private theorem bddBelow_range_quittingSharedPunishmentGap :
    BddBelow (Set.range quittingSharedPunishmentGap) := by
  refine ⟨3 / 4, ?_⟩
  rintro _ ⟨profile, rfl⟩
  exact three_quarters_le_quittingSharedPunishmentGap profile

private theorem bddBelow_range_quittingSharedStationaryPunishmentGap :
    BddBelow (Set.range quittingSharedStationaryPunishmentGap) := by
  refine ⟨3 / 4, ?_⟩
  rintro _ ⟨root, rfl⟩
  exact three_quarters_le_quittingSharedStationaryPunishmentGap root

/-- **Exact three-player shared-punishment price.**  Arbitrary
history-dependent committed plans cannot reduce the worst excess below
`3/4`, and the fair stationary profile attains this bound. -/
theorem quittingSharedPunishmentExcess_eq_three_quarters :
    quittingSharedPunishmentExcess = (3 / 4 : ℝ) := by
  apply le_antisymm
  · exact (ciInf_le bddBelow_range_quittingSharedPunishmentGap
      (quittingStationaryProfile reward fairRoot)).trans_eq
        fairRoot_sharedPunishmentGap
  · unfold quittingSharedPunishmentExcess
    haveI : Nonempty ((quittingGame reward).BehaviorProfile) :=
      ⟨quittingAlwaysContinueProfile reward⟩
    exact le_ciInf fun profile =>
      three_quarters_le_quittingSharedPunishmentGap profile

/-- Restricting the shared punishment plan to a constant row has the same
exact value `3/4`. -/
theorem quittingSharedStationaryPunishmentExcess_eq_three_quarters :
    quittingSharedStationaryPunishmentExcess = (3 / 4 : ℝ) := by
  apply le_antisymm
  · exact (ciInf_le bddBelow_range_quittingSharedStationaryPunishmentGap
      fairRoot).trans_eq fairRoot_sharedStationaryPunishmentGap
  · unfold quittingSharedStationaryPunishmentExcess
    haveI : Nonempty (Player → PMF Bool) :=
      ⟨fun _ => PMF.pure false⟩
    exact le_ciInf fun root =>
      three_quarters_le_quittingSharedStationaryPunishmentGap root

/-- Stationarity is optimal for the shared problem on this table. -/
theorem quittingSharedPunishmentExcess_eq_stationary :
    quittingSharedPunishmentExcess =
      quittingSharedStationaryPunishmentExcess := by
  rw [quittingSharedPunishmentExcess_eq_three_quarters,
    quittingSharedStationaryPunishmentExcess_eq_three_quarters]

end QuittingSharedThreePlayer

end GameTheory
