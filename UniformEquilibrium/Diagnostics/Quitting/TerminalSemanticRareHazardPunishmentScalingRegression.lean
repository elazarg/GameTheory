/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFixedTableDiffuseIncidenceRegression
import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Coordinatewise rare hazards do not preserve a punishment row

A tempting way to attack a zero-slack singleton vertex is to choose a good
stationary punishment row and multiply every opponent Quit probability by a
small common scale.  The honest owner could then approach its singleton
payoff while, one might hope, its stationary unilateral cap retained the
punishment value.

This is false for product roots.  Coordinatewise scaling makes singleton
opponent events first order and simultaneous opponent coalitions higher
order.  A punishment carried by a collision can therefore disappear—or even
reverse sign—under every sufficiently rare scaling.

The fixed three-player table below is exact.  The row where both opponents
Quit surely gives the owner stationary cap `-1`.  Replacing both opponents by
independent Quit probability `q_n = 1/(n+2)` gives cap

`(2-3q_n)/(2-q_n)`,

which is at least `1/3` and tends to `1`.  Thus neither the punishment cap nor
its sign survives coordinatewise rare-hazard scaling.  A successful rare
phase construction must scale whole coalition phases (or retain a correlated
public controller), not merely shrink independent marginals.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped Topology

namespace QuittingRareHazardPunishmentScalingRegression

abbrev Player := Fin 3

abbrev owner : Player := 0
abbrev left : Player := 1
abbrev right : Player := 2

abbrev q := QuittingFixedTableDiffuseIncidenceRegression.q
abbrev coin := QuittingFixedTableDiffuseIncidenceRegression.switchCoin

/-- Only the owner's payoff matters.  When the owner Quits, its singleton
payoff is zero and the full three-player collision pays `-1`.  When the owner
Continues, either opponent singleton pays `1`, while their joint collision
pays `-1`. -/
def reward (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who =>
    if who = owner then
      if owner ∈ terminal.1 then
        if left ∈ terminal.1 ∧ right ∈ terminal.1 then -1 else 0
      else
        if left ∈ terminal.1 ∧ right ∈ terminal.1 then -1 else 1
    else
      0

/-- The collision punishment row. -/
def collisionRoot : Player -> PMF Bool := fun who =>
  if who = owner then PMF.pure false else PMF.pure true

/-- Coordinatewise rare scaling of the two opponent hazards. -/
def rareRoot (n : ℕ) : Player -> PMF Bool := fun who =>
  if who = owner then PMF.pure false else coin n

theorem rareRoot_probabilities (n : ℕ) :
    ((rareRoot n owner true).toReal = 0) ∧
      ((rareRoot n left true).toReal = q n) ∧
      ((rareRoot n right true).toReal = q n) := by
  simp [rareRoot, coin, QuittingFixedTableDiffuseIncidenceRegression.switchCoin,
    owner, left, right]

theorem collision_quitValue :
    quittingStationaryFixedOpponentsQuitValue reward collisionRoot owner =
      -1 := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [QuittingFixedTableDiffuseIncidenceRegression.expect_pmfPi_fin3]
  simp [expect_eq_sum, quittingRootPayoff, reward, collisionRoot,
    owner, left, right]

theorem collision_continueReward :
    quittingStationaryFixedOpponentsContinueReward reward collisionRoot owner =
      -1 := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [QuittingFixedTableDiffuseIncidenceRegression.expect_pmfPi_fin3]
  simp [expect_eq_sum, quittingRootPayoff, reward, collisionRoot,
    owner, left, right]

theorem collision_continueMass :
    quittingStationaryFixedOpponentsContinueMass collisionRoot owner = 0 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [show (Finset.univ : Finset Player) = {owner, left, right} by decide]
  simp [collisionRoot, owner, left, right]

/-- The unscaled collision row really has cap `-1`. -/
theorem collision_unilateralCap :
    quittingStationaryUnilateralCap reward collisionRoot owner = -1 := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [collision_quitValue, collision_continueReward,
    collision_continueMass]
  norm_num

theorem reward_owner_lower (terminal : {S : Finset Player // S.Nonempty}) :
    (-1 : ℝ) ≤ reward terminal owner := by
  simp [reward]
  split_ifs <;> norm_num

/-- The collision row is not merely a convenient negative row: it attains
the owner's full behavioral punishment value. -/
theorem punishmentValue_eq_neg_one :
    quittingPunishmentValue reward owner = -1 := by
  rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
  apply le_antisymm
  · have hupper := quittingStationaryPunishmentValue_le
      reward owner collisionRoot
    rwa [collision_unilateralCap] at hupper
  · haveI : Nonempty (Player -> PMF Bool) :=
      ⟨fun _ => PMF.pure false⟩
    apply le_ciInf
    intro root
    exact le_quittingStationaryUnilateralCap_of_forall_le
      reward owner (by norm_num) reward_owner_lower root

theorem rare_quitValue (n : ℕ) :
    quittingStationaryFixedOpponentsQuitValue reward (rareRoot n) owner =
      -(q n) ^ 2 := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [QuittingFixedTableDiffuseIncidenceRegression.expect_pmfPi_fin3]
  simp [expect_eq_sum, quittingRootPayoff, reward, rareRoot, coin,
    QuittingFixedTableDiffuseIncidenceRegression.switchCoin,
    owner, left, right]
  ring

theorem rare_continueReward (n : ℕ) :
    quittingStationaryFixedOpponentsContinueReward reward (rareRoot n) owner =
      2 * q n - 3 * (q n) ^ 2 := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [QuittingFixedTableDiffuseIncidenceRegression.expect_pmfPi_fin3]
  simp [expect_eq_sum, quittingRootPayoff, reward, rareRoot, coin,
    QuittingFixedTableDiffuseIncidenceRegression.switchCoin,
    owner, left, right]
  ring

theorem rare_continueMass (n : ℕ) :
    quittingStationaryFixedOpponentsContinueMass (rareRoot n) owner =
      (1 - q n) ^ 2 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [show (Finset.univ : Finset Player) = {owner, left, right} by decide]
  simp [rareRoot, coin,
    QuittingFixedTableDiffuseIncidenceRegression.switchCoin,
    owner, left, right]
  ring

/-- Exact selected cap after coordinatewise rare scaling. -/
theorem rare_unilateralCap (n : ℕ) :
    quittingStationaryUnilateralCap reward (rareRoot n) owner =
      (2 - 3 * q n) / (2 - q n) := by
  have hq0 := QuittingFixedTableDiffuseIncidenceRegression.q_pos n
  have hqHalf := QuittingFixedTableDiffuseIncidenceRegression.q_le_half n
  have hden : 0 < 2 - q n := by linarith
  have hneverNonneg : 0 ≤ (2 - 3 * q n) / (2 - q n) := by
    exact div_nonneg (by linarith) hden.le
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [rare_quitValue, rare_continueReward, rare_continueMass]
  have hratio :
      (2 * q n - 3 * (q n) ^ 2) / (1 - (1 - q n) ^ 2) =
        (2 - 3 * q n) / (2 - q n) := by
    have hfactor : 1 - (1 - q n) ^ 2 = q n * (2 - q n) := by ring
    rw [hfactor]
    field_simp [hq0.ne', hden.ne']
  rw [hratio, max_eq_right]
  nlinarith [sq_nonneg (q n)]

theorem one_third_le_rare_unilateralCap (n : ℕ) :
    (1 : ℝ) / 3 ≤
      quittingStationaryUnilateralCap reward (rareRoot n) owner := by
  rw [rare_unilateralCap]
  have hqHalf := QuittingFixedTableDiffuseIncidenceRegression.q_le_half n
  have hden : 0 < 2 - q n := by linarith
  rw [le_div_iff₀ hden]
  linarith

theorem q_tendsto_zero : Tendsto (fun n : ℕ => q n) atTop (nhds 0) := by
  have hzero := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hshift : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 2))
      atTop (nhds 0) := by
    apply (hzero.comp (tendsto_add_atTop_nat 1)).congr'
    exact Filter.Eventually.of_forall fun n => by
      simp [Nat.cast_add]
      ring
  simpa [q, QuittingFixedTableDiffuseIncidenceRegression.q] using hshift

theorem rare_unilateralCap_tendsto_one :
    Tendsto (fun n =>
      quittingStationaryUnilateralCap reward (rareRoot n) owner)
      atTop (nhds 1) := by
  have hnumerator : Tendsto (fun n : ℕ => 2 - 3 * q n)
      atTop (nhds 2) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_const_nhds.mul q_tendsto_zero)
  have hdenominator : Tendsto (fun n : ℕ => 2 - q n)
      atTop (nhds 2) := by
    simpa using tendsto_const_nhds.sub q_tendsto_zero
  rw [show (fun n =>
      quittingStationaryUnilateralCap reward (rareRoot n) owner) =
        fun n => (2 - 3 * q n) / (2 - q n) by
      funext n
      exact rare_unilateralCap n]
  have hdiv := hnumerator.div hdenominator (by norm_num)
  change Tendsto (fun n : ℕ => (2 - 3 * q n) / (2 - q n))
    atTop (nhds (2 / 2)) at hdiv
  norm_num at hdiv
  exact hdiv

/-- **Regression headline.**  The collision punishment cap is `-1`, whereas
every coordinatewise rare scaling has cap at least `1/3` and the caps converge
to `1`. -/
theorem coordinatewise_rare_scaling_destroys_collision_punishment :
    quittingPunishmentValue reward owner = -1 ∧
      quittingStationaryUnilateralCap reward collisionRoot owner = -1 ∧
      (∀ n, (1 : ℝ) / 3 ≤
        quittingStationaryUnilateralCap reward (rareRoot n) owner) ∧
      Tendsto (fun n =>
        quittingStationaryUnilateralCap reward (rareRoot n) owner)
        atTop (nhds 1) := by
  exact ⟨punishmentValue_eq_neg_one, collision_unilateralCap,
    one_third_le_rare_unilateralCap, rare_unilateralCap_tendsto_one⟩

end QuittingRareHazardPunishmentScalingRegression

end GameTheory
