/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticQuantileNashificationAlternative
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Quitting.Cycles.PeriodOneTangentAtlas

/-!
# Endpoint control at a quantile debt vertex

The singleton-clock support budget controls complementary debt, but by itself
does not control the owner's singleton slack.  The missing endpoint estimate
comes from multiplying the owner's exact Nash inequality by its quit rate.
The resulting error is supported only on collisions involving the owner, and
hence is paid by the same collision budget.

Consequently, at a positive minimum-debt scale, a preserved singleton clock
forces both complementary debt and singleton slack to zero as the debt excess
vanishes.  Thus the apparent "full-debt vertex without endpoint control"
branch cannot persist independently of the exact solo gate.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The probability that `who` quits while some opponent also quits is at
most the total collision mass.  This is the product-law incidence estimate
needed to turn an owner's endpoint error into collision charge. -/
theorem quittingRoot_quitProbability_mul_opponentAbsorptionMass_le_collisionMass
    (root : ι → PMF Bool) (who : ι) :
    (root who true).toReal *
        quittingRootOpponentAbsorptionMass root who ≤
      quittingRootCollisionMass root := by
  let x : ι → ℝ := quittingRootQuitRates root
  let opponents : Finset ι := Finset.univ.erase who
  have hwho : who ∉ opponents := by simp [opponents]
  have huniv : insert who opponents = (Finset.univ : Finset ι) := by
    exact Finset.insert_erase (Finset.mem_univ who)
  have hx0 : ∀ player ∈ opponents, 0 ≤ x player := by
    intro player _
    exact ENNReal.toReal_nonneg
  have hx1 : ∀ player ∈ opponents, x player ≤ 1 := by
    intro player _
    dsimp only [x, quittingRootQuitRates]
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      ((root player).coe_le_one true)
  have hopponentsCollision :
      0 ≤ collisionMassFormulaOn x opponents :=
    collisionMassFormulaOn_nonneg x opponents hx0 hx1
  have hquitLe : x who ≤ 1 := by
    dsimp only [x, quittingRootQuitRates]
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      ((root who).coe_le_one true)
  have hforced :
      quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) =
        ∏ player ∈ opponents, (1 - x player) := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability,
      ← Finset.mul_prod_erase Finset.univ
        (fun player ↦
          (Function.update root who (PMF.pure false) player false).toReal)
        (Finset.mem_univ who)]
    have hpure : ((PMF.pure false) false).toReal = (1 : ℝ) := by simp
    rw [Function.update_self, hpure, one_mul]
    apply Finset.prod_congr rfl
    intro player hplayer
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hplayer)]
    have hprobability :=
      quittingRoot_continueProbability_add_quitProbability root player
    dsimp only [x, quittingRootQuitRates]
    linarith
  have hrec := collisionMassFormulaOn_insert x hwho
  rw [huniv] at hrec
  have hcollisionFormula :
      quittingRootCollisionMass root =
        collisionMassFormulaOn x Finset.univ := by
    unfold quittingRootCollisionMass
    rw [collisionMass_eq_one_sub_continueMass_sub_singletonMass]
    rfl
  rw [hcollisionFormula, hrec]
  unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  rw [hforced]
  dsimp only [x, quittingRootQuitRates]
  exact le_add_of_nonneg_left
    (mul_nonneg (sub_nonneg.mpr hquitLe) hopponentsCollision)

/-- Quantitative owner-endpoint control.  For an exact Nash root above a
minimum semantic pair, collision charge controls the singleton mass times
the complete prescribed singleton gap, including both complementary debt
and singleton slack. -/
theorem exactNash_preservedSingletonClock_mul_singletonGap_le_collision
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingRootCoalitionMass root {owner} *
        (pair.1 owner - reward (quittingSingletonTerminal owner) owner) ≤
      2 * M * quittingRootCollisionMass root := by
  let opponentAbsorption := quittingRootOpponentAbsorptionMass root owner
  let opponentContinue := quittingRootOpponentContinueMass root owner
  let joining := quittingOutsiderJoiningContribution reward root owner
  let quit := (root owner true).toReal
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward pair.1 root).mpr hnash
  have hendpointLower :
      0 ≤ quit * quittingRootEndpointDifference reward pair.1 root owner := by
    simpa [quit] using (hendpoint owner).2
  have hdecomposition :=
    quittingRootEndpointDifference_eq_outsiderNever
      reward pair.1 root owner
  have hopponentComplement : opponentContinue = 1 - opponentAbsorption :=
    quittingRootOpponentContinueMass_eq_one_sub_absorptionMass root owner
  have hjoining : joining ≤ 2 * M * opponentAbsorption := by
    change quittingOutsiderJoiningContribution reward root owner ≤
      2 * M * quittingRootAbsorptionMass
        (Function.update root owner (PMF.pure false))
    simpa [joining, opponentAbsorption,
      quittingRootOpponentAbsorptionMass] using
      quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
        reward root owner hM hreward
  have hgap :
      quit * opponentContinue *
          (pair.1 owner - reward (quittingSingletonTerminal owner) owner) ≤
        quit * joining := by
    change quittingRootEndpointDifference reward pair.1 root owner =
        (1 - opponentAbsorption) *
          (reward (quittingSingletonTerminal owner) owner - pair.1 owner) +
            joining at hdecomposition
    rw [← hopponentComplement] at hdecomposition
    rw [hdecomposition] at hendpointLower
    nlinarith
  have hquitNonneg : 0 ≤ quit := ENNReal.toReal_nonneg
  have hjoiningScaled : quit * joining ≤
      quit * (2 * M * opponentAbsorption) :=
    mul_le_mul_of_nonneg_left hjoining hquitNonneg
  have hcollision :=
    quittingRoot_quitProbability_mul_opponentAbsorptionMass_le_collisionMass
      root owner
  have htwoMNonneg : 0 ≤ 2 * M := by positivity
  have hcollisionScaled :
      2 * M * (quit * opponentAbsorption) ≤
        2 * M * quittingRootCollisionMass root :=
    mul_le_mul_of_nonneg_left (by simpa [quit, opponentAbsorption] using hcollision)
      htwoMNonneg
  have hsingleton :=
    quittingRootCoalitionMass_singleton_eq_opponentContinue_mul_quit
      root owner
  calc
    quittingRootCoalitionMass root {owner} *
          (pair.1 owner - reward (quittingSingletonTerminal owner) owner) =
        quit * opponentContinue *
          (pair.1 owner - reward (quittingSingletonTerminal owner) owner) := by
      rw [hsingleton]
      simp only [opponentContinue, quittingRootOpponentContinueMass]
      ring
    _ ≤ quit * joining := hgap
    _ ≤ quit * (2 * M * opponentAbsorption) := hjoiningScaled
    _ = 2 * M * (quit * opponentAbsorption) := by ring
    _ ≤ 2 * M * quittingRootCollisionMass root := hcollisionScaled

/-- Debt-excess form of endpoint control.  This is the quantitative bridge
for the quantile vertex branch: positive minimum debt and positive singleton
clock force the whole singleton gap, hence also the nonnegative singleton
slack, to vanish with the near-minimum excess. -/
theorem debtSum_mul_preservedSingletonClock_mul_singletonGap_le_twoM_mul_excess
    (base pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingTerminalSemanticDebtSum pair *
        (quittingRootCoalitionMass root {owner} *
          (pair.1 owner - reward (quittingSingletonTerminal owner) owner)) ≤
      2 * M *
        (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebtSum base) := by
  have hendpoint :=
    exactNash_preservedSingletonClock_mul_singletonGap_le_collision
      (reward := reward) pair root owner hM hreward hnash
  have hdebtNonneg : 0 ≤ quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hM hreward hpair who
  have hscaled := mul_le_mul_of_nonneg_left hendpoint hdebtNonneg
  have hbudget :=
    (exactNash_preservedSingletonClock_mul_complementDebt_le_excess
      (reward := reward) base pair root owner 0 hM hreward hminimum hpair
        hnash (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {owner})).2
  have htwoMNonneg : 0 ≤ 2 * M := by positivity
  have hbudgetScaled := mul_le_mul_of_nonneg_left hbudget htwoMNonneg
  calc
    quittingTerminalSemanticDebtSum pair *
          (quittingRootCoalitionMass root {owner} *
            (pair.1 owner - reward (quittingSingletonTerminal owner) owner)) ≤
        quittingTerminalSemanticDebtSum pair *
          (2 * M * quittingRootCollisionMass root) := hscaled
    _ = 2 * M * (quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root) := by ring
    _ ≤ 2 * M *
        (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebtSum base) := hbudgetScaled

/-- Floor-facing form of the vertex estimate.  Uniform positive lower bounds
on total debt and on the preserved singleton clock quantitatively pay the
owner's singleton slack.  No prior sign assumption on the near-minimizer's
slack is needed. -/
theorem debtFloor_mul_clockFloor_mul_singletonSlack_le_twoM_mul_excess
    (base pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (owner : ι)
    (debtFloor clockFloor : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hdebtFloorNonneg : 0 ≤ debtFloor)
    (hdebtFloor : debtFloor ≤ quittingTerminalSemanticDebtSum pair)
    (hclockFloorNonneg : 0 ≤ clockFloor)
    (hclockFloor : clockFloor ≤ quittingRootCoalitionMass root {owner}) :
    debtFloor * clockFloor *
        quittingTerminalSemanticSingletonSlack reward pair owner ≤
      2 * M *
        (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebtSum base) := by
  let gap := pair.1 owner -
    reward (quittingSingletonTerminal owner) owner
  let floor := debtFloor * clockFloor
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hcomplement : 0 ≤ quittingTerminalSemanticDebtSum pair -
      quittingTerminalSemanticDebt pair owner := by
    unfold quittingTerminalSemanticDebtSum
    exact sub_nonneg.mpr (Finset.single_le_sum
      (fun who _ => hdebtNonneg who) (Finset.mem_univ owner))
  have hgapIdentity :=
    minimumTerminalSemantic_singletonGap_eq_complementaryDebt_add_slack
      (reward := reward) pair owner
  have hslackLeGap :
      quittingTerminalSemanticSingletonSlack reward pair owner ≤ gap := by
    dsimp only [gap]
    linarith
  have hfloorNonneg : 0 ≤ floor :=
    mul_nonneg hdebtFloorNonneg hclockFloorNonneg
  have hrightNonneg : 0 ≤ 2 * M *
      (quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebtSum base) := by
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (hminimum pair hpair))
  have hmain :=
    debtSum_mul_preservedSingletonClock_mul_singletonGap_le_twoM_mul_excess
      (reward := reward) base pair root owner hM hreward hminimum hpair hnash
  by_cases hgap : 0 ≤ gap
  · have hmassNonneg : 0 ≤ quittingRootCoalitionMass root {owner} :=
      MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {owner}
    have hfloorLe : floor ≤
        quittingTerminalSemanticDebtSum pair *
          quittingRootCoalitionMass root {owner} := by
      dsimp only [floor]
      exact mul_le_mul hdebtFloor hclockFloor hclockFloorNonneg
        (le_trans hdebtFloorNonneg hdebtFloor)
    have hfloorGap : floor * gap ≤
        quittingTerminalSemanticDebtSum pair *
          quittingRootCoalitionMass root {owner} * gap :=
      mul_le_mul_of_nonneg_right hfloorLe hgap
    calc
      debtFloor * clockFloor *
            quittingTerminalSemanticSingletonSlack reward pair owner ≤
          floor * gap :=
        mul_le_mul_of_nonneg_left hslackLeGap hfloorNonneg
      _ ≤ quittingTerminalSemanticDebtSum pair *
            quittingRootCoalitionMass root {owner} * gap := hfloorGap
      _ ≤ 2 * M *
          (quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebtSum base) := by
        simpa [gap, mul_assoc] using hmain
  · have hgapNeg : gap < 0 := lt_of_not_ge hgap
    have hslackNeg :
        quittingTerminalSemanticSingletonSlack reward pair owner < 0 :=
      lt_of_le_of_lt hslackLeGap hgapNeg
    have hleftNonpos : debtFloor * clockFloor *
        quittingTerminalSemanticSingletonSlack reward pair owner ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hfloorNonneg hslackNeg.le
    exact hleftNonpos.trans hrightNonneg

/-- A visible positive singleton slack is therefore a quantitative
near-minimality separator.  In a quantile block with fixed positive debt and
clock floors, slack `eta` costs at least `debtFloor * clockFloor * eta` in
the collision/excess account. -/
theorem debtFloor_mul_clockFloor_mul_eta_le_twoM_mul_excess_of_slack
    (base pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (owner : ι)
    (debtFloor clockFloor eta : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hdebtFloorNonneg : 0 ≤ debtFloor)
    (hdebtFloor : debtFloor ≤ quittingTerminalSemanticDebtSum pair)
    (hclockFloorNonneg : 0 ≤ clockFloor)
    (hclockFloor : clockFloor ≤ quittingRootCoalitionMass root {owner})
    (heta : eta ≤
      quittingTerminalSemanticSingletonSlack reward pair owner) :
    debtFloor * clockFloor * eta ≤
      2 * M *
        (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebtSum base) := by
  have hslack :=
    debtFloor_mul_clockFloor_mul_singletonSlack_le_twoM_mul_excess
      (reward := reward) base pair root owner debtFloor clockFloor hM hreward
        hminimum hpair hnash hdebtFloorNonneg hdebtFloor hclockFloorNonneg
        hclockFloor
  have hfloorNonneg : 0 ≤ debtFloor * clockFloor :=
    mul_nonneg hdebtFloorNonneg hclockFloorNonneg
  exact (mul_le_mul_of_nonneg_left heta hfloorNonneg).trans hslack

end GameTheory
