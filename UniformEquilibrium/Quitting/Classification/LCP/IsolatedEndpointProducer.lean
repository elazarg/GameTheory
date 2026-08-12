/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.LaterLayerAbnormal
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium
import GameTheory.Concepts.Stochastic.Models.Quitting.RootPerturbation

/-!
# Repairing an isolated absorbing endpoint

An exact absorbing solo-quitter row can fail terminal Nash only for its
owner: if every opponent Continues, the owner may refuse forever and obtain
zero.  Recursive normality supplies a distinct blocker whose singleton exit
does not improve that refusal value.  Giving the blocker an arbitrarily small
positive hazard makes every unilateral problem contract.

The owner's original hazard is retained.  Consequently every inactive
player's exact joining inequality survives, up to only the total-variation
error caused by the blocker's new marginal.  The stationary payoff moves by
at most the same small hazard divided by the owner's fixed positive hazard.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Add a small blocker hazard to a fixed absorbing solo-owner row. -/
def isolatedEndpointThreatRoot (owner blocker : ι) (hazard : PMF Bool)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) : ι → PMF Bool :=
  Function.update (quittingSoloStationaryRoot owner hazard) blocker
    (quittingHazardCoin eta heta0 heta1)

omit [Fintype ι] in
@[simp] theorem isolatedEndpointThreatRoot_owner
    {owner blocker : ι} (hne : blocker ≠ owner) (hazard : PMF Bool)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    isolatedEndpointThreatRoot owner blocker hazard eta heta0 heta1 owner =
      hazard := by
  simp [isolatedEndpointThreatRoot, quittingSoloStationaryRoot, Ne.symm hne]

omit [Fintype ι] in
@[simp] theorem isolatedEndpointThreatRoot_blocker
    (owner blocker : ι) (hazard : PMF Bool)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    isolatedEndpointThreatRoot owner blocker hazard eta heta0 heta1 blocker =
      quittingHazardCoin eta heta0 heta1 := by
  simp [isolatedEndpointThreatRoot]

omit [Fintype ι] in
theorem isolatedEndpointThreatRoot_other
    {owner blocker other : ι} (howner : other ≠ owner)
    (hblocker : other ≠ blocker) (hazard : PMF Bool)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    isolatedEndpointThreatRoot owner blocker hazard eta heta0 heta1 other =
      PMF.pure false := by
  simp [isolatedEndpointThreatRoot, quittingSoloStationaryRoot,
    howner, hblocker]

omit [Fintype ι] in
theorem update_isolatedEndpointThreatRoot_owner_continue
    {owner blocker : ι} (hne : blocker ≠ owner) (hazard : PMF Bool)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    Function.update
        (isolatedEndpointThreatRoot owner blocker hazard eta heta0 heta1)
        owner (PMF.pure false) =
      quittingSoloStationaryRoot blocker
        (quittingHazardCoin eta heta0 heta1) := by
  unfold isolatedEndpointThreatRoot quittingSoloStationaryRoot
  rw [Function.update_comm hne, Function.update_idem]
  simp

omit [Fintype ι] in
theorem update_isolatedEndpointThreatRoot_blocker_continue
    {owner blocker : ι} (hne : blocker ≠ owner) (hazard : PMF Bool)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    Function.update
        (isolatedEndpointThreatRoot owner blocker hazard eta heta0 heta1)
        blocker (PMF.pure false) =
      quittingSoloStationaryRoot owner hazard := by
  unfold isolatedEndpointThreatRoot
  rw [Function.update_idem]
  rw [← quittingSoloStationaryRoot_apply_other hne hazard]
  exact Function.update_eq_self blocker _

omit [Fintype ι] in
theorem update_isolatedEndpointThreatRoot_other_continue
    {owner blocker other : ι} (howner : other ≠ owner)
    (hblocker : other ≠ blocker) (hazard : PMF Bool)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    Function.update
        (isolatedEndpointThreatRoot owner blocker hazard eta heta0 heta1)
        other (PMF.pure false) =
      isolatedEndpointThreatRoot owner blocker hazard eta heta0 heta1 := by
  rw [← isolatedEndpointThreatRoot_other howner hblocker
    hazard eta heta0 heta1]
  exact Function.update_eq_self other _

/-- Joint survival of the owner/blocker repair row. -/
theorem isolatedEndpointThreatRoot_continueMass
    {owner blocker : ι} (hne : blocker ≠ owner) (hazard : PMF Bool)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    quittingStationaryContinueMass
        (isolatedEndpointThreatRoot owner blocker hazard eta heta0 heta1) =
      (1 - eta) * (hazard false).toReal := by
  rw [quittingStationaryContinueMass_eq_forcedContinue_mul_own
    (isolatedEndpointThreatRoot owner blocker hazard eta heta0 heta1) owner,
    update_isolatedEndpointThreatRoot_owner_continue hne,
    quittingStationaryContinueMass_solo,
    isolatedEndpointThreatRoot_owner hne,
    quittingHazardCoin_false_toReal]

/-- Deleting the owner leaves exactly the blocker's small hazard. -/
theorem isolatedEndpointThreatRoot_owner_opponentAbsorption
    {owner blocker : ι} (hne : blocker ≠ owner) (hazard : PMF Bool)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    quittingRootOpponentAbsorptionMass
        (isolatedEndpointThreatRoot owner blocker hazard eta heta0 heta1)
        owner = eta := by
  unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  rw [update_isolatedEndpointThreatRoot_owner_continue hne,
    quittingStationaryContinueMass_solo,
    quittingHazardCoin_false_toReal]
  ring

/-- The repaired row absorbs at least as fast as its fixed owner hazard. -/
theorem isolatedEndpointThreatRoot_ownerHazard_le_absorption
    {owner blocker : ι} (hne : blocker ≠ owner) (hazard : PMF Bool)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    (hazard true).toReal ≤ quittingRootAbsorptionMass
      (isolatedEndpointThreatRoot owner blocker hazard eta heta0 heta1) := by
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (fun _ : Unit => hazard) ()
  rw [quittingRootAbsorptionMass,
    isolatedEndpointThreatRoot_continueMass hne]
  have hfalse0 : 0 ≤ (hazard false).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg heta0 hfalse0]

/-- Every unilateral problem contracts after the blocker receives positive
hazard. -/
theorem isolatedEndpointThreatRoot_fixedOpponents_contracts
    {owner blocker : ι} (hne : blocker ≠ owner) (hazard : PMF Bool)
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (howner : 0 < (hazard true).toReal) :
    ∀ who, quittingStationaryFixedOpponentsContinueMass
      (isolatedEndpointThreatRoot owner blocker hazard eta heta.le heta1) who < 1 := by
  intro who
  by_cases hwho : who = owner
  · subst who
    change quittingStationaryContinueMass
      (Function.update
        (isolatedEndpointThreatRoot owner blocker hazard eta heta.le heta1)
        owner (PMF.pure false)) < 1
    rw [update_isolatedEndpointThreatRoot_owner_continue hne,
      quittingStationaryContinueMass_solo,
      quittingHazardCoin_false_toReal]
    linarith
  · change quittingStationaryContinueMass
      (Function.update
        (isolatedEndpointThreatRoot owner blocker hazard eta heta.le heta1)
        who (PMF.pure false)) < 1
    have hle := quittingStationaryContinueMass_le_ownContinueProbability
      (Function.update
        (isolatedEndpointThreatRoot owner blocker hazard eta heta.le heta1)
        who (PMF.pure false)) owner
    have hvalue :
        (Function.update
          (isolatedEndpointThreatRoot owner blocker hazard eta heta.le heta1)
          who (PMF.pure false)) owner = hazard := by
      rw [Function.update]
      simp only [Ne.symm hwho, ↓reduceDIte]
      exact isolatedEndpointThreatRoot_owner hne hazard eta heta.le heta1
    rw [hvalue] at hle
    have hsum := quittingRoot_continueProbability_add_quitProbability
      (fun _ : Unit => hazard) ()
    linarith

/-- The TV distance from an `eta`-hazard coin to pure Continue is `eta`. -/
theorem pmfTV_quittingHazardCoin_pure_false
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    pmfTV (quittingHazardCoin eta heta0 heta1) (PMF.pure false) = eta := by
  unfold pmfTV pmfPositiveVariation
  rw [Fintype.sum_bool]
  simp [quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal,
    heta0]

/-- The repaired stationary payoff stays close to the original owner's solo
vector. -/
theorem abs_isolatedEndpointThreat_terminalPayoff_sub_ownerSolo_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : blocker ≠ owner) (hazard : PMF Bool)
    {eta M : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (howner : 0 < (hazard true).toReal) (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (who : ι) :
    |quittingTerminalPayoff reward
          (quittingStationaryProfile reward
            (isolatedEndpointThreatRoot owner blocker hazard eta heta.le heta1)) who -
        quittingSoloReward reward owner who| ≤
      2 * M * eta / (hazard true).toReal := by
  let root := isolatedEndpointThreatRoot owner blocker hazard eta heta.le heta1
  let absorption := quittingRootAbsorptionMass root
  have habsLower := isolatedEndpointThreatRoot_ownerHazard_le_absorption
    hne hazard eta heta.le heta1
  have habs : 0 < absorption := lt_of_lt_of_le howner habsLower
  have hcontinue : quittingStationaryContinueMass root < 1 := by
    unfold absorption quittingRootAbsorptionMass at habs
    linarith
  have hanchor :=
    abs_quittingRootAbsorbingContribution_sub_absorption_mul_solo_le
      (reward := reward) root owner who hM hreward
  rw [isolatedEndpointThreatRoot_owner_opponentAbsorption hne] at hanchor
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div
    reward root who hcontinue]
  have hrearrange :
      quittingRootAbsorbingContribution reward root who /
            (1 - quittingStationaryContinueMass root) -
          quittingSoloReward reward owner who =
        (quittingRootAbsorbingContribution reward root who -
            absorption * quittingSoloReward reward owner who) / absorption := by
    have hdenEq : 1 - quittingStationaryContinueMass root = absorption := rfl
    rw [hdenEq]
    calc
      _ = quittingRootAbsorbingContribution reward root who / absorption -
          (absorption * quittingSoloReward reward owner who) / absorption := by
        rw [mul_div_cancel_left₀ _ habs.ne']
      _ = _ := (sub_div _ _ _).symm
  rw [hrearrange, abs_div, abs_of_pos habs]
  have hquotient : eta / absorption ≤ eta / (hazard true).toReal :=
    div_le_div_of_nonneg_left heta.le howner habsLower
  calc
    _ ≤ (2 * M * eta) / absorption :=
      (div_le_div_iff_of_pos_right habs).2 hanchor
    _ = (2 * M) * (eta / absorption) := by ring
    _ ≤ (2 * M) * (eta / (hazard true).toReal) :=
      mul_le_mul_of_nonneg_left hquotient (by positivity)
    _ = 2 * M * eta / (hazard true).toReal := by ring

/-- Adding the blocker changes every immediate-Quit value by at most
`2 M eta`. -/
theorem abs_isolatedEndpointThreat_quitValue_sub_soloRoot_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : blocker ≠ owner) (hazard : PMF Bool)
    {eta M : ℝ} (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (who : ι) :
    |quittingStationaryFixedOpponentsQuitValue reward
          (isolatedEndpointThreatRoot owner blocker hazard eta heta0 heta1) who -
        quittingStationaryFixedOpponentsQuitValue reward
          (quittingSoloStationaryRoot owner hazard) who| ≤ 2 * M * eta := by
  classical
  by_cases hwho : who = blocker
  · subst who
    have hnonneg : 0 ≤ 2 * M * eta := by positivity
    simpa [quittingStationaryFixedOpponentsQuitValue,
      quittingFixedOpponentsQuitValue,
      isolatedEndpointThreatRoot] using hnonneg
  · have hperturb := abs_quittingRootExpectedPayoff_update_sub_le
      reward (0 : Payoff ι)
      (Function.update (quittingSoloStationaryRoot owner hazard) who
        (PMF.pure true)) blocker
      (quittingHazardCoin eta heta0 heta1) (PMF.pure false) who
      hM hreward (by intro; simpa using hM)
      (show pmfTV (quittingHazardCoin eta heta0 heta1) (PMF.pure false) ≤ eta by
        rw [pmfTV_quittingHazardCoin_pure_false])
    have hfirst :
        Function.update
            (Function.update (quittingSoloStationaryRoot owner hazard) who
              (PMF.pure true)) blocker
              (quittingHazardCoin eta heta0 heta1) =
          Function.update
            (Function.update (quittingSoloStationaryRoot owner hazard) blocker
              (quittingHazardCoin eta heta0 heta1)) who (PMF.pure true) :=
      Function.update_comm hwho _ _ _
    have hsecond :
        Function.update
            (Function.update (quittingSoloStationaryRoot owner hazard) who
              (PMF.pure true)) blocker (PMF.pure false) =
          Function.update (quittingSoloStationaryRoot owner hazard) who
            (PMF.pure true) := by
      rw [Function.update_comm hwho]
      rw [← quittingSoloStationaryRoot_apply_other hne hazard]
      rw [Function.update_eq_self]
    rw [hfirst, hsecond] at hperturb
    simpa [quittingStationaryFixedOpponentsQuitValue,
      quittingFixedOpponentsQuitValue,
      quittingRootExpectedPayoff_eq_absorbingContribution_add,
      isolatedEndpointThreatRoot, quittingSoloStationaryRoot,
      hwho] using hperturb

/-- A normal blocker repairs any exact absorbing isolated endpoint into
terminal approximate equilibria at every accuracy. -/
theorem terminalNash_all_errors_of_isolatedEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : blocker ≠ owner) (hazard : PMF Bool)
    (howner : 0 < (hazard true).toReal)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard))
    (hblocker : quittingSoloReward reward blocker owner ≤
      quittingSoloReward reward owner owner) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) epsilon profile := by
  intro epsilon hepsilon
  let M := quittingRewardBound reward
  let coefficient := 2 * M + 2 * M / (hazard true).toReal
  let eta := epsilon / (coefficient + epsilon)
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  have hden : 0 < coefficient + epsilon := by positivity
  have heta : 0 < eta := div_pos hepsilon hden
  have heta1 : eta ≤ 1 := (div_le_one hden).2 (by
    dsimp only [coefficient]
    nlinarith)
  have herror : coefficient * eta < epsilon := by
    calc
      coefficient * eta < (coefficient + epsilon) * eta :=
        mul_lt_mul_of_pos_right (by linarith) heta
      _ = epsilon := by
        dsimp only [eta]
        exact mul_div_cancel₀ epsilon hden.ne'
  let root := isolatedEndpointThreatRoot owner blocker hazard eta heta.le heta1
  let payoff := fun who => quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) who
  refine ⟨quittingStationaryProfile reward root, ?_⟩
  have hnashCoefficient :
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (coefficient * eta)
        (quittingStationaryProfile reward root) := by
    apply isεAsymptoticNash_stationary_of_unilateralCap_le
    · exact isolatedEndpointThreatRoot_fixedOpponents_contracts
        hne hazard heta heta1 howner
    · intro who
      unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
      apply max_le
      · have hbase : quittingStationaryFixedOpponentsQuitValue reward
          (quittingSoloStationaryRoot owner hazard) who ≤
        quittingSoloReward reward owner who := by
          have hnashRoot :=
            (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
              reward (quittingSoloReward reward owner)
                (quittingSoloStationaryRoot owner hazard)).1 hnash
          have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
            reward (quittingSoloReward reward owner)
              (quittingSoloStationaryRoot owner hazard) who hnashRoot
          have hfixed := quittingRootSuccessorPayoff_soloStationaryRoot_self
            reward owner hazard
          rw [congrFun hfixed who] at hquit
          unfold quittingRootQuitPayoff at hquit
          rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
            quittingStationaryContinueMass_update_pure_true_eq_zero,
            zero_mul, add_zero] at hquit
          exact hquit
        have hquitClose := abs_isolatedEndpointThreat_quitValue_sub_soloRoot_le
          reward hne hazard heta.le heta1 hM
          (abs_reward_le_quittingRewardBound reward) who
        have hpayoffClose :=
          abs_isolatedEndpointThreat_terminalPayoff_sub_ownerSolo_le
          reward hne hazard heta heta1 howner hM
          (abs_reward_le_quittingRewardBound reward) who
        have hquitUpper := (abs_le.mp hquitClose).2
        have hpayoffLower := (abs_le.mp hpayoffClose).1
        have hbudget :
            2 * M * eta + 2 * M * eta / (hazard true).toReal =
              coefficient * eta := by
          dsimp only [coefficient]
          ring
        dsimp only [root, payoff]
        linarith [hbudget]
      · change
          quittingStationaryNeverValue
              (quittingRootAbsorbingContribution reward
                (Function.update root who (PMF.pure false)) who)
              (quittingStationaryContinueMass
                (Function.update root who (PMF.pure false))) ≤
            payoff who + coefficient * eta
        by_cases hwhoOwner : who = owner
        · subst who
          have hpayoffClose :=
            abs_isolatedEndpointThreat_terminalPayoff_sub_ownerSolo_le
            reward hne hazard heta heta1 howner hM
            (abs_reward_le_quittingRewardBound reward) owner
          have hpayoffLower := (abs_le.mp hpayoffClose).1
          change
            quittingStationaryNeverValue
                (quittingRootAbsorbingContribution reward
                  (Function.update
                    (isolatedEndpointThreatRoot owner blocker hazard eta
                      heta.le heta1)
                    owner (PMF.pure false)) owner)
                (quittingStationaryContinueMass
                  (Function.update
                    (isolatedEndpointThreatRoot owner blocker hazard eta
                      heta.le heta1)
                    owner (PMF.pure false))) ≤ _
          rw [update_isolatedEndpointThreatRoot_owner_continue hne,
          quittingRootAbsorbingContribution_solo,
          quittingStationaryContinueMass_solo,
          quittingHazardCoin_true_toReal,
          quittingHazardCoin_false_toReal]
          unfold quittingStationaryNeverValue
          rw [show 1 - (1 - eta) = eta by ring,
          mul_div_cancel_left₀ _ heta.ne']
          have hbudget :
              2 * M * eta + 2 * M * eta / (hazard true).toReal =
                coefficient * eta := by
            dsimp only [coefficient]
            ring
          dsimp only [root, payoff]
          linarith [hblocker, hbudget, mul_nonneg hM heta.le]
        · by_cases hwhoBlocker : who = blocker
          · subst who
            have hpayoffClose :=
              abs_isolatedEndpointThreat_terminalPayoff_sub_ownerSolo_le
              reward hne hazard heta heta1 howner hM
              (abs_reward_le_quittingRewardBound reward) blocker
            have hpayoffLower := (abs_le.mp hpayoffClose).1
            change
              quittingStationaryNeverValue
                  (quittingRootAbsorbingContribution reward
                    (Function.update
                      (isolatedEndpointThreatRoot owner blocker hazard eta
                        heta.le heta1)
                      blocker (PMF.pure false)) blocker)
                  (quittingStationaryContinueMass
                    (Function.update
                      (isolatedEndpointThreatRoot owner blocker hazard eta
                        heta.le heta1)
                      blocker (PMF.pure false))) ≤ _
            rw [update_isolatedEndpointThreatRoot_blocker_continue hne,
            quittingRootAbsorbingContribution_solo,
            quittingStationaryContinueMass_solo]
            unfold quittingStationaryNeverValue
            have hsum := quittingRoot_continueProbability_add_quitProbability
              (fun _ : Unit => hazard) ()
            rw [show 1 - (hazard false).toReal = (hazard true).toReal by linarith,
            mul_div_cancel_left₀ _ howner.ne']
            have hbudget :
                2 * M * eta + 2 * M * eta / (hazard true).toReal =
                  coefficient * eta := by
              dsimp only [coefficient]
              ring
            dsimp only [root, payoff]
            linarith [hbudget, mul_nonneg hM heta.le]
          · have hupdate := update_isolatedEndpointThreatRoot_other_continue
              hwhoOwner hwhoBlocker hazard eta heta.le heta1
            rw [hupdate]
            unfold quittingStationaryNeverValue
            have hcontinue : quittingStationaryContinueMass root < 1 := by
              have hcontracts := isolatedEndpointThreatRoot_fixedOpponents_contracts
                hne hazard heta heta1 howner who
              change quittingStationaryContinueMass
                (Function.update root who (PMF.pure false)) < 1 at hcontracts
              rw [hupdate] at hcontracts
              exact hcontracts
            rw [← quittingTerminalPayoff_stationary_eq_absorbingContribution_div
              reward root who hcontinue]
            exact le_add_of_nonneg_right
              (mul_nonneg hcoefficient heta.le)
  exact hnashCoefficient.mono herror.le

/-- Strategic closure of the isolated endpoint repair. -/
theorem exists_uniformEquilibriumPayoff_of_isolatedEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : blocker ≠ owner) (hazard : PMF Bool)
    (howner : 0 < (hazard true).toReal)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard))
    (hblocker : quittingSoloReward reward blocker owner ≤
      quittingSoloReward reward owner owner) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  exact terminalNash_all_errors_of_isolatedEndpoint
    reward hne hazard howner hnash hblocker

end QuittingLCPClassification
end GameTheory
