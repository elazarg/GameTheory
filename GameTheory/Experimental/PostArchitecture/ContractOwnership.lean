/-
# Canonical principal-agent ownership regression

The stochastic fixture exercises the shared principal-agent model and its
operation-local payoff guards.
-/

import GameTheory.Mechanism.PrincipalAgent
import GameTheory.Math.Probability.Expectation
import GameTheory.Math.Probability.Mixture

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.ContractOwnership

open GameTheory.Math.Probability
open GameTheory.Mechanism

namespace Hostile

/-- The productive action succeeds fairly; the safe action deterministically fails. -/
def environment : PrincipalAgent Bool Bool where
  outcomeLaw action :=
    if action then
      mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure false) (PMF.pure true)
    else PMF.pure false
  reward outcome := if outcome then 4 else 0
  cost action := if action then 1 else 0

def zeroPayment : Bool → ℝ := fun _ => 0

def successBonus : Bool → ℝ := fun outcome => if outcome then 3 else 0

theorem paymentIntegrable (action : Bool) :
    PayoffIntegrable (environment.outcomeLaw action) successBonus :=
  payoffIntegrable_of_finite _ _

theorem zeroPaymentIntegrable (action : Bool) :
    PayoffIntegrable (environment.outcomeLaw action) zeroPayment :=
  payoffIntegrable_of_finite _ _

theorem rewardIntegrable (action : Bool) :
    PayoffIntegrable (environment.outcomeLaw action) environment.reward :=
  payoffIntegrable_of_finite _ _

theorem bonusNetIntegrable (action : Bool) :
    PayoffIntegrable (environment.outcomeLaw action)
      (fun outcome => environment.reward outcome - successBonus outcome) :=
  payoffIntegrable_of_finite _ _

theorem expectedPayment_zero (action : Bool) :
    environment.expectedPayment zeroPayment action
      (zeroPaymentIntegrable action) = 0 := by
  rw [PrincipalAgent.expectedPayment]
  exact expect_constant _ 0 (payoffIntegrable_constant _ 0)

theorem expectedPayment_bonus_safe :
    environment.expectedPayment successBonus false (paymentIntegrable false) = 0 := by
  rw [PrincipalAgent.expectedPayment, expect_eq_sum]
  norm_num [environment, successBonus, PMF.pure_apply]

theorem expectedPayment_bonus_productive :
    environment.expectedPayment successBonus true (paymentIntegrable true) = 3 / 2 := by
  rw [PrincipalAgent.expectedPayment, expect_eq_sum]
  norm_num [environment, successBonus, mix_apply, PMF.pure_apply]

theorem agentUtility_zero_safe :
    environment.agentUtility zeroPayment false (zeroPaymentIntegrable false) = 0 := by
  rw [PrincipalAgent.agentUtility, expectedPayment_zero]
  norm_num [environment]

theorem agentUtility_zero_productive :
    environment.agentUtility zeroPayment true (zeroPaymentIntegrable true) = -1 := by
  rw [PrincipalAgent.agentUtility, expectedPayment_zero]
  norm_num [environment]

theorem agentUtility_bonus_safe :
    environment.agentUtility successBonus false (paymentIntegrable false) = 0 := by
  rw [PrincipalAgent.agentUtility, expectedPayment_bonus_safe]
  norm_num [environment]

theorem agentUtility_bonus_productive :
    environment.agentUtility successBonus true (paymentIntegrable true) = 1 / 2 := by
  rw [PrincipalAgent.agentUtility, expectedPayment_bonus_productive]
  norm_num [environment]

theorem zero_incentivizes_safe : environment.IsIncentivized zeroPayment false := by
  refine ⟨zeroPaymentIntegrable, ?_⟩
  intro alternative
  cases alternative with
  | false => exact le_rfl
  | true => rw [agentUtility_zero_safe, agentUtility_zero_productive]; norm_num

theorem bonus_incentivizes_productive :
    environment.IsIncentivized successBonus true := by
  refine ⟨paymentIntegrable, ?_⟩
  intro alternative
  cases alternative with
  | false => rw [agentUtility_bonus_safe, agentUtility_bonus_productive]; norm_num
  | true => exact le_rfl

theorem bonus_limitedLiability : PrincipalAgent.IsLimitedLiability successBonus := by
  intro outcome
  cases outcome <;> norm_num [successBonus]

theorem productive_participates_quarter :
    environment.Participates (1 / 4) successBonus true := by
  exact ⟨paymentIntegrable true, by
    rw [PrincipalAgent.agentUtility, expectedPayment_bonus_productive]
    norm_num [environment]⟩

theorem productive_rejects_three_quarters :
    ¬environment.Participates (3 / 4) successBonus true := by
  rintro ⟨hpayment, hparticipates⟩
  have heq : hpayment = paymentIntegrable true := Subsingleton.elim _ _
  rw [heq, PrincipalAgent.agentUtility, expectedPayment_bonus_productive] at hparticipates
  norm_num [environment] at hparticipates

theorem bonus_has_participation_option :
    environment.OffersParticipation (1 / 4) successBonus :=
  ⟨true, productive_participates_quarter⟩

theorem productive_participates_from_incentives :
    environment.Participates (1 / 4) successBonus true :=
  environment.participates_of_offersParticipation_of_isIncentivized
    bonus_has_participation_option bonus_incentivizes_productive

theorem incentivized_action_exists :
    ∃ action, environment.IsIncentivized successBonus action := by
  exact environment.exists_incentivized successBonus paymentIntegrable

theorem productive_welfare_identity :
    environment.principalUtility successBonus true (bonusNetIntegrable true) +
        environment.agentUtility successBonus true (paymentIntegrable true) =
      environment.socialSurplus true (rewardIntegrable true) := by
  exact environment.principalUtility_add_agentUtility successBonus true
    (rewardIntegrable true) (paymentIntegrable true) (bonusNetIntegrable true)

def negativeControl : PrincipalAgent Unit Bool where
  outcomeLaw _ := PMF.pure false
  reward _ := 0
  cost _ := 1

def negativePayment : Bool → ℝ := fun _ => 0

theorem negativePaymentIntegrable :
    PayoffIntegrable (negativeControl.outcomeLaw ()) negativePayment :=
  payoffIntegrable_of_finite _ _

theorem negative_limitedLiability : PrincipalAgent.IsLimitedLiability negativePayment := by
  intro outcome
  simp [negativePayment]

theorem negative_incentivized :
    negativeControl.IsIncentivized negativePayment () := by
  refine ⟨fun _ => negativePaymentIntegrable, ?_⟩
  intro alternative
  cases alternative
  exact le_rfl

theorem negative_not_participating :
    ¬negativeControl.Participates 0 negativePayment () := by
  rintro ⟨hpayment, hparticipates⟩
  have hproof : hpayment = negativePaymentIntegrable := Subsingleton.elim _ _
  rw [hproof, PrincipalAgent.agentUtility, PrincipalAgent.expectedPayment] at hparticipates
  have hvalue : expect (negativeControl.outcomeLaw ()) negativePayment hpayment = 0 := by
    rw [expect_proof_irrel _ _ hpayment (payoffIntegrable_constant _ 0)]
    exact expect_constant _ 0 (payoffIntegrable_constant _ 0)
  rw [hvalue] at hparticipates
  norm_num [negativeControl] at hparticipates

end Hostile

end GameTheory.Experimental.PostArchitecture.ContractOwnership
