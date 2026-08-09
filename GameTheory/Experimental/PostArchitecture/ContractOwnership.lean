/-
# Finite hidden-action contract ownership experiment

This hostile slice tests a native role-asymmetric principal-agent model over
finite-support outcome laws.  It deliberately does not manufacture strategic
players or reuse auction-specific allocation data.
-/

import GameTheory.Probability.FinDist

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.ContractOwnership

open Probability

universe uAction uOutcome

/-- Candidate capability-free data for a hidden-action environment. -/
structure PrincipalAgentCandidate (Action : Type uAction) (Outcome : Type uOutcome) where
  outcomeLaw : Action → FinDist Outcome
  reward : Outcome → ℝ
  cost : Action → ℝ

namespace PrincipalAgentCandidate

variable {Action : Type uAction} {Outcome : Type uOutcome}
variable (I : PrincipalAgentCandidate Action Outcome)

/-- Expected transfer received by the agent. -/
def expectedPayment (payment : Outcome → ℝ) (action : Action) : ℝ :=
  (I.outcomeLaw action).expect payment

/-- The risk-neutral agent's expected transfer less effort cost. -/
def agentUtility (payment : Outcome → ℝ) (action : Action) : ℝ :=
  I.expectedPayment payment action - I.cost action

/-- The principal's expected reward net of the transfer. -/
def principalUtility (payment : Outcome → ℝ) (action : Action) : ℝ :=
  (I.outcomeLaw action).expect fun outcome => I.reward outcome - payment outcome

/-- Expected gross reward before transfers. -/
def expectedReward (action : Action) : ℝ :=
  (I.outcomeLaw action).expect I.reward

/-- Expected reward net of effort cost. -/
def socialSurplus (action : Action) : ℝ :=
  I.expectedReward action - I.cost action

/-- An incentivized action weakly maximizes the agent's utility. -/
def IsIncentivized (payment : Outcome → ℝ) (action : Action) : Prop :=
  ∀ alternative, I.agentUtility payment alternative ≤ I.agentUtility payment action

/-- Participation compares the selected action with an explicit outside option. -/
def Participates (outsideOption : ℝ) (payment : Outcome → ℝ) (action : Action) : Prop :=
  outsideOption ≤ I.agentUtility payment action

/-- The contract offers at least one action that meets the outside option. -/
def HasParticipationOption (outsideOption : ℝ) (payment : Outcome → ℝ) : Prop :=
  ∃ action, I.Participates outsideOption payment action

/-- Transfers only split social surplus between principal and agent. -/
theorem principalUtility_add_agentUtility (payment : Outcome → ℝ) (action : Action) :
    I.principalUtility payment action + I.agentUtility payment action =
      I.socialSurplus action := by
  simp only [principalUtility, agentUtility, expectedPayment, socialSurplus, expectedReward]
  rw [show (fun outcome => I.reward outcome - payment outcome) =
      (fun outcome => I.reward outcome + (-1) * payment outcome) from
        funext fun outcome => by ring]
  rw [FinDist.expect_add, FinDist.expect_smul]
  ring

/-- A finite nonempty action set has an agent-optimal action. -/
theorem exists_incentivized [Finite Action] [Nonempty Action] (payment : Outcome → ℝ) :
    ∃ action, I.IsIncentivized payment action := by
  obtain ⟨action, hmax⟩ := Finite.exists_max (I.agentUtility payment)
  exact ⟨action, hmax⟩

/-- Any optimal action participates when the contract offers an acceptable fallback. -/
theorem participates_of_isIncentivized
    {outsideOption : ℝ} {payment : Outcome → ℝ} {action : Action}
    (hoption : I.HasParticipationOption outsideOption payment)
    (hincentivized : I.IsIncentivized payment action) :
    I.Participates outsideOption payment action := by
  obtain ⟨fallback, hfallback⟩ := hoption
  exact hfallback.trans (hincentivized fallback)

end PrincipalAgentCandidate

/-- Limited liability prevents a contract from charging the agent. -/
def LimitedLiability {Outcome : Type uOutcome} (payment : Outcome → ℝ) : Prop :=
  ∀ outcome, 0 ≤ payment outcome

/-! ## Hostile stochastic fixture -/

namespace Hostile

/-- The productive action succeeds fairly; the safe action deterministically fails. -/
def environment : PrincipalAgentCandidate Bool Bool where
  outcomeLaw action :=
    if action then
      FinDist.mix (1 / 2) (by norm_num) (by norm_num)
        (FinDist.pure false) (FinDist.pure true)
    else
      FinDist.pure false
  reward outcome := if outcome then 4 else 0
  cost action := if action then 1 else 0

/-- No transfer makes the safe action uniquely attractive. -/
def zeroPayment : Bool → ℝ := fun _ => 0

/-- A success bonus makes the costly productive action uniquely attractive. -/
def successBonus : Bool → ℝ := fun outcome => if outcome then 3 else 0

theorem expectedPayment_zero (action : Bool) :
    environment.expectedPayment zeroPayment action = 0 := by
  unfold PrincipalAgentCandidate.expectedPayment zeroPayment
  exact FinDist.expect_const _ 0

theorem expectedPayment_bonus_safe :
    environment.expectedPayment successBonus false = 0 := by
  simp [PrincipalAgentCandidate.expectedPayment, environment, successBonus]

theorem expectedPayment_bonus_productive :
    environment.expectedPayment successBonus true = 3 / 2 := by
  simp [PrincipalAgentCandidate.expectedPayment, environment, successBonus,
    FinDist.expect_mix]
  norm_num

theorem agentUtility_zero_safe : environment.agentUtility zeroPayment false = 0 := by
  rw [PrincipalAgentCandidate.agentUtility, expectedPayment_zero]
  norm_num [environment]

theorem agentUtility_zero_productive : environment.agentUtility zeroPayment true = -1 := by
  rw [PrincipalAgentCandidate.agentUtility, expectedPayment_zero]
  norm_num [environment]

theorem agentUtility_bonus_safe : environment.agentUtility successBonus false = 0 := by
  rw [PrincipalAgentCandidate.agentUtility, expectedPayment_bonus_safe]
  norm_num [environment]

theorem agentUtility_bonus_productive :
    environment.agentUtility successBonus true = 1 / 2 := by
  rw [PrincipalAgentCandidate.agentUtility, expectedPayment_bonus_productive]
  norm_num [environment]

theorem zero_incentivizes_safe : environment.IsIncentivized zeroPayment false := by
  intro alternative
  cases alternative <;>
    norm_num [agentUtility_zero_safe, agentUtility_zero_productive]

theorem bonus_incentivizes_productive :
    environment.IsIncentivized successBonus true := by
  intro alternative
  cases alternative <;>
    norm_num [agentUtility_bonus_safe, agentUtility_bonus_productive]

theorem bonus_limitedLiability : LimitedLiability successBonus := by
  intro outcome
  cases outcome <;> norm_num [successBonus]

theorem productive_participates_quarter :
    environment.Participates (1 / 4) successBonus true := by
  norm_num [PrincipalAgentCandidate.Participates, agentUtility_bonus_productive]

theorem productive_rejects_three_quarters :
    ¬environment.Participates (3 / 4) successBonus true := by
  norm_num [PrincipalAgentCandidate.Participates, agentUtility_bonus_productive]

theorem bonus_has_participation_option :
    environment.HasParticipationOption (1 / 4) successBonus :=
  ⟨true, productive_participates_quarter⟩

theorem productive_participates_from_incentives :
    environment.Participates (1 / 4) successBonus true :=
  environment.participates_of_isIncentivized
    bonus_has_participation_option bonus_incentivizes_productive

theorem incentivized_action_exists :
    ∃ action, environment.IsIncentivized successBonus action :=
  environment.exists_incentivized successBonus

theorem productive_welfare_identity :
    environment.principalUtility successBonus true +
        environment.agentUtility successBonus true =
      environment.socialSurplus true :=
  environment.principalUtility_add_agentUtility successBonus true

/-- Without an acceptable fallback, limited liability and optimality do not imply participation. -/
def negativeControl : PrincipalAgentCandidate Unit Bool where
  outcomeLaw _ := FinDist.pure false
  reward _ := 0
  cost _ := 1

def negativePayment : Bool → ℝ := fun _ => 0

theorem negative_limitedLiability : LimitedLiability negativePayment := by
  intro outcome
  simp [negativePayment]

theorem negative_incentivized : negativeControl.IsIncentivized negativePayment () := by
  intro alternative
  cases alternative
  exact le_rfl

theorem negative_not_participating :
    ¬negativeControl.Participates 0 negativePayment () := by
  norm_num [PrincipalAgentCandidate.Participates, PrincipalAgentCandidate.agentUtility,
    PrincipalAgentCandidate.expectedPayment, negativeControl, negativePayment]

end Hostile

end GameTheory.Experimental.PostArchitecture.ContractOwnership
