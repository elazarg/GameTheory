/-
Hostile finite principal-agent regression fixture.

The productive action has a genuinely stochastic success law.  A success
bonus, unlike zero payment, strictly changes the agent's preferred action;
participation uses nonzero outside options.
-/

import GameTheory.Mechanism.PrincipalAgent

noncomputable section

namespace GameTheory.Tests.PrincipalAgent

open GameTheory GameTheory.Mechanism GameTheory.Math.Probability

def fairCoin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

/-- `false` is safe and costless; `true` is productive, costly, and noisy. -/
@[reducible]
def fixture : Mechanism.PrincipalAgent Bool Bool where
  outcomeLaw
    | false => FinDist.pure false
    | true => fairCoin
  reward
    | false => 0
    | true => 2
  cost
    | false => 0
    | true => 1 / 4

def zeroPayment : Bool → ℝ := fun _ => 0
def successBonus : Bool → ℝ
  | false => 0
  | true => 1

@[simp] theorem expectedReward_safe : fixture.expectedReward false = 0 := by
  simp [Mechanism.PrincipalAgent.expectedReward]

@[simp] theorem expectedReward_productive : fixture.expectedReward true = 1 := by
  rw [Mechanism.PrincipalAgent.expectedReward]
  simp [fairCoin, FinDist.expect_mix]
  norm_num

@[simp] theorem zeroPayment_safe : fixture.agentUtility zeroPayment false = 0 := by
  simp [Mechanism.PrincipalAgent.agentUtility,
    Mechanism.PrincipalAgent.expectedPayment, zeroPayment]

@[simp] theorem zeroPayment_productive : fixture.agentUtility zeroPayment true = -(1 / 4 : ℝ) := by
  unfold Mechanism.PrincipalAgent.agentUtility Mechanism.PrincipalAgent.expectedPayment
  rw [show fixture.outcomeLaw true = fairCoin from rfl,
    show zeroPayment = (fun _ : Bool => 0) from rfl]
  rw [FinDist.expect_const]
  norm_num

@[simp] theorem successBonus_safe : fixture.agentUtility successBonus false = 0 := by
  simp [Mechanism.PrincipalAgent.agentUtility,
    Mechanism.PrincipalAgent.expectedPayment, successBonus]

@[simp] theorem successBonus_productive :
    fixture.agentUtility successBonus true = 1 / 4 := by
  simp [Mechanism.PrincipalAgent.agentUtility,
    Mechanism.PrincipalAgent.expectedPayment, successBonus,
    fairCoin, FinDist.expect_mix]
  norm_num

theorem zeroPayment_prefers_safe :
    fixture.agentUtility zeroPayment true < fixture.agentUtility zeroPayment false := by
  norm_num

theorem successBonus_prefers_productive :
    fixture.agentUtility successBonus false < fixture.agentUtility successBonus true := by
  norm_num

theorem successBonus_incentivizes_productive : fixture.IsIncentivized successBonus true := by
  intro alternative
  cases alternative <;> norm_num

theorem successBonus_participates_at_quarter :
    fixture.Participates (1 / 4) successBonus true := by
  norm_num [Mechanism.PrincipalAgent.Participates]

theorem successBonus_rejects_three_quarters :
    ¬ fixture.OffersParticipation (3 / 4) successBonus := by
  rintro ⟨action, haction⟩
  cases action <;> norm_num [Mechanism.PrincipalAgent.Participates] at haction

/-- The accounting identity specializes to the nonconstant-reward productive
action. -/
theorem productive_welfare_accounting :
    fixture.principalUtility successBonus true + fixture.agentUtility successBonus true =
      fixture.socialSurplus true :=
  fixture.principalUtility_add_agentUtility successBonus true

theorem fixture_exists_incentivized : ∃ action, fixture.IsIncentivized successBonus action :=
  fixture.exists_incentivized successBonus

/-- Generic participation transport moves an offered contract to the selected
incentivized action. -/
theorem participation_from_incentives :
    fixture.Participates (1 / 4) successBonus true := by
  apply fixture.participates_of_offersParticipation_of_isIncentivized
    (action := true)
  · exact ⟨true, successBonus_participates_at_quarter⟩
  · exact successBonus_incentivizes_productive

@[reducible]
def singletonNegative : Mechanism.PrincipalAgent Unit Bool where
  outcomeLaw _ := FinDist.pure false
  reward _ := 0
  cost _ := 1

theorem zeroPayment_limitedLiability :
    Mechanism.PrincipalAgent.IsLimitedLiability (fun _ : Bool => 0) := by
  intro outcome
  norm_num

theorem singleton_zero_payment_incentivized :
    singletonNegative.IsIncentivized (fun _ : Bool => 0) () := by
  intro alternative
  rcases alternative with ⟨⟩
  exact le_rfl

/-- Limited liability and IC alone do not imply participation: the only action
has positive cost and no payment, hence rejects outside option zero. -/
theorem singleton_zero_payment_rejects_zero :
    ¬ singletonNegative.Participates 0 (fun _ : Bool => 0) () := by
  norm_num [Mechanism.PrincipalAgent.Participates,
    Mechanism.PrincipalAgent.agentUtility,
    Mechanism.PrincipalAgent.expectedPayment, singletonNegative]

end GameTheory.Tests.PrincipalAgent
