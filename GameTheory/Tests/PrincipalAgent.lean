/-
Hostile finite principal-agent regression fixture.

The productive action has a genuinely stochastic success law.  A success
bonus, unlike zero payment, strictly changes the agent's preferred action;
participation uses nonzero outside options.
-/

import GameTheory.Mechanism.PrincipalAgent
import GameTheory.Math.Probability.Uniform

noncomputable section

namespace GameTheory.Tests.PrincipalAgent

open GameTheory GameTheory.Mechanism GameTheory.Math.Probability

def fairCoin : PMF Bool := PMF.uniformOfFintype Bool

/-- `false` is safe and costless; `true` is productive, costly, and noisy. -/
@[reducible]
def fixture : Mechanism.PrincipalAgent Bool Bool where
  outcomeLaw
    | false => PMF.pure false
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

/-- Finite outcome support integrates each payment schedule. -/
theorem paymentGuard (payment : Bool → ℝ) (action : Bool) :
    PayoffIntegrable (fixture.outcomeLaw action) payment :=
  payoffIntegrable_of_finite _ _

/-- Finite outcome support integrates the fixture's reward. -/
theorem rewardGuard (action : Bool) :
    PayoffIntegrable (fixture.outcomeLaw action) fixture.reward :=
  payoffIntegrable_of_finite _ _

/-- Finite outcome support integrates principal net revenue. -/
theorem netGuard (payment : Bool → ℝ) (action : Bool) :
    PayoffIntegrable (fixture.outcomeLaw action)
      (fun outcome => fixture.reward outcome - payment outcome) :=
  payoffIntegrable_of_finite _ _

@[simp] theorem expectedReward_safe :
    fixture.expectedReward false (rewardGuard false) = 0 := by
  norm_num [Mechanism.PrincipalAgent.expectedReward, expect_eq_sum,
    Fintype.sum_bool, PMF.pure_apply, fixture]

@[simp] theorem expectedReward_productive :
    fixture.expectedReward true (rewardGuard true) = 1 := by
  norm_num [Mechanism.PrincipalAgent.expectedReward, expect_eq_sum,
    Fintype.sum_bool, fairCoin, PMF.uniformOfFintype_apply, fixture]

@[simp] theorem zeroPayment_safe :
    fixture.agentUtility zeroPayment false (paymentGuard zeroPayment false) = 0 := by
  norm_num [Mechanism.PrincipalAgent.agentUtility,
    Mechanism.PrincipalAgent.expectedPayment, expect_eq_sum,
    Fintype.sum_bool, PMF.pure_apply, zeroPayment, fixture]

@[simp] theorem zeroPayment_productive :
    fixture.agentUtility zeroPayment true (paymentGuard zeroPayment true) =
      -(1 / 4 : ℝ) := by
  norm_num [Mechanism.PrincipalAgent.agentUtility,
    Mechanism.PrincipalAgent.expectedPayment, expect_eq_sum,
    Fintype.sum_bool, PMF.uniformOfFintype_apply, fairCoin,
    zeroPayment, fixture]

@[simp] theorem successBonus_safe :
    fixture.agentUtility successBonus false
      (paymentGuard successBonus false) = 0 := by
  norm_num [Mechanism.PrincipalAgent.agentUtility,
    Mechanism.PrincipalAgent.expectedPayment, expect_eq_sum,
    Fintype.sum_bool, PMF.pure_apply, successBonus, fixture]

@[simp] theorem successBonus_productive :
    fixture.agentUtility successBonus true
      (paymentGuard successBonus true) = 1 / 4 := by
  norm_num [Mechanism.PrincipalAgent.agentUtility,
    Mechanism.PrincipalAgent.expectedPayment, expect_eq_sum,
    Fintype.sum_bool, PMF.uniformOfFintype_apply, fairCoin,
    successBonus, fixture]

theorem zeroPayment_prefers_safe :
    fixture.agentUtility zeroPayment true (paymentGuard zeroPayment true) <
      fixture.agentUtility zeroPayment false (paymentGuard zeroPayment false) := by
  norm_num [zeroPayment_safe, zeroPayment_productive]

theorem successBonus_prefers_productive :
    fixture.agentUtility successBonus false (paymentGuard successBonus false) <
      fixture.agentUtility successBonus true (paymentGuard successBonus true) := by
  norm_num [successBonus_safe, successBonus_productive]

theorem successBonus_incentivizes_productive : fixture.IsIncentivized successBonus true := by
  refine ⟨paymentGuard successBonus, ?_⟩
  intro alternative
  cases alternative <;>
    norm_num [successBonus_safe, successBonus_productive]

theorem successBonus_participates_at_quarter :
    fixture.Participates (1 / 4) successBonus true := by
  exact ⟨paymentGuard successBonus true, by
    norm_num [successBonus_productive]⟩

theorem successBonus_rejects_three_quarters :
    ¬ fixture.OffersParticipation (3 / 4) successBonus := by
  rintro ⟨action, haction⟩
  rcases haction with ⟨hpayment, hvalue⟩
  cases action <;> norm_num [successBonus_safe, successBonus_productive] at hvalue

/-- The accounting identity specializes to the nonconstant-reward productive
action. -/
theorem productive_welfare_accounting :
    fixture.principalUtility successBonus true (netGuard successBonus true) +
      fixture.agentUtility successBonus true (paymentGuard successBonus true) =
      fixture.socialSurplus true (rewardGuard true) :=
  fixture.principalUtility_add_agentUtility successBonus true
    (rewardGuard true) (paymentGuard successBonus true) (netGuard successBonus true)

theorem fixture_exists_incentivized : ∃ action, fixture.IsIncentivized successBonus action :=
  fixture.exists_incentivized successBonus
    (paymentGuard successBonus)

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
  outcomeLaw _ := PMF.pure false
  reward _ := 0
  cost _ := 1

theorem zeroPayment_limitedLiability :
    Mechanism.PrincipalAgent.IsLimitedLiability (fun _ : Bool => 0) := by
  intro outcome
  norm_num

theorem singleton_zero_payment_incentivized :
    singletonNegative.IsIncentivized (fun _ : Bool => 0) () := by
  refine ⟨fun _ => payoffIntegrable_of_finite _ _, ?_⟩
  intro alternative
  rcases alternative with ⟨⟩
  exact le_rfl

/-- Limited liability and IC alone do not imply participation: the only action
has positive cost and no payment, hence rejects outside option zero. -/
theorem singleton_zero_payment_rejects_zero :
    ¬ singletonNegative.Participates 0 (fun _ : Bool => 0) () := by
  rintro ⟨hpayment, hvalue⟩
  norm_num [Mechanism.PrincipalAgent.agentUtility,
    Mechanism.PrincipalAgent.expectedPayment, expect_pure,
    singletonNegative] at hvalue

end GameTheory.Tests.PrincipalAgent
