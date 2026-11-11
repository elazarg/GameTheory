module

/-
# Undefined and infinite continuation values

Mixing independent signed geometric tails gives infinite expected gains and
losses, so the resulting continuation has no expectation. Both the incumbent
and allowed alternatives need their own guards. A defined negative infinite
value remains admissible even though its absolute payoff is not integrable.
-/

public import GameTheory.Protocol.Context
public import GameTheory.Tests.InfiniteExpectation

@[expose] public section

noncomputable section

namespace GameTheory.Tests.ContextGuards

open GameTheory.Math.Probability GameTheory.Protocol
open GameTheory.Tests.InfiniteExpectation (halving loss loss_nonneg weighted_loss)
open scoped ENNReal

/-- The sign is retained in the realized outcome. -/
def signedPayoff (outcome : Bool × ℕ) : ℝ :=
  if outcome.1 then loss outcome.2 else -loss outcome.2

def branch (sign : Bool) : PMF (Bool × ℕ) :=
  halving.map fun n => (sign, n)

def coin : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure true) (PMF.pure false)

def undefinedLaw : PMF (Bool × ℕ) := coin.bind branch

theorem positive_branch_gains : positiveExpect (branch true) signedPayoff = ⊤ := by
  unfold positiveExpect branch
  rw [tsum_map_mul]
  change (∑' n, halving n * ENNReal.ofReal (loss n)) = ⊤
  simp only [weighted_loss]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

theorem negative_branch_losses : negativeExpect (branch false) signedPayoff = ⊤ := by
  unfold negativeExpect branch
  rw [tsum_map_mul]
  change (∑' n, halving n * ENNReal.ofReal (- -loss n)) = ⊤
  simp only [neg_neg, weighted_loss]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

theorem undefinedLaw_gains : positiveExpect undefinedLaw signedPayoff = ⊤ := by
  rw [undefinedLaw, positiveExpect_bind]
  apply top_unique
  calc
    (⊤ : ℝ≥0∞) = coin true * positiveExpect (branch true) signedPayoff := by
      rw [positive_branch_gains]
      exact (ENNReal.mul_top (by norm_num [coin, mix_apply] : coin true ≠ 0)).symm
    _ ≤ ∑' sign, coin sign * positiveExpect (branch sign) signedPayoff :=
      ENNReal.le_tsum (f := fun sign => coin sign * positiveExpect (branch sign) signedPayoff)
        true

theorem undefinedLaw_losses : negativeExpect undefinedLaw signedPayoff = ⊤ := by
  rw [undefinedLaw, negativeExpect_bind]
  apply top_unique
  calc
    (⊤ : ℝ≥0∞) = coin false * negativeExpect (branch false) signedPayoff := by
      rw [negative_branch_losses]
      exact (ENNReal.mul_top (by norm_num [coin, mix_apply] : coin false ≠ 0)).symm
    _ ≤ ∑' sign, coin sign * negativeExpect (branch sign) signedPayoff :=
      ENNReal.le_tsum (f := fun sign => coin sign * negativeExpect (branch sign) signedPayoff)
        false

theorem undefinedLaw_hasNoExpectation : ¬ HasExpectation undefinedLaw signedPayoff := by
  simp [HasExpectation, undefinedLaw_gains, undefinedLaw_losses]

/-- Staying is a finite deterministic outcome; moving yields an actually
undefined continuation expectation. -/
def context : Context Bool (Bool × ℕ) where
  outcome choice := if choice then undefinedLaw else PMF.pure (true, 0)
  continuation := signedPayoff

theorem incumbent_hasValue : context.HasValueAt false :=
  hasExpectation_of_payoffIntegrable (payoffIntegrable_pure (true, 0) signedPayoff)

theorem alternative_hasNoValue : ¬ context.HasValueAt true :=
  undefinedLaw_hasNoExpectation

/-- Undefined alternatives never meet the profitable-deviation guard. -/
theorem no_profitable_deviation :
    ¬ ∃ alternative, context.IsProfitableDeviation {true} false alternative := by
  rintro ⟨alternative, hallowed, _, hvalue, _⟩
  have hchoice : alternative = true := by simpa using hallowed
  subst alternative
  exact alternative_hasNoValue hvalue

/-- Absence of profitable deviations does not establish guarded local
optimality when an allowed alternative is undefined. -/
theorem incumbent_not_locallyOptimal : ¬ context.IsLocallyOptimal {true} false := by
  intro hoptimal
  exact alternative_hasNoValue (hoptimal.2.1 true (by simp))

/-- The incumbent's guard remains necessary when the allowed set is empty. -/
theorem undefined_incumbent_not_locallyOptimal :
    ¬ context.IsLocallyOptimal ∅ true := by
  intro hoptimal
  exact alternative_hasNoValue hoptimal.1

theorem empty_allowed_no_profitable_deviation :
    ¬ ∃ alternative, context.IsProfitableDeviation ∅ true alternative := by
  rintro ⟨_, hallowed, _⟩
  exact hallowed

/-- A defined negative infinite value remains admissible even though it is
not an integrable finite value. -/
theorem negative_branch_hasExpectation : HasExpectation (branch false) signedPayoff := by
  apply Or.inl
  have hzero : positiveExpect (branch false) signedPayoff = 0 := by
    unfold positiveExpect branch
    rw [tsum_map_mul]
    apply ENNReal.tsum_eq_zero.2
    intro n
    change halving n * ENNReal.ofReal (-loss n) = 0
    rw [ENNReal.ofReal_eq_zero.2 (neg_nonpos.2 (loss_nonneg n)), mul_zero]
  rw [hzero]
  exact ENNReal.zero_ne_top

theorem negative_branch_value : extendedExpect (branch false) signedPayoff = ⊥ :=
  extendedExpect_eq_bot_of_negativeExpect_eq_top negative_branch_losses

/-- A defined infinite loss is admissible even though absolute payoff is not
integrable. This distinguishes value-definedness from finite-value guards. -/
theorem negative_branch_not_integrable :
    ¬ PayoffIntegrable (branch false) signedPayoff := by
  intro h
  exact ((payoffIntegrable_iff_parts _ _).mp h).2 negative_branch_losses

def lossContext : Context Bool (Bool × ℕ) where
  outcome choice := if choice then branch false else PMF.pure (true, 0)
  continuation := signedPayoff

theorem finite_incumbent_optimal_against_infinite_loss :
    lossContext.IsLocallyOptimal {true} false := by
  refine ⟨hasExpectation_of_payoffIntegrable (payoffIntegrable_pure _ _), ?_, ?_⟩
  · intro alternative allowed
    have hchoice : alternative = true := by simpa using allowed
    subst alternative
    exact negative_branch_hasExpectation
  · intro alternative allowed
    have hchoice : alternative = true := by simpa using allowed
    subst alternative
    change extendedExpect (branch false) signedPayoff ≤ _
    rw [negative_branch_value]
    exact bot_le

end GameTheory.Tests.ContextGuards
