/-
# Infinite expected loss is a defined value

A player who stays home is paid `0`. The only deviation is a gamble whose every
outcome pays strictly less than `0` and whose expected loss is infinite. The
gamble's payoff is not integrable, but its extended expected utility is the
defined value `⊥`, so staying home is a Nash equilibrium. A preference that
compares only integrable payoffs rejects that equilibrium.
-/

import GameTheory.Core.Equilibrium
import GameTheory.Core.ExpectedUtility
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace GameTheory.Tests.InfiniteExpectation

open GameTheory GameTheory.Math.Probability
open scoped ENNReal

/-- Probability `2^-(n+1)` at `n`. -/
def halving : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal ((1 : ℝ) / 2 / 2 ^ n), by
    have hsum : HasSum (fun n : ℕ => (1 : ℝ) / 2 / 2 ^ n) 1 := by
      simpa only [one_div] using hasSum_geometric_two' (1 : ℝ)
    apply ENNReal.summable.hasSum_iff.mpr
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable,
      hsum.tsum_eq, ENNReal.ofReal_one]⟩

/-- The loss at `n`, which exactly offsets its probability. -/
def loss (n : ℕ) : ℝ := 2 ^ (n + 1)

theorem loss_nonneg (n : ℕ) : 0 ≤ loss n := by
  unfold loss
  positivity

theorem weighted_loss (n : ℕ) : halving n * ENNReal.ofReal (loss n) = 1 := by
  show ENNReal.ofReal ((1 : ℝ) / 2 / 2 ^ n) * ENNReal.ofReal (2 ^ (n + 1)) = 1
  have hproduct : (1 : ℝ) / 2 / 2 ^ n * 2 ^ (n + 1) = 1 := by
    rw [pow_succ]
    field_simp
  rw [← ENNReal.ofReal_mul (by positivity), hproduct, ENNReal.ofReal_one]

/-- `true` stays home; `false` gambles. -/
@[reducible]
def form : GameForm Unit where
  sig := { Strategy := fun _ => Bool, Outcome := Option ℕ }
  play profile := if profile () then PMF.pure none else halving.map some

def utility : Option ℕ → Unit → ℝ
  | none, _ => 0
  | some n, _ => -loss n

def stayHome : Profile form.sig := fun _ => true

theorem gamble_play : form.play (Profile.update stayHome () false) = halving.map some := rfl

theorem gamble_gains : positiveExpect halving (fun n => utility (some n) ()) = 0 := by
  unfold positiveExpect
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  show halving n * ENNReal.ofReal (-loss n) = 0
  rw [ENNReal.ofReal_eq_zero.2 (neg_nonpos.2 (loss_nonneg n)), mul_zero]

theorem gamble_losses : negativeExpect halving (fun n => utility (some n) ()) = ⊤ := by
  unfold negativeExpect
  simp only [utility, neg_neg, weighted_loss]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

theorem gamble_not_integrable : ¬ UtilityIntegrable utility () (halving.map some) := by
  rw [UtilityIntegrable, payoffIntegrable_map_iff, payoffIntegrable_iff_parts]
  exact fun h => h.2 gamble_losses

theorem gamble_hasExpectation : UtilityHasExpectation utility () (halving.map some) := by
  rw [UtilityHasExpectation, hasExpectation_map_iff]
  exact Or.inl (by
    show positiveExpect halving (fun n => utility (some n) ()) ≠ ⊤
    rw [gamble_gains]
    exact ENNReal.zero_ne_top)

theorem gamble_value : extendedExpectedUtility utility () (halving.map some) = ⊥ := by
  rw [extendedExpectedUtility, extendedExpect_map]
  exact extendedExpect_eq_bot_of_negativeExpect_eq_top gamble_losses

/-- Staying home is a Nash equilibrium: the only deviation is worth `⊥`. -/
theorem stayHome_nash : IsNash form (euPreference utility) stayHome := by
  rw [isNash_iff]
  intro who replacement
  cases who
  have hhome : form.play stayHome = PMF.pure none := rfl
  have hhomeExpectation : UtilityHasExpectation utility () (PMF.pure none) :=
    UtilityIntegrable.hasExpectation (payoffIntegrable_pure _ _)
  cases replacement with
  | true =>
      have hsame : form.play (Profile.update stayHome () true) = PMF.pure none := rfl
      rw [hhome, hsame]
      exact ⟨hhomeExpectation, hhomeExpectation, le_rfl⟩
  | false =>
      rw [hhome, gamble_play]
      exact ⟨hhomeExpectation, gamble_hasExpectation,
        (congrArg (· ≤ _) gamble_value).mpr bot_le⟩

/-- A preference that compares only integrable payoffs. -/
def integrablePreference (u : Option ℕ → Unit → ℝ) : WeakPreference Unit (Option ℕ) :=
  fun agent preferred alternative =>
    UtilityIntegrable u agent preferred ∧ UtilityIntegrable u agent alternative ∧
      expectedUtility u agent alternative ≤ expectedUtility u agent preferred

/-- The integrable-payoff preference rejects the same equilibrium, because the
gamble's payoff is not integrable. -/
theorem stayHome_not_integrablePreference_nash :
    ¬ IsNash form (integrablePreference utility) stayHome := by
  rw [isNash_iff]
  intro h
  have hgamble := (h () false).2.1
  rw [gamble_play] at hgamble
  exact gamble_not_integrable hgamble

end GameTheory.Tests.InfiniteExpectation
