/-
# EXP-122: general-PMF restoration feasibility

This probe recovers the bounded countable Fubini argument from v1-final
`Math/Probability.lean` using the current Mathlib. It also checks actual
infinite support, countable conditioning, and the danger of interpreting a
totalized real sum as an expected payoff. It introduces no game interface.
-/

import GameTheory.Math.Probability.Expectation
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open scoped ENNReal BigOperators

namespace GameTheory.Experimental.PMFRestoration

open GameTheory.Math.Probability

/-- The geometric law gives every natural number positive probability. -/
def geometric : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal ((1 : ℝ) / 2 / 2 ^ n), by
    have hsum : HasSum (fun n : ℕ => (1 : ℝ) / 2 / 2 ^ n) 1 := by
      simpa only [one_div] using hasSum_geometric_two' (1 : ℝ)
    apply ENNReal.summable.hasSum_iff.mpr
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable,
      hsum.tsum_eq, ENNReal.ofReal_one]⟩

theorem geometric_real (n : ℕ) :
    (geometric n).toReal = (1 : ℝ) / 2 / 2 ^ n :=
  ENNReal.toReal_ofReal (by positivity)

theorem geometric_positive (n : ℕ) : 0 < geometric n := by
  exact ENNReal.ofReal_pos.mpr (by positivity)

theorem geometric_support : geometric.support = Set.univ := by
  ext n
  simp only [PMF.mem_support_iff, Set.mem_univ, iff_true]
  exact (geometric_positive n).ne'

/-- This consumer cannot be represented by any PMF with finite support. -/
theorem geometric_no_finite_support_representation :
    ¬ ∃ law : PMF ℕ, law.support.Finite ∧ law = geometric := by
  rintro ⟨law, hfinite, rfl⟩
  rw [geometric_support] at hfinite
  exact Set.infinite_univ hfinite

/-- Conditioning retains an infinite information fiber. -/
def posterior : PMF ℕ :=
  geometric.filter {n | n ≠ 0} ⟨1, by decide, (geometric_positive 1).ne'⟩

theorem posterior_support : posterior.support = {n | n ≠ 0} := by
  rw [posterior, PMF.support_filter, geometric_support, Set.inter_univ]

/-- Bayes normalization is available without enumerating the information fiber. -/
theorem posterior_bayes (n : ℕ) :
    posterior n = ({n : ℕ | n ≠ 0}.indicator geometric n) *
      (∑' k, {n : ℕ | n ≠ 0}.indicator geometric k)⁻¹ :=
  PMF.filter_apply _ n

theorem posterior_positive (n : ℕ) : 0 < posterior (n + 1) := by
  apply pos_iff_ne_zero.mpr
  rw [← PMF.mem_support_iff, posterior_support]
  exact Nat.succ_ne_zero n

/-- The v1 bounded-Fubini summability argument works on arbitrary carriers. -/
theorem bounded_joint_summable {α β : Type*}
    (p : PMF α) (q : α → PMF β) (f : β → ℝ)
    {bound : ℝ} (hbound : ∀ b, |f b| ≤ bound) :
    Summable (fun ab : α × β => (p ab.1).toReal * (q ab.1 ab.2).toReal * f ab.2) := by
  have hmass : ∑' ab : α × β, p ab.1 * q ab.1 ab.2 = 1 := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
    exact PMF.tsum_coe p
  have hprob : Summable (fun ab : α × β =>
      (p ab.1).toReal * (q ab.1 ab.2).toReal) := by
    simp_rw [← ENNReal.toReal_mul]
    apply ENNReal.summable_toReal
    rw [hmass]
    exact ENNReal.one_ne_top
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun ab => ?_) (hprob.mul_right bound)
  rw [abs_mul, abs_of_nonneg
    (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
  exact mul_le_mul_of_nonneg_left (hbound ab.2)
    (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

/-- Bounded continuation values satisfy the tower identity for ordinary PMFs.
The boundedness condition ensures the summability that gives the sums their
expected-payoff interpretation; no finiteness or countability class is used. -/
theorem bounded_bind_tower {α β : Type*}
    (p : PMF α) (q : α → PMF β) (f : β → ℝ)
    {bound : ℝ} (hbound : ∀ b, |f b| ≤ bound) :
    (∑' b, (p.bind q b).toReal * f b) =
      ∑' a, (p a).toReal * ∑' b, (q a b).toReal * f b := by
  have hjoint := bounded_joint_summable p q f hbound
  have hmass (b : β) : (p.bind q b).toReal =
      ∑' a, (p a).toReal * (q a b).toReal := by
    rw [PMF.bind_apply, ENNReal.tsum_toReal_eq
      (fun a => ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b))]
    simp_rw [ENNReal.toReal_mul]
  simp_rw [hmass, ← tsum_mul_right, ← tsum_mul_left]
  have hcomm :
      (∑' b, ∑' a, (p a).toReal * (q a b).toReal * f b) =
        ∑' a, ∑' b, (p a).toReal * (q a b).toReal * f b :=
    hjoint.tsum_comm
  simpa only [mul_assoc] using hcomm

/-- A nonconstant kernel keeps the infinite hidden draw in the outcome. -/
def continuation (n : ℕ) : PMF (ℕ × ℕ) :=
  posterior.map fun m => (n, m)

/-- Bounded nonconstant terminal payoff for the composed law. -/
def payoff (outcome : ℕ × ℕ) : ℝ := if outcome.1 = 0 then 1 else 0

theorem composed_payoff_tower :
    (∑' outcome, (geometric.bind continuation outcome).toReal * payoff outcome) =
      ∑' n, (geometric n).toReal *
        ∑' outcome, (continuation n outcome).toReal * payoff outcome := by
  apply bounded_bind_tower (bound := 1)
  intro outcome
  simp only [payoff]
  split_ifs <;> norm_num

/-- A nonnegative unbounded reward whose true expectation is infinite. -/
def exploding (n : ℕ) : ℝ := 2 ^ (n + 1)

theorem exploding_weighted_term (n : ℕ) :
    (geometric n).toReal * exploding n = 1 := by
  rw [geometric_real, exploding, pow_succ]
  have hne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

theorem exploding_not_summable :
    ¬ Summable (fun n => (geometric n).toReal * exploding n) := by
  simp_rw [exploding_weighted_term]
  intro hsum
  have hzero : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hsum.tendsto_atTop_zero
  norm_num at hzero

theorem exploding_nonnegative_expectation_infinite :
    (∑' n, ENNReal.ofReal ((geometric n).toReal * exploding n)) = ∞ := by
  simp_rw [exploding_weighted_term, ENNReal.ofReal_one]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

/-- Unguarded real `tsum` returns zero here, so it cannot certify finite utility. -/
theorem exploding_totalized_sum_zero :
    (∑' n, (geometric n).toReal * exploding n) = 0 :=
  tsum_eq_zero_of_not_summable exploding_not_summable

end GameTheory.Experimental.PMFRestoration
