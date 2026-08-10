/-
# Finite multiplicative weights

The exponential-potential argument is game-independent.  This module exposes
it as finite real-vector mathematics: probabilities are coordinates summing
to one, not a second probability-law type.  `GameTheory.Probability` may turn
those coordinates into the canonical `FinDist` representation.
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace GameTheoryMath.OnlineLearning

variable {A : Type*}

/-- Cumulative gain of action `a` over the first `t` rounds. -/
def cumGain (gain : ℕ → A → ℝ) (t : ℕ) (a : A) : ℝ :=
  ∑ s ∈ Finset.range t, gain s a

@[simp]
theorem cumGain_zero (gain : ℕ → A → ℝ) (a : A) : cumGain gain 0 a = 0 := by
  simp [cumGain]

theorem cumGain_succ (gain : ℕ → A → ℝ) (t : ℕ) (a : A) :
    cumGain gain (t + 1) a = cumGain gain t a + gain t a := by
  simp [cumGain, Finset.sum_range_succ]

/-- The unnormalized multiplicative weight of one action. -/
def weight (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) (a : A) : ℝ :=
  Real.exp (eta * cumGain gain t a)

theorem weight_pos (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) (a : A) :
    0 < weight eta gain t a :=
  Real.exp_pos _

variable [Fintype A] [Nonempty A]

/-- The normalizing constant for multiplicative weights. -/
def denominator (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) : ℝ :=
  ∑ a, weight eta gain t a

theorem denominator_pos (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) :
    0 < denominator eta gain t :=
  Finset.sum_pos (fun a _ => weight_pos eta gain t a) Finset.univ_nonempty

omit [Nonempty A] in
@[simp]
theorem denominator_zero (eta : ℝ) (gain : ℕ → A → ℝ) :
    denominator eta gain 0 = Fintype.card A := by
  simp [denominator, weight]

/-- One coordinate of the normalized exponential-weights vector. -/
def probability (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) (a : A) : ℝ :=
  weight eta gain t a / denominator eta gain t

theorem probability_nonneg (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) (a : A) :
    0 ≤ probability eta gain t a :=
  div_nonneg (weight_pos eta gain t a).le (denominator_pos eta gain t).le

theorem sum_probability (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) :
    ∑ a, probability eta gain t a = 1 := by
  simp_rw [probability, div_eq_mul_inv]
  rw [← Finset.sum_mul, denominator]
  exact mul_inv_cancel₀ (denominator_pos eta gain t).ne'

/-- Expected value against the normalized exponential-weights vector. -/
def expected (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) (f : A → ℝ) : ℝ :=
  ∑ a, probability eta gain t a * f a

omit [Nonempty A] in
theorem expected_eq_weighted (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ)
    (f : A → ℝ) :
    expected eta gain t f =
      (∑ a, weight eta gain t a * f a) / denominator eta gain t := by
  simp_rw [expected, probability, div_mul_eq_mul_div, div_eq_mul_inv]
  rw [← Finset.sum_mul]

/-- Accumulated expected gain of multiplicative weights. -/
def algorithmGain (eta : ℝ) (gain : ℕ → A → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, expected eta gain t (gain t)

omit [Nonempty A] in
theorem algorithmGain_succ (eta : ℝ) (gain : ℕ → A → ℝ) (T : ℕ) :
    algorithmGain eta gain (T + 1) =
      algorithmGain eta gain T + expected eta gain T (gain T) := by
  simp [algorithmGain, Finset.sum_range_succ]

/-- Best fixed action's cumulative gain in hindsight. -/
def bestGain (gain : ℕ → A → ℝ) (T : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => cumGain gain T a)

/-- External regret of multiplicative weights. -/
def externalRegret (eta : ℝ) (gain : ℕ → A → ℝ) (T : ℕ) : ℝ :=
  bestGain gain T - algorithmGain eta gain T

/-- The chord bound for `exp` on the unit interval. -/
theorem exp_mul_le_of_mem_Icc {eta x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (eta * x) ≤ 1 + x * (Real.exp eta - 1) := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ eta)
    (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x) hx.1 (by ring)
  simp only [smul_eq_mul, mul_zero, Real.exp_zero, mul_one, zero_add] at hconv
  have key : 1 + x * (Real.exp eta - 1) = 1 - x + x * Real.exp eta := by ring
  rw [mul_comm eta x, key]
  exact hconv

theorem denominator_succ_le (eta : ℝ) {gain : ℕ → A → ℝ}
    (hgain : ∀ s a, gain s a ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    denominator eta gain (t + 1) ≤
      denominator eta gain t *
        Real.exp ((Real.exp eta - 1) * expected eta gain t (gain t)) := by
  have hstep : denominator eta gain (t + 1) ≤
      denominator eta gain t +
        (Real.exp eta - 1) * (∑ a, weight eta gain t a * gain t a) := by
    rw [denominator, denominator, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun a _ => ?_)
    have hw : weight eta gain (t + 1) a =
        weight eta gain t a * Real.exp (eta * gain t a) := by
      rw [weight, weight, cumGain_succ, mul_add, Real.exp_add]
    rw [hw]
    nlinarith [weight_pos eta gain t a, exp_mul_le_of_mem_Icc (eta := eta) (hgain t a)]
  have hExpected : (∑ a, weight eta gain t a * gain t a) =
      denominator eta gain t * expected eta gain t (gain t) := by
    rw [expected_eq_weighted, mul_div_cancel₀ _ (denominator_pos eta gain t).ne']
  rw [hExpected] at hstep
  calc
    denominator eta gain (t + 1) ≤
        denominator eta gain t + (Real.exp eta - 1) *
          (denominator eta gain t * expected eta gain t (gain t)) := hstep
    _ = denominator eta gain t *
          (1 + (Real.exp eta - 1) * expected eta gain t (gain t)) := by ring
    _ ≤ denominator eta gain t *
          Real.exp ((Real.exp eta - 1) * expected eta gain t (gain t)) := by
      apply mul_le_mul_of_nonneg_left _ (denominator_pos eta gain t).le
      linarith [Real.add_one_le_exp ((Real.exp eta - 1) * expected eta gain t (gain t))]

theorem denominator_le (eta : ℝ) {gain : ℕ → A → ℝ}
    (hgain : ∀ s a, gain s a ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    denominator eta gain T ≤
      (Fintype.card A) * Real.exp ((Real.exp eta - 1) * algorithmGain eta gain T) := by
  induction T with
  | zero => simp [algorithmGain, Real.exp_zero]
  | succ T ih =>
      calc
        denominator eta gain (T + 1) ≤ denominator eta gain T *
            Real.exp ((Real.exp eta - 1) * expected eta gain T (gain T)) :=
          denominator_succ_le eta hgain T
        _ ≤ ((Fintype.card A) *
              Real.exp ((Real.exp eta - 1) * algorithmGain eta gain T)) *
            Real.exp ((Real.exp eta - 1) * expected eta gain T (gain T)) :=
          mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
        _ = (Fintype.card A) *
            Real.exp ((Real.exp eta - 1) * algorithmGain eta gain (T + 1)) := by
          rw [algorithmGain_succ, mul_add, Real.exp_add]
          ring

theorem exp_bestGain_le_denominator (eta : ℝ) (gain : ℕ → A → ℝ) (T : ℕ) :
    Real.exp (eta * bestGain gain T) ≤ denominator eta gain T := by
  obtain ⟨a, -, ha⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun a => cumGain gain T a)
  have heq : Real.exp (eta * bestGain gain T) = weight eta gain T a := by
    rw [bestGain, ha, weight]
  rw [heq]
  exact Finset.single_le_sum (fun b _ => (weight_pos eta gain T b).le) (Finset.mem_univ a)

/-- Fixed-rate multiplicative-weights external-regret bound. -/
theorem externalRegret_le {eta : ℝ} (heta : 0 < eta) {gain : ℕ → A → ℝ}
    (hgain : ∀ s a, gain s a ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    externalRegret eta gain T ≤
      Real.log (Fintype.card A) / eta +
        (Real.exp eta - 1 - eta) / eta * T := by
  have hcard : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast Fintype.card_pos
  have hcombined : Real.exp (eta * bestGain gain T) ≤
      (Fintype.card A) * Real.exp ((Real.exp eta - 1) * algorithmGain eta gain T) :=
    le_trans (exp_bestGain_le_denominator eta gain T) (denominator_le eta hgain T)
  have hlog : eta * bestGain gain T ≤
      Real.log (Fintype.card A) + (Real.exp eta - 1) * algorithmGain eta gain T := by
    have h := Real.log_le_log (Real.exp_pos _) hcombined
    rwa [Real.log_exp, Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  have halgorithm : algorithmGain eta gain T ≤ T := by
    rw [algorithmGain]
    calc
      ∑ t ∈ Finset.range T, expected eta gain t (gain t) ≤
          ∑ _t ∈ Finset.range T, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun t _ => ?_)
        rw [expected]
        calc
          ∑ a, probability eta gain t a * gain t a ≤
              ∑ a, probability eta gain t a * 1 := by
            exact Finset.sum_le_sum fun a _ =>
              mul_le_mul_of_nonneg_left (hgain t a).2
                (probability_nonneg eta gain t a)
          _ = 1 := by simp [sum_probability]
      _ = T := by simp
  have hbest : bestGain gain T ≤
      Real.log (Fintype.card A) / eta +
        (Real.exp eta - 1) / eta * algorithmGain eta gain T := by
    have key : Real.log (Fintype.card A) / eta +
        (Real.exp eta - 1) / eta * algorithmGain eta gain T =
        (Real.log (Fintype.card A) +
          (Real.exp eta - 1) * algorithmGain eta gain T) / eta := by ring
    rw [key, le_div_iff₀ heta]
    linarith [hlog]
  have hcoefficient : 0 ≤ (Real.exp eta - 1 - eta) / eta :=
    div_nonneg (by linarith [Real.add_one_le_exp eta]) heta.le
  have hmul := mul_le_mul_of_nonneg_left halgorithm hcoefficient
  have hsplit : (Real.exp eta - 1) / eta * algorithmGain eta gain T =
      algorithmGain eta gain T +
        (Real.exp eta - 1 - eta) / eta * algorithmGain eta gain T := by
    field_simp
    ring
  rw [externalRegret]
  linarith [hbest, hmul, hsplit]

/-- Exponential weights for a supplied score vector. -/
def scoreProbability (eta : ℝ) (score : A → ℝ) (a : A) : ℝ :=
  Real.exp (eta * score a) / ∑ b, Real.exp (eta * score b)

theorem scoreProbability_nonneg (eta : ℝ) (score : A → ℝ) (a : A) :
    0 ≤ scoreProbability eta score a :=
  div_nonneg (Real.exp_pos _).le
    (Finset.sum_pos (fun _b _ => Real.exp_pos _) Finset.univ_nonempty).le

theorem sum_scoreProbability (eta : ℝ) (score : A → ℝ) :
    ∑ a, scoreProbability eta score a = 1 := by
  simp_rw [scoreProbability, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀
    (Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty).ne'

omit [Nonempty A] in
theorem probability_eq_scoreProbability (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) :
    probability eta gain t = scoreProbability eta (cumGain gain t) := by
  funext a
  rfl

/-- A quadratic remainder bound used for horizon-dependent tuning. -/
theorem exp_sub_one_sub_self_le_sq {eta : ℝ} (hzero : 0 ≤ eta) (hone : eta ≤ 1) :
    Real.exp eta - 1 - eta ≤ eta ^ 2 := by
  have hx : |eta| ≤ 1 := abs_le.mpr ⟨by linarith, hone⟩
  have hb := Real.exp_bound hx (n := 2) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 2, eta ^ m / (m.factorial : ℝ)) = 1 + eta := by
    norm_num [Finset.sum_range_succ]
  rw [hsum, sq_abs] at hb
  norm_num [Nat.factorial] at hb
  nlinarith [hb, le_abs_self (Real.exp eta - (1 + eta)), sq_nonneg eta]

/-- On the usual learning-rate range, the exponential remainder is at most
quadratic. This game-independent form is the convenient input for choosing a
horizon-dependent rate in downstream learning reductions. -/
theorem externalRegret_le_quadratic {eta : ℝ} (heta : 0 < eta)
    (hetaOne : eta ≤ 1) {gain : ℕ → A → ℝ}
    (hgain : ∀ s a, gain s a ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    externalRegret eta gain T ≤
      Real.log (Fintype.card A) / eta + eta * T := by
  have hremainder :
      (Real.exp eta - 1 - eta) / eta ≤ eta := by
    rw [div_le_iff₀ heta]
    simpa [pow_two] using exp_sub_one_sub_self_le_sq heta.le hetaOne
  have hscaled :=
    mul_le_mul_of_nonneg_right hremainder (Nat.cast_nonneg T)
  calc
    externalRegret eta gain T ≤
        Real.log (Fintype.card A) / eta +
          (Real.exp eta - 1 - eta) / eta * T :=
      externalRegret_le heta hgain T
    _ ≤ Real.log (Fintype.card A) / eta + eta * T := by
      linarith

theorem fixedActionRegret_le_externalRegret
    (eta : ℝ) (gain : ℕ → A → ℝ) (T : ℕ) (a : A) :
    cumGain gain T a - algorithmGain eta gain T ≤ externalRegret eta gain T := by
  have hle : cumGain gain T a ≤ bestGain gain T :=
    Finset.le_sup' (fun b => cumGain gain T b) (Finset.mem_univ a)
  rw [externalRegret]
  linarith

end GameTheoryMath.OnlineLearning
