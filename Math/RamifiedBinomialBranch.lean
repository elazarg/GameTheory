/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AlgebraicSelection
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Convergent ramified roots of a binomial branch

This file formalizes one genuine Newton--Puiseux step.  Consider the local
equation

`y ^ m = λ ^ n * u(λ)`,

where `m > 0` and `u` is an analytic unit with positive value at zero.
After the ramification `λ = s ^ m`, the equation has an ordinary real
analytic solution.  The proof constructs the convergent branch explicitly
using the positive analytic `m`-th root of the unit.

The polynomial corollary packages this as a bivariate algebraic curve.  This
does not assert general Newton--Puiseux: a general Weierstrass polynomial
must first be reduced to binomial Newton edges and iterated while controlling
the residual polynomial.
-/

noncomputable section

open Filter Polynomial Set Topology

namespace Math

/-- A positive analytic unit has a positive analytic `m`-th root. -/
theorem exists_analytic_nthRoot_of_pos
    {u : ℝ → ℝ} (hu : AnalyticAt ℝ u 0) (hu0 : 0 < u 0)
    {m : ℕ} (hm : 0 < m) :
    ∃ root : ℝ → ℝ,
      AnalyticAt ℝ root 0 ∧
      0 < root 0 ∧
      (∀ x, 0 < root x) ∧
      ∀ᶠ x in 𝓝 (0 : ℝ), root x ^ m = u x := by
  let root : ℝ → ℝ :=
    fun x => Real.exp (Real.log (u x) / (m : ℝ))
  have hroot : AnalyticAt ℝ root 0 := by
    exact (hu.log hu0).div_const.rexp'
  have hroot_pos : ∀ x, 0 < root x :=
    fun x => Real.exp_pos _
  have hu_pos : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < u x :=
    continuousAt_const.eventually_lt hu.continuousAt hu0
  have hpow : ∀ᶠ x in 𝓝 (0 : ℝ), root x ^ m = u x := by
    filter_upwards [hu_pos] with x hx
    calc
      root x ^ m =
          Real.exp ((m : ℝ) * (Real.log (u x) / (m : ℝ))) := by
            rw [Real.exp_nat_mul]
      _ = Real.exp (Real.log (u x)) := by
            congr 1
            field_simp [Nat.ne_of_gt hm]
      _ = u x := Real.exp_log hx
  exact ⟨root, hroot, hroot_pos 0, hroot_pos, hpow⟩

/-- A binomial analytic curve acquires a convergent ordinary-power-series
branch after the ramification `λ = s ^ m`. -/
theorem exists_analytic_ramified_binomial_root
    {u : ℝ → ℝ} (hu : AnalyticAt ℝ u 0) (hu0 : 0 < u 0)
    {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ∃ gamma : ℝ → ℝ,
      AnalyticAt ℝ gamma 0 ∧
      (∀ᶠ s in 𝓝 (0 : ℝ),
        gamma s ^ m = (s ^ m) ^ n * u (s ^ m)) ∧
      (∀ s, 0 < s → 0 < gamma s) := by
  let ramify : ℝ → ℝ := fun s => s ^ m
  have hramify : AnalyticAt ℝ ramify 0 := by
    exact analyticAt_id.pow m
  have hu_ramify : AnalyticAt ℝ (u ∘ ramify) 0 :=
    hu.comp_of_eq hramify (by simp [ramify, Nat.ne_of_gt hm])
  obtain ⟨root, hroot, _hroot0, hroot_pos, hroot_pow⟩ :=
    exists_analytic_nthRoot_of_pos hu_ramify
      (by simpa [ramify, Nat.ne_of_gt hm] using hu0) hm
  let gamma : ℝ → ℝ := fun s => s ^ n * root s
  have hgamma : AnalyticAt ℝ gamma 0 :=
    (analyticAt_id.pow n).mul hroot
  have heq :
      ∀ᶠ s in 𝓝 (0 : ℝ),
        gamma s ^ m = (s ^ m) ^ n * u (s ^ m) := by
    filter_upwards [hroot_pow] with s hs
    calc
      gamma s ^ m = (s ^ n) ^ m * root s ^ m := by
        change (s ^ n * root s) ^ m = _
        rw [mul_pow]
      _ = (s ^ m) ^ n * u (s ^ m) := by
        rw [hs]
        change (s ^ n) ^ m * u (s ^ m) =
          (s ^ m) ^ n * u (s ^ m)
        congr 1
        calc
          (s ^ n) ^ m = s ^ (n * m) := (pow_mul s n m).symm
          _ = s ^ (m * n) := by rw [Nat.mul_comm]
          _ = (s ^ m) ^ n := pow_mul s m n
  have hpos : ∀ s, 0 < s → 0 < gamma s := by
    intro s hs
    exact mul_pos (pow_pos hs n) (hroot_pos s)
  exact ⟨gamma, hgamma, heq, hpos⟩

/-- The bivariate binomial whose outer variable is the selected value and
whose coefficient variable is the parameter. -/
def binomialBivPolynomial
    (m n : ℕ) (u : Polynomial ℝ) :
    Polynomial (Polynomial ℝ) :=
  (X : Polynomial (Polynomial ℝ)) ^ m -
    C ((X : Polynomial ℝ) ^ n * u)

theorem bivEval_binomialBivPolynomial
    (m n : ℕ) (u : Polynomial ℝ) (lam y : ℝ) :
    bivEval (binomialBivPolynomial m n u) lam y =
      y ^ m - lam ^ n * u.eval lam := by
  unfold binomialBivPolynomial bivEval
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  rw [map_mul, map_pow]
  simp

/-- Polynomial-unit specialization: a real binomial algebraic curve has an
analytic branch after one explicit ramification. -/
theorem exists_analytic_ramified_binomial_polynomial_root
    (u : Polynomial ℝ) (hu0 : 0 < u.eval 0)
    {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ∃ gamma : ℝ → ℝ,
      AnalyticAt ℝ gamma 0 ∧
      (∀ᶠ s in 𝓝 (0 : ℝ),
        bivEval (binomialBivPolynomial m n u)
          (s ^ m) (gamma s) = 0) ∧
      (∀ s, 0 < s → 0 < gamma s) := by
  have hu : AnalyticAt ℝ (fun x : ℝ => u.eval x) 0 := by
    exact (AnalyticOnNhd.eval_polynomial u) 0 (Set.mem_univ 0)
  obtain ⟨gamma, hgamma, heq, hpos⟩ :=
    exists_analytic_ramified_binomial_root hu hu0 hm n
  refine ⟨gamma, hgamma, ?_, hpos⟩
  filter_upwards [heq] with s hs
  rw [bivEval_binomialBivPolynomial, hs]
  ring

end Math
