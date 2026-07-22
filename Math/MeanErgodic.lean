/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Math.Probability
import Math.ProbabilityMassFunction
import Math.PMFIter

/-!
# Mean Ergodic Theorem (finite dimension) and Markov Operators

The finite-dimensional mean ergodic theorem: a linear endomorphism with
uniformly bounded powers has convergent Cesàro averages, and the limit is a
fixed point.  The proof is the elementary decomposition
`E = ker (P - 1) ⊕ im (P - 1)`:

* on `ker (P - 1)` the Cesàro averages are eventually constant;
* on `im (P - 1)` they telescope to `(P ^ T) y - y` over `T`, which tends
  to zero by power-boundedness;
* the subspaces are disjoint because a fixed point in the image is its own
  Cesàro average and telescopes to zero, and they span by rank–nullity.

Applied to the Markov operator of a PMF kernel on a finite state space this
yields Cesàro convergence of expected values along the iterated kernel
(`Math.PMFIter.iter`) — the mean ergodic theorem for finite Markov chains.
This is the analytic input for uniform equilibrium payoffs in stochastic
games whose state process is autonomous (see
`GameTheory.Concepts.Stochastic.TransitionIndependent`).

## Main results

* `Math.MeanErgodic.tendsto_cesaro_of_pow_norm_le` — the abstract
  finite-dimensional mean ergodic theorem
* `Math.MeanErgodic.markovOperator` — the Markov operator of a PMF kernel
* `Math.MeanErgodic.tendsto_cesaro_expect_iter` — Cesàro convergence of
  expected values along a finite Markov chain
-/

namespace Math
namespace MeanErgodic

open Filter Math.Probability
open scoped BigOperators

-- ============================================================================
-- The abstract finite-dimensional mean ergodic theorem
-- ============================================================================

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Powers fix fixed points. -/
theorem pow_apply_eq_of_fixed {P : E →ₗ[ℝ] E} {z : E} (hz : P z = z) :
    ∀ t : ℕ, (P ^ t) z = z := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, Module.End.mul_apply, hz, ih]

/-- The orbit sums of a one-step increment telescope. -/
theorem sum_range_pow_apply_sub (P : E →ₗ[ℝ] E) (y : E) (T : ℕ) :
    ∑ t ∈ Finset.range T, (P ^ t) (P y - y) = (P ^ T) y - y := by
  have hterm : ∀ t : ℕ,
      (P ^ t) (P y - y) = (P ^ (t + 1)) y - (P ^ t) y := by
    intro t
    rw [map_sub, pow_succ, Module.End.mul_apply]
  rw [Finset.sum_congr rfl fun t _ => hterm t,
    Finset.sum_range_sub (fun t => (P ^ t) y)]
  simp

/-- Under power-boundedness, normalized orbit increments tend to zero. -/
theorem tendsto_inv_smul_pow_sub_of_pow_norm_le (P : E →ₗ[ℝ] E) {C : ℝ}
    (hC : ∀ (n : ℕ) (x : E), ‖(P ^ n) x‖ ≤ C * ‖x‖) (y : E) :
    Tendsto (fun T : ℕ => (T : ℝ)⁻¹ • ((P ^ T) y - y)) atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun T : ℕ => (C * ‖y‖ + ‖y‖) / T)
  · intro T
    have hbd : ‖(P ^ T) y - y‖ ≤ C * ‖y‖ + ‖y‖ :=
      (norm_sub_le _ _).trans (add_le_add (hC T y) le_rfl)
    calc ‖(T : ℝ)⁻¹ • ((P ^ T) y - y)‖
        = (T : ℝ)⁻¹ * ‖(P ^ T) y - y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (T : ℝ)⁻¹ * (C * ‖y‖ + ‖y‖) :=
          mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = (C * ‖y‖ + ‖y‖) / T := by
          rw [inv_mul_eq_div]
  · exact tendsto_const_div_atTop_nhds_zero_nat _

/-- **The finite-dimensional mean ergodic theorem.**  A linear endomorphism
of a finite-dimensional real normed space whose powers are uniformly
bounded has convergent Cesàro averages at every point, and the limit is a
fixed point. -/
theorem tendsto_cesaro_of_pow_norm_le [FiniteDimensional ℝ E]
    (P : E →ₗ[ℝ] E) {C : ℝ}
    (hC : ∀ (n : ℕ) (x : E), ‖(P ^ n) x‖ ≤ C * ‖x‖) (x : E) :
    ∃ z, P z = z ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (P ^ t) x)
        atTop (nhds z) := by
  -- Fixed points and the image of `P - 1` are disjoint: a fixed point of
  -- the form `P y - y` equals every normalized orbit increment of `y`,
  -- and those tend to zero.
  have hdisj : Disjoint (LinearMap.ker (P - LinearMap.id))
      (LinearMap.range (P - LinearMap.id)) := by
    rw [Submodule.disjoint_def]
    intro z hzk hzr
    obtain ⟨y, hy⟩ := hzr
    have hy' : P y - y = z := by simpa using hy
    have hPz : P z = z := by
      have h0 := LinearMap.mem_ker.mp hzk
      have h1 : P z - z = 0 := by simpa using h0
      exact sub_eq_zero.mp h1
    have hzeq : ∀ᶠ T : ℕ in atTop,
        z = (T : ℝ)⁻¹ • ((P ^ T) y - y) := by
      filter_upwards [eventually_ge_atTop 1] with T hT
      have hTne : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hsum : (T : ℕ) • z = (P ^ T) y - y := by
        calc (T : ℕ) • z
            = ∑ t ∈ Finset.range T, (P ^ t) z := by
              rw [Finset.sum_congr rfl fun t _ =>
                pow_apply_eq_of_fixed hPz t, Finset.sum_const,
                Finset.card_range]
          _ = ∑ t ∈ Finset.range T, (P ^ t) (P y - y) := by rw [hy']
          _ = (P ^ T) y - y := sum_range_pow_apply_sub P y T
      rw [← hsum, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        inv_mul_cancel₀ hTne, one_smul]
    have hz0 : Tendsto (fun _ : ℕ => z) atTop (nhds 0) :=
      Tendsto.congr' (EventuallyEq.symm hzeq)
        (tendsto_inv_smul_pow_sub_of_pow_norm_le P hC y)
    exact tendsto_nhds_unique tendsto_const_nhds hz0
  -- Rank–nullity: the two subspaces span.
  have hsup : LinearMap.ker (P - LinearMap.id) ⊔
      LinearMap.range (P - LinearMap.id) = ⊤ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (P - LinearMap.id)
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (P - LinearMap.id))
      (LinearMap.range (P - LinearMap.id))
    rw [disjoint_iff.mp hdisj, finrank_bot, add_zero] at h2
    exact Submodule.eq_top_of_finrank_eq (by omega)
  -- Decompose `x` and take limits on each part.
  have hx : x ∈ LinearMap.ker (P - LinearMap.id) ⊔
      LinearMap.range (P - LinearMap.id) := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨z, hzk, w, hwr, hzw⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y, hy⟩ := hwr
  have hy' : P y - y = w := by simpa using hy
  have hPz : P z = z := by
    have h0 := LinearMap.mem_ker.mp hzk
    have h1 : P z - z = 0 := by simpa using h0
    exact sub_eq_zero.mp h1
  refine ⟨z, hPz, ?_⟩
  have hzlim : Tendsto
      (fun T : ℕ => (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (P ^ t) z)
      atTop (nhds z) := by
    have hzconst : ∀ᶠ T : ℕ in atTop,
        (fun _ : ℕ => z) T =
          (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (P ^ t) z := by
      filter_upwards [eventually_ge_atTop 1] with T hT
      have hTne : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [Finset.sum_congr rfl fun t _ => pow_apply_eq_of_fixed hPz t,
        Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ,
        smul_smul, inv_mul_cancel₀ hTne, one_smul]
    exact Tendsto.congr' hzconst tendsto_const_nhds
  have hwlim : Tendsto
      (fun T : ℕ => (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (P ^ t) w)
      atTop (nhds 0) := by
    have hsum : ∀ T : ℕ,
        (T : ℝ)⁻¹ • ((P ^ T) y - y) =
          (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (P ^ t) w := by
      intro T
      rw [← hy', sum_range_pow_apply_sub]
    exact (tendsto_inv_smul_pow_sub_of_pow_norm_le P hC y).congr hsum
  have hsplit : ∀ T : ℕ,
      ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (P ^ t) z) +
          (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (P ^ t) w =
        (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (P ^ t) x := by
    intro T
    rw [← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← map_add, hzw]
  have hfinal := hzlim.add hwlim
  rw [add_zero] at hfinal
  exact hfinal.congr hsplit

end Abstract

-- ============================================================================
-- Markov operators of PMF kernels on finite state spaces
-- ============================================================================

section Markov

variable {S : Type*} [Fintype S]

/-- The Markov operator of a PMF kernel on a finite state space, acting on
real-valued observables: `markovOperator κ w s` is the expected value of
`w` one step after `s`. -/
noncomputable def markovOperator (κ : S → PMF S) : (S → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun w s := expect (κ s) w
  map_add' u v := by
    funext s
    exact expect_add (κ s) u v
  map_smul' c w := by
    funext s
    have hfun : c • w = fun ω => c * w ω := by
      funext ω
      simp
    rw [hfun]
    simpa using expect_const_mul (κ s) c w

@[simp] theorem markovOperator_apply (κ : S → PMF S) (w : S → ℝ) (s : S) :
    markovOperator κ w s = expect (κ s) w :=
  rfl

/-- Powers of the Markov operator compute expectations along the iterated
kernel. -/
theorem markovOperator_pow_apply (κ : S → PMF S) (t : ℕ) (w : S → ℝ)
    (s : S) :
    ((markovOperator κ ^ t) w) s = expect (Math.PMFIter.iter κ t s) w := by
  induction t generalizing w with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Module.End.mul_apply, ih, Math.PMFIter.iter_succ',
      expect_bind]
    rfl

/-- The Markov operator is a sup-norm contraction, uniformly over powers. -/
theorem norm_markovOperator_pow_apply_le (κ : S → PMF S) (t : ℕ)
    (w : S → ℝ) :
    ‖(markovOperator κ ^ t) w‖ ≤ 1 * ‖w‖ := by
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun s => ?_
  rw [markovOperator_pow_apply, Real.norm_eq_abs]
  refine abs_expect_le_of_abs_le _ _ fun s' => ?_
  simpa [Real.norm_eq_abs] using norm_le_pi_norm w s'

end Markov

section MarkovFinite

variable {S : Type*} [Finite S]

/-- **Mean ergodic theorem for finite Markov chains**: Cesàro averages of
expected values along the iterated kernel converge. -/
theorem tendsto_cesaro_expect_iter (κ : S → PMF S) (w : S → ℝ) (s₀ : S) :
    ∃ v : ℝ, Tendsto
      (fun T : ℕ => (T : ℝ)⁻¹ *
        ∑ t ∈ Finset.range T, expect (Math.PMFIter.iter κ t s₀) w)
      atTop (nhds v) := by
  letI : Fintype S := Fintype.ofFinite S
  obtain ⟨z, -, hlim⟩ := tendsto_cesaro_of_pow_norm_le (markovOperator κ)
    (fun t x => norm_markovOperator_pow_apply_le κ t x) w
  refine ⟨z s₀, ?_⟩
  have hcoord := ((continuous_apply s₀).tendsto z).comp hlim
  refine hcoord.congr fun T => ?_
  simp [Finset.sum_apply, markovOperator_pow_apply, Function.comp]

end MarkovFinite

end MeanErgodic
end Math
