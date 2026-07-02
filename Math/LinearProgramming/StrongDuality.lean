/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.Farkas
import Math.LinearProgramming.Standard

/-!
# Finite Linear Programming Strong Duality

Strong duality for the standard-form finite LP API:

* primal: minimize `c ⬝ x` subject to `A x ≥ b` and `x ≥ 0`;
* dual: maximize `b ⬝ y` subject to `y A ≤ c` and `y ≥ 0`.

The proof is a direct application of the objective-bound Farkas lemma to the
combined system whose original rows are `A x ≥ b` and whose extra rows encode
the nonnegativity constraints `x ≥ 0`.

This module adapts EconCSLib's Farkas-based strong-duality proof to the
existing finite LP API.
-/

open scoped BigOperators

namespace Math
namespace LinearProgramming

variable {Row Col : Type*} [Fintype Row] [Fintype Col]

namespace StrongDuality

private noncomputable def unitCoeff (k j : Col) : ℝ := by
  classical
  exact if k = j then 1 else 0

omit [Fintype Row] in
private theorem sum_unitCoeff_mul (x : Col → ℝ) (j : Col) :
    (∑ k, unitCoeff j k * x k) = x j := by
  classical
  unfold unitCoeff
  simp

omit [Fintype Row] in
private theorem sum_mul_unitCoeff (x : Col → ℝ) (j : Col) :
    (∑ k, x k * unitCoeff k j) = x j := by
  classical
  unfold unitCoeff
  simp

private noncomputable def primalSystemA (A : Row → Col → ℝ) : Row ⊕ Col → Col → ℝ
  | Sum.inl i, j => A i j
  | Sum.inr k, j => unitCoeff k j

private def primalSystemB (b : Row → ℝ) : Row ⊕ Col → ℝ
  | Sum.inl i => b i
  | Sum.inr _ => 0

omit [Fintype Row] in
private theorem primalSystem_feasible_iff (A : Row → Col → ℝ) (b : Row → ℝ)
    (x : Col → ℝ) :
    (∀ r, primalSystemB b r ≤ ∑ j, primalSystemA A r j * x j) ↔
    MinPrimalFeasible A b x := by
  classical
  constructor
  · intro h
    constructor
    · intro j
      have hj := h (Sum.inr j)
      change 0 ≤ ∑ k, unitCoeff j k * x k at hj
      rwa [sum_unitCoeff_mul] at hj
    · intro i
      have hi := h (Sum.inl i)
      simpa [primalSystemA, primalSystemB, rowEval] using hi
  · intro hx r
    cases r with
    | inl i =>
        simpa [primalSystemA, primalSystemB, rowEval] using hx.2 i
    | inr j =>
        change 0 ≤ ∑ k, unitCoeff j k * x k
        rw [sum_unitCoeff_mul]
        exact hx.1 j

omit [Fintype Row] in
private theorem primalSystem_feasible_nonempty {A : Row → Col → ℝ} {b : Row → ℝ}
    (hfeas : ∃ x, MinPrimalFeasible A b x) :
    ∃ x : Col → ℝ, ∀ r, primalSystemB b r ≤ ∑ j, primalSystemA A r j * x j := by
  obtain ⟨x, hx⟩ := hfeas
  exact ⟨x, (primalSystem_feasible_iff A b x).mpr hx⟩

omit [Fintype Row] in
private theorem primalSystem_bound_iff {A : Row → Col → ℝ} {b : Row → ℝ}
    {c : Col → ℝ} {d : ℝ} :
    (∀ x : Col → ℝ,
        (∀ r, primalSystemB b r ≤ ∑ j, primalSystemA A r j * x j) →
        d ≤ ∑ j, c j * x j) ↔
    (∀ x : Col → ℝ, MinPrimalFeasible A b x → d ≤ minPrimalValue c x) := by
  constructor
  · intro h x hx
    simpa [minPrimalValue, dot] using
      h x ((primalSystem_feasible_iff A b x).mpr hx)
  · intro h x hx
    simpa [minPrimalValue, dot] using
      h x ((primalSystem_feasible_iff A b x).mp hx)

private theorem sum_primalSystemB
    (b : Row → ℝ) (u : Row ⊕ Col → ℝ) :
    (∑ r, u r * primalSystemB b r) = ∑ i, u (Sum.inl i) * b i := by
  classical
  rw [Fintype.sum_sum_type]
  simp [primalSystemB]

private theorem sum_primalSystemA
    (A : Row → Col → ℝ) (u : Row ⊕ Col → ℝ) (j : Col) :
    (∑ r, u r * primalSystemA A r j) =
      (∑ i, u (Sum.inl i) * A i j) + u (Sum.inr j) := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [primalSystemA]
  rw [sum_mul_unitCoeff]

end StrongDuality

/-- Every lower bound on the standard-form primal objective has a feasible dual
certificate reaching at least that bound. -/
theorem exists_maxDualFeasible_of_minPrimal_lower_bound
    {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ} {d : ℝ}
    (hfeas : ∃ x, MinPrimalFeasible A b x)
    (hbound : ∀ x, MinPrimalFeasible A b x → d ≤ minPrimalValue c x) :
    ∃ y, MaxDualFeasible A c y ∧ d ≤ maxDualValue b y := by
  classical
  obtain ⟨u, hu_nonneg, hu_col, hu_bound⟩ :=
    (Math.LinearAlgebra.farkas_lemma_fintype
      (StrongDuality.primalSystemA A) (StrongDuality.primalSystemB b) c d
      (StrongDuality.primalSystem_feasible_nonempty hfeas)).mp
      ((StrongDuality.primalSystem_bound_iff (A := A) (b := b) (c := c) (d := d)).mpr hbound)
  let y : Row → ℝ := fun i => u (Sum.inl i)
  refine ⟨y, ?_, ?_⟩
  · constructor
    · intro i
      exact hu_nonneg (Sum.inl i)
    · intro j
      have hcol := hu_col j
      rw [StrongDuality.sum_primalSystemA A u j] at hcol
      dsimp [colEval, y]
      have hz_nonneg : 0 ≤ u (Sum.inr j) := hu_nonneg (Sum.inr j)
      linarith
  · have hbound_y : d ≤ ∑ i, u (Sum.inl i) * b i := by
      rwa [StrongDuality.sum_primalSystemB b u] at hu_bound
    calc
      d ≤ ∑ i, u (Sum.inl i) * b i := hbound_y
      _ = maxDualValue b y := by
        simp [maxDualValue, dot, y, mul_comm]

/-- Strong duality for a standard-form finite LP, stated from an optimal primal
solution: an optimal primal point has a feasible dual point with the same
objective value. -/
theorem lp_strong_duality
    {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ} {x : Col → ℝ}
    (hx : MinPrimalFeasible A b x)
    (hopt : ∀ z, MinPrimalFeasible A b z → minPrimalValue c x ≤ minPrimalValue c z) :
    ∃ y, MaxDualFeasible A c y ∧ maxDualValue b y = minPrimalValue c x := by
  obtain ⟨y, hy, hge⟩ :=
    exists_maxDualFeasible_of_minPrimal_lower_bound
      (A := A) (b := b) (c := c) (d := minPrimalValue c x)
      ⟨x, hx⟩ hopt
  refine ⟨y, hy, ?_⟩
  exact le_antisymm (min_weak_duality hx hy) hge

end LinearProgramming
end Math
