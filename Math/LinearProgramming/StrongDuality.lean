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
  rw [Fintype.sum_sum_type]
  simp [primalSystemB]

private theorem sum_primalSystemA
    (A : Row → Col → ℝ) (u : Row ⊕ Col → ℝ) (j : Col) :
    (∑ r, u r * primalSystemA A r j) =
      (∑ i, u (Sum.inl i) * A i j) + u (Sum.inr j) := by
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

/-- Every upper bound on the standard-form dual objective has a feasible
primal certificate reaching at most that bound.  This is the transposed,
sign-reversed form of
`exists_maxDualFeasible_of_minPrimal_lower_bound`. -/
theorem exists_minPrimalFeasible_of_maxDual_upper_bound
    {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ} {d : ℝ}
    (hfeas : ∃ y, MaxDualFeasible A c y)
    (hbound : ∀ y, MaxDualFeasible A c y → maxDualValue b y ≤ d) :
    ∃ x, MinPrimalFeasible A b x ∧ minPrimalValue c x ≤ d := by
  let dualA : Col → Row → ℝ := fun j i => -A i j
  let dualB : Col → ℝ := fun j => -c j
  let dualC : Row → ℝ := fun i => -b i
  have hfeas' : ∃ y, MinPrimalFeasible dualA dualB y := by
    obtain ⟨y, hy⟩ := hfeas
    refine ⟨y, hy.1, ?_⟩
    intro j
    calc
      dualB j = -c j := rfl
      _ ≤ -(colEval A y j) := neg_le_neg (hy.2 j)
      _ = rowEval dualA y j := by
        unfold colEval rowEval dualA
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hbound' : ∀ y, MinPrimalFeasible dualA dualB y →
      -d ≤ minPrimalValue dualC y := by
    intro y hy
    have hyOriginal : MaxDualFeasible A c y := by
      refine ⟨hy.1, ?_⟩
      intro j
      have hj := hy.2 j
      have hrow : rowEval dualA y j = -(colEval A y j) := by
        unfold rowEval colEval dualA
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      dsimp only [dualB] at hj
      rw [hrow] at hj
      linarith
    have hvalue := hbound y hyOriginal
    have hnegValue :
        minPrimalValue dualC y = -(maxDualValue b y) := by
      unfold minPrimalValue maxDualValue dot dualC
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hnegValue]
    linarith
  obtain ⟨x, hx, hxValue⟩ :=
    exists_maxDualFeasible_of_minPrimal_lower_bound
      (A := dualA) (b := dualB) (c := dualC)
      (d := -d) hfeas' hbound'
  have hxOriginal : MinPrimalFeasible A b x := by
    refine ⟨hx.1, ?_⟩
    intro i
    have hi := hx.2 i
    have hcol : colEval dualA x i = -(rowEval A x i) := by
      unfold colEval rowEval dualA
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    dsimp only [dualC] at hi
    rw [hcol] at hi
    linarith
  refine ⟨x, hxOriginal, ?_⟩
  have hvalue :
      maxDualValue dualB x = -(minPrimalValue c x) := by
    unfold maxDualValue minPrimalValue dot dualB
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hvalue] at hxValue
  linarith

omit [Fintype Row] in
/-- A nonempty finite standard-form primal whose objective is bounded below
attains its minimum.  The proof uses the infimum only to obtain an optimal
dual certificate, then the transposed Farkas theorem above produces an
actual primal optimizer. -/
theorem exists_minPrimalOptimal_of_feasible_of_bounded [Finite Row]
    {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ}
    (hfeas : ∃ x, MinPrimalFeasible A b x)
    (hbounded : ∃ lower : ℝ,
      ∀ x, MinPrimalFeasible A b x → lower ≤ minPrimalValue c x) :
    ∃ x, MinPrimalFeasible A b x ∧
      ∀ z, MinPrimalFeasible A b z →
        minPrimalValue c x ≤ minPrimalValue c z := by
  letI := Fintype.ofFinite Row
  let values : Set ℝ :=
    {value | ∃ x, MinPrimalFeasible A b x ∧
      minPrimalValue c x = value}
  have hvaluesNonempty : values.Nonempty := by
    obtain ⟨x, hx⟩ := hfeas
    exact ⟨minPrimalValue c x, x, hx, rfl⟩
  have hvaluesBddBelow : BddBelow values := by
    obtain ⟨lower, hlower⟩ := hbounded
    refine ⟨lower, ?_⟩
    rintro value ⟨x, hx, rfl⟩
    exact hlower x hx
  let optimum : ℝ := sInf values
  have hoptimumLower : ∀ x, MinPrimalFeasible A b x →
      optimum ≤ minPrimalValue c x := by
    intro x hx
    exact csInf_le hvaluesBddBelow ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hoptimum_le_y⟩ :=
    exists_maxDualFeasible_of_minPrimal_lower_bound
      (A := A) (b := b) (c := c) (d := optimum)
      hfeas hoptimumLower
  have hyOptimal : ∀ z, MaxDualFeasible A c z →
      maxDualValue b z ≤ maxDualValue b y := by
    intro z hz
    have hz_le_optimum : maxDualValue b z ≤ optimum := by
      apply le_csInf hvaluesNonempty
      intro value hvalue
      obtain ⟨x, hx, rfl⟩ := hvalue
      exact min_weak_duality hx hz
    exact hz_le_optimum.trans hoptimum_le_y
  obtain ⟨x, hx, hx_le_y⟩ :=
    exists_minPrimalFeasible_of_maxDual_upper_bound
      (A := A) (b := b) (c := c)
      ⟨y, hy⟩ hyOptimal
  exact ⟨x, hx, fun z hz =>
    hx_le_y.trans (min_weak_duality hz hy)⟩

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
