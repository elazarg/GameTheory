/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.FourierMotzkin
import Math.LinearProgramming.Basic
import Math.LinearProgramming.Standard

/-!
# Infeasibility certificates for finite packing LPs

This module adds the Farkas alternative for the packing-form LP API from
`Math.LinearProgramming.Basic`.  The basic file intentionally contains only
algebraic weak-duality facts; this file imports the Fourier-Motzkin theorem of
alternatives and proves the converse certificate:

`Ax ≤ b`, `x ≥ 0` is infeasible iff there is `y ≥ 0` with `yA ≥ 0` and
`b ⬝ y < 0`.
-/

open scoped BigOperators

namespace Math
namespace LinearProgramming

variable {Row Col : Type*} [Fintype Row] [Fintype Col]

namespace PackingCertificate

private noncomputable def unitCoeff (k : Col) (j : Fin (Fintype.card Col)) : ℝ := by
  classical
  exact if (Fintype.equivFin Col).symm j = k then 1 else 0

private noncomputable def systemA (A : Row → Col → ℝ) :
    Row ⊕ Col → Fin (Fintype.card Col) → ℝ
  | Sum.inl i, j => -A i ((Fintype.equivFin Col).symm j)
  | Sum.inr k, j => unitCoeff k j

private def systemB (b : Row → ℝ) : Row ⊕ Col → ℝ
  | Sum.inl i => -b i
  | Sum.inr _ => 0

private theorem sum_unitCoeff_mul (x : Col → ℝ) (k : Col) :
    (∑ j : Fin (Fintype.card Col),
      unitCoeff k j * x ((Fintype.equivFin Col).symm j)) = x k := by
  classical
  let e := Fintype.equivFin Col
  calc
    (∑ j : Fin (Fintype.card Col), unitCoeff k j * x (e.symm j))
        = ∑ c : Col, unitCoeff k (e c) * x c := by
            simpa [e] using
              (e.sum_comp (fun j : Fin (Fintype.card Col) => unitCoeff k j * x (e.symm j))).symm
    _ = ∑ c : Col, (if c = k then (1 : ℝ) else 0) * x c := by
            refine Finset.sum_congr rfl ?_
            intro c _
            simp [unitCoeff, e]
    _ = x k := by
            simp

omit [Fintype Row] in
private theorem sum_neg_reindex (A : Row → Col → ℝ) (x : Col → ℝ) (i : Row) :
    (∑ j : Fin (Fintype.card Col),
        -A i ((Fintype.equivFin Col).symm j) *
          x ((Fintype.equivFin Col).symm j)) =
      -∑ c : Col, A i c * x c := by
  classical
  let e := Fintype.equivFin Col
  calc
    (∑ j : Fin (Fintype.card Col), -A i (e.symm j) * x (e.symm j))
        = ∑ c : Col, -A i c * x c := by
            simpa [e] using
              (e.sum_comp
                (fun j : Fin (Fintype.card Col) => -A i (e.symm j) * x (e.symm j))).symm
    _ = -∑ c : Col, A i c * x c := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl ?_
            intro c _
            ring

omit [Fintype Row] in
private theorem system_feasible_iff (A : Row → Col → ℝ) (b : Row → ℝ)
    (x : Col → ℝ) :
    (∀ r : Row ⊕ Col,
      systemB b r ≤
        ∑ j : Fin (Fintype.card Col), systemA A r j * x ((Fintype.equivFin Col).symm j))
      ↔ PrimalFeasible A b x := by
  classical
  constructor
  · intro h
    constructor
    · intro k
      have hk := h (Sum.inr k)
      simpa [systemB, systemA, sum_unitCoeff_mul] using hk
    · intro i
      have hi := h (Sum.inl i)
      have hi' :
          -b i ≤
            ∑ j : Fin (Fintype.card Col),
              -A i ((Fintype.equivFin Col).symm j) *
                x ((Fintype.equivFin Col).symm j) := by
        simpa [systemB, systemA] using hi
      rw [sum_neg_reindex A x i] at hi'
      dsimp [rowEval]
      linarith
  · intro hx r
    cases r with
    | inl i =>
        have hi := hx.2 i
        have hle :
            -b i ≤
              ∑ j : Fin (Fintype.card Col),
                -A i ((Fintype.equivFin Col).symm j) *
                  x ((Fintype.equivFin Col).symm j) := by
          rw [sum_neg_reindex A x i]
          dsimp [rowEval] at hi
          linarith
        simpa [systemB, systemA] using hle
    | inr k =>
        simpa [systemB, systemA, sum_unitCoeff_mul] using hx.1 k

private theorem system_feasible_exists_iff (A : Row → Col → ℝ) (b : Row → ℝ) :
    Math.LinearAlgebra.IsFeasible (systemA A) (systemB b) ↔
      ∃ x : Col → ℝ, PrimalFeasible A b x := by
  classical
  constructor
  · rintro ⟨xfin, hxfin⟩
    let x : Col → ℝ := fun c => xfin ((Fintype.equivFin Col) c)
    refine ⟨x, ?_⟩
    exact (system_feasible_iff A b x).mp (by
      intro r
      have hr := hxfin r
      have hsum :
          (∑ j : Fin (Fintype.card Col), systemA A r j * xfin j) =
            ∑ j : Fin (Fintype.card Col),
              systemA A r j * x ((Fintype.equivFin Col).symm j) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        simp [x]
      rwa [← hsum])
  · rintro ⟨x, hx⟩
    refine ⟨fun j => x ((Fintype.equivFin Col).symm j), ?_⟩
    exact (system_feasible_iff A b x).mpr hx

private theorem certificate_dualValue_neg (A : Row → Col → ℝ) (b : Row → ℝ)
    {u : Row ⊕ Col → ℝ}
    (hu : Math.LinearAlgebra.IsCertificate (systemA A) (systemB b) u) :
    ∃ y : Row → ℝ, DualFeasible A (fun _ : Col => 0) y ∧ dualValue b y < 0 := by
  classical
  rcases hu with ⟨hu_nonneg, hu_col, hu_pos⟩
  let y : Row → ℝ := fun i => u (Sum.inl i)
  refine ⟨y, ?_, ?_⟩
  · constructor
    · intro i
      exact hu_nonneg (Sum.inl i)
    · intro c
      have hcol := hu_col ((Fintype.equivFin Col) c)
      have hbudget :
          (∑ i : Row, u (Sum.inl i) * -A i c) +
              u (Sum.inr c) = 0 := by
        rw [Fintype.sum_sum_type] at hcol
        have hleft :
            (∑ i : Row,
                u (Sum.inl i) * systemA A (Sum.inl i) ((Fintype.equivFin Col) c)) =
              ∑ i : Row, u (Sum.inl i) * -A i c := by
          simp [systemA]
        have hright :
            (∑ k : Col,
                u (Sum.inr k) * systemA A (Sum.inr k) ((Fintype.equivFin Col) c)) =
              u (Sum.inr c) := by
          simp [systemA, unitCoeff]
        rw [hleft, hright] at hcol
        exact hcol
      have hy :
          colEval A y c = u (Sum.inr c) := by
        dsimp [colEval, y]
        have hneg :
            (∑ i : Row, u (Sum.inl i) * -A i c) =
              -(∑ i : Row, u (Sum.inl i) * A i c) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
        rw [hneg] at hbudget
        linarith
      dsimp
      rw [hy]
      exact hu_nonneg (Sum.inr c)
  · have hsum :
        (∑ r : Row ⊕ Col, u r * systemB b r) =
          -∑ i : Row, u (Sum.inl i) * b i := by
      rw [Fintype.sum_sum_type]
      simp [systemB, Finset.sum_neg_distrib, mul_neg]
    rw [hsum] at hu_pos
    have hdot :
        dualValue b y = ∑ i : Row, u (Sum.inl i) * b i := by
      simp [dualValue, dot, y, mul_comm]
    rw [hdot]
    linarith

end PackingCertificate

/-- Farkas alternative for packing-form finite LP feasibility.

The system `Ax ≤ b`, `x ≥ 0` is infeasible iff a nonnegative dual vector
separates it from zero: `yA ≥ 0` and `b ⬝ y < 0`. -/
theorem not_exists_primalFeasible_iff_exists_dual_certificate
    {A : Row → Col → ℝ} {b : Row → ℝ} :
    (¬ ∃ x : Col → ℝ, PrimalFeasible A b x) ↔
      ∃ y : Row → ℝ,
        DualFeasible A (fun _ : Col => 0) y ∧ dualValue b y < 0 := by
  classical
  constructor
  · intro h
    have hsystem :
        ¬ Math.LinearAlgebra.IsFeasible
            (PackingCertificate.systemA A) (PackingCertificate.systemB b) := by
      intro hfeas
      exact h ((PackingCertificate.system_feasible_exists_iff A b).mp hfeas)
    rcases (Math.LinearAlgebra.theorem_of_alternative
        (PackingCertificate.systemA A) (PackingCertificate.systemB b)).mp hsystem with ⟨u, hu⟩
    exact PackingCertificate.certificate_dualValue_neg A b hu
  · rintro ⟨y, hy, hneg⟩ ⟨x, hx⟩
    have hweak := weak_duality hx hy
    have hzero : primalValue (fun _ : Col => 0) x = 0 := by
      simp [primalValue, dot]
    rw [hzero] at hweak
    linarith

/-- Infeasibility of a packing-form finite LP produces a negative
zero-objective dual certificate. -/
theorem exists_dual_certificate_of_not_exists_primalFeasible
    {A : Row → Col → ℝ} {b : Row → ℝ}
    (h : ¬ ∃ x : Col → ℝ, PrimalFeasible A b x) :
    ∃ y : Row → ℝ,
      DualFeasible A (fun _ : Col => 0) y ∧ dualValue b y < 0 :=
  not_exists_primalFeasible_iff_exists_dual_certificate.mp h

omit [Fintype Row] in
private theorem rowEval_neg (A : Row → Col → ℝ) (x : Col → ℝ) (i : Row) :
    rowEval (fun i j => -A i j) x i = -rowEval A x i := by
  simp [rowEval, Finset.sum_neg_distrib]

omit [Fintype Col] in
private theorem colEval_neg (A : Row → Col → ℝ) (y : Row → ℝ) (j : Col) :
    colEval (fun i j => -A i j) y j = -colEval A y j := by
  simp [colEval, Finset.sum_neg_distrib]

private theorem dualValue_neg (b : Row → ℝ) (y : Row → ℝ) :
    dualValue (fun i => -b i) y = -dot b y := by
  simp [dualValue, dot, Finset.sum_neg_distrib]

omit [Fintype Row] in
theorem minPrimalFeasible_iff_primalFeasible_neg
    (A : Row → Col → ℝ) (b : Row → ℝ) (x : Col → ℝ) :
    MinPrimalFeasible A b x ↔
      PrimalFeasible (fun i j => -A i j) (fun i => -b i) x := by
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro i
    rw [rowEval_neg]
    linarith [hx.2 i]
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro i
    have hi := hx.2 i
    rw [rowEval_neg] at hi
    linarith

/-- Farkas-style infeasibility certificate for the standard min-primal
orientation `Ax ≥ b`, `x ≥ 0`.  It is the packing-form certificate applied to
the negated matrix. -/
theorem not_exists_minPrimalFeasible_iff_exists_dual_certificate
    {A : Row → Col → ℝ} {b : Row → ℝ} :
    (¬ ∃ x : Col → ℝ, MinPrimalFeasible A b x) ↔
      ∃ y : Row → ℝ,
        Nonnegative y ∧ (∀ j : Col, colEval A y j ≤ 0) ∧ 0 < dot b y := by
  rw [show (¬ ∃ x : Col → ℝ, MinPrimalFeasible A b x) ↔
      ¬ ∃ x : Col → ℝ, PrimalFeasible (fun i j => -A i j) (fun i => -b i) x by
    constructor
    · intro h hpack
      rcases hpack with ⟨x, hx⟩
      exact h ⟨x, (minPrimalFeasible_iff_primalFeasible_neg A b x).mpr hx⟩
    · intro h hmin
      rcases hmin with ⟨x, hx⟩
      exact h ⟨x, (minPrimalFeasible_iff_primalFeasible_neg A b x).mp hx⟩]
  rw [not_exists_primalFeasible_iff_exists_dual_certificate]
  constructor
  · rintro ⟨y, hy, hval⟩
    refine ⟨y, hy.1, ?_, ?_⟩
    · intro j
      have hj := hy.2 j
      rw [colEval_neg] at hj
      linarith
    · rw [dualValue_neg] at hval
      linarith
  · rintro ⟨y, hy_nonneg, hy_col, hy_val⟩
    refine ⟨y, ⟨hy_nonneg, ?_⟩, ?_⟩
    · intro j
      rw [colEval_neg]
      linarith [hy_col j]
    · rw [dualValue_neg]
      linarith

end LinearProgramming
end Math
