/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.FourierMotzkin
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi

/-!
# Compatibility of finite linear inequalities

This file transports the Fourier--Motzkin theorem of alternatives from
`Fin (Fintype.card State)` to an arbitrary finite state type.

For finitely many vectors `delta action` and lower bounds `base action`,
exactly one of the following is possible:

* one potential pairs with every vector above its lower bound;
* nonnegative action weights balance every coordinate of the vectors and
  have strictly positive weighted lower bound.

The final theorem records the sign information supplied by a Bellman
residual inequality.
-/

namespace Math

open scoped BigOperators

variable {State Action : Type*}

/-- The matrix obtained by transporting state coordinates along the
canonical equivalence with `Fin`. -/
noncomputable def finiteInequalityMatrix [Fintype State]
    (delta : Action → State → ℝ) :
    Action → Fin (Fintype.card State) → ℝ :=
  fun action coordinate =>
    delta action ((Fintype.equivFin State).symm coordinate)

theorem finiteInequalityMatrix_rowEval [Fintype State] [Fintype Action]
    (delta : Action → State → ℝ) (action : Action)
    (x : Fin (Fintype.card State) → ℝ) :
    LinearAlgebra.rowEval (finiteInequalityMatrix delta) action x =
      dotProduct (delta action)
        (fun state => x (Fintype.equivFin State state)) := by
  classical
  let e := Fintype.equivFin State
  unfold LinearAlgebra.rowEval
  calc
    (∑ coordinate, finiteInequalityMatrix delta action coordinate *
        x coordinate) =
        ∑ state, finiteInequalityMatrix delta action (e state) *
          x (e state) := by
            simpa [e] using
              (e.sum_comp
                (fun coordinate =>
                  finiteInequalityMatrix delta action coordinate *
                    x coordinate)).symm
    _ = dotProduct (delta action) (fun state => x (e state)) := by
          apply Finset.sum_congr rfl
          intro state _
          simp [finiteInequalityMatrix, e]

/-- Feasibility after transport to `Fin` is exactly feasibility by a
potential on the original finite state type. -/
theorem finiteInequality_feasible_iff
    [Fintype State] [Fintype Action]
    (delta : Action → State → ℝ) (base : Action → ℝ) :
    LinearAlgebra.IsFeasible (finiteInequalityMatrix delta) base ↔
      ∃ potential : State → ℝ,
        ∀ action, base action ≤
          dotProduct (delta action) potential := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun state => x (Fintype.equivFin State state), ?_⟩
    intro action
    have haction := hx action
    rw [finiteInequalityMatrix_rowEval] at haction
    exact haction
  · rintro ⟨potential, hpotential⟩
    let x : Fin (Fintype.card State) → ℝ :=
      fun coordinate => potential ((Fintype.equivFin State).symm coordinate)
    refine ⟨x, ?_⟩
    intro action
    rw [finiteInequalityMatrix_rowEval]
    simpa [x] using hpotential action

/-- **Finite inequality compatibility alternative.** Either all lower
bounds are represented by one potential, or a nonnegative dependence among
the vectors has strictly positive weighted lower bound. -/
theorem exists_potential_or_nonnegative_incompatibility
    [Fintype State] [Fintype Action]
    (delta : Action → State → ℝ) (base : Action → ℝ) :
    (∃ potential : State → ℝ,
      ∀ action, base action ≤
        dotProduct (delta action) potential) ∨
    (∃ coefficient : Action → ℝ,
      (∀ action, 0 ≤ coefficient action) ∧
      (∀ state,
        ∑ action, coefficient action * delta action state = 0) ∧
      0 < ∑ action, coefficient action * base action) := by
  classical
  by_cases hfeasible :
      LinearAlgebra.IsFeasible
        (finiteInequalityMatrix delta) base
  · left
    exact (finiteInequality_feasible_iff delta base).mp hfeasible
  · right
    obtain ⟨coefficient, hnonnegative, hbalance, hpositive⟩ :=
      (LinearAlgebra.theorem_of_alternative
        (finiteInequalityMatrix delta) base).mp hfeasible
    refine ⟨coefficient, hnonnegative, ?_, hpositive⟩
    intro state
    have hcolumn := hbalance (Fintype.equivFin State state)
    simpa [finiteInequalityMatrix] using hcolumn

/-- A feasible potential and a nonnegative incompatibility certificate
cannot coexist. -/
theorem not_nonnegative_incompatibility_of_potential
    [Fintype State] [Fintype Action]
    {delta : Action → State → ℝ} {base : Action → ℝ}
    {potential : State → ℝ}
    (hpotential :
      ∀ action, base action ≤
        dotProduct (delta action) potential)
    {coefficient : Action → ℝ}
    (hnonnegative : ∀ action, 0 ≤ coefficient action)
    (hbalance :
      ∀ state,
        ∑ action, coefficient action * delta action state = 0) :
    ∑ action, coefficient action * base action ≤ 0 := by
  classical
  calc
    ∑ action, coefficient action * base action ≤
        ∑ action, coefficient action *
          dotProduct (delta action) potential := by
            apply Finset.sum_le_sum
            intro action _
            exact mul_le_mul_of_nonneg_left
              (hpotential action) (hnonnegative action)
    _ = ∑ state,
        (∑ action, coefficient action * delta action state) *
          potential state := by
            simp only [dotProduct, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro state _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro action _
            ring
    _ = 0 := by simp [hbalance]

/-- Potential feasibility is equivalent to the absence of a nonnegative
incompatibility certificate. -/
theorem exists_potential_iff_no_nonnegative_incompatibility
    [Fintype State] [Fintype Action]
    (delta : Action → State → ℝ) (base : Action → ℝ) :
    (∃ potential : State → ℝ,
      ∀ action, base action ≤
        dotProduct (delta action) potential) ↔
    ¬∃ coefficient : Action → ℝ,
      (∀ action, 0 ≤ coefficient action) ∧
      (∀ state,
        ∑ action, coefficient action * delta action state = 0) ∧
      0 < ∑ action, coefficient action * base action := by
  constructor
  · rintro ⟨potential, hpotential⟩
    rintro ⟨coefficient, hnonnegative, hbalance, hpositive⟩
    exact (not_lt_of_ge
      (not_nonnegative_incompatibility_of_potential
        hpotential hnonnegative hbalance)) hpositive
  · intro hnoCertificate
    rcases exists_potential_or_nonnegative_incompatibility delta base with
      hpotential | hcertificate
    · exact hpotential
    · exact False.elim (hnoCertificate hcertificate)

private theorem exists_positive_weighted_term
    [Fintype Action]
    {coefficient base : Action → ℝ}
    (hnonnegative : ∀ action, 0 ≤ coefficient action)
    (hpositive : 0 < ∑ action, coefficient action * base action) :
    ∃ action, 0 < coefficient action ∧ 0 < base action := by
  classical
  by_contra hnone
  push Not at hnone
  have hterm (action : Action) :
      coefficient action * base action ≤ 0 := by
    by_cases hzero : coefficient action = 0
    · simp [hzero]
    · have hcoefficient : 0 < coefficient action :=
        lt_of_le_of_ne (hnonnegative action) (Ne.symm hzero)
      have hbase : base action ≤ 0 := hnone action hcoefficient
      exact mul_nonpos_of_nonneg_of_nonpos
        (hnonnegative action) hbase
  have hsum :
      ∑ action, coefficient action * base action ≤ 0 :=
    Finset.sum_nonpos fun action _ => hterm action
  exact (not_lt_of_ge hsum) hpositive

/-- Bellman-residual form of the finite inequality alternative.

If `base action + level action ≤ 0` for every action, then a failure of
potential feasibility produces nonnegative balanced weights with positive
weighted base and strictly negative weighted level. In particular, one
positively weighted action has positive base. -/
theorem exists_potential_or_bellmanResidual_obstruction
    [Fintype State] [Fintype Action]
    (delta : Action → State → ℝ)
    (base level : Action → ℝ)
    (hresidual : ∀ action, base action + level action ≤ 0) :
    (∃ potential : State → ℝ,
      ∀ action, base action ≤
        dotProduct (delta action) potential) ∨
    (∃ coefficient : Action → ℝ,
      (∀ action, 0 ≤ coefficient action) ∧
      (∀ state,
        ∑ action, coefficient action * delta action state = 0) ∧
      0 < ∑ action, coefficient action * base action ∧
      ∑ action, coefficient action * level action < 0 ∧
      ∃ action, 0 < coefficient action ∧ 0 < base action) := by
  classical
  rcases exists_potential_or_nonnegative_incompatibility delta base with
    hpotential | ⟨coefficient, hnonnegative, hbalance, hbase⟩
  · exact Or.inl hpotential
  · right
    have hweightedResidual :
        ∑ action,
          coefficient action * (base action + level action) ≤ 0 := by
      exact Finset.sum_nonpos fun action _ =>
        mul_nonpos_of_nonneg_of_nonpos
          (hnonnegative action) (hresidual action)
    have hsplit :
        ∑ action,
          coefficient action * (base action + level action) =
        (∑ action, coefficient action * base action) +
          ∑ action, coefficient action * level action := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro action _
      ring
    have hlevel :
        ∑ action, coefficient action * level action < 0 := by
      rw [hsplit] at hweightedResidual
      linarith
    exact ⟨coefficient, hnonnegative, hbalance, hbase, hlevel,
      exists_positive_weighted_term hnonnegative hbase⟩

end Math
