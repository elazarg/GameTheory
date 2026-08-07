/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.FourierMotzkin

/-!
# Affine equalities plus inequalities: the resolved Farkas alternative

A resolved projective chart produces a finite affine tangent system

`A h = b`,

`G h ≥ 0`.

This file packages the repository's theorem of the alternative in exactly that
form.  Equalities are encoded as the pair of weak inequalities
`A h ≥ b` and `-A h ≥ -b`.  If the system is infeasible, the ordinary
nonnegative Farkas multipliers of the encoded rows decode into an unrestricted
multiplier `y` for the equalities and a nonnegative multiplier `lambda` for
the inequalities:

`Aᵀ y + Gᵀ lambda = 0`,

`bᵀ y > 0`.

This is a local linear-algebra theorem.  It does not decode a Farkas row into
a game-theoretic strategy, punishment, chronological path, or rank-descent
certificate.
-/

open Finset BigOperators

namespace Math
namespace LinearAlgebra

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {EqRow IneqRow : Type*}
  [Fintype EqRow] [DecidableEq EqRow]
  [Fintype IneqRow] [DecidableEq IneqRow]
variable {n : ℕ}

/-- Rows of the weak-inequality encoding.  `false` is the positive equality
row and `true` is its negation. -/
abbrev AffineEqualityFarkasRow (EqRow IneqRow : Type*) :=
  (EqRow × Bool) ⊕ IneqRow

/-- Matrix of the weak-inequality encoding of `A h = b`, `G h ≥ 0`. -/
def affineEqualityFarkasMatrix
    (A : EqRow → Fin n → 𝕜) (G : IneqRow → Fin n → 𝕜) :
    AffineEqualityFarkasRow EqRow IneqRow → Fin n → 𝕜
  | Sum.inl (row, false), column => A row column
  | Sum.inl (row, true), column => -A row column
  | Sum.inr row, column => G row column

/-- Right-hand side of the weak-inequality encoding. -/
def affineEqualityFarkasRhs
    (b : EqRow → 𝕜) : AffineEqualityFarkasRow EqRow IneqRow → 𝕜
  | Sum.inl (row, false) => b row
  | Sum.inl (row, true) => -b row
  | Sum.inr _ => 0

/-- Feasibility of the resolved affine tangent system. -/
def IsAffineEqualityInequalityFeasible
    (A : EqRow → Fin n → 𝕜) (b : EqRow → 𝕜)
    (G : IneqRow → Fin n → 𝕜) : Prop :=
  ∃ h : Fin n → 𝕜,
    (∀ row, ∑ column, A row column * h column = b row) ∧
    ∀ row, 0 ≤ ∑ column, G row column * h column

/-- A decoded Farkas obstruction for `A h = b`, `G h ≥ 0`. -/
def IsAffineEqualityFarkasCertificate
    (A : EqRow → Fin n → 𝕜) (b : EqRow → 𝕜)
    (G : IneqRow → Fin n → 𝕜)
    (y : EqRow → 𝕜) (lambda : IneqRow → 𝕜) : Prop :=
  (∀ row, 0 ≤ lambda row) ∧
    (∀ column,
      (∑ row, y row * A row column) +
        ∑ row, lambda row * G row column = 0) ∧
    0 < ∑ row, y row * b row

/-- The weak-inequality encoding is feasible exactly when the original affine
system is feasible. -/
theorem isFeasible_affineEqualityFarkas_iff
    (A : EqRow → Fin n → 𝕜) (b : EqRow → 𝕜)
    (G : IneqRow → Fin n → 𝕜) :
    IsFeasible (affineEqualityFarkasMatrix A G)
        (affineEqualityFarkasRhs (IneqRow := IneqRow) b) ↔
      IsAffineEqualityInequalityFeasible A b G := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_, ?_⟩
    · intro row
      have hpos := hh (Sum.inl (row, false))
      have hneg := hh (Sum.inl (row, true))
      simp only [affineEqualityFarkasRhs, rowEval,
        affineEqualityFarkasMatrix] at hpos hneg
      linarith
    · intro row
      have hineq := hh (Sum.inr row)
      simpa only [affineEqualityFarkasRhs, rowEval,
        affineEqualityFarkasMatrix] using hineq
  · rintro ⟨h, heq, hineq⟩
    refine ⟨h, ?_⟩
    intro row
    rcases row with ⟨eqRow, sign⟩ | ineqRow
    · cases sign with
      | false =>
          simp only [affineEqualityFarkasRhs, rowEval,
            affineEqualityFarkasMatrix]
          exact le_of_eq (heq eqRow).symm
      | true =>
          simp only [affineEqualityFarkasRhs, rowEval,
            affineEqualityFarkasMatrix, Finset.sum_neg_distrib]
          exact neg_le_neg (le_of_eq (heq eqRow).symm)
    · simpa only [affineEqualityFarkasRhs, rowEval,
        affineEqualityFarkasMatrix] using hineq ineqRow

/-- Decode the unrestricted equality multiplier from the two nonnegative
multipliers of the equality row and its negation. -/
def affineEqualityFarkasY
    (u : AffineEqualityFarkasRow EqRow IneqRow → 𝕜)
    (row : EqRow) : 𝕜 :=
  u (Sum.inl (row, false)) - u (Sum.inl (row, true))

/-- Decode the nonnegative inequality multiplier. -/
def affineEqualityFarkasLambda
    (u : AffineEqualityFarkasRow EqRow IneqRow → 𝕜)
    (row : IneqRow) : 𝕜 :=
  u (Sum.inr row)

/-- Infeasibility of the resolved affine system produces the expected decoded
Farkas row. -/
theorem exists_affineEqualityFarkasCertificate_of_not_feasible
    (A : EqRow → Fin n → 𝕜) (b : EqRow → 𝕜)
    (G : IneqRow → Fin n → 𝕜)
    (hinfeasible : ¬IsAffineEqualityInequalityFeasible A b G) :
    ∃ y : EqRow → 𝕜, ∃ lambda : IneqRow → 𝕜,
      IsAffineEqualityFarkasCertificate A b G y lambda := by
  have hencoded :
      ¬IsFeasible (affineEqualityFarkasMatrix A G)
        (affineEqualityFarkasRhs (IneqRow := IneqRow) b) := by
    intro h
    exact hinfeasible
      ((isFeasible_affineEqualityFarkas_iff A b G).1 h)
  obtain ⟨u, huNonneg, huColumns, huPositive⟩ :=
    (theorem_of_alternative
      (affineEqualityFarkasMatrix A G)
      (affineEqualityFarkasRhs (IneqRow := IneqRow) b)).1 hencoded
  refine ⟨affineEqualityFarkasY u,
    affineEqualityFarkasLambda u, ?_, ?_, ?_⟩
  · intro row
    exact huNonneg (Sum.inr row)
  · intro column
    have hcolumn := huColumns column
    simp only [affineEqualityFarkasMatrix,
      affineEqualityFarkasY, affineEqualityFarkasLambda,
      Fintype.sum_sum_type, Fintype.sum_prod_type,
      Bool.sum_bool] at hcolumn ⊢
    linear_combination hcolumn
  · have hpositive := huPositive
    simp only [affineEqualityFarkasRhs,
      affineEqualityFarkasY,
      Fintype.sum_sum_type, Fintype.sum_prod_type,
      Bool.sum_bool, mul_neg] at hpositive ⊢
    convert hpositive using 1 <;> ring

/-- **Resolved affine pivot-or-Farkas alternative.**  Either a physical
candidate tangent satisfies all frozen affine equations and inequalities, or
a decoded Farkas obstruction exists. -/
theorem affineEqualityInequality_feasible_or_farkas
    (A : EqRow → Fin n → 𝕜) (b : EqRow → 𝕜)
    (G : IneqRow → Fin n → 𝕜) :
    IsAffineEqualityInequalityFeasible A b G ∨
      ∃ y : EqRow → 𝕜, ∃ lambda : IneqRow → 𝕜,
        IsAffineEqualityFarkasCertificate A b G y lambda := by
  by_cases h : IsAffineEqualityInequalityFeasible A b G
  · exact Or.inl h
  · exact Or.inr
      (exists_affineEqualityFarkasCertificate_of_not_feasible A b G h)

end LinearAlgebra
end Math
