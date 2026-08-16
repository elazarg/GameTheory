/-
# EXP-104: rank-one finite-table algebra

This module contains the representation-neutral algebra needed after a moral
component argument has separated a finite factor product.  A future graph
proof must supply two component scores `left` and `right` and the pointwise
identity

`joint z x y = left z x * right z y`.

No probability normalization, positivity, nonemptiness, graph structure, or
conditional-law construction is used below.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.FiniteBNRankOne

universe uX uY uZ uR

variable {X : Type uX} {Y : Type uY} {Z : Type uZ} {R : Type uR}

/-- Summing a rank-one table over its second coordinate leaves the first
factor times the total right factor. -/
theorem sum_right_of_rankOne [Fintype Y] [CommSemiring R]
    (joint : Z → X → Y → R) (left : Z → X → R)
    (right : Z → Y → R)
    (hjoint : ∀ z x y, joint z x y = left z x * right z y)
    (z : Z) (x : X) :
    ∑ y, joint z x y = left z x * ∑ y, right z y := by
  simp_rw [hjoint]
  exact (Finset.mul_sum Finset.univ (fun y => right z y) (left z x)).symm

/-- Summing a rank-one table over its first coordinate leaves the total left
factor times the second factor. -/
theorem sum_left_of_rankOne [Fintype X] [CommSemiring R]
    (joint : Z → X → Y → R) (left : Z → X → R)
    (right : Z → Y → R)
    (hjoint : ∀ z x y, joint z x y = left z x * right z y)
    (z : Z) (y : Y) :
    ∑ x, joint z x y = (∑ x, left z x) * right z y := by
  simp_rw [hjoint]
  exact (Finset.sum_mul Finset.univ (fun x => left z x) (right z y)).symm

/-- The total of a finite rank-one table is the product of the two factor
totals. -/
theorem sum_sum_of_rankOne [Fintype X] [Fintype Y] [CommSemiring R]
    (joint : Z → X → Y → R) (left : Z → X → R)
    (right : Z → Y → R)
    (hjoint : ∀ z x y, joint z x y = left z x * right z y)
    (z : Z) :
    ∑ x, ∑ y, joint z x y =
      (∑ x, left z x) * ∑ y, right z y := by
  simp_rw [hjoint]
  exact (Fintype.sum_mul_sum (left z) (right z)).symm

/-- Every finite rank-one table satisfies the division-free cross-product
identity.  This is the exact algebraic conclusion consumed by finite
conditional-independence proofs, including at zero-mass evidence values. -/
theorem crossMul_of_rankOne [Fintype X] [Fintype Y] [CommSemiring R]
    (joint : Z → X → Y → R) (left : Z → X → R)
    (right : Z → Y → R)
    (hjoint : ∀ z x y, joint z x y = left z x * right z y) :
    ∀ z x y,
      joint z x y * (∑ x', ∑ y', joint z x' y') =
        (∑ y', joint z x y') * ∑ x', joint z x' y := by
  intro z x y
  rw [hjoint, sum_sum_of_rankOne joint left right hjoint,
    sum_right_of_rankOne joint left right hjoint,
    sum_left_of_rankOne joint left right hjoint]
  ac_rfl

/-! ## Numeric controls -/

namespace Controls

def left (_ : Unit) (x : Fin 2) : ℕ := x.1 + 1

def right (_ : Unit) (y : Fin 2) : ℕ := y.1 + 3

def rankOne (_ : Unit) (x y : Fin 2) : ℕ := left () x * right () y

theorem rankOne_factorization (z : Unit) (x y : Fin 2) :
    rankOne z x y = left z x * right z y := rfl

/-- The positive `[[3,4],[6,8]]` table passes the cross-product identity. -/
theorem rankOne_crossMul :
    ∀ x y : Fin 2,
      rankOne () x y * (∑ x', ∑ y', rankOne () x' y') =
        (∑ y', rankOne () x y') * ∑ x', rankOne () x' y :=
  crossMul_of_rankOne rankOne left right rankOne_factorization ()

/-- The selected positive control evaluates both sides to `84`. -/
theorem rankOne_numeric :
    rankOne () 0 1 * (∑ x', ∑ y', rankOne () x' y') = 84 := by
  norm_num [rankOne, left, right, Finset.univ_fin2]

def diagonal (_ : Unit) (x y : Fin 2) : ℕ :=
  if x = y then 1 else 0

/-- The diagonal `[[1,0],[0,1]]` table is not rank one: its `(0,0)` joint
minor violates the cross-product identity (`2 ≠ 1`). -/
theorem diagonal_rejects_crossMul :
    ¬ ∀ x y : Fin 2,
      diagonal () x y * (∑ x', ∑ y', diagonal () x' y') =
        (∑ y', diagonal () x y') * ∑ x', diagonal () x' y := by
  intro hcross
  have hbad := hcross 0 0
  norm_num [diagonal, Finset.univ_fin2] at hbad
  have hcard :
      {x ∈ ({0, 1} : Finset (Fin 2)) | x = 0 ∨ x = 1}.card = 2 := by
    decide
  rw [hcard] at hbad
  norm_num at hbad

end Controls

end GameTheory.Experimental.PostArchitecture.FiniteBNRankOne
