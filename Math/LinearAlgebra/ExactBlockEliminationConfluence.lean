/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.ExactBlockElimination
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Confluence of exact block elimination

This file proves the Crabtree--Haynsworth quotient formula for the finite exact
block-elimination layer.  Eliminating one leading block and then a second gives
literally the same retained matrix as eliminating their union, once both use
the common `F ⊕ G` coordinate order.

Right-hand sides and affine tests are included by representing them as column
and row blocks.  No asymptotic truncation or stochastic interpretation occurs
here.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace Math
namespace ExactBlockElimination

variable {𝕜 F G R X Y : Type*}
variable [Field 𝕜]
variable [Fintype F] [DecidableEq F]
variable [Fintype G] [DecidableEq G]

/-- The rectangular block update induced by eliminating an invertible square
leading block. -/
def quotientBlock (A : Matrix F F 𝕜) [Invertible A]
    (left : Matrix X F 𝕜) (right : Matrix F Y 𝕜)
    (corner : Matrix X Y 𝕜) : Matrix X Y 𝕜 :=
  corner - left * ⅟A * right

theorem schurComplement_eq_quotientBlock
    (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F R 𝕜) (C : Matrix R F 𝕜) (D : Matrix R R 𝕜) :
    schurComplement A B C D = quotientBlock A C B D :=
  rfl

/-- Crabtree--Haynsworth quotient formula in a fixed sum-coordinate order.
The hypotheses are exactly the invertibility of the first pivot and of the
second pivot after the first elimination. -/
theorem quotientBlock_quotientBlock
    (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F G 𝕜) (C : Matrix F R 𝕜)
    (D : Matrix G F 𝕜) (E : Matrix G G 𝕜)
    (L : Matrix G R 𝕜) (P : Matrix R F 𝕜)
    (Q : Matrix R G 𝕜) (T : Matrix R R 𝕜)
    [Invertible (E - D * ⅟A * B)] :
    quotientBlock (E - D * ⅟A * B)
        (quotientBlock A P B Q) (quotientBlock A D C L)
        (quotientBlock A P C T) =
      letI : Invertible (Matrix.fromBlocks A B D E) :=
        Matrix.fromBlocks₁₁Invertible A B D E
      quotientBlock (Matrix.fromBlocks A B D E)
        (Matrix.fromCols P Q) (Matrix.fromRows C L) T := by
  letI : Invertible (Matrix.fromBlocks A B D E) :=
    Matrix.fromBlocks₁₁Invertible A B D E
  simp only [quotientBlock]
  rw [Matrix.invOf_fromBlocks₁₁_eq]
  simp only [Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows,
    sub_eq_add_neg, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- A scalar regarded as a one-by-one matrix. -/
def scalarBlock (c : 𝕜) : Matrix Unit Unit 𝕜 :=
  fun _ _ => c

theorem quotientBlock_replicateCol
    (A : Matrix F F 𝕜) [Invertible A]
    (C : Matrix R F 𝕜) (bF : F → 𝕜) (bR : R → 𝕜) :
    quotientBlock A C (Matrix.replicateCol Unit bF)
        (Matrix.replicateCol Unit bR) =
      Matrix.replicateCol Unit (reducedRhs A C bF bR) := by
  unfold quotientBlock reducedRhs
  rw [Matrix.mul_assoc,
    ← Matrix.replicateCol_mulVec (ι := Unit) (⅟A) bF,
    ← Matrix.replicateCol_mulVec (ι := Unit) C (⅟A *ᵥ bF)]
  rfl

theorem quotientBlock_replicateRow
    (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F R 𝕜) (aF : F → 𝕜) (aR : R → 𝕜) :
    quotientBlock A (Matrix.replicateRow Unit aF) B
        (Matrix.replicateRow Unit aR) =
      Matrix.replicateRow Unit (reducedAffineRow A B aF aR) := by
  ext (_ : Unit) coordinate
  simp [quotientBlock, reducedAffineRow, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Matrix.mul_assoc]

theorem quotientBlock_scalarBlock
    (A : Matrix F F 𝕜) [Invertible A]
    (aF bF : F → 𝕜) (c : 𝕜) :
    quotientBlock A (Matrix.replicateRow Unit aF)
        (Matrix.replicateCol Unit bF) (scalarBlock c) =
      scalarBlock (reducedAffineConstant A aF bF c) := by
  ext (_ : Unit) (_ : Unit)
  simp [quotientBlock, scalarBlock, reducedAffineConstant, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.mul_assoc]

end ExactBlockElimination
end Math
