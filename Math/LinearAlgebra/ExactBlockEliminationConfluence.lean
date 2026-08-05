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
    (B : Matrix F G 𝕜) (C : Matrix F Y 𝕜)
    (D : Matrix G F 𝕜) (E : Matrix G G 𝕜)
    (L : Matrix G Y 𝕜) (P : Matrix X F 𝕜)
    (Q : Matrix X G 𝕜) (T : Matrix X Y 𝕜)
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

omit [Field 𝕜] [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G] in
theorem fromRows_replicateCol (xF : F → 𝕜) (xG : G → 𝕜) :
    Matrix.fromRows (Matrix.replicateCol Unit xF)
        (Matrix.replicateCol Unit xG) =
      Matrix.replicateCol Unit (Sum.elim xF xG) := by
  ext (coordinate | coordinate) (_ : Unit) <;> rfl

omit [Field 𝕜] [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G] in
theorem fromCols_replicateRow (xF : F → 𝕜) (xG : G → 𝕜) :
    Matrix.fromCols (Matrix.replicateRow Unit xF)
        (Matrix.replicateRow Unit xG) =
      Matrix.replicateRow Unit (Sum.elim xF xG) := by
  ext (_ : Unit) (coordinate | coordinate) <;> rfl

omit [Field 𝕜] in
@[simp]
theorem scalarBlock_inj {c d : 𝕜} : scalarBlock c = scalarBlock d ↔ c = d := by
  constructor
  · intro h
    exact congr_fun₂ h () ()
  · exact congrArg scalarBlock

/-- Two-step reduction of a right-hand side equals one-step reduction by the
union block. -/
theorem reducedRhs_reducedRhs
    (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F G 𝕜) (D : Matrix G F 𝕜) (E : Matrix G G 𝕜)
    (P : Matrix R F 𝕜) (Q : Matrix R G 𝕜)
    (bF : F → 𝕜) (bG : G → 𝕜) (bR : R → 𝕜)
    [Invertible (E - D * ⅟A * B)] :
    reducedRhs (E - D * ⅟A * B) (quotientBlock A P B Q)
        (reducedRhs A D bF bG) (reducedRhs A P bF bR) =
      letI : Invertible (Matrix.fromBlocks A B D E) :=
        Matrix.fromBlocks₁₁Invertible A B D E
      reducedRhs (Matrix.fromBlocks A B D E) (Matrix.fromCols P Q)
        (Sum.elim bF bG) bR := by
  have h := quotientBlock_quotientBlock A B (Matrix.replicateCol Unit bF)
    D E (Matrix.replicateCol Unit bG) P Q (Matrix.replicateCol Unit bR)
  simpa only [quotientBlock_replicateCol, fromRows_replicateCol,
    Matrix.replicateCol_inj] using h

/-- Two-step reduction of an affine row equals one-step reduction by the union
block. -/
theorem reducedAffineRow_reducedAffineRow
    (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F G 𝕜) (C : Matrix F R 𝕜)
    (D : Matrix G F 𝕜) (E : Matrix G G 𝕜) (L : Matrix G R 𝕜)
    (aF : F → 𝕜) (aG : G → 𝕜) (aR : R → 𝕜)
    [Invertible (E - D * ⅟A * B)] :
    reducedAffineRow (E - D * ⅟A * B) (quotientBlock A D C L)
        (reducedAffineRow A B aF aG) (reducedAffineRow A C aF aR) =
      letI : Invertible (Matrix.fromBlocks A B D E) :=
        Matrix.fromBlocks₁₁Invertible A B D E
      reducedAffineRow (Matrix.fromBlocks A B D E) (Matrix.fromRows C L)
        (Sum.elim aF aG) aR := by
  have h := quotientBlock_quotientBlock A B C D E L
    (Matrix.replicateRow Unit aF) (Matrix.replicateRow Unit aG)
    (Matrix.replicateRow Unit aR)
  simpa only [quotientBlock_replicateRow, fromCols_replicateRow,
    Matrix.replicateRow_inj] using h

/-- Two-step reduction of an affine-test constant equals one-step reduction by
the union block, using the correspondingly reduced row and right-hand side. -/
theorem reducedAffineConstant_reducedAffineConstant
    (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F G 𝕜) (D : Matrix G F 𝕜) (E : Matrix G G 𝕜)
    (aF bF : F → 𝕜) (aG bG : G → 𝕜) (c : 𝕜)
    [Invertible (E - D * ⅟A * B)] :
    reducedAffineConstant (E - D * ⅟A * B)
        (reducedAffineRow A B aF aG) (reducedRhs A D bF bG)
        (reducedAffineConstant A aF bF c) =
      letI : Invertible (Matrix.fromBlocks A B D E) :=
        Matrix.fromBlocks₁₁Invertible A B D E
      reducedAffineConstant (Matrix.fromBlocks A B D E)
        (Sum.elim aF aG) (Sum.elim bF bG) c := by
  have h := quotientBlock_quotientBlock A B (Matrix.replicateCol Unit bF)
    D E (Matrix.replicateCol Unit bG) (Matrix.replicateRow Unit aF)
    (Matrix.replicateRow Unit aG) (scalarBlock c)
  simpa only [quotientBlock_replicateCol, quotientBlock_replicateRow,
    quotientBlock_scalarBlock, fromRows_replicateCol, fromCols_replicateRow,
    scalarBlock_inj] using h

end ExactBlockElimination
end Math
