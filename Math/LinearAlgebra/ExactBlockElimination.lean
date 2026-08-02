/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Exact finite block elimination

This file isolates the algebra used by exact state elimination.  Over a field,
an invertible leading block can be removed by its Schur complement.  Solutions
reconstruct exactly, affine residuals retain their literal value, and affine
continuation rebasing commutes with the reduction.

The results are about finite matrices only.  They do not attach stochastic,
ordered-germ, or asymptotic semantics to the coefficients.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace Math
namespace ExactBlockElimination

variable {𝕜 F R : Type*}
variable [Field 𝕜]
variable [Fintype F] [DecidableEq F] [Fintype R]

/-- The Schur complement obtained by eliminating the leading `F` block. -/
def schurComplement (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F R 𝕜) (C : Matrix R F 𝕜) (D : Matrix R R 𝕜) :
    Matrix R R 𝕜 :=
  D - C * ⅟A * B

/-- The right-hand side after eliminating the leading `F` block. -/
def reducedRhs (A : Matrix F F 𝕜) [Invertible A]
    (C : Matrix R F 𝕜) (bF : F → 𝕜) (bR : R → 𝕜) : R → 𝕜 :=
  bR - C *ᵥ (⅟A *ᵥ bF)

/-- Reconstruct the eliminated coordinates from retained coordinates. -/
def reconstructEliminated (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F R 𝕜) (bF : F → 𝕜) (xR : R → 𝕜) : F → 𝕜 :=
  ⅟A *ᵥ (bF - B *ᵥ xR)

/-- The row of an affine test after eliminating the leading block. -/
def reducedAffineRow (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F R 𝕜) (aF : F → 𝕜) (aR : R → 𝕜) : R → 𝕜 :=
  aR - (aF ᵥ* ⅟A) ᵥ* B

/-- The constant of an affine test after eliminating the leading block. -/
def reducedAffineConstant (A : Matrix F F 𝕜) [Invertible A]
    (aF bF : F → 𝕜) (c : 𝕜) : 𝕜 :=
  c - (aF ⬝ᵥ (⅟A *ᵥ bF))

/-- An affine residual written in two coordinate blocks. -/
def affineResidual (aF : F → 𝕜) (aR : R → 𝕜)
    (xF : F → 𝕜) (xR : R → 𝕜) (c : 𝕜) : 𝕜 :=
  (aF ⬝ᵥ xF) + (aR ⬝ᵥ xR) - c

theorem eliminated_block_reconstruction
    (A : Matrix F F 𝕜) [Invertible A] (B : Matrix F R 𝕜)
    (bF : F → 𝕜) (xR : R → 𝕜) :
    A *ᵥ reconstructEliminated A B bF xR + B *ᵥ xR = bF := by
  rw [reconstructEliminated, Matrix.mulVec_mulVec, mul_invOf_self,
    Matrix.one_mulVec]
  exact sub_add_cancel _ _

theorem retained_block_reconstruction_identity
    (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F R 𝕜) (C : Matrix R F 𝕜) (D : Matrix R R 𝕜)
    (bF : F → 𝕜) (xR : R → 𝕜) :
    C *ᵥ reconstructEliminated A B bF xR + D *ᵥ xR =
      C *ᵥ (⅟A *ᵥ bF) + schurComplement A B C D *ᵥ xR := by
  simp only [reconstructEliminated, schurComplement, Matrix.mulVec_sub,
    Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  abel

theorem retained_block_eq_iff_reduced
    (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F R 𝕜) (C : Matrix R F 𝕜) (D : Matrix R R 𝕜)
    (bF : F → 𝕜) (bR : R → 𝕜) (xR : R → 𝕜) :
    C *ᵥ reconstructEliminated A B bF xR + D *ᵥ xR = bR ↔
      schurComplement A B C D *ᵥ xR = reducedRhs A C bF bR := by
  rw [retained_block_reconstruction_identity]
  constructor
  · intro h
    apply (eq_sub_iff_add_eq).2
    simpa [reducedRhs, add_comm] using h
  · intro h
    have hadd := (eq_sub_iff_add_eq).1 h
    simpa [reducedRhs, add_comm] using hadd

/-- Solving the Schur-reduced equation and reconstructing gives a solution of
the original block system. -/
theorem reconstruct_solution
    (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F R 𝕜) (C : Matrix R F 𝕜) (D : Matrix R R 𝕜)
    (bF : F → 𝕜) (bR : R → 𝕜) (xR : R → 𝕜)
    (hreduced : schurComplement A B C D *ᵥ xR = reducedRhs A C bF bR) :
    Matrix.fromBlocks A B C D *ᵥ
        Sum.elim (reconstructEliminated A B bF xR) xR =
      Sum.elim bF bR := by
  rw [Matrix.fromBlocks_mulVec]
  funext coordinate
  cases coordinate with
  | inl coordinate =>
      exact congrFun (eliminated_block_reconstruction A B bF xR) coordinate
  | inr coordinate =>
      exact congrFun ((retained_block_eq_iff_reduced A B C D bF bR xR).2 hreduced)
        coordinate

/-- Conversely, every solution of the original block system has the canonical
reconstructed eliminated coordinates and solves the reduced equation. -/
theorem solution_iff_reconstruction_and_reduced
    (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F R 𝕜) (C : Matrix R F 𝕜) (D : Matrix R R 𝕜)
    (bF : F → 𝕜) (bR : R → 𝕜) (xF : F → 𝕜) (xR : R → 𝕜) :
    Matrix.fromBlocks A B C D *ᵥ Sum.elim xF xR = Sum.elim bF bR ↔
      xF = reconstructEliminated A B bF xR ∧
        schurComplement A B C D *ᵥ xR = reducedRhs A C bF bR := by
  constructor
  · intro hsystem
    have hF : A *ᵥ xF + B *ᵥ xR = bF := by
      funext coordinate
      simpa [Matrix.fromBlocks_mulVec] using congrFun hsystem (Sum.inl coordinate)
    have hR : C *ᵥ xF + D *ᵥ xR = bR := by
      funext coordinate
      simpa [Matrix.fromBlocks_mulVec] using congrFun hsystem (Sum.inr coordinate)
    have hxF : xF = reconstructEliminated A B bF xR := by
      have hAxF : A *ᵥ xF = bF - B *ᵥ xR :=
        (eq_sub_iff_add_eq).2 hF
      apply_fun fun y => ⅟A *ᵥ y at hAxF
      simpa [reconstructEliminated, Matrix.mulVec_mulVec, invOf_mul_self]
        using hAxF
    refine ⟨hxF, ?_⟩
    apply (retained_block_eq_iff_reduced A B C D bF bR xR).1
    simpa [← hxF] using hR
  · rintro ⟨rfl, hreduced⟩
    exact reconstruct_solution A B C D bF bR xR hreduced

/-- Reducing an affine row and its constant preserves the residual literally,
not merely up to sign or multiplication by a unit. -/
theorem affineResidual_reconstructEliminated
    (A : Matrix F F 𝕜) [Invertible A] (B : Matrix F R 𝕜)
    (bF aF : F → 𝕜) (aR xR : R → 𝕜) (c : 𝕜) :
    affineResidual aF aR (reconstructEliminated A B bF xR) xR c =
      (reducedAffineRow A B aF aR ⬝ᵥ xR) -
        reducedAffineConstant A aF bF c := by
  simp only [affineResidual, reconstructEliminated, reducedAffineRow,
    reducedAffineConstant, Matrix.mulVec_sub, dotProduct_sub,
    Matrix.dotProduct_mulVec, sub_dotProduct]
  ring

/-- Rebase a finite linear system by changing the continuation origin. -/
def rebaseRhs {S : Type*} [Fintype S]
    (M : Matrix S S 𝕜) (b h : S → 𝕜) : S → 𝕜 :=
  b - M *ᵥ h

/-- Rebase the constant in an affine test. -/
def rebaseAffineConstant {S : Type*} [Fintype S]
    (a : S → 𝕜) (c : 𝕜) (h : S → 𝕜) : 𝕜 :=
  c - (a ⬝ᵥ h)

omit [DecidableEq F] in
theorem affineResidual_rebase
    (aF : F → 𝕜) (aR : R → 𝕜)
    (xF hF : F → 𝕜) (xR hR : R → 𝕜) (c : 𝕜) :
    affineResidual aF aR (xF - hF) (xR - hR)
        (c - (aF ⬝ᵥ hF + aR ⬝ᵥ hR)) =
      affineResidual aF aR xF xR c := by
  simp only [affineResidual, dotProduct_sub]
  ring

theorem rebaseRhs_add {S : Type*} [Fintype S]
    (M : Matrix S S 𝕜) (b h k : S → 𝕜) :
    rebaseRhs M (rebaseRhs M b h) k = rebaseRhs M b (h + k) := by
  simp only [rebaseRhs, Matrix.mulVec_add]
  abel

theorem rebaseAffineConstant_add {S : Type*} [Fintype S]
    (a : S → 𝕜) (c : 𝕜) (h k : S → 𝕜) :
    rebaseAffineConstant a (rebaseAffineConstant a c h) k =
      rebaseAffineConstant a c (h + k) := by
  simp only [rebaseAffineConstant, dotProduct_add]
  ring

/-- Reducing a rebased right-hand side equals rebasing the reduced system by
the retained part of the same continuation. -/
theorem reducedRhs_rebase
    (A : Matrix F F 𝕜) [Invertible A]
    (B : Matrix F R 𝕜) (C : Matrix R F 𝕜) (D : Matrix R R 𝕜)
    (bF hF : F → 𝕜) (bR hR : R → 𝕜) :
    reducedRhs A C
        (bF - (A *ᵥ hF + B *ᵥ hR))
        (bR - (C *ᵥ hF + D *ᵥ hR)) =
      reducedRhs A C bF bR - schurComplement A B C D *ᵥ hR := by
  simp only [reducedRhs, schurComplement, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, invOf_mul_self,
    Matrix.one_mulVec]
  abel

/-- The affine-test constant transforms compatibly with a rebase and block
elimination. -/
theorem reducedAffineConstant_rebase
    (A : Matrix F F 𝕜) [Invertible A] (B : Matrix F R 𝕜)
    (bF hF aF : F → 𝕜) (aR hR : R → 𝕜) (c : 𝕜) :
    reducedAffineConstant A aF
        (bF - (A *ᵥ hF + B *ᵥ hR))
        (c - (aF ⬝ᵥ hF + aR ⬝ᵥ hR)) =
      reducedAffineConstant A aF bF c -
        (reducedAffineRow A B aF aR ⬝ᵥ hR) := by
  simp only [reducedAffineConstant, reducedAffineRow, Matrix.mulVec_add,
    Matrix.mulVec_sub, Matrix.mulVec_mulVec, dotProduct_sub, Matrix.dotProduct_mulVec,
    dotProduct_add, sub_dotProduct, Matrix.vecMul_vecMul, invOf_mul_self,
    Matrix.one_mulVec]
  ring

end ExactBlockElimination
end Math
