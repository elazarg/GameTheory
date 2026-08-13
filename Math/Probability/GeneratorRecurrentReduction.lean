/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite Markov generators and their recurrent quotient reduction

This file develops the first two layers of the multiscale Abel reduction for
finite state spaces, in a strictly *resolvent-only* formulation: no matrix
exponential appears anywhere.

## Layer 0: generators and resolvents

A real square matrix is a `Math.Probability.IsGenerator` when its off-diagonal
entries are nonnegative and every row sums to zero.  Subtracting the identity
from a stochastic matrix produces one.  For a generator `G` and `z > 0` the
*resolvent matrix* `z • 1 - G` is invertible and the normalized resolvent
`z • (z • 1 - G)⁻¹` is stochastic.  Both facts come from a discrete minimum
principle rather than from a Neumann series: at a coordinate where a vector is
minimal, a generator has nonnegative drift, so `(z • 1 - G) x ≥ 0` forces
`x ≥ 0`.  The criterion is sharp: rows summing to zero together with resolvent
nonnegativity *for every* `z > 0` characterizes generators.

## Layer 1: the recurrent quotient and the invariant graph

The recurrent data of a generator is packaged as
`Math.Probability.ErgodicQuotientData`: an absorption matrix `H` from states to
classes, a stationary matrix `J` from classes to states, both stochastic, with
`G * H = 0`, `J * G = 0`, `J * H = 1`, and the harmonic-representation axiom
that every `G`-harmonic vector is an absorption average.  From those fields the
ergodic projection `Π = H * J`, the invertibility of `G + Π`, the group inverse
`G# = (G + Π)⁻¹ - Π` and its identities, and the bijectivity of `G` on
`ker (J · )` are all derived.

The reduction itself is the invariant-graph equation

`redEq A W = (1 - Π) * A * (H + W) - W * (J * A * (H + W))`

on the linear slice `{W | J * W = 0}`, whose zero set carries the reduced
generator `Red A W = J * A * (H + W)` intertwined with `A` through
`U = H + W`.  Row sums, the two equivariances (reparameterization and scalar
rescaling), the base-point linearization, and the first-order coefficients are
proved here.

## Scope

Everything below is stated pointwise in the deformation parameter, so no
analytic machinery is used.  The nondegeneracy input for an analytic implicit
function theorem is supplied in the form it is needed: `redEq_base` identifies
the invariant-graph equation at the base point with `W ↦ G * W`, and
`bijective_graphSliceGenerator` shows that this map is a bijection of the slice
`{W | J * W = 0}`.  Producing an *analytic family* `W t` from that data is not
carried out in this file.
-/

noncomputable section

namespace Math
namespace Probability

open Finset
open scoped Matrix

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Stochastic matrices and generators -/

/-- A real (possibly rectangular) matrix is stochastic when all its entries are
nonnegative and each of its rows sums to one. -/
structure IsStochasticMatrix {m n : Type*} [Fintype n] (P : Matrix m n ℝ) : Prop where
  /-- All entries are nonnegative. -/
  nonneg : ∀ i j, 0 ≤ P i j
  /-- Every row sums to one. -/
  mulVec_one : P *ᵥ (1 : n → ℝ) = (1 : m → ℝ)

/-- Row sums of a stochastic matrix, in explicit summation form. -/
theorem IsStochasticMatrix.row_sum {m n : Type*} [Fintype n] {P : Matrix m n ℝ}
    (hP : IsStochasticMatrix P) (i : m) : ∑ j, P i j = 1 := by
  have h := congrFun hP.mulVec_one i
  simpa [Matrix.mulVec, dotProduct] using h

/-- Entries of a stochastic matrix are bounded by one. -/
theorem IsStochasticMatrix.le_one {m n : Type*} [Fintype n] {P : Matrix m n ℝ}
    (hP : IsStochasticMatrix P) (i : m) (j : n) : P i j ≤ 1 := by
  rw [← hP.row_sum i]
  exact Finset.single_le_sum (fun k _ => hP.nonneg i k) (Finset.mem_univ j)

/-- Entries of a stochastic matrix have absolute value at most one. -/
theorem IsStochasticMatrix.abs_le_one {m n : Type*} [Fintype n] {P : Matrix m n ℝ}
    (hP : IsStochasticMatrix P) (i : m) (j : n) : |P i j| ≤ 1 := by
  rw [abs_of_nonneg (hP.nonneg i j)]
  exact hP.le_one i j

/-- A real square matrix is a Markov generator when its off-diagonal entries are
nonnegative and every row sums to zero. -/
structure IsGenerator (G : Matrix S S ℝ) : Prop where
  /-- Off-diagonal entries are nonnegative. -/
  offDiag_nonneg : ∀ i j, i ≠ j → 0 ≤ G i j
  /-- Every row sums to zero. -/
  mulVec_one : G *ᵥ (1 : S → ℝ) = 0

omit [DecidableEq S] in
/-- Row sums of a generator, in explicit summation form. -/
theorem IsGenerator.row_sum {G : Matrix S S ℝ} (hG : IsGenerator G) (i : S) :
    ∑ j, G i j = 0 := by
  have h := congrFun hG.mulVec_one i
  simpa [Matrix.mulVec, dotProduct] using h

/-- Subtracting the identity from a stochastic matrix gives a generator. -/
theorem isGenerator_sub_one {P : Matrix S S ℝ} (hP : IsStochasticMatrix P) :
    IsGenerator (P - 1) where
  offDiag_nonneg i j hij := by
    simpa [Matrix.one_apply_ne hij] using hP.nonneg i j
  mulVec_one := by
    rw [Matrix.sub_mulVec, hP.mulVec_one, Matrix.one_mulVec, sub_self]

omit [DecidableEq S] in
/-- **Discrete minimum principle.**  At a coordinate where a vector attains its
minimum, a generator has nonnegative drift. -/
theorem IsGenerator.mulVec_nonneg_of_isMin {G : Matrix S S ℝ} (hG : IsGenerator G)
    (x : S → ℝ) (i : S) (hi : ∀ j, x i ≤ x j) : 0 ≤ (G *ᵥ x) i := by
  have hval : (G *ᵥ x) i = ∑ j, G i j * x j := by
    simp [Matrix.mulVec, dotProduct]
  have hsplit : ∑ j, G i j * (x j - x i) = (G *ᵥ x) i := by
    have hrow := hG.row_sum i
    calc ∑ j, G i j * (x j - x i)
        = (∑ j, G i j * x j) - (∑ j, G i j) * x i := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = (G *ᵥ x) i := by rw [hrow, zero_mul, sub_zero, hval]
  rw [← hsplit]
  refine Finset.sum_nonneg fun j _ => ?_
  rcases eq_or_ne j i with hj | hj
  · simp [hj]
  · exact mul_nonneg (hG.offDiag_nonneg i j (Ne.symm hj)) (sub_nonneg.mpr (hi j))

/-! ## The resolvent of a generator -/

/-- The resolvent matrix `z • 1 - G` of a square matrix `G`. -/
def resolventMatrix (G : Matrix S S ℝ) (z : ℝ) : Matrix S S ℝ :=
  z • (1 : Matrix S S ℝ) - G

/-- Action of the resolvent matrix on a vector. -/
theorem resolventMatrix_mulVec (G : Matrix S S ℝ) (z : ℝ) (x : S → ℝ) :
    resolventMatrix G z *ᵥ x = z • x - G *ᵥ x := by
  rw [resolventMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The resolvent matrix of a generator sends the all-ones vector to `z • 1`. -/
theorem resolventMatrix_mulVec_one {G : Matrix S S ℝ} (hrow : G *ᵥ (1 : S → ℝ) = 0) (z : ℝ) :
    resolventMatrix G z *ᵥ (1 : S → ℝ) = z • (1 : S → ℝ) := by
  rw [resolventMatrix_mulVec, hrow, sub_zero]

/-- **Inverse positivity.**  For a generator and `z > 0`, a vector with
nonnegative resolvent image is itself nonnegative. -/
theorem nonneg_of_resolventMatrix_mulVec_nonneg {G : Matrix S S ℝ} (hG : IsGenerator G)
    {z : ℝ} (hz : 0 < z) {x : S → ℝ}
    (hx : ∀ i, 0 ≤ (resolventMatrix G z *ᵥ x) i) : ∀ i, 0 ≤ x i := by
  rcases isEmpty_or_nonempty S with hS | hS
  · exact fun i => (hS.false i).elim
  obtain ⟨i₀, -, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset S) x
      ⟨Classical.arbitrary S, Finset.mem_univ _⟩
  have hdrift : 0 ≤ (G *ᵥ x) i₀ :=
    hG.mulVec_nonneg_of_isMin x i₀ fun j => hmin j (Finset.mem_univ j)
  have hval := hx i₀
  rw [resolventMatrix_mulVec] at hval
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hval
  have hpos : 0 ≤ z * x i₀ := by linarith
  have hmin₀ : 0 ≤ x i₀ := nonneg_of_mul_nonneg_right hpos hz
  exact fun i => le_trans hmin₀ (hmin i (Finset.mem_univ i))

/-- The resolvent matrix of a generator is invertible for every `z > 0`. -/
theorem isUnit_resolventMatrix {G : Matrix S S ℝ} (hG : IsGenerator G) {z : ℝ} (hz : 0 < z) :
    IsUnit (resolventMatrix G z) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hzero : resolventMatrix G z *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub]
    simpa using sub_eq_zero.mpr hxy
  have hpos : ∀ i, 0 ≤ (x - y) i := by
    refine nonneg_of_resolventMatrix_mulVec_nonneg hG hz fun i => ?_
    rw [hzero]
    exact le_rfl
  have hneg : ∀ i, 0 ≤ (-(x - y)) i := by
    refine nonneg_of_resolventMatrix_mulVec_nonneg hG hz fun i => ?_
    rw [show resolventMatrix G z *ᵥ (-(x - y)) = 0 by rw [Matrix.mulVec_neg, hzero, neg_zero]]
    exact le_rfl
  have : x - y = 0 := by
    funext i
    have h₁ := hpos i
    have h₂ := hneg i
    simp only [Pi.neg_apply] at h₂
    simpa using le_antisymm (by linarith) h₁
  exact sub_eq_zero.mp this

/-- The determinant of the resolvent matrix of a generator is a unit. -/
theorem isUnit_det_resolventMatrix {G : Matrix S S ℝ} (hG : IsGenerator G) {z : ℝ} (hz : 0 < z) :
    IsUnit (resolventMatrix G z).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_resolventMatrix hG hz)

/-- The normalized resolvent `z • (z • 1 - G)⁻¹`. -/
def resolventKernel (G : Matrix S S ℝ) (z : ℝ) : Matrix S S ℝ :=
  z • (resolventMatrix G z)⁻¹

/-- Row sums of the normalized resolvent are one as soon as the rows of `G` sum
to zero and the resolvent matrix is invertible. -/
theorem resolventKernel_mulVec_one {G : Matrix S S ℝ} (hrow : G *ᵥ (1 : S → ℝ) = 0)
    {z : ℝ} (hunit : IsUnit (resolventMatrix G z)) :
    resolventKernel G z *ᵥ (1 : S → ℝ) = (1 : S → ℝ) := by
  have hdet : IsUnit (resolventMatrix G z).det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hkey : (resolventMatrix G z)⁻¹ *ᵥ (z • (1 : S → ℝ)) = (1 : S → ℝ) := by
    rw [← resolventMatrix_mulVec_one hrow z, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  rw [resolventKernel, Matrix.smul_mulVec, ← Matrix.mulVec_smul, hkey]

/-- **Stochasticity of the resolvent.**  For a generator `G` and `z > 0` the
resolvent matrix is invertible and `z • (z • 1 - G)⁻¹` is a stochastic matrix:
its entries are nonnegative and its rows sum to one. -/
theorem isStochasticMatrix_resolventKernel {G : Matrix S S ℝ} (hG : IsGenerator G)
    {z : ℝ} (hz : 0 < z) : IsStochasticMatrix (resolventKernel G z) := by
  have hdet : IsUnit (resolventMatrix G z).det := isUnit_det_resolventMatrix hG hz
  refine ⟨fun i j => ?_,
    resolventKernel_mulVec_one hG.mulVec_one (isUnit_resolventMatrix hG hz)⟩
  have hcol : ∀ i, 0 ≤ ((resolventMatrix G z)⁻¹ *ᵥ (fun k => if k = j then (1 : ℝ) else 0)) i := by
    refine nonneg_of_resolventMatrix_mulVec_nonneg hG hz fun i => ?_
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    positivity
  have hentry :
      ((resolventMatrix G z)⁻¹ *ᵥ (fun k => if k = j then (1 : ℝ) else 0)) i =
        (resolventMatrix G z)⁻¹ i j := by
    simp [Matrix.mulVec, dotProduct]
  have := hcol i
  rw [hentry] at this
  simp only [resolventKernel, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg hz.le this

/-! ## The converse criterion -/

/-- The Neumann-type resolvent identity `P - 1 = z⁻¹ • (G * P)` for the
normalized resolvent `P`. -/
theorem resolventKernel_sub_one {G : Matrix S S ℝ} {z : ℝ} (hz : z ≠ 0)
    (hunit : IsUnit (resolventMatrix G z)) :
    resolventKernel G z - 1 = z⁻¹ • (G * resolventKernel G z) := by
  have hdet : IsUnit (resolventMatrix G z).det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hmul : resolventMatrix G z * (resolventMatrix G z)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  have hexpand :
      z • (resolventMatrix G z)⁻¹ - G * (resolventMatrix G z)⁻¹ = 1 := by
    rw [← hmul, resolventMatrix, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  have hleft : resolventKernel G z - 1 = G * (resolventMatrix G z)⁻¹ := by
    rw [resolventKernel, ← hexpand]
    abel
  rw [hleft, resolventKernel, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hz, one_smul]

/-- Off-diagonal entries of `G * P` are `z` times the corresponding entry of the
normalized resolvent `P`. -/
theorem mul_resolventKernel_offDiag {G : Matrix S S ℝ} {z : ℝ} (hz : z ≠ 0)
    (hunit : IsUnit (resolventMatrix G z)) {i j : S} (hij : i ≠ j) :
    (G * resolventKernel G z) i j = z * resolventKernel G z i j := by
  have h := congrFun (congrFun (resolventKernel_sub_one hz hunit) i) j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_ne hij, sub_zero] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]

/-- **Converse criterion.**  Rows summing to zero together with invertibility and
entrywise nonnegativity of the resolvent for every `z > 0` characterize
generators. -/
theorem isGenerator_of_resolvent_nonneg {G : Matrix S S ℝ}
    (hrow : G *ᵥ (1 : S → ℝ) = 0)
    (hres : ∀ z : ℝ, 0 < z →
      IsUnit (resolventMatrix G z) ∧ ∀ i j, 0 ≤ (resolventMatrix G z)⁻¹ i j) :
    IsGenerator G := by
  refine ⟨fun i j hij => ?_, hrow⟩
  set D : ℝ := ∑ l, |G i l| * ∑ m, |G l m| with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun l _ =>
    mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun m _ => abs_nonneg _)
  have hbound : ∀ z : ℝ, 0 < z → -D ≤ G i j * z := by
    intro z hz
    obtain ⟨hunit, hnonneg⟩ := hres z hz
    have hP : IsStochasticMatrix (resolventKernel G z) := by
      refine ⟨fun k l => ?_, resolventKernel_mulVec_one hrow hunit⟩
      simp only [resolventKernel, Matrix.smul_apply, smul_eq_mul]
      exact mul_nonneg hz.le (hnonneg k l)
    -- Every row of `P - 1` is `O(1/z)`.
    have hdiff : ∀ k l,
        |resolventKernel G z k l - (1 : Matrix S S ℝ) k l| ≤ (∑ m, |G k m|) / z := by
      intro k l
      have h := congrFun (congrFun (resolventKernel_sub_one hz.ne' hunit) k) l
      rw [Matrix.sub_apply] at h
      rw [h]
      simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hz]
      rw [div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc |(G * resolventKernel G z) k l|
          = |∑ m, G k m * resolventKernel G z m l| := by rw [Matrix.mul_apply]
        _ ≤ ∑ m, |G k m * resolventKernel G z m l| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m, |G k m| := by
            refine Finset.sum_le_sum fun m _ => ?_
            rw [abs_mul]
            calc |G k m| * |resolventKernel G z m l| ≤ |G k m| * 1 :=
                  mul_le_mul_of_nonneg_left (hP.abs_le_one m l) (abs_nonneg _)
              _ = |G k m| := mul_one _
    -- Expand `(G * P) i j` around `(G * 1) i j = G i j`.
    have hexpand : (G * resolventKernel G z) i j =
        G i j + ∑ l, G i l * (resolventKernel G z l j - (1 : Matrix S S ℝ) l j) := by
      have hone : ∑ l, G i l * (1 : Matrix S S ℝ) l j = G i j := by
        simp [Matrix.one_apply, Finset.sum_ite_eq' Finset.univ j fun l => G i l]
      rw [Matrix.mul_apply, ← hone, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    have herr : |∑ l, G i l * (resolventKernel G z l j - (1 : Matrix S S ℝ) l j)| ≤ D / z := by
      calc |∑ l, G i l * (resolventKernel G z l j - (1 : Matrix S S ℝ) l j)|
          ≤ ∑ l, |G i l * (resolventKernel G z l j - (1 : Matrix S S ℝ) l j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ l, |G i l| * ((∑ m, |G l m|) / z) := by
            refine Finset.sum_le_sum fun l _ => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hdiff l j) (abs_nonneg _)
        _ = D / z := by
            rw [hD, eq_div_iff hz.ne', Finset.sum_mul]
            refine Finset.sum_congr rfl fun l _ => ?_
            field_simp
    have hnn : 0 ≤ (G * resolventKernel G z) i j := by
      rw [mul_resolventKernel_offDiag hz.ne' hunit hij]
      exact mul_nonneg hz.le (hP.nonneg i j)
    rw [hexpand] at hnn
    have habs := abs_le.mp herr
    have hge : -(D / z) ≤ G i j := by linarith [habs.1, habs.2]
    have hmul := mul_le_mul_of_nonneg_right hge hz.le
    have hcancel : D / z * z = D := by field_simp
    rw [neg_mul, hcancel] at hmul
    exact hmul
  by_contra hcontra
  rw [not_le] at hcontra
  have hne : G i j ≠ 0 := ne_of_lt hcontra
  have hpos : (0 : ℝ) < D + 1 := by linarith
  have hzpos : 0 < (D + 1) / (-G i j) := div_pos hpos (by linarith)
  have hb := hbound _ hzpos
  have hratio : G i j / (-G i j) = -1 := by rw [div_neg, div_self hne]
  have hkey : G i j * ((D + 1) / (-G i j)) = -(D + 1) := by
    calc G i j * ((D + 1) / (-G i j)) = G i j / (-G i j) * (D + 1) := by ring
      _ = -(D + 1) := by rw [hratio]; ring
  rw [hkey] at hb
  linarith

/-! ## Recurrent quotient data -/

/-- The identity matrix is stochastic. -/
theorem isStochasticMatrix_one : IsStochasticMatrix (1 : Matrix S S ℝ) where
  nonneg i j := by
    rcases eq_or_ne i j with h | h
    · rw [h, Matrix.one_apply_eq]
      exact zero_le_one
    · rw [Matrix.one_apply_ne h]
  mulVec_one := Matrix.one_mulVec _

/-- Recurrent quotient data for a finite generator `G` with class index type `C`.

`absorption` is the matrix `H` of absorption probabilities from each state into
each recurrent class, `stationary` is the matrix `J` whose rows are the
stationary laws of the classes.  The last field is the harmonic-representation
axiom: every `G`-harmonic vector is an absorption average of class values.  It
is exactly the statement that the columns of `H` span `ker G`, and it is what
makes the ergodic projection `H * J` the spectral projection at `0`. -/
structure ErgodicQuotientData (G : Matrix S S ℝ) (C : Type*) [Fintype C] [DecidableEq C] where
  /-- Absorption probabilities from states into classes. -/
  absorption : Matrix S C ℝ
  /-- Stationary laws of the classes. -/
  stationary : Matrix C S ℝ
  /-- Absorption probabilities form a stochastic matrix. -/
  isStochasticMatrix_absorption : IsStochasticMatrix absorption
  /-- Class stationary laws form a stochastic matrix. -/
  isStochasticMatrix_stationary : IsStochasticMatrix stationary
  /-- Absorption probabilities are harmonic. -/
  mul_absorption : G * absorption = 0
  /-- Class laws are stationary. -/
  stationary_mul : stationary * G = 0
  /-- The class laws are supported by their own class. -/
  stationary_mul_absorption : stationary * absorption = 1
  /-- Every harmonic vector is an absorption average. -/
  harmonic_mem_range : ∀ x : S → ℝ, G *ᵥ x = 0 → ∃ y : C → ℝ, x = absorption *ᵥ y

namespace ErgodicQuotientData

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {G : Matrix S S ℝ} (Q : ErgodicQuotientData G C)

/-- The ergodic projection `Π = H * J`. -/
def proj : Matrix S S ℝ := Q.absorption * Q.stationary

/-- The complementary projection `N = 1 - Π`. -/
def cproj : Matrix S S ℝ := 1 - Q.proj

omit [DecidableEq S] in
/-- The ergodic projection fixes the absorption matrix. -/
theorem proj_mul_absorption : Q.proj * Q.absorption = Q.absorption := by
  rw [proj, Matrix.mul_assoc, Q.stationary_mul_absorption, Matrix.mul_one]

omit [DecidableEq S] in
/-- The ergodic projection fixes the stationary matrix. -/
theorem stationary_mul_proj : Q.stationary * Q.proj = Q.stationary := by
  rw [proj, ← Matrix.mul_assoc, Q.stationary_mul_absorption, Matrix.one_mul]

omit [DecidableEq S] in
/-- The ergodic projection is idempotent. -/
theorem proj_mul_proj : Q.proj * Q.proj = Q.proj := by
  calc Q.proj * Q.proj = Q.proj * (Q.absorption * Q.stationary) := rfl
    _ = Q.proj * Q.absorption * Q.stationary := (Matrix.mul_assoc _ _ _).symm
    _ = Q.absorption * Q.stationary := by rw [Q.proj_mul_absorption]
    _ = Q.proj := rfl

omit [DecidableEq S] in
/-- The generator annihilates the ergodic projection on the right. -/
theorem mul_proj : G * Q.proj = 0 := by
  rw [proj, ← Matrix.mul_assoc, Q.mul_absorption, Matrix.zero_mul]

omit [DecidableEq S] in
/-- The generator annihilates the ergodic projection on the left. -/
theorem proj_mul : Q.proj * G = 0 := by
  rw [proj, Matrix.mul_assoc, Q.stationary_mul, Matrix.mul_zero]

/-- The complementary projection annihilates the stationary matrix. -/
theorem stationary_mul_cproj : Q.stationary * Q.cproj = 0 := by
  rw [cproj, Matrix.mul_sub, Matrix.mul_one, Q.stationary_mul_proj, sub_self]

omit [DecidableEq S] in
/-- **Injectivity of the generator on the kernel of `J`.** -/
theorem eq_zero_of_mulVec_eq_zero {x : S → ℝ} (hGx : G *ᵥ x = 0)
    (hJx : Q.stationary *ᵥ x = 0) : x = 0 := by
  obtain ⟨y, hy⟩ := Q.harmonic_mem_range x hGx
  have hy0 : y = 0 := by
    rw [hy, Matrix.mulVec_mulVec, Q.stationary_mul_absorption, Matrix.one_mulVec] at hJx
    exact hJx
  rw [hy, hy0, Matrix.mulVec_zero]

omit [DecidableEq S] in
/-- Vectors killed by `G + Π` are killed by `J`. -/
theorem stationary_mulVec_eq_zero_of_add_proj {x : S → ℝ} (h : (G + Q.proj) *ᵥ x = 0) :
    Q.stationary *ᵥ x = 0 := by
  have h1 : Q.stationary *ᵥ ((G + Q.proj) *ᵥ x) = 0 := by rw [h, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, Matrix.mul_add, Q.stationary_mul, zero_add,
    Q.stationary_mul_proj] at h1
  exact h1

omit [DecidableEq S] in
/-- `G + Π` is injective. -/
theorem eq_zero_of_add_proj_mulVec {x : S → ℝ} (h : (G + Q.proj) *ᵥ x = 0) : x = 0 := by
  have hJx : Q.stationary *ᵥ x = 0 := Q.stationary_mulVec_eq_zero_of_add_proj h
  have hproj : Q.proj *ᵥ x = 0 := by
    rw [proj, ← Matrix.mulVec_mulVec, hJx, Matrix.mulVec_zero]
  have hGx : G *ᵥ x = 0 := by
    rw [Matrix.add_mulVec, hproj, add_zero] at h
    exact h
  exact Q.eq_zero_of_mulVec_eq_zero hGx hJx

/-- The fundamental matrix `G + Π` is invertible. -/
theorem isUnit_add_proj : IsUnit (G + Q.proj) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hzero : (G + Q.proj) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub]
    simpa using sub_eq_zero.mpr hxy
  exact sub_eq_zero.mp (Q.eq_zero_of_add_proj_mulVec hzero)

/-- The determinant of the fundamental matrix is a unit. -/
theorem isUnit_det_add_proj : IsUnit (G + Q.proj).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp Q.isUnit_add_proj

omit [DecidableEq S] in
/-- The ergodic projection is invariant under the fundamental matrix on the right. -/
theorem proj_mul_add_proj : Q.proj * (G + Q.proj) = Q.proj := by
  rw [Matrix.mul_add, Q.proj_mul, zero_add, Q.proj_mul_proj]

omit [DecidableEq S] in
/-- The ergodic projection is invariant under the fundamental matrix on the left. -/
theorem add_proj_mul_proj : (G + Q.proj) * Q.proj = Q.proj := by
  rw [Matrix.add_mul, Q.mul_proj, zero_add, Q.proj_mul_proj]

/-- The ergodic projection is invariant under the fundamental inverse. -/
theorem proj_mul_inv_add_proj : Q.proj * (G + Q.proj)⁻¹ = Q.proj := by
  calc Q.proj * (G + Q.proj)⁻¹
      = Q.proj * (G + Q.proj) * (G + Q.proj)⁻¹ := by rw [Q.proj_mul_add_proj]
    _ = Q.proj * ((G + Q.proj) * (G + Q.proj)⁻¹) := Matrix.mul_assoc _ _ _
    _ = Q.proj := by
        rw [Matrix.mul_nonsing_inv _ Q.isUnit_det_add_proj, Matrix.mul_one]

/-- The ergodic projection is invariant under the fundamental inverse, on the left. -/
theorem inv_add_proj_mul_proj : (G + Q.proj)⁻¹ * Q.proj = Q.proj := by
  calc (G + Q.proj)⁻¹ * Q.proj
      = (G + Q.proj)⁻¹ * ((G + Q.proj) * Q.proj) := by rw [Q.add_proj_mul_proj]
    _ = (G + Q.proj)⁻¹ * (G + Q.proj) * Q.proj := (Matrix.mul_assoc _ _ _).symm
    _ = Q.proj := by
        rw [Matrix.nonsing_inv_mul _ Q.isUnit_det_add_proj, Matrix.one_mul]

/-- The group inverse `G# = (G + Π)⁻¹ - Π` of the generator. -/
def groupInverse : Matrix S S ℝ := (G + Q.proj)⁻¹ - Q.proj

/-- Fundamental identity for the fundamental inverse, on the right. -/
theorem mul_inv_add_proj : G * (G + Q.proj)⁻¹ = 1 - Q.proj := by
  have h1 : G * (G + Q.proj)⁻¹ + Q.proj * (G + Q.proj)⁻¹ = 1 := by
    rw [← Matrix.add_mul, Matrix.mul_nonsing_inv _ Q.isUnit_det_add_proj]
  rw [Q.proj_mul_inv_add_proj] at h1
  exact eq_sub_of_add_eq h1

/-- Fundamental identity for the fundamental inverse, on the left. -/
theorem inv_add_proj_mul : (G + Q.proj)⁻¹ * G = 1 - Q.proj := by
  have h1 : (G + Q.proj)⁻¹ * G + (G + Q.proj)⁻¹ * Q.proj = 1 := by
    rw [← Matrix.mul_add, Matrix.nonsing_inv_mul _ Q.isUnit_det_add_proj]
  rw [Q.inv_add_proj_mul_proj] at h1
  exact eq_sub_of_add_eq h1

/-- `G * G# = 1 - Π`. -/
theorem mul_groupInverse : G * Q.groupInverse = 1 - Q.proj := by
  rw [groupInverse, Matrix.mul_sub, Q.mul_proj, sub_zero, Q.mul_inv_add_proj]

/-- `G# * G = 1 - Π`. -/
theorem groupInverse_mul : Q.groupInverse * G = 1 - Q.proj := by
  rw [groupInverse, Matrix.sub_mul, Q.proj_mul, sub_zero, Q.inv_add_proj_mul]

/-- `G# * Π = 0`. -/
theorem groupInverse_mul_proj : Q.groupInverse * Q.proj = 0 := by
  rw [groupInverse, Matrix.sub_mul, Q.inv_add_proj_mul_proj, Q.proj_mul_proj, sub_self]

/-- `Π * G# = 0`. -/
theorem proj_mul_groupInverse : Q.proj * Q.groupInverse = 0 := by
  rw [groupInverse, Matrix.mul_sub, Q.proj_mul_inv_add_proj, Q.proj_mul_proj, sub_self]

/-- `G# * H = 0`. -/
theorem groupInverse_mul_absorption : Q.groupInverse * Q.absorption = 0 := by
  conv_lhs => rw [← Q.proj_mul_absorption]
  rw [← Matrix.mul_assoc, Q.groupInverse_mul_proj, Matrix.zero_mul]

/-- `J * G# = 0`. -/
theorem stationary_mul_groupInverse : Q.stationary * Q.groupInverse = 0 := by
  conv_lhs => rw [← Q.stationary_mul_proj]
  rw [Matrix.mul_assoc, Q.proj_mul_groupInverse, Matrix.mul_zero]

/-- The kernel of `J · ` inside the state space. -/
def kerStationary : Submodule ℝ (S → ℝ) :=
  LinearMap.ker (Matrix.mulVecLin Q.stationary)

omit [DecidableEq S] in
/-- Membership in `ker (J · )` unfolds to `J *ᵥ x = 0`. -/
theorem mem_kerStationary_iff (x : S → ℝ) :
    x ∈ Q.kerStationary ↔ Q.stationary *ᵥ x = 0 := by
  simp [kerStationary, LinearMap.mem_ker]

omit [DecidableEq S] in
/-- The generator preserves `ker (J · )`. -/
theorem mapsTo_kerStationary :
    ∀ x ∈ Q.kerStationary, Matrix.mulVecLin G x ∈ Q.kerStationary := by
  intro x _
  rw [mem_kerStationary_iff, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Q.stationary_mul,
    Matrix.zero_mulVec]

/-- The generator restricted to `ker (J · )`. -/
def restrictedGenerator : Q.kerStationary →ₗ[ℝ] Q.kerStationary :=
  (Matrix.mulVecLin G).restrict Q.mapsTo_kerStationary

/-- Every element of `ker (J · )` is `G` applied to an element of `ker (J · )`. -/
theorem exists_mulVec_eq_of_mem_kerStationary {b : S → ℝ} (hb : Q.stationary *ᵥ b = 0) :
    Q.stationary *ᵥ (Q.groupInverse *ᵥ b) = 0 ∧ G *ᵥ (Q.groupInverse *ᵥ b) = b := by
  constructor
  · rw [Matrix.mulVec_mulVec, Q.stationary_mul_groupInverse, Matrix.zero_mulVec]
  · rw [Matrix.mulVec_mulVec, Q.mul_groupInverse, Matrix.sub_mulVec, Matrix.one_mulVec]
    have hproj : Q.proj *ᵥ b = 0 := by
      rw [proj, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_zero]
    rw [hproj, sub_zero]

omit [DecidableEq S] in
/-- **The generator acts bijectively on the kernel of `J`.** -/
theorem bijective_restrictedGenerator : Function.Bijective Q.restrictedGenerator := by
  classical
  constructor
  · intro x y hxy
    have hx := (Q.mem_kerStationary_iff x.1).mp x.2
    have hy := (Q.mem_kerStationary_iff y.1).mp y.2
    have hval : G *ᵥ x.1 = G *ᵥ y.1 := congrArg Subtype.val hxy
    have hsub : G *ᵥ (x.1 - y.1) = 0 := by
      rw [Matrix.mulVec_sub, hval, sub_self]
    have hJ : Q.stationary *ᵥ (x.1 - y.1) = 0 := by
      rw [Matrix.mulVec_sub, hx, hy, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (Q.eq_zero_of_mulVec_eq_zero hsub hJ))
  · intro b
    obtain ⟨hker, hval⟩ :=
      Q.exists_mulVec_eq_of_mem_kerStationary ((Q.mem_kerStationary_iff b.1).mp b.2)
    refine ⟨⟨Q.groupInverse *ᵥ b.1, (Q.mem_kerStationary_iff _).mpr hker⟩, ?_⟩
    exact Subtype.ext hval

/-! ### The invariant graph -/

/-- The invariant graph `U = H + W` attached to a slice element `W`. -/
def graph (W : Matrix S C ℝ) : Matrix S C ℝ := Q.absorption + W

/-- The reduced generator `Red A W = J * A * (H + W)` on the class space. -/
def red (A : Matrix S S ℝ) (W : Matrix S C ℝ) : Matrix C C ℝ :=
  Q.stationary * A * Q.graph W

/-- The invariant-graph equation
`redEq A W = (1 - Π) * A * (H + W) - W * (J * A * (H + W))`. -/
def redEq (A : Matrix S S ℝ) (W : Matrix S C ℝ) : Matrix S C ℝ :=
  Q.cproj * A * Q.graph W - W * Q.red A W

omit [DecidableEq S] in
/-- The graph at the origin of the slice is the absorption matrix. -/
theorem graph_zero : Q.graph 0 = Q.absorption := by
  rw [graph, add_zero]

/-- **The invariant-graph equation is a square system on the slice `J * W = 0`.** -/
theorem stationary_mul_redEq (A : Matrix S S ℝ) {W : Matrix S C ℝ}
    (hW : Q.stationary * W = 0) : Q.stationary * Q.redEq A W = 0 := by
  have h1 : Q.stationary * (Q.cproj * A * Q.graph W) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Q.stationary_mul_cproj, Matrix.zero_mul,
      Matrix.zero_mul]
  have h2 : Q.stationary * (W * Q.red A W) = 0 := by
    rw [← Matrix.mul_assoc, hW, Matrix.zero_mul]
  rw [redEq, Matrix.mul_sub, h1, h2, sub_zero]

/-- **Intertwining.**  On the zero set of the invariant-graph equation the graph
conjugates the ambient matrix into the reduced generator. -/
theorem mul_graph_eq (A : Matrix S S ℝ) (W : Matrix S C ℝ) (h : Q.redEq A W = 0) :
    A * Q.graph W = Q.graph W * Q.red A W := by
  have hsum : Q.proj + Q.cproj = 1 := by
    rw [cproj]
    abel
  have hzero : Q.cproj * (A * Q.graph W) = W * Q.red A W := by
    rw [redEq, sub_eq_zero] at h
    rw [← Matrix.mul_assoc]
    exact h
  have hPA : Q.proj * (A * Q.graph W) = Q.absorption * Q.red A W := by
    simp only [proj, red, Matrix.mul_assoc]
  calc A * Q.graph W
      = (Q.proj + Q.cproj) * (A * Q.graph W) := by rw [hsum, Matrix.one_mul]
    _ = Q.proj * (A * Q.graph W) + Q.cproj * (A * Q.graph W) := Matrix.add_mul _ _ _
    _ = Q.absorption * Q.red A W + W * Q.red A W := by rw [hPA, hzero]
    _ = Q.graph W * Q.red A W := by rw [graph, Matrix.add_mul]

omit [DecidableEq S] in
/-- Row sums of the graph are one exactly when `W` kills the all-ones vector. -/
theorem graph_mulVec_one_of_mulVec_one_eq_zero {W : Matrix S C ℝ}
    (hW : W *ᵥ (1 : C → ℝ) = 0) : Q.graph W *ᵥ (1 : C → ℝ) = (1 : S → ℝ) := by
  rw [graph, Matrix.add_mulVec, hW, add_zero, Q.isStochasticMatrix_absorption.mulVec_one]

omit [DecidableEq S] in
/-- **Row sums of the reduced generator vanish** once the graph has unit row
sums and the ambient matrix has vanishing row sums. -/
theorem red_mulVec_one (A : Matrix S S ℝ) (W : Matrix S C ℝ)
    (hA : A *ᵥ (1 : S → ℝ) = 0) (hU : Q.graph W *ᵥ (1 : C → ℝ) = (1 : S → ℝ)) :
    Q.red A W *ᵥ (1 : C → ℝ) = 0 := by
  rw [red, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hU, hA,
    Matrix.mulVec_zero]

omit [DecidableEq S] in
/-- The graph is stochastic on rows: `J * (H + W) = 1` on the slice. -/
theorem stationary_mul_graph {W : Matrix S C ℝ} (hW : Q.stationary * W = 0) :
    Q.stationary * Q.graph W = 1 := by
  rw [graph, Matrix.mul_add, Q.stationary_mul_absorption, hW, add_zero]

/-- **The all-ones vector lies on the invariant graph.**  Under the linear
uniqueness hypothesis at the parameter, the graph has unit row sums; combined
with `red_mulVec_one` this gives `Red A W *ᵥ 1 = 0`. -/
theorem graph_mulVec_one_of_unique (A : Matrix S S ℝ) (W : Matrix S C ℝ)
    (hW : Q.redEq A W = 0) (hJW : Q.stationary * W = 0) (hA : A *ᵥ (1 : S → ℝ) = 0)
    (huniq : ∀ w : S → ℝ, Q.stationary *ᵥ w = 0 →
        A *ᵥ w = Q.graph W *ᵥ (Q.stationary *ᵥ (A *ᵥ w)) → w = 0) :
    Q.graph W *ᵥ (1 : C → ℝ) = (1 : S → ℝ) := by
  have hinter := Q.mul_graph_eq A W hW
  have hu : Q.stationary *ᵥ (Q.graph W *ᵥ (1 : C → ℝ)) = (1 : C → ℝ) := by
    rw [Matrix.mulVec_mulVec, Q.stationary_mul_graph hJW, Matrix.one_mulVec]
  have hone : Q.stationary *ᵥ (1 : S → ℝ) = (1 : C → ℝ) :=
    Q.isStochasticMatrix_stationary.mulVec_one
  have hred1 : Q.red A W *ᵥ (1 : C → ℝ)
      = Q.stationary *ᵥ (A *ᵥ (Q.graph W *ᵥ (1 : C → ℝ))) := by
    rw [red, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hkey : A *ᵥ (Q.graph W *ᵥ (1 : C → ℝ))
      = Q.graph W *ᵥ (Q.stationary *ᵥ (A *ᵥ (Q.graph W *ᵥ (1 : C → ℝ)))) := by
    rw [← hred1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hinter]
  have hAw : A *ᵥ (Q.graph W *ᵥ (1 : C → ℝ) - (1 : S → ℝ))
      = A *ᵥ (Q.graph W *ᵥ (1 : C → ℝ)) := by
    rw [Matrix.mulVec_sub, hA, sub_zero]
  have hzero : Q.graph W *ᵥ (1 : C → ℝ) - (1 : S → ℝ) = 0 := by
    refine huniq _ ?_ ?_
    · rw [Matrix.mulVec_sub, hu, hone, sub_self]
    · rw [hAw]
      exact hkey
  exact sub_eq_zero.mp hzero

/-! ### The base point -/

/-- **At the base point the invariant-graph equation is linear**: it is exactly
`W ↦ G * W`.  This is the derivative that drives the analytic implicit function
theorem, and it is bijective on the slice `J * W = 0`. -/
theorem redEq_base (W : Matrix S C ℝ) : Q.redEq G W = G * W := by
  have hNG : Q.cproj * G = G := by
    rw [cproj, Matrix.sub_mul, Matrix.one_mul, Q.proj_mul, sub_zero]
  have hred : Q.red G W = 0 := by
    rw [red, Q.stationary_mul, Matrix.zero_mul]
  rw [redEq, hred, Matrix.mul_zero, sub_zero, hNG, graph, Matrix.mul_add, Q.mul_absorption,
    zero_add]

/-- The origin of the slice solves the invariant-graph equation at the base
point. -/
theorem redEq_base_zero : Q.redEq G 0 = 0 := by
  rw [redEq_base, Matrix.mul_zero]

omit [DecidableEq S] in
/-- Left multiplication by `G` is injective on the slice `J * W = 0`. -/
theorem eq_zero_of_mul_eq_zero {W : Matrix S C ℝ} (hJ : Q.stationary * W = 0)
    (h : G * W = 0) : W = 0 := by
  have hcol : ∀ c : C, W *ᵥ (fun d => if d = c then (1 : ℝ) else 0) = 0 := by
    intro c
    refine Q.eq_zero_of_mulVec_eq_zero ?_ ?_
    · rw [Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]
    · rw [Matrix.mulVec_mulVec, hJ, Matrix.zero_mulVec]
  ext i c
  have hval := congrFun (hcol c) i
  simpa [Matrix.mulVec, dotProduct] using hval

/-- **Base-point uniqueness.**  The origin is the only slice solution of the
invariant-graph equation at the base point. -/
theorem eq_zero_of_redEq_base_eq_zero {W : Matrix S C ℝ} (hJ : Q.stationary * W = 0)
    (h : Q.redEq G W = 0) : W = 0 := by
  rw [redEq_base] at h
  exact Q.eq_zero_of_mul_eq_zero hJ h

/-! ### The slice and the base-point derivative -/

/-- Left multiplication by the generator on the slice `{W | J * W = 0}`.  By
`redEq_base` this is exactly the derivative of the invariant-graph equation at
the base point. -/
def graphSliceGenerator (W : {W : Matrix S C ℝ // Q.stationary * W = 0}) :
    {W : Matrix S C ℝ // Q.stationary * W = 0} :=
  ⟨G * W.1, by rw [← Matrix.mul_assoc, Q.stationary_mul, Matrix.zero_mul]⟩

omit [DecidableEq S] in
@[simp] theorem graphSliceGenerator_val (W : {W : Matrix S C ℝ // Q.stationary * W = 0}) :
    (Q.graphSliceGenerator W).1 = G * W.1 := rfl

omit [DecidableEq S] in
/-- **The base-point derivative of the invariant-graph equation is a bijection of
the slice.**  This is the nondegeneracy hypothesis under which the analytic
implicit function theorem produces the invariant graph. -/
theorem bijective_graphSliceGenerator : Function.Bijective Q.graphSliceGenerator := by
  classical
  constructor
  · intro W W' hWW'
    have hval : G * W.1 = G * W'.1 := congrArg Subtype.val hWW'
    refine Subtype.ext (sub_eq_zero.mp (Q.eq_zero_of_mul_eq_zero ?_ ?_))
    · rw [Matrix.mul_sub, W.2, W'.2, sub_self]
    · rw [Matrix.mul_sub, hval, sub_self]
  · intro B
    have hslice : Q.stationary * (Q.groupInverse * B.1) = 0 := by
      rw [← Matrix.mul_assoc, Q.stationary_mul_groupInverse, Matrix.zero_mul]
    refine ⟨⟨Q.groupInverse * B.1, hslice⟩, Subtype.ext ?_⟩
    rw [graphSliceGenerator_val, ← Matrix.mul_assoc, Q.mul_groupInverse, Matrix.sub_mul,
      Matrix.one_mul, proj, Matrix.mul_assoc, B.2, Matrix.mul_zero, sub_zero]

omit [DecidableEq S] in
/-- The base-point uniqueness hypothesis of `graph_mulVec_one_of_unique` holds at
the base point. -/
theorem unique_base (w : S → ℝ) (hJw : Q.stationary *ᵥ w = 0)
    (hw : G *ᵥ w = Q.graph 0 *ᵥ (Q.stationary *ᵥ (G *ᵥ w))) : w = 0 := by
  have hJG : Q.stationary *ᵥ (G *ᵥ w) = 0 := by
    rw [Matrix.mulVec_mulVec, Q.stationary_mul, Matrix.zero_mulVec]
  rw [hJG, Matrix.mulVec_zero] at hw
  exact Q.eq_zero_of_mulVec_eq_zero hw hJw

/-! ### Invariant-graph families and equivariance -/

/-- A family `W` of slice elements solving the invariant-graph equation for an
ambient family `A`, normalized at the base point. -/
structure IsInvariantGraph (A : ℝ → Matrix S S ℝ) (W : ℝ → Matrix S C ℝ) : Prop where
  /-- The graph starts at the absorption matrix. -/
  base : W 0 = 0
  /-- Every member lies on the slice `J * W = 0`. -/
  stationary_mul_eq_zero : ∀ t, Q.stationary * W t = 0
  /-- Every member solves the invariant-graph equation. -/
  redEq_eq_zero : ∀ t, Q.redEq (A t) (W t) = 0

/-- **Reparameterization equivariance.**  Precomposing the ambient family with an
origin-preserving reparameterization precomposes the invariant graph. -/
theorem isInvariantGraph_comp {A : ℝ → Matrix S S ℝ} {W : ℝ → Matrix S C ℝ}
    (h : Q.IsInvariantGraph A W) {θ : ℝ → ℝ} (hθ : θ 0 = 0) :
    Q.IsInvariantGraph (A ∘ θ) (W ∘ θ) where
  base := by
    simp only [Function.comp_apply, hθ, h.base]
  stationary_mul_eq_zero t := h.stationary_mul_eq_zero (θ t)
  redEq_eq_zero t := h.redEq_eq_zero (θ t)

omit [DecidableEq S] in
/-- **Reparameterization equivariance for the reduced generator**:
`Red (A ∘ θ) = (Red A) ∘ θ`. -/
theorem red_comp (A : ℝ → Matrix S S ℝ) (W : ℝ → Matrix S C ℝ) (θ : ℝ → ℝ) (t : ℝ) :
    Q.red ((A ∘ θ) t) ((W ∘ θ) t) = Q.red (A (θ t)) (W (θ t)) := rfl

/-- Rescaling the generator by a nonzero scalar leaves the quotient data
unchanged. -/
def smul (c : ℝ) (hc : c ≠ 0) : ErgodicQuotientData (c • G) C where
  absorption := Q.absorption
  stationary := Q.stationary
  isStochasticMatrix_absorption := Q.isStochasticMatrix_absorption
  isStochasticMatrix_stationary := Q.isStochasticMatrix_stationary
  mul_absorption := by rw [Matrix.smul_mul, Q.mul_absorption, smul_zero]
  stationary_mul := by rw [Matrix.mul_smul, Q.stationary_mul, smul_zero]
  stationary_mul_absorption := Q.stationary_mul_absorption
  harmonic_mem_range := by
    intro x hx
    refine Q.harmonic_mem_range x ?_
    have hcx : c • (G *ᵥ x) = 0 := by
      rw [← Matrix.smul_mulVec]
      exact hx
    have hscaled := congrArg (fun v : S → ℝ => c⁻¹ • v) hcx
    simpa [smul_smul, inv_mul_cancel₀ hc] using hscaled

omit [DecidableEq S] in
/-- Rescaling preserves the absorption matrix. -/
theorem smul_absorption (c : ℝ) (hc : c ≠ 0) : (Q.smul c hc).absorption = Q.absorption := rfl

omit [DecidableEq S] in
/-- Rescaling preserves the stationary matrix. -/
theorem smul_stationary (c : ℝ) (hc : c ≠ 0) : (Q.smul c hc).stationary = Q.stationary := rfl

omit [DecidableEq S] in
/-- Rescaling preserves the ergodic projection. -/
theorem smul_proj (c : ℝ) (hc : c ≠ 0) : (Q.smul c hc).proj = Q.proj := rfl

/-- Rescaling preserves the complementary projection. -/
theorem smul_cproj (c : ℝ) (hc : c ≠ 0) : (Q.smul c hc).cproj = Q.cproj := rfl

omit [DecidableEq S] in
/-- Rescaling preserves the graph map. -/
theorem smul_graph (c : ℝ) (hc : c ≠ 0) (W : Matrix S C ℝ) :
    (Q.smul c hc).graph W = Q.graph W := rfl

omit [DecidableEq S] in
/-- **Scalar equivariance of the reduced generator.** -/
theorem smul_red (c d : ℝ) (hc : c ≠ 0) (A : Matrix S S ℝ) (W : Matrix S C ℝ) :
    (Q.smul c hc).red (d • A) W = d • Q.red A W := by
  rw [red, red, smul_stationary, smul_graph, Matrix.mul_smul, Matrix.smul_mul]

/-- **Scalar equivariance of the invariant-graph equation.** -/
theorem smul_redEq (c d : ℝ) (hc : c ≠ 0) (A : Matrix S S ℝ) (W : Matrix S C ℝ) :
    (Q.smul c hc).redEq (d • A) W = d • Q.redEq A W := by
  rw [redEq, redEq, smul_cproj, smul_graph, Q.smul_red c d hc, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_sub]

/-- **Scalar equivariance for families.**  An analytic rescaling `f • A` of the
ambient family has the same invariant graph, over the rescaled base generator
`f 0 • G`. -/
theorem isInvariantGraph_smul {A : ℝ → Matrix S S ℝ} {W : ℝ → Matrix S C ℝ}
    (h : Q.IsInvariantGraph A W) {f : ℝ → ℝ} (hf : f 0 ≠ 0) :
    (Q.smul (f 0) hf).IsInvariantGraph (fun t => f t • A t) W where
  base := h.base
  stationary_mul_eq_zero t := h.stationary_mul_eq_zero t
  redEq_eq_zero t := by
    rw [Q.smul_redEq (f 0) (f t) hf, h.redEq_eq_zero t, smul_zero]

/-! ### First-order coefficients -/

/-- The linearization of the invariant-graph equation at the base point in the
direction `A₁`. -/
def linearRedEq (A₁ : Matrix S S ℝ) (W₁ : Matrix S C ℝ) : Matrix S C ℝ :=
  Q.cproj * A₁ * Q.absorption + G * W₁

/-- **First-order graph coefficient.**  The linearized invariant-graph equation
has a unique slice solution, namely `W₁ = -G# * A₁ * H`. -/
theorem existsUnique_linear_graphCoeff (A₁ : Matrix S S ℝ) :
    ∃! W₁ : Matrix S C ℝ, Q.stationary * W₁ = 0 ∧ Q.linearRedEq A₁ W₁ = 0 := by
  have hGN : Q.groupInverse * Q.cproj = Q.groupInverse := by
    rw [cproj, Matrix.mul_sub, Matrix.mul_one, Q.groupInverse_mul_proj, sub_zero]
  refine ⟨-(Q.groupInverse * A₁ * Q.absorption), ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Q.stationary_mul_groupInverse,
      Matrix.zero_mul, Matrix.zero_mul, neg_zero]
  · have hGG : G * (Q.groupInverse * A₁ * Q.absorption) = Q.cproj * A₁ * Q.absorption := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Q.mul_groupInverse, cproj]
    rw [linearRedEq, Matrix.mul_neg, hGG, add_neg_cancel]
  · rintro W₁ ⟨hJ, heq⟩
    have hGW : G * W₁ = -(Q.cproj * A₁ * Q.absorption) := by
      rw [linearRedEq, add_comm] at heq
      exact eq_neg_of_add_eq_zero_left heq
    have hleft : Q.groupInverse * (G * W₁) = W₁ := by
      rw [← Matrix.mul_assoc, Q.groupInverse_mul, Matrix.sub_mul, Matrix.one_mul, proj,
        Matrix.mul_assoc, hJ, Matrix.mul_zero, sub_zero]
    rw [hGW, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGN] at hleft
    exact hleft.symm

omit [DecidableEq S] in
/-- **The first-order reduced coefficient depends only on `A₁`.**  Whatever the
first-order graph coefficient `W₁` is, `B₁ = J * A₁ * H`. -/
theorem redCoeff_one_dependsOn (A₁ : Matrix S S ℝ) (W₁ : Matrix S C ℝ) :
    Q.stationary * A₁ * Q.absorption + Q.stationary * G * W₁
      = Q.stationary * A₁ * Q.absorption := by
  rw [Q.stationary_mul, Matrix.zero_mul, add_zero]

end ErgodicQuotientData

/-! ## Instantiations -/

/-- The zero generator has recurrent quotient data with one class per state. -/
def ergodicQuotientDataOfZero : ErgodicQuotientData (0 : Matrix S S ℝ) S where
  absorption := 1
  stationary := 1
  isStochasticMatrix_absorption := isStochasticMatrix_one
  isStochasticMatrix_stationary := isStochasticMatrix_one
  mul_absorption := Matrix.zero_mul _
  stationary_mul := Matrix.mul_zero _
  stationary_mul_absorption := Matrix.one_mul _
  harmonic_mem_range := fun x _ => ⟨x, (Matrix.one_mulVec x).symm⟩

/-- **Unichain quotient data.**  A generator whose harmonic vectors are the
constants, together with a stationary probability vector, has recurrent quotient
data over a single class. -/
def ergodicQuotientDataOfStationary (G : Matrix S S ℝ) (hG : G *ᵥ (1 : S → ℝ) = 0)
    (weight : S → ℝ) (hnonneg : ∀ i, 0 ≤ weight i) (hmass : ∑ i, weight i = 1)
    (hstat : ∀ j, ∑ i, weight i * G i j = 0)
    (hker : ∀ x : S → ℝ, G *ᵥ x = 0 → ∃ c : ℝ, x = fun _ => c) :
    ErgodicQuotientData G Unit where
  absorption := Matrix.of fun _ _ => 1
  stationary := Matrix.of fun _ i => weight i
  isStochasticMatrix_absorption :=
    ⟨fun _ _ => zero_le_one, by
      funext i
      simp [Matrix.mulVec, dotProduct]⟩
  isStochasticMatrix_stationary :=
    ⟨fun _ i => hnonneg i, by
      funext c
      simpa [Matrix.mulVec, dotProduct] using hmass⟩
  mul_absorption := by
    funext i c
    have hrow : ∑ j, G i j = 0 := by
      have h := congrFun hG i
      simpa [Matrix.mulVec, dotProduct] using h
    simpa [Matrix.mul_apply] using hrow
  stationary_mul := by
    funext c j
    simpa [Matrix.mul_apply] using hstat j
  stationary_mul_absorption := by
    funext c c'
    have : (1 : Matrix Unit Unit ℝ) c c' = 1 := by
      rw [Subsingleton.elim c c', Matrix.one_apply_eq]
    simpa [Matrix.mul_apply, this] using hmass
  harmonic_mem_range := by
    intro x hx
    obtain ⟨c, hc⟩ := hker x hx
    refine ⟨fun _ => c, ?_⟩
    funext i
    rw [hc]
    simp [Matrix.mulVec, dotProduct]

end Probability
end Math
