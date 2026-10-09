import GameTheory.Math.FiniteLinearBinaryBound
import GameTheory.Math.SmallRationalWitness
import Mathlib.Algebra.BigOperators.Field

/-! Integer certificates for nonnegative feasibility of finite linear systems.

A positive common denominator and nonnegative integer numerators certify the
equations by clearing denominators. Their width is polynomial in the dimensions
and in the binary coefficient width, including signed coefficients.
-/

namespace GameTheory.Math

open scoped BigOperators

/-- A finite nonnegative rational solution recorded as bounded natural
numerators and a positive common denominator, with integer equations. -/
structure BoundedLinearCertificate {ρ κ : Type*} [Fintype κ]
    (M : Matrix ρ κ ℤ) (b : ρ → ℤ) (width : ℕ) where
  /-- Positive common denominator of the represented rational coordinates. -/
  denominator : ℕ
  /-- Nonnegative integer numerator of each represented coordinate. -/
  numerator : κ → ℕ
  denominator_pos : 0 < denominator
  denominator_lt : denominator < 2 ^ width
  numerator_lt : ∀ j, numerator j < 2 ^ width
  equations : ∀ i, ∑ j, M i j * (numerator j : ℤ) = (denominator : ℤ) * b i

namespace BoundedLinearCertificate

/-- The nonnegative real solution represented by a cleared integer certificate. -/
noncomputable def realSolution {ρ κ : Type*} [Fintype κ]
    {M : Matrix ρ κ ℤ} {b : ρ → ℤ} {width : ℕ}
    (c : BoundedLinearCertificate M b width) : κ → ℝ :=
  fun j => (c.numerator j : ℝ) / c.denominator

/-- Decoding natural numerators and a positive denominator gives nonnegative
coordinates. -/
theorem realSolution_nonneg {ρ κ : Type*} [Fintype κ]
    {M : Matrix ρ κ ℤ} {b : ρ → ℤ} {width : ℕ}
    (c : BoundedLinearCertificate M b width) (j : κ) :
    0 ≤ c.realSolution j :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Clearing denominators is sound for the represented real solution. -/
theorem realSolution_equations {ρ κ : Type*} [Fintype κ]
    {M : Matrix ρ κ ℤ} {b : ρ → ℤ} {width : ℕ}
    (c : BoundedLinearCertificate M b width) (i : ρ) :
    ∑ j, (M i j : ℝ) * c.realSolution j = (b i : ℝ) := by
  have hD : (c.denominator : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt c.denominator_pos
  have heq : ∑ j, (M i j : ℝ) * (c.numerator j : ℝ) =
      (c.denominator : ℝ) * (b i : ℝ) := by
    exact_mod_cast c.equations i
  simp only [realSolution, ← mul_div_assoc, ← Finset.sum_div]
  rw [heq, mul_div_cancel_left₀ _ hD]

end BoundedLinearCertificate

/-- Every feasible finite integer linear system with a nonnegative real solution
has a certificate whose binary width is polynomial in its dimensions and its
coefficient bit bound. -/
theorem exists_bounded_nonnegative_linear_certificate {ρ κ : Type*}
    [Fintype ρ] [Fintype κ]
    (M : Matrix ρ κ ℤ) (b : ρ → ℤ) (h : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) (hb : ∀ i, (b i).natAbs ≤ 2 ^ h)
    (x : κ → ℝ) (hx : ∀ j, 0 ≤ x j)
    (heq : ∀ i, ∑ j, (M i j : ℝ) * x j = (b i : ℝ)) :
    Nonempty (BoundedLinearCertificate M b
      (linearCertificateWidth (Fintype.card κ) (Fintype.card ρ) h)) := by
  obtain ⟨D, N, hD, hDbound, hNbound, hEq⟩ :=
    exists_small_nonnegative_solution M b (2 ^ h) hM hb x hx heq
  have hbound := factorial_mul_pow_lt_two_pow_of_le_two_pow
    (Fintype.card κ) (Fintype.card ρ) (2 ^ h) h (le_refl _)
  exact ⟨⟨D, N, hD, hDbound.trans_lt hbound,
    fun j => (hNbound j).trans_lt hbound, hEq⟩⟩

/-- Nonnegative feasibility gives natural numerators and a common positive
denominator, all fitting the polynomial binary width. -/
theorem exists_bounded_nonnegative_linear_solution {ρ κ : Type*}
    [Fintype ρ] [Fintype κ]
    (M : Matrix ρ κ ℤ) (b : ρ → ℤ) (h : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) (hb : ∀ i, (b i).natAbs ≤ 2 ^ h)
    (x : κ → ℝ) (hx : ∀ j, 0 ≤ x j)
    (heq : ∀ i, ∑ j, (M i j : ℝ) * x j = (b i : ℝ)) :
    ∃ (D : ℕ) (N : κ → ℕ), 0 < D ∧
      D < 2 ^ linearCertificateWidth (Fintype.card κ) (Fintype.card ρ) h ∧
      (∀ j, N j < 2 ^ linearCertificateWidth (Fintype.card κ) (Fintype.card ρ) h) ∧
      (∀ i, ∑ j, M i j * (N j : ℤ) = (D : ℤ) * b i) := by
  obtain ⟨c⟩ := exists_bounded_nonnegative_linear_certificate M b h hM hb x hx heq
  exact ⟨c.denominator, c.numerator, c.denominator_pos, c.denominator_lt,
    c.numerator_lt, c.equations⟩

end GameTheory.Math
