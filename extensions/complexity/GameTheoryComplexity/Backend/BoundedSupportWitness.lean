import GameTheoryComplexity.Backend.NashSupportSystem
import GameTheory.Math.SmallRationalWitness
import GameTheory.Math.FiniteLinearBitBound

/-! Fixed-support best-response feasibility has integer numerator solutions
whose common denominator and every coordinate have polynomial binary width. -/

namespace GameTheory.Complexity.Backend
open GameTheory.Math (constrainedNashCertificateWidth)

open scoped BigOperators

/-- A feasible support system for a bounded integer table has a positive common
denominator and natural numerators fitting the quadratic field width. -/
theorem exists_bounded_support_solution {q : ℕ} (A : Fin q → Fin q → ℤ)
    (S T : Fin q → Bool) (hA : ∀ i j, (A i j).natAbs ≤ q + 2)
    (w : Fin q → ℝ) (u : ℝ) (h : realSupportFeasible A S T w u) :
    ∃ (D : ℕ) (N : SupportVariable q → ℕ), 0 < D ∧
      D < 2 ^ (constrainedNashCertificateWidth q) ∧
      (∀ j, N j < 2 ^ (constrainedNashCertificateWidth q)) ∧
      (∀ i, ∑ j, supportMatrix A S T i j * (N j : ℤ) =
        (D : ℤ) * supportRhs i) := by
  obtain ⟨D, N, hD, hDbound, hNbound, hEq⟩ :=
    GameTheory.Math.exists_small_nonnegative_solution
      (supportMatrix A S T) (@supportRhs q) (q + 2)
      (supportMatrix_bound A S T (by omega) hA)
      (supportRhs_bound (by omega))
      (supportVector A w u) (supportVector_nonneg A S T w u h)
      (supportVector_solution A S T w u h)
  simp only [supportRow_card, supportVariable_card] at hDbound hNbound
  have hbound := GameTheory.Math.bimatrix_factorial_bound_lt_two_pow q
  refine ⟨D, N, hD, ?_, ?_, hEq⟩
  · exact hDbound.trans_lt hbound
  · intro j
    exact (hNbound j).trans_lt hbound

/-- Any input-length upper bound on the dimension bounds the same numerator
solution by the corresponding polynomial certificate field width. -/
theorem exists_bounded_support_solution_of_le {q L : ℕ}
    (A : Fin q → Fin q → ℤ) (S T : Fin q → Bool)
    (hA : ∀ i j, (A i j).natAbs ≤ q + 2) (hq : q ≤ L)
    (w : Fin q → ℝ) (u : ℝ) (h : realSupportFeasible A S T w u) :
    ∃ (D : ℕ) (N : SupportVariable q → ℕ), 0 < D ∧
      D < 2 ^ (constrainedNashCertificateWidth L) ∧
      (∀ j, N j < 2 ^ (constrainedNashCertificateWidth L)) ∧
      (∀ i, ∑ j, supportMatrix A S T i j * (N j : ℤ) =
        (D : ℤ) * supportRhs i) := by
  obtain ⟨D, N, hD, hDbound, hNbound, hEq⟩ :=
    exists_bounded_support_solution A S T hA w u h
  have hwidth : 2 ^ (constrainedNashCertificateWidth q) ≤
      2 ^ (constrainedNashCertificateWidth L) :=
    pow_le_pow_right' (by decide) (GameTheory.Math.bimatrix_width_mono hq)
  exact ⟨D, N, hD, hDbound.trans_le hwidth,
    fun j => (hNbound j).trans_le hwidth, hEq⟩

end GameTheory.Complexity.Backend
