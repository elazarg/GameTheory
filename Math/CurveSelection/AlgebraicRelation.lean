import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

set_option autoImplicit false
set_option linter.unnecessarySimpa false

noncomputable section

open Polynomial

namespace Math
namespace CurveSelection.AlgebraicRelation

/--
An algebraic element over a fraction field satisfies a polynomial over the
base domain whose value derivative remains nonzero.  This is denominator
clearing applied to the separable minimal polynomial.
-/
theorem exists_base_relation_derivative_ne_zero
    {R K L : Type*}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    [Field L] [Algebra K L]
    (q : L) (hq : IsAlgebraic K q) :
    ∃ Q : Polynomial R,
      Q ≠ 0 ∧
      aeval q (Q.map (algebraMap R K)) = 0 ∧
      aeval q (Q.derivative.map (algebraMap R K)) ≠ 0 := by
  let m : Polynomial K := minpoly K q
  have hqInt : IsIntegral K q := hq.isIntegral
  have hm0 : m ≠ 0 := minpoly.ne_zero hqInt
  have hmroot : aeval q m = 0 := minpoly.aeval K q
  have hmderiv : aeval q m.derivative ≠ 0 := by
    exact
      (minpoly.irreducible hqInt).separable.aeval_derivative_ne_zero
        hmroot
  let M : Submonoid R := nonZeroDivisors R
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples M m.support m.coeff
  have hcoeff :
      ∀ i : ℕ,
        IsLocalization.IsInteger R
          ((d : R) • m.coeff i) := by
    intro i
    by_cases hi : i ∈ m.support
    · exact hd i hi
    · rw [Polynomial.notMem_support_iff.mp hi, smul_zero]
      exact IsLocalization.isInteger_zero
  let D : K := algebraMap R K (d : R)
  have hD : D ≠ 0 := by
    intro hD0
    have hd0 : (d : R) = 0 := by
      apply IsFractionRing.injective R K
      simpa [D] using hD0
    exact nonZeroDivisors.coe_ne_zero d hd0
  have hlifts :
      Polynomial.C D * m ∈
        Polynomial.lifts (algebraMap R K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_C_mul]
    obtain ⟨a, ha⟩ := hcoeff i
    exact ⟨a, by simpa [D, Algebra.smul_def] using ha⟩
  obtain ⟨Q, hQmap⟩ :=
    (Polynomial.mem_lifts _).mp hlifts
  have hQ0 : Q ≠ 0 := by
    intro hQ
    have : Polynomial.C D * m = 0 := by
      rw [← hQmap, hQ, Polynomial.map_zero]
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hD) hm0) this
  refine ⟨Q, hQ0, ?_, ?_⟩
  · rw [hQmap, map_mul, aeval_C, hmroot, mul_zero]
  · have hderivMap :
        Q.derivative.map (algebraMap R K) =
          Polynomial.C D * m.derivative := by
      rw [← Polynomial.derivative_map, hQmap,
        Polynomial.derivative_mul]
      simp
    rw [hderivMap, map_mul, aeval_C]
    exact
      mul_ne_zero
        ((_root_.map_ne_zero (algebraMap K L)).2 hD)
        hmderiv

end CurveSelection.AlgebraicRelation
end Math
