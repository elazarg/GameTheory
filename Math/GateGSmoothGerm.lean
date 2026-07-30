import Math.MultivariateElimination
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

set_option autoImplicit false

noncomputable section

open Filter

namespace Math
namespace GateGSmoothGermScratch

abbrev sequenceUltrafilter : Ultrafilter ℕ :=
  hyperfilter ℕ

/-- A prime affine quotient over the perfect field `ℝ` has a smooth basic
open containing its generic point.  The polynomial defining that open is
nonzero in the quotient, equivalently it does not belong to the prime. -/
theorem exists_smooth_basicOpen_of_prime
    {σ : Type*} [Finite σ]
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime] :
    ∃ g : MvPolynomial σ ℝ,
      g ∉ J ∧
      Algebra.Smooth ℝ
        (Localization.Away
          (Ideal.Quotient.mk J g)) := by
  let A := MvPolynomial σ ℝ ⧸ J
  letI : Nontrivial A :=
    Ideal.Quotient.nontrivial_iff.mpr
      (by
        have hJ : J.IsPrime := inferInstance
        exact hJ.ne_top)
  letI : IsDomain A := Ideal.Quotient.isDomain J
  letI : Algebra.FinitePresentation ℝ A :=
    Algebra.FinitePresentation.quotient
      (IsNoetherian.noetherian J)
  have hminimal :
      (⊥ : Ideal A) ∈ minimalPrimes A := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    exact Set.mem_singleton _
  let K := Localization.AtPrime (⊥ : Ideal A)
  haveI : Ring.KrullDimLE 0 K :=
    Ring.KrullDimLE.of_isLocalization
      (⊥ : Ideal A) hminimal K
  letI : Field K :=
    Ring.KrullDimLE.isField_of_isReduced.toField
  letI : Algebra.FormallySmooth ℝ K :=
    Algebra.FormallySmooth.of_perfectField
  letI : Algebra.IsSmoothAt ℝ (⊥ : Ideal A) :=
    inferInstance
  obtain ⟨f, hf, hsmooth⟩ :=
    Algebra.IsSmoothAt.exists_notMem_smooth
      ℝ (⊥ : Ideal A)
  obtain ⟨g, rfl⟩ :=
    Ideal.Quotient.mk_surjective f
  refine ⟨g, ?_, hsmooth⟩
  intro hg
  exact hf (Ideal.Quotient.eq_zero_iff_mem.mpr hg)

/-- The generic smooth neighbourhood may be shrunk to a standard-smooth
basic open.  This exposes a finite polynomial presentation with invertible
Jacobian minor, the form needed for a polar construction. -/
theorem exists_standardSmooth_basicOpen_of_prime
    {σ : Type*} [Finite σ]
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime] :
    ∃ g : MvPolynomial σ ℝ,
      g ∉ J ∧
      Algebra.IsStandardSmooth ℝ
        (Localization.Away
          (Ideal.Quotient.mk J g)) := by
  let A := MvPolynomial σ ℝ ⧸ J
  letI : Nontrivial A :=
    Ideal.Quotient.nontrivial_iff.mpr
      (by
        have hJ : J.IsPrime := inferInstance
        exact hJ.ne_top)
  letI : IsDomain A := Ideal.Quotient.isDomain J
  letI : Algebra.FinitePresentation ℝ A :=
    Algebra.FinitePresentation.quotient
      (IsNoetherian.noetherian J)
  have hminimal :
      (⊥ : Ideal A) ∈ minimalPrimes A := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    exact Set.mem_singleton _
  let K := Localization.AtPrime (⊥ : Ideal A)
  haveI : Ring.KrullDimLE 0 K :=
    Ring.KrullDimLE.of_isLocalization
      (⊥ : Ideal A) hminimal K
  letI : Field K :=
    Ring.KrullDimLE.isField_of_isReduced.toField
  letI : Algebra.FormallySmooth ℝ K :=
    Algebra.FormallySmooth.of_perfectField
  letI : Algebra.IsSmoothAt ℝ (⊥ : Ideal A) :=
    inferInstance
  obtain ⟨f, hf, hstandard⟩ :=
    Algebra.IsSmoothAt.exists_notMem_isStandardSmooth
      ℝ (⊥ : Ideal A)
  obtain ⟨g, rfl⟩ :=
    Ideal.Quotient.mk_surjective f
  refine ⟨g, ?_, hstandard⟩
  intro hg
  exact hf (Ideal.Quotient.eq_zero_iff_mem.mpr hg)

/-- Apply the generic-smooth-open theorem to the prime component selected
by a strict parameter sequence.  The defining polynomial is eventually
nonzero along the same ultrafilter germ, so the original sign-cell sequence
is retained on the smooth locus. -/
theorem exists_eventually_smooth_basicOpen_of_strictParameter
    {I σ : Type*} [Finite σ]
    (P : I → MvPolynomial σ ℝ)
    (x : ℕ → (σ → ℝ))
    (parameter : σ)
    (J : Ideal (MvPolynomial σ ℝ))
    (hJprime : J.IsPrime)
    (_hPJ : Ideal.span (Set.range P) ≤ J)
    (_hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0)
    (hJmem : ∀ Q : MvPolynomial σ ℝ,
      Q ∈ J ↔
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          MvPolynomial.eval (x n) Q = 0) :
    ∃ g : MvPolynomial σ ℝ,
      g ∉ J ∧
      (∀ᶠ n in
          (sequenceUltrafilter : Filter ℕ),
        MvPolynomial.eval (x n) g ≠ 0) ∧
      Algebra.Smooth ℝ
        (Localization.Away
          (Ideal.Quotient.mk J g)) := by
  letI : J.IsPrime := hJprime
  obtain ⟨g, hgJ, hsmooth⟩ :=
    exists_smooth_basicOpen_of_prime J
  have hnotEventuallyZero :
      ¬∀ᶠ n in
          (sequenceUltrafilter : Filter ℕ),
        MvPolynomial.eval (x n) g = 0 := by
    intro hzero'
    exact hgJ ((hJmem g).mpr hzero')
  have hEventuallyNonzero :
      ∀ᶠ n in
          (sequenceUltrafilter : Filter ℕ),
        MvPolynomial.eval (x n) g ≠ 0 := by
    rw [Ultrafilter.eventually_not]
    exact hnotEventuallyZero
  exact ⟨g, hgJ, hEventuallyNonzero, hsmooth⟩

/-- The standard-smooth refinement retains the selected sequence: its chart
denominator is eventually nonzero in the same ultrafilter germ. -/
theorem exists_eventually_standardSmooth_basicOpen_of_strictParameter
    {I σ : Type*} [Finite σ]
    (P : I → MvPolynomial σ ℝ)
    (x : ℕ → (σ → ℝ))
    (parameter : σ)
    (J : Ideal (MvPolynomial σ ℝ))
    (hJprime : J.IsPrime)
    (_hPJ : Ideal.span (Set.range P) ≤ J)
    (_hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0)
    (hJmem : ∀ Q : MvPolynomial σ ℝ,
      Q ∈ J ↔
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          MvPolynomial.eval (x n) Q = 0) :
    ∃ g : MvPolynomial σ ℝ,
      g ∉ J ∧
      (∀ᶠ n in
          (sequenceUltrafilter : Filter ℕ),
        MvPolynomial.eval (x n) g ≠ 0) ∧
      Algebra.IsStandardSmooth ℝ
        (Localization.Away
          (Ideal.Quotient.mk J g)) := by
  letI : J.IsPrime := hJprime
  obtain ⟨g, hgJ, hstandard⟩ :=
    exists_standardSmooth_basicOpen_of_prime J
  have hnotEventuallyZero :
      ¬∀ᶠ n in
          (sequenceUltrafilter : Filter ℕ),
        MvPolynomial.eval (x n) g = 0 := by
    intro hzero'
    exact hgJ ((hJmem g).mpr hzero')
  have hEventuallyNonzero :
      ∀ᶠ n in
          (sequenceUltrafilter : Filter ℕ),
        MvPolynomial.eval (x n) g ≠ 0 := by
    rw [Ultrafilter.eventually_not]
    exact hnotEventuallyZero
  exact ⟨g, hgJ, hEventuallyNonzero, hstandard⟩

end GateGSmoothGermScratch
end Math
