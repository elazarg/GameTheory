/- Coordinate identities for the localized prime germ used by analytic
curve selection. -/
import Math.CurveSelection.RelativeChartSequence

noncomputable section

open Filter

namespace Math
namespace CurveSelection.LocalizedCoordinates

open CurveSelection.FunctionField
open CurveSelection.GermChart
open CurveSelection.GermComponentScratch
open CurveSelection.RelativePresentation

/-- The image of an affine coordinate in a basic open of an affine
quotient. -/
def localizedCoordinate
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ))
    (g : MvPolynomial σ ℝ)
    (i : σ) :
    Localization.Away (Ideal.Quotient.mk J g) :=
  algebraMap
    (MvPolynomial σ ℝ ⧸ J)
    (Localization.Away (Ideal.Quotient.mk J g))
    (Ideal.Quotient.mk J (MvPolynomial.X i))

/-- Regard a real multivariate polynomial as a polynomial whose
coefficients are constant polynomials in the distinguished parameter. -/
def overParameter
    {σ : Type*} :
    MvPolynomial σ ℝ →+*
      MvPolynomial σ (Polynomial ℝ) :=
  MvPolynomial.map Polynomial.C

/-- Evaluation at the localized coordinate tuple is the quotient map,
after regarding real coefficients as constant parameter polynomials. -/
theorem eval₂_overParameter_localizedCoordinate
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ))
    (parameter : σ)
    (g : MvPolynomial σ ℝ)
    (Q : MvPolynomial σ ℝ) :
    letI : Algebra (Polynomial ℝ)
        (MvPolynomial σ ℝ ⧸ J) :=
      parameterPolynomialAlgebra J parameter
    MvPolynomial.eval₂
        (algebraMap (Polynomial ℝ)
          (Localization.Away
            (Ideal.Quotient.mk J g)))
        (localizedCoordinate J g)
        (overParameter Q) =
      algebraMap
        (MvPolynomial σ ℝ ⧸ J)
        (Localization.Away
          (Ideal.Quotient.mk J g))
        (Ideal.Quotient.mk J Q) := by
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial σ ℝ ⧸ J) :=
    parameterPolynomialAlgebra J parameter
  induction Q using MvPolynomial.induction_on with
  | C r =>
      simp only [overParameter, MvPolynomial.map_C,
        MvPolynomial.eval₂_C]
      change
        algebraMap
            (MvPolynomial σ ℝ ⧸ J)
            (Localization.Away
              (Ideal.Quotient.mk J g))
            (parameterPolynomialHom J parameter
              (Polynomial.C r)) =
          algebraMap
            (MvPolynomial σ ℝ ⧸ J)
            (Localization.Away
              (Ideal.Quotient.mk J g))
            (Ideal.Quotient.mk J
              (MvPolynomial.C r))
      congr 1
      simp [parameterPolynomialHom]
  | add P Q hP hQ =>
      simp only [map_add, MvPolynomial.eval₂_add]
      rw [hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, MvPolynomial.eval₂_mul]
      rw [hP]
      simp [overParameter, localizedCoordinate]

/-- Every polynomial in the prime ideal becomes a relative polynomial
identity on the localized coordinate tuple. -/
theorem eval₂_overParameter_localizedCoordinate_eq_zero
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ))
    (parameter : σ)
    (g : MvPolynomial σ ℝ)
    {Q : MvPolynomial σ ℝ}
    (hQ : Q ∈ J) :
    letI : Algebra (Polynomial ℝ)
        (MvPolynomial σ ℝ ⧸ J) :=
      parameterPolynomialAlgebra J parameter
    MvPolynomial.eval₂
        (algebraMap (Polynomial ℝ)
          (Localization.Away
            (Ideal.Quotient.mk J g)))
        (localizedCoordinate J g)
        (overParameter Q) = 0 := by
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial σ ℝ ⧸ J) :=
    parameterPolynomialAlgebra J parameter
  rw [eval₂_overParameter_localizedCoordinate
    J parameter g Q]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hQ,
    map_zero]

/-- The localized generic-point map sends each localized coordinate to
the corresponding coordinate sequence germ. -/
theorem localizedGermParameterAlgHom_localizedCoordinate
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (J : Ideal (MvPolynomial σ ℝ))
    (parameter : σ)
    (g : MvPolynomial σ ℝ)
    (hg : g ∉ J)
    (hJmem :
      ∀ Q : MvPolynomial σ ℝ,
        Q ∈ J ↔
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (x n) Q = 0)
    (i : σ) :
    letI : Algebra (Polynomial ℝ)
        (MvPolynomial σ ℝ ⧸ J) :=
      parameterPolynomialAlgebra J parameter
    letI : Algebra (Polynomial ℝ) GermField :=
      parameterGermAlgebra x parameter
    localizedGermParameterAlgHom
        x J parameter g hg hJmem
        (localizedCoordinate J g i) =
      ((fun n => x n i) : GermField) := by
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial σ ℝ ⧸ J) :=
    parameterPolynomialAlgebra J parameter
  letI : Algebra (Polynomial ℝ) GermField :=
    parameterGermAlgebra x parameter
  change
    localizedGermParameterAlgHom
        x J parameter g hg hJmem
        (algebraMap
          (MvPolynomial σ ℝ ⧸ J)
          (Localization.Away
            (Ideal.Quotient.mk J g))
          (Ideal.Quotient.mk J
            (MvPolynomial.X i))) =
      ((fun n => x n i) : GermField)
  rw [localizedGermParameterAlgHom,
    IsLocalization.liftAlgHom_apply,
    IsLocalization.lift_eq]
  change
    quotientGermAlgHom x J hJmem
        (Ideal.Quotient.mk J
          (MvPolynomial.X i)) =
      ((fun n => x n i) : GermField)
  change
    sequenceGermEval x (MvPolynomial.X i) =
      ((fun n => x n i) : GermField)
  simp [sequenceGermEval]

/-- A presentation representative of the localized generic point recovers
the original affine sequence, simultaneously in every coordinate, on an
ultrafilter-large set. -/
theorem eventually_presentationSectionMap_eq
    {σ ι κ : Type*} [Finite σ]
    (x : ℕ → (σ → ℝ))
    (J : Ideal (MvPolynomial σ ℝ))
    (parameter : σ)
    (g : MvPolynomial σ ℝ)
    [Algebra (Polynomial ℝ)
      (MvPolynomial σ ℝ ⧸ J)]
    [Algebra (Polynomial ℝ) GermField]
    (hg : g ∉ J)
    (hJmem :
      ∀ Q : MvPolynomial σ ℝ,
        Q ∈ J ↔
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (x n) Q = 0)
    (P :
      Algebra.Presentation
        (Polynomial ℝ)
        (Localization.Away
          (Ideal.Quotient.mk J g))
        ι κ)
    (a : ℕ → (ι → ℝ))
    (hsection :
      ∀ s :
          Localization.Away
            (Ideal.Quotient.mk J g),
        ∀ᶠ n in
            (sequenceUltrafilter : Filter ℕ),
          MvPolynomial.eval₂
              (Polynomial.evalRingHom
                (x n parameter))
              (a n) (P.σ s) =
            germRepresentative
              (localizedGermParameterAlgHom
                x J parameter g hg hJmem s) n) :
    ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
      presentationSectionMap P
          (x n parameter)
          (localizedCoordinate J g)
          (a n) =
        x n := by
  letI : Fintype σ := Fintype.ofFinite σ
  have hcoordinate :
      ∀ i : σ,
        ∀ᶠ n in
            (sequenceUltrafilter : Filter ℕ),
          presentationSectionMap P
              (x n parameter)
              (localizedCoordinate J g)
              (a n) i =
            x n i := by
    intro i
    have hgerm :
        ((germRepresentative
            (localizedGermParameterAlgHom
              x J parameter g hg hJmem
              (localizedCoordinate J g i))) :
            GermField) =
          ((fun n => x n i) : GermField) := by
      rw [coe_germRepresentative,
        localizedGermParameterAlgHom_localizedCoordinate
          x J parameter g hg hJmem i]
    have hrep :
        ∀ᶠ n in
            (sequenceUltrafilter : Filter ℕ),
          germRepresentative
              (localizedGermParameterAlgHom
                x J parameter g hg hJmem
                (localizedCoordinate J g i)) n =
            x n i :=
      Filter.Germ.coe_eq.mp hgerm
    filter_upwards
      [hsection (localizedCoordinate J g i),
        hrep] with n hn hni
    rw [presentationSectionMap,
      eval_specializeParameterPolynomial]
    exact hn.trans hni
  filter_upwards
    [Filter.eventually_all.mpr hcoordinate] with n hn
  funext i
  exact hn i

end CurveSelection.LocalizedCoordinates
end Math
