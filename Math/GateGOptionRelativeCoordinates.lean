/- Relative coordinates obtained by separating the `none` parameter from
an `Option`-indexed affine germ. -/
import Math.GateGLocalizedCoordinates

set_option autoImplicit false
set_option linter.unusedFintypeInType false

noncomputable section

open Filter

namespace Math
namespace GateGOptionRelativeCoordinates

open GateGFunctionField
open GateGGermChart
open GateGGermComponentScratch
open GateGLocalizedCoordinates
open GateGRelativePresentation

/-- The non-parameter affine coordinates in the localized prime quotient. -/
def optionLocalizedCoordinate
    {ν : Type*}
    (J : Ideal (MvPolynomial (Option ν) ℝ))
    (g : MvPolynomial (Option ν) ℝ)
    (v : ν) :
    Localization.Away (Ideal.Quotient.mk J g) :=
  localizedCoordinate J g (some v)

/--
Separating the `none` variable into the coefficient polynomial commutes
with evaluation at the localized affine coordinates.  Thus the resulting
relative polynomial represents exactly the localization of the original
`Option`-indexed polynomial.
-/
theorem eval₂_optionEquivRight_optionLocalizedCoordinate
    {ν : Type*}
    (J : Ideal (MvPolynomial (Option ν) ℝ))
    (g : MvPolynomial (Option ν) ℝ)
    (Q : MvPolynomial (Option ν) ℝ) :
    letI : Algebra (Polynomial ℝ)
        (MvPolynomial (Option ν) ℝ ⧸ J) :=
      parameterPolynomialAlgebra J none
    MvPolynomial.eval₂
        (algebraMap (Polynomial ℝ)
          (Localization.Away
            (Ideal.Quotient.mk J g)))
        (optionLocalizedCoordinate J g)
        (MvPolynomial.optionEquivRight ℝ ν Q) =
      algebraMap
        (MvPolynomial (Option ν) ℝ ⧸ J)
        (Localization.Away
          (Ideal.Quotient.mk J g))
        (Ideal.Quotient.mk J Q) := by
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial (Option ν) ℝ ⧸ J) :=
    parameterPolynomialAlgebra J none
  induction Q using MvPolynomial.induction_on with
  | C r =>
      rw [MvPolynomial.optionEquivRight_C,
        MvPolynomial.eval₂_C]
      change
        algebraMap
            (MvPolynomial (Option ν) ℝ ⧸ J)
            (Localization.Away
              (Ideal.Quotient.mk J g))
            (parameterPolynomialHom J none
              (Polynomial.C r)) =
          algebraMap
            (MvPolynomial (Option ν) ℝ ⧸ J)
            (Localization.Away
              (Ideal.Quotient.mk J g))
            (Ideal.Quotient.mk J
              (MvPolynomial.C r))
      congr 1
      simp [parameterPolynomialHom]
  | add P Q hP hQ =>
      simp only [map_add, MvPolynomial.eval₂_add,
        hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, MvPolynomial.eval₂_mul,
        hP]
      congr 1
      cases i with
      | none =>
          rw [MvPolynomial.optionEquivRight_X_none,
            MvPolynomial.eval₂_C]
          change
            algebraMap
                (MvPolynomial (Option ν) ℝ ⧸ J)
                (Localization.Away
                  (Ideal.Quotient.mk J g))
                (parameterPolynomialHom J none
                  Polynomial.X) =
              algebraMap
                (MvPolynomial (Option ν) ℝ ⧸ J)
                (Localization.Away
                  (Ideal.Quotient.mk J g))
                (Ideal.Quotient.mk J
                  (MvPolynomial.X none))
          congr 1
          simp [parameterPolynomialHom]
      | some v =>
          rw [MvPolynomial.optionEquivRight_X_some,
            MvPolynomial.eval₂_X]
          rfl

/-- Every equation in the option-indexed prime ideal becomes a relative
`ℝ[t]`-polynomial identity on the non-parameter localized coordinates. -/
theorem eval₂_optionEquivRight_optionLocalizedCoordinate_eq_zero
    {ν : Type*}
    (J : Ideal (MvPolynomial (Option ν) ℝ))
    (g : MvPolynomial (Option ν) ℝ)
    {Q : MvPolynomial (Option ν) ℝ}
    (hQ : Q ∈ J) :
    letI : Algebra (Polynomial ℝ)
        (MvPolynomial (Option ν) ℝ ⧸ J) :=
      parameterPolynomialAlgebra J none
    MvPolynomial.eval₂
        (algebraMap (Polynomial ℝ)
          (Localization.Away
            (Ideal.Quotient.mk J g)))
        (optionLocalizedCoordinate J g)
        (MvPolynomial.optionEquivRight ℝ ν Q) =
      0 := by
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial (Option ν) ℝ ⧸ J) :=
    parameterPolynomialAlgebra J none
  rw [eval₂_optionEquivRight_optionLocalizedCoordinate
    J g Q]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hQ,
    map_zero]

/--
The presentation sections of the non-parameter localized coordinates
eventually recover the source assignments with their `none` coordinate
removed.
-/
theorem eventually_optionPresentationSectionMap_eq
    {ν ι κ : Type*} [Fintype ν]
    (x : ℕ → (Option ν → ℝ))
    (J : Ideal (MvPolynomial (Option ν) ℝ))
    (g : MvPolynomial (Option ν) ℝ)
    [Algebra (Polynomial ℝ)
      (MvPolynomial (Option ν) ℝ ⧸ J)]
    [Algebra (Polynomial ℝ) GermField]
    (hg : g ∉ J)
    (hJmem :
      ∀ Q : MvPolynomial (Option ν) ℝ,
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
              (Polynomial.evalRingHom (x n none))
              (a n) (P.σ s) =
            germRepresentative
              (localizedGermParameterAlgHom
                x J none g hg hJmem s) n) :
    ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
      presentationSectionMap P
          (x n none)
          (optionLocalizedCoordinate J g)
          (a n) =
        fun v => x n (some v) := by
  have hfull :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        presentationSectionMap P
            (x n none)
            (localizedCoordinate J g)
            (a n) =
          x n :=
    eventually_presentationSectionMap_eq
      x J none g hg hJmem P a hsection
  filter_upwards [hfull] with n hn
  funext v
  exact congrFun hn (some v)

/-- Canonical `sequenceGermIdeal` specialization of
`eventually_optionPresentationSectionMap_eq`. -/
theorem eventually_optionPresentationSectionMap_eq_sequenceGerm
    {ν ι κ : Type*} [Fintype ν]
    (x : ℕ → (Option ν → ℝ))
    (g : MvPolynomial (Option ν) ℝ)
    (hg : g ∉ sequenceGermIdeal x) :
    let J := sequenceGermIdeal x
    letI : Algebra (Polynomial ℝ)
        (MvPolynomial (Option ν) ℝ ⧸ J) :=
      parameterPolynomialAlgebra J none
    letI : Algebra (Polynomial ℝ) GermField :=
      parameterGermAlgebra x none
    ∀ (P :
        Algebra.Presentation
          (Polynomial ℝ)
          (Localization.Away
            (Ideal.Quotient.mk J g))
          ι κ)
      (a : ℕ → (ι → ℝ)),
      (∀ s :
          Localization.Away
            (Ideal.Quotient.mk J g),
        ∀ᶠ n in
            (sequenceUltrafilter : Filter ℕ),
          MvPolynomial.eval₂
              (Polynomial.evalRingHom (x n none))
              (a n) (P.σ s) =
            germRepresentative
              (localizedGermParameterAlgHom
                x J none g hg
                (mem_sequenceGermIdeal_iff x) s) n) →
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        presentationSectionMap P
            (x n none)
            (optionLocalizedCoordinate J g)
            (a n) =
          fun v => x n (some v) := by
  dsimp only
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial (Option ν) ℝ ⧸
        sequenceGermIdeal x) :=
    parameterPolynomialAlgebra
      (sequenceGermIdeal x) none
  letI : Algebra (Polynomial ℝ) GermField :=
    parameterGermAlgebra x none
  intro P a hsection
  exact eventually_optionPresentationSectionMap_eq
    x (sequenceGermIdeal x) g hg
    (mem_sequenceGermIdeal_iff x) P a hsection

end GateGOptionRelativeCoordinates
end Math
