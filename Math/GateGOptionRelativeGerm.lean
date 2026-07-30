import Math.GateGOptionRelativeCoordinates

set_option autoImplicit false

noncomputable section

open Filter

namespace Math
namespace GateGOptionRelativeGerm

open GateGFunctionField
open GateGGermChart
open GateGGermComponentScratch
open GateGOptionRelativeCoordinates
open GateGRelativePresentation

/-- Pointwise evaluation after separating the `none` variable into the
coefficient parameter is ordinary evaluation of the original polynomial. -/
theorem eval₂_optionEquivRight
    {ν : Type*}
    (Q : MvPolynomial (Option ν) ℝ)
    (t : ℝ) (y : ν → ℝ) :
    MvPolynomial.eval₂
        (Polynomial.evalRingHom t) y
        (MvPolynomial.optionEquivRight ℝ ν Q) =
      MvPolynomial.eval
        (fun o => o.elim t y) Q := by
  have h :=
    eval_flattenParameterPolynomial
      (MvPolynomial.optionEquivRight ℝ ν Q) t y
  rw [show
      flattenParameterPolynomial
          (MvPolynomial.optionEquivRight ℝ ν Q) =
        Q by
      exact
        (MvPolynomial.optionEquivRight ℝ ν).symm_apply_apply Q]
    at h
  exact h.symm

/--
The localized germ map sends evaluation of an option-separated relative
polynomial to the germ of its ordinary values on the source sequence.
-/
theorem localizedGermParameterAlgHom_eval₂_optionEquivRight
    {ν : Type*}
    (x : ℕ → (Option ν → ℝ))
    (J : Ideal (MvPolynomial (Option ν) ℝ))
    (g : MvPolynomial (Option ν) ℝ)
    (hg : g ∉ J)
    (hJmem :
      ∀ Q : MvPolynomial (Option ν) ℝ,
        Q ∈ J ↔
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (x n) Q = 0)
    (Q : MvPolynomial (Option ν) ℝ) :
    letI : Algebra (Polynomial ℝ)
        (MvPolynomial (Option ν) ℝ ⧸ J) :=
      parameterPolynomialAlgebra J none
    letI : Algebra (Polynomial ℝ) GermField :=
      parameterGermAlgebra x none
    localizedGermParameterAlgHom
        x J none g hg hJmem
        (MvPolynomial.eval₂
          (algebraMap (Polynomial ℝ)
            (Localization.Away
              (Ideal.Quotient.mk J g)))
          (optionLocalizedCoordinate J g)
          (MvPolynomial.optionEquivRight ℝ ν Q)) =
      ((fun n => MvPolynomial.eval (x n) Q) :
        GermField) := by
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial (Option ν) ℝ ⧸ J) :=
    parameterPolynomialAlgebra J none
  letI : Algebra (Polynomial ℝ) GermField :=
    parameterGermAlgebra x none
  rw [eval₂_optionEquivRight_optionLocalizedCoordinate
    J g Q]
  change
    localizedGermParameterAlgHom
        x J none g hg hJmem
        (algebraMap
          (MvPolynomial (Option ν) ℝ ⧸ J)
          (Localization.Away
            (Ideal.Quotient.mk J g))
          (Ideal.Quotient.mk J Q)) =
      ((fun n => MvPolynomial.eval (x n) Q) :
        GermField)
  rw [localizedGermParameterAlgHom,
    IsLocalization.liftAlgHom_apply,
    IsLocalization.lift_eq]
  change
    quotientGermAlgHom x J hJmem
        (Ideal.Quotient.mk J Q) =
      ((fun n => MvPolynomial.eval (x n) Q) :
        GermField)
  change
    sequenceGermEval x Q =
      ((fun n => MvPolynomial.eval (x n) Q) :
        GermField)
  exact sequenceGermEval_apply x Q

end GateGOptionRelativeGerm
end Math
