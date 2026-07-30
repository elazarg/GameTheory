/- Function-field infrastructure for the algebraic Gate G selection step. -/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Ideal

set_option autoImplicit false

noncomputable section

open Set

namespace Math
namespace CurveSelection.FunctionField

/-- Evaluation of the univariate parameter polynomial followed by passage to
the chosen prime affine quotient. -/
def parameterPolynomialHom
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ))
    (parameter : σ) :
    Polynomial ℝ →+* (MvPolynomial σ ℝ ⧸ J) :=
  (Ideal.Quotient.mk J).comp
    (Polynomial.aeval (MvPolynomial.X parameter)).toRingHom

/-- The prime affine quotient viewed as an algebra over the polynomial ring
in its distinguished parameter. -/
@[reducible] def parameterPolynomialAlgebra
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ))
    (parameter : σ) :
    Algebra (Polynomial ℝ) (MvPolynomial σ ℝ ⧸ J) :=
  (parameterPolynomialHom J parameter).toAlgebra

/-- The parameter polynomial embedding is injective precisely because the
prime germ contains no nonzero polynomial in the parameter alone. -/
theorem parameterPolynomialHom_injective
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ))
    (parameter : σ)
    (hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0) :
    Function.Injective (parameterPolynomialHom J parameter) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply (hparameter (p - q)).mp
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change parameterPolynomialHom J parameter (p - q) = 0
  rw [map_sub, hpq, sub_self]

/-- Embed parameter polynomials into the fraction field of the prime affine
quotient. -/
def parameterToFunctionFieldHom
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime]
    (parameter : σ) :
    Polynomial ℝ →+*
      FractionRing (MvPolynomial σ ℝ ⧸ J) :=
  (algebraMap
      (MvPolynomial σ ℝ ⧸ J)
      (FractionRing (MvPolynomial σ ℝ ⧸ J))).comp
    (parameterPolynomialHom J parameter)

theorem parameterToFunctionFieldHom_injective
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime]
    (parameter : σ)
    (hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0) :
    Function.Injective (parameterToFunctionFieldHom J parameter) :=
  (IsFractionRing.injective
      (MvPolynomial σ ℝ ⧸ J)
      (FractionRing (MvPolynomial σ ℝ ⧸ J))).comp
    (parameterPolynomialHom_injective J parameter hparameter)

/-- The induced embedding of the rational parameter field into the affine
function field. -/
def parameterFractionRingHom
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime]
    (parameter : σ)
    (hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0) :
    FractionRing (Polynomial ℝ) →+*
      FractionRing (MvPolynomial σ ℝ ⧸ J) :=
  IsFractionRing.lift
    (parameterToFunctionFieldHom_injective
      J parameter hparameter)

theorem parameterFractionRingHom_injective
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime]
    (parameter : σ)
    (hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0) :
    Function.Injective
      (parameterFractionRingHom J parameter hparameter) :=
  (parameterFractionRingHom J parameter hparameter).injective

/-- The function field as an algebra over the rational parameter field. -/
@[reducible] def parameterFractionRingAlgebra
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime]
    (parameter : σ)
    (hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0) :
    Algebra
      (FractionRing (Polynomial ℝ))
      (FractionRing (MvPolynomial σ ℝ ⧸ J)) :=
  (parameterFractionRingHom J parameter hparameter).toAlgebra

/-- The image in the affine function field of one coordinate class. -/
def quotientCoordinate
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime]
    (i : σ) :
    FractionRing (MvPolynomial σ ℝ ⧸ J) :=
  algebraMap
      (MvPolynomial σ ℝ ⧸ J)
      (FractionRing (MvPolynomial σ ℝ ⧸ J))
    (Ideal.Quotient.mk J (MvPolynomial.X i))

/-- The quotient coordinate classes generate the entire affine function
field over the rational parameter field. -/
theorem adjoin_range_quotientCoordinate_eq_top
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime]
    (parameter : σ)
    (hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0) :
    letI : Algebra
        (FractionRing (Polynomial ℝ))
        (FractionRing (MvPolynomial σ ℝ ⧸ J)) :=
      parameterFractionRingAlgebra J parameter hparameter
    IntermediateField.adjoin
        (FractionRing (Polynomial ℝ))
        (Set.range (quotientCoordinate J)) =
      ⊤ := by
  letI : Algebra
      (FractionRing (Polynomial ℝ))
      (FractionRing (MvPolynomial σ ℝ ⧸ J)) :=
    parameterFractionRingAlgebra J parameter hparameter
  let A := MvPolynomial σ ℝ ⧸ J
  let L := FractionRing A
  let K := FractionRing (Polynomial ℝ)
  let F : IntermediateField K L :=
    IntermediateField.adjoin K (Set.range (quotientCoordinate J))
  have hpoly :
      ∀ P : MvPolynomial σ ℝ,
        algebraMap A L (Ideal.Quotient.mk J P) ∈ F := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C r =>
        have heq :
            algebraMap A L
                (Ideal.Quotient.mk J (MvPolynomial.C r)) =
              algebraMap K L
                (algebraMap (Polynomial ℝ) K
                  (Polynomial.C r)) := by
          rw [show
            (algebraMap K L) =
                parameterFractionRingHom
                  J parameter hparameter by
              exact RingHom.algebraMap_toAlgebra _]
          rw [parameterFractionRingHom,
            IsFractionRing.lift_algebraMap]
          simp [A, L, parameterToFunctionFieldHom,
            parameterPolynomialHom]
        rw [heq]
        exact F.algebraMap_mem _
    | add P Q hP hQ =>
        simpa only [map_add] using F.add_mem hP hQ
    | mul_X P i hP =>
        have hXi : quotientCoordinate J i ∈ F :=
          IntermediateField.subset_adjoin K
            (Set.range (quotientCoordinate J))
            (Set.mem_range_self i)
        simpa only [map_mul, quotientCoordinate] using
          F.mul_mem hP hXi
  apply top_unique
  intro z _hz
  obtain ⟨a, b, _hb, rfl⟩ :=
    IsFractionRing.div_surjective A z
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact F.div_mem (hpoly P) (hpoly Q)

/-- For finitely many affine coordinates, the function field of the prime
quotient is essentially of finite type over the rational parameter field.
This is the finite-generation hypothesis used by the Kähler-differential
algebraicity argument. -/
theorem essFiniteType_parameterFunctionField
    {σ : Type*} [Finite σ]
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime]
    (parameter : σ)
    (hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0) :
    letI : Algebra
        (FractionRing (Polynomial ℝ))
        (FractionRing (MvPolynomial σ ℝ ⧸ J)) :=
      parameterFractionRingAlgebra J parameter hparameter
    Algebra.EssFiniteType
      (FractionRing (Polynomial ℝ))
      (FractionRing (MvPolynomial σ ℝ ⧸ J)) := by
  letI : Algebra
      (FractionRing (Polynomial ℝ))
      (FractionRing (MvPolynomial σ ℝ ⧸ J)) :=
    parameterFractionRingAlgebra J parameter hparameter
  have hfg :
      (⊤ : IntermediateField
        (FractionRing (Polynomial ℝ))
        (FractionRing (MvPolynomial σ ℝ ⧸ J))).FG := by
    rw [← adjoin_range_quotientCoordinate_eq_top
      J parameter hparameter]
    exact IntermediateField.fg_adjoin_of_finite
      (Set.finite_range (quotientCoordinate J))
  exact IntermediateField.fg_top_iff.mp hfg

end CurveSelection.FunctionField
end Math
