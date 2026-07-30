import Math.GateGAlgebraicRelation
import Math.GateGFunctionField
import Math.GateGKaehlerAlgebraicity
import Math.GateGGermRelation

set_option autoImplicit false

noncomputable section

namespace Math
namespace GateGFunctionFieldRelationScratch

open GateGAlgebraicRelation
open GateGFunctionField
open GateGGermRelationScratch

/-- Realizing a bivariate polynomial in the affine coordinate ring and then
passing to its function field agrees with evaluating the same polynomial
over the rational parameter field. -/
theorem algebraMap_realizeBivariate
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime]
    (parameter : σ)
    (hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0)
    (objective : MvPolynomial σ ℝ)
    (Q : Polynomial (Polynomial ℝ)) :
    let K := FractionRing (Polynomial ℝ)
    let A := MvPolynomial σ ℝ ⧸ J
    let L := FractionRing A
    letI : Algebra K L :=
      parameterFractionRingAlgebra J parameter hparameter
    algebraMap A L
        (Ideal.Quotient.mk J
          (realizeBivariate parameter objective Q)) =
      Polynomial.aeval
        (algebraMap A L
          (Ideal.Quotient.mk J objective))
        (Q.map (algebraMap (Polynomial ℝ) K)) := by
  dsimp only
  let K := FractionRing (Polynomial ℝ)
  let A := MvPolynomial σ ℝ ⧸ J
  let L := FractionRing A
  letI : Algebra K L :=
    parameterFractionRingAlgebra J parameter hparameter
  let φ : MvPolynomial σ ℝ →+* L :=
    (algebraMap A L).comp (Ideal.Quotient.mk J)
  have hbase :
      ∀ p : Polynomial ℝ,
        algebraMap K L
            (algebraMap (Polynomial ℝ) K p) =
          φ
            (Polynomial.aeval
              (MvPolynomial.X parameter) p) := by
    intro p
    rw [show
      (algebraMap K L) =
          parameterFractionRingHom
            J parameter hparameter by
        exact RingHom.algebraMap_toAlgebra _]
    rw [parameterFractionRingHom,
      IsFractionRing.lift_algebraMap]
    rfl
  have hcoeff :
      φ.comp
          (Polynomial.aeval
            (MvPolynomial.X parameter)).toRingHom =
        (algebraMap K L).comp
          (algebraMap (Polynomial ℝ) K) := by
    apply DFunLike.ext _ _
    intro p
    exact (hbase p).symm
  change
    φ (realizeBivariate parameter objective Q) =
      Polynomial.aeval
        (φ objective)
        (Q.map (algebraMap (Polynomial ℝ) K))
  rw [realizeBivariate, Polynomial.hom_eval₂,
    hcoeff, Polynomial.aeval_def,
    Polynomial.eval₂_map]

/-- Algebraicity of an affine objective in the parameter function field
produces one fixed real bivariate relation in the prime ideal, while its
value derivative stays outside the prime.  This is the exact bridge from
Kähler algebraicity back to real local root isolation. -/
theorem exists_bivariateRelation_mem_derivative_not_mem
    {σ : Type*}
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime]
    (parameter : σ)
    (hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0)
    (objective : MvPolynomial σ ℝ)
    (halgebraic :
      let K := FractionRing (Polynomial ℝ)
      let A := MvPolynomial σ ℝ ⧸ J
      let L := FractionRing A
      letI : Algebra K L :=
        parameterFractionRingAlgebra J parameter hparameter
      IsAlgebraic K
        (algebraMap A L
          (Ideal.Quotient.mk J objective))) :
    ∃ Q : Polynomial (Polynomial ℝ),
      Q ≠ 0 ∧
      realizeBivariate parameter objective Q ∈ J ∧
      realizeBivariate parameter objective Q.derivative ∉ J := by
  let K := FractionRing (Polynomial ℝ)
  let A := MvPolynomial σ ℝ ⧸ J
  let L := FractionRing A
  letI : Algebra K L :=
    parameterFractionRingAlgebra J parameter hparameter
  let q : L :=
    algebraMap A L (Ideal.Quotient.mk J objective)
  obtain ⟨Q, hQne, hQroot, hQderiv⟩ :=
    exists_base_relation_derivative_ne_zero
      (R := Polynomial ℝ) (K := K) (L := L)
      q halgebraic
  refine ⟨Q, hQne, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply (IsFractionRing.injective A L)
    rw [algebraMap_realizeBivariate
      J parameter hparameter objective Q]
    simpa only [map_zero] using hQroot
  · intro hmem
    apply hQderiv
    rw [← algebraMap_realizeBivariate
      J parameter hparameter objective Q.derivative]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
    exact map_zero _

end GateGFunctionFieldRelationScratch
end Math
