/- Fixed algebraic relations for all nonparameter coordinates of a source germ. -/
import Math.GateGAmbientGermRelation
import Math.GateGLocalizedSeparableRelation
import Math.GateGOptionRelativeCoordinates

set_option autoImplicit false

noncomputable section

open Filter

namespace Math
namespace GateGSourceCoordinateRelations

open GateGAmbientGermRelation
open GateGFunctionField
open GateGGermChart
open GateGGermComponentScratch
open GateGLocalizedCoordinates
open GateGOptionRelativeCoordinates

/--
Algebraicity of every nonparameter localized coordinate produces one fixed
nonzero bivariate relation for every corresponding coordinate of the
original source sequence.
-/
theorem exists_eventual_relations_of_localizedCoordinates_isAlgebraic
    {ν : Type*}
    (source : ℕ → (Option ν → ℝ))
    (g : MvPolynomial (Option ν) ℝ)
    (hg : g ∉ sequenceGermIdeal source)
    (hinjective :
      Function.Injective (fun n => source n none)) :
    let J := sequenceGermIdeal source
    letI : Algebra (Polynomial ℝ)
        (MvPolynomial (Option ν) ℝ ⧸ J) :=
      parameterPolynomialAlgebra J none
    letI : Algebra (Polynomial ℝ) GermField :=
      parameterGermAlgebra source none
    let φ :
        Localization.Away
            (Ideal.Quotient.mk J g) →ₐ[Polynomial ℝ]
          GermField :=
      localizedGermParameterAlgHom
        source J none g hg
          (mem_sequenceGermIdeal_iff source)
    (let K := FractionRing (Polynomial ℝ)
     letI : Algebra K GermField :=
       parameterFractionRingGermAlgebra
         source none hinjective
     ∀ v : ν,
       IsAlgebraic K
         (φ (optionLocalizedCoordinate J g v))) →
    ∃ relation :
        {j : Option ν // j ≠ none} →
          Polynomial (Polynomial ℝ),
      (∀ j, relation j ≠ 0) ∧
      ∀ j,
        ∀ᶠ n in
            (sequenceUltrafilter : Filter ℕ),
          bivEval (relation j)
            (source n none) (source n j.1) = 0 := by
  dsimp only
  let J := sequenceGermIdeal source
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial (Option ν) ℝ ⧸ J) :=
    parameterPolynomialAlgebra J none
  letI : Algebra (Polynomial ℝ) GermField :=
    parameterGermAlgebra source none
  let φ :
      Localization.Away
          (Ideal.Quotient.mk J g) →ₐ[Polynomial ℝ]
        GermField :=
    localizedGermParameterAlgHom
      source J none g hg
        (mem_sequenceGermIdeal_iff source)
  let K := FractionRing (Polynomial ℝ)
  letI : Algebra K GermField :=
    parameterFractionRingGermAlgebra
      source none hinjective
  intro halgebraic
  have hcoordinate :
      ∀ v : ν,
        IsAlgebraic K
          (((fun n => source n (some v)) :
            ℕ → ℝ) : GermField) := by
    intro v
    have hv := halgebraic v
    change
      IsAlgebraic K
        (localizedGermParameterAlgHom
          source J none g hg
            (mem_sequenceGermIdeal_iff source)
          (localizedCoordinate J g (some v))) at hv
    rw [localizedGermParameterAlgHom_localizedCoordinate
      source J none g hg
      (mem_sequenceGermIdeal_iff source)
      (some v)] at hv
    exact hv
  have hex :
      ∀ j : {j : Option ν // j ≠ none},
        ∃ Q : Polynomial (Polynomial ℝ),
          Q ≠ 0 ∧
          ∀ᶠ n in
              (sequenceUltrafilter : Filter ℕ),
            bivEval Q (source n none)
              (source n j.1) = 0 := by
    intro j
    cases hj : j.1 with
    | none =>
        exact (j.2 hj).elim
    | some v =>
        obtain ⟨Q, hQne, hQroot, _hQderiv⟩ :=
          exists_bivariateRelation_eventually
            source none hinjective
            (fun n => source n (some v))
            (hcoordinate v)
        refine ⟨Q, hQne, ?_⟩
        simpa [hj] using hQroot
  choose relation hne hroot using hex
  exact ⟨relation, hne, hroot⟩

end GateGSourceCoordinateRelations
end Math
