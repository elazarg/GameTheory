/- A regular relative standard-smooth chart extracted from a strict
parameter sequence. -/
import Math.CurveSelection.RelativePresentationGerm

set_option autoImplicit false
set_option linter.unusedFintypeInType false

noncomputable section

open Filter

namespace Math
namespace CurveSelection.RelativeChartSequence

open CurveSelection.FunctionField
open CurveSelection.GermChart
open CurveSelection.GermComponentScratch
open CurveSelection.RelativePresentation
open CurveSelection.RelativePresentationGerm
open CurveSelection.RelativeSmoothGerm

/--
A sequence whose distinguished parameter is strictly decreasing determines
one prime algebraic germ.  After shrinking that germ by an eventually
nonzero denominator, it admits a finite relative submersive presentation
and a real representative sequence on which all relations and its selected
Jacobian minor hold eventually.

The variable and relation types are reindexed by finite ordinals so the
caller receives ordinary `Fintype` instances without carrying existential
typeclass witnesses.
-/
theorem exists_eventually_regular_parameterChart_of_strictAnti
    {σ : Type*} [Fintype σ]
    (x : ℕ → (σ → ℝ))
    (parameter : σ)
    (hanti :
      StrictAnti (fun n => x n parameter)) :
    ∃ (g : MvPolynomial σ ℝ)
        (hg : g ∉ sequenceGermIdeal x),
      (∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        MvPolynomial.eval (x n) g ≠ 0) ∧
      letI : Algebra (Polynomial ℝ)
          (MvPolynomial σ ℝ ⧸ sequenceGermIdeal x) :=
        parameterPolynomialAlgebra
          (sequenceGermIdeal x) parameter
      letI : Algebra (Polynomial ℝ) GermField :=
        parameterGermAlgebra x parameter
      let φ :
          Localization.Away
              (Ideal.Quotient.mk
                (sequenceGermIdeal x) g) →ₐ[Polynomial ℝ]
            GermField :=
        localizedGermParameterAlgHom
          x (sequenceGermIdeal x) parameter g hg
          (mem_sequenceGermIdeal_iff x)
      ∃ (numberOfVariables numberOfRelations : ℕ)
          (P :
            Algebra.SubmersivePresentation
              (Polynomial ℝ)
              (Localization.Away
                (Ideal.Quotient.mk
                  (sequenceGermIdeal x) g))
              (Fin numberOfVariables)
              (Fin numberOfRelations))
          (a : ℕ → (Fin numberOfVariables → ℝ)),
        (∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          (∀ j : Fin numberOfRelations,
            MvPolynomial.eval₂
                (Polynomial.evalRingHom
                  (x n parameter))
                (a n) (P.relation j) =
              0) ∧
            (evaluatedJacobiMatrix
              P.toPreSubmersivePresentation
              (x n parameter) (a n)).det ≠
              0) ∧
        (∀ s :
            Localization.Away
              (Ideal.Quotient.mk
                (sequenceGermIdeal x) g),
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval₂
                (Polynomial.evalRingHom
                  (x n parameter))
                (a n) (P.σ s) =
              germRepresentative (φ s) n) := by
  let J := sequenceGermIdeal x
  letI : J.IsPrime :=
    sequenceGermIdeal_isPrime x
  have hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval
              (MvPolynomial.X parameter) p ∈ J ↔
          p = 0 := by
    intro p
    exact
      aeval_X_mem_sequenceGermIdeal_iff_of_strictAnti
        x parameter hanti p
  have hJmem :
      ∀ Q : MvPolynomial σ ℝ,
        Q ∈ J ↔
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (x n) Q = 0 := by
    intro Q
    exact mem_sequenceGermIdeal_iff x Q
  obtain ⟨g, hg, hgeventually, hstandard⟩ :=
    exists_eventually_parameter_standardSmooth_basicOpen
      x J parameter hparameter hJmem
  refine ⟨g, hg, hgeventually, ?_⟩
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial σ ℝ ⧸ J) :=
    parameterPolynomialAlgebra J parameter
  letI : Algebra (Polynomial ℝ) GermField :=
    parameterGermAlgebra x parameter
  let S :=
    Localization.Away (Ideal.Quotient.mk J g)
  let φ : S →ₐ[Polynomial ℝ] GermField :=
    localizedGermParameterAlgHom
      x J parameter g hg hJmem
  have hstandard' :
      Algebra.IsStandardSmooth (Polynomial ℝ) S :=
    hstandard
  obtain ⟨ι, κ, hκ, hι, ⟨P⟩⟩ :=
    hstandard'.out
  letI : Finite κ := hκ
  letI : Finite ι := hι
  letI : Fintype κ := Fintype.ofFinite κ
  letI : Fintype ι := Fintype.ofFinite ι
  let Pfin :
      Algebra.SubmersivePresentation
        (Polynomial ℝ) S
        (Fin (Fintype.card ι))
        (Fin (Fintype.card κ)) :=
    P.reindex
      (Fintype.equivFin ι).symm
      (Fintype.equivFin κ).symm
  have hbase :
      ∀ p : Polynomial ℝ,
        algebraMap (Polynomial ℝ) GermField p =
          ((fun n => p.eval (x n parameter)) :
            GermField) :=
    parameterGermAlgebra_algebraMap_apply
      x parameter
  obtain ⟨a, hregular, hsection⟩ :=
    exists_eventually_regular_evaluatedPresentationSequence
      φ Pfin (fun n => x n parameter) hbase
  exact
    ⟨Fintype.card ι, Fintype.card κ,
      Pfin, a, hregular, hsection⟩

end CurveSelection.RelativeChartSequence
end Math
