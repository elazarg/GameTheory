import Math.GateGAmbientGermRelation
import Math.GateGLocalizedSeparableRelation
import Math.GateGOptionRelativeGerm
import Math.GateGRelativeChartSequence
import Math.GateGRelativeLexInduction
import Math.GateGRelativeLexPullback
import Math.GateGSourceFinalization
import Math.GateGSourceLexExtrema
import Math.GateGSourceSequence

set_option autoImplicit false
set_option linter.unusedFintypeInType false

noncomputable section

open Filter Set Topology
open Math.PolynomialSignCell

namespace Math
namespace GateGSelectionCapstone

open GateGAmbientGermRelation
open GateGAlgebraicReductionScratch
open GateGFunctionField
open GateGGermChart
open GateGGermComponentScratch
open GateGLocalizedSeparableRelation
open GateGOptionRelativeCoordinates
open GateGOptionRelativeGerm
open GateGRelativeChartSequence
open GateGRelativeLexInduction
open GateGRelativeLexPullback
open GateGRelativePresentation
open GateGRelativePresentationGerm
open GateGSourceFinalization
open GateGSourceCell
open GateGSourceLexExtrema
open GateGSourceSequence
open GateGSquareLiftScratch

/--
Unconditional mathematical curve selection for a complete real polynomial
sign cell, through a boundary point approached from one positive
coordinate.  This is the generic geometric capstone consumed by Gate G.
-/
theorem hasPositiveCoordinateAnalyticArcAt_signCell
    {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (coordinate : σ)
    (x₀ : Assignment σ)
    (hcoordinate₀ : x₀ coordinate = 0)
    (hclosure :
      x₀ ∈
        closure
          (signCell P τ ∩
            {x | 0 < x coordinate})) :
    HasPositiveCoordinateAnalyticArcAt
      (signCell P τ)
      (ContinuousLinearMap.proj coordinate) x₀ := by
  classical
  let Ppos :=
    withPositiveCoordinatePolynomial P coordinate
  let τpos :=
    withPositiveCoordinateSignPattern τ
  obtain
      ⟨approach, lift, _selected, source,
        _happroachCell, _hradiusAnti, _happroachLim,
        hliftClosure, _hselectedRadius, _hliftEq,
        hliftStrict, _hliftCell, _hliftLim,
        hsourceEq, hsourceCell, hsourcePos,
        hsourceAnti, hsourceLim, hscoreMax,
        hcoordinateLex⟩ :=
    exists_lexSelected_source_sequence
      P τ coordinate x₀ hcoordinate₀ hclosure
  obtain ⟨g, hg, _hgeventually, hchart⟩ :=
    exists_eventually_regular_parameterChart_of_strictAnti
      source none hsourceAnti
  let J := sequenceGermIdeal source
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial
          (Option (σ ⊕ Option ι)) ℝ ⧸ J) :=
    parameterPolynomialAlgebra J none
  letI : Algebra (Polynomial ℝ) GermField :=
    parameterGermAlgebra source none
  let S :=
    Localization.Away
      (Ideal.Quotient.mk J g)
  let φ : S →ₐ[Polynomial ℝ] GermField :=
    localizedGermParameterAlgHom
      source J none g hg
      (mem_sequenceGermIdeal_iff source)
  obtain
      ⟨numberOfVariables, numberOfRelations,
        chart, _chartSequence, _hchartRegular,
        _hchartSection⟩ :=
    hchart
  let chartPresentation :=
    chart.toPreSubmersivePresentation.toPresentation
  let canonicalChartSequence :
      ℕ → (Fin numberOfVariables → ℝ) :=
    relativePresentationSequence φ chartPresentation
  let relativeCoordinate :
      (σ ⊕ Option ι) → S :=
    optionLocalizedCoordinate J g
  let relativeEquation :
      ParameterizedSquareLiftEquation τpos →
        MvPolynomial
          (σ ⊕ Option ι) (Polynomial ℝ) :=
    fun e =>
      MvPolynomial.optionEquivRight ℝ
        (σ ⊕ Option ι)
        (parameterizedSquareLiftPolynomial
          Ppos τpos x₀ e)
  let relativeObjective :
      Fin (Fintype.card (σ ⊕ Option ι) + 1) →
        MvPolynomial
          (σ ⊕ Option ι) (Polynomial ℝ) :=
    fun j =>
      MvPolynomial.optionEquivRight ℝ
        (σ ⊕ Option ι)
        (triangularLexObjectivePolynomial τpos j)
  let objectiveValue :
      Fin (Fintype.card (σ ⊕ Option ι) + 1) → S :=
    fun j =>
      MvPolynomial.eval₂
        (algebraMap (Polynomial ℝ) S)
        relativeCoordinate
        (relativeObjective j)
  have hpermanentMem :
      ∀ e : ParameterizedSquareLiftEquation τpos,
        parameterizedSquareLiftPolynomial
            Ppos τpos x₀ e ∈ J := by
    intro e
    apply (mem_sequenceGermIdeal_iff source _).mpr
    exact Eventually.of_forall fun n => by
      have hzero :=
        (eval_eq_zero_iff_of_mem_signCell
          (hsourceCell n) (Sum.inl e)).2 rfl
      simpa [Ppos, τpos, sourcePolynomial] using hzero
  have hrelativeEquation :
      ∀ e : ParameterizedSquareLiftEquation τpos,
        MvPolynomial.eval₂
            (algebraMap (Polynomial ℝ) S)
            relativeCoordinate
            (relativeEquation e) = 0 := by
    intro e
    exact
      eval₂_optionEquivRight_optionLocalizedCoordinate_eq_zero
        J g (hpermanentMem e)
  have hrelativeObjective :
      ∀ j,
        MvPolynomial.eval₂
            (algebraMap (Polynomial ℝ) S)
            relativeCoordinate
            (relativeObjective j) =
          objectiveValue j := by
    intro j
    rfl
  have hbase :
      ∀ p : Polynomial ℝ,
        algebraMap (Polynomial ℝ) GermField p =
          ((fun n => p.eval (source n none)) :
            GermField) :=
    parameterGermAlgebra_algebraMap_apply
      source none
  have hcanonicalRelations :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        ∀ k : Fin numberOfRelations,
          MvPolynomial.eval₂
              (Polynomial.evalRingHom (source n none))
              (canonicalChartSequence n)
              (chart.relation k) = 0 := by
    exact
      Filter.eventually_all.mpr fun k =>
        eventually_eval₂_relativeRelation
          φ chartPresentation
          (fun n => source n none)
          hbase k
  have hcanonicalSection :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        presentationSectionMap chartPresentation
            (source n none) relativeCoordinate
            (canonicalChartSequence n) =
          fun v => source n (some v) := by
    apply
      eventually_optionPresentationSectionMap_eq_sequenceGerm
        source g hg chartPresentation
        canonicalChartSequence
    intro s
    exact
      eventually_eval₂_relativeSection
        φ chartPresentation
        (fun n => source n none)
        hbase s
  have hsourceLex :
      ∀ n
          (j :
            Fin
              (Fintype.card
                (σ ⊕ Option ι) + 1)),
        IsLocalExtrOn
          (fun w : Assignment (σ ⊕ Option ι) =>
            MvPolynomial.eval₂
              (Polynomial.evalRingHom (source n none))
              w (relativeObjective j))
          ({w |
              ∀ e : ParameterizedSquareLiftEquation τpos,
                MvPolynomial.eval₂
                  (Polynomial.evalRingHom (source n none))
                  w (relativeEquation e) = 0} ∩
            GateGLexIsolationScratch.previousObjectiveLevelSet
              (fun l w =>
                MvPolynomial.eval₂
                  (Polynomial.evalRingHom (source n none))
                  w (relativeObjective l))
              (fun v => source n (some v)) j)
          (fun v => source n (some v)) := by
    intro n j
    have hnone :
        source n none =
          squaredRadius x₀ (approach n) := by
      exact congrFun (hsourceEq n) none
    have hsome :
        (fun v => source n (some v)) =
          lift n := by
      funext v
      exact congrFun (hsourceEq n) (some v)
    have heval
        (Q : MvPolynomial
          (Option (σ ⊕ Option ι)) ℝ)
        (r : ℝ)
        (w : Assignment (σ ⊕ Option ι)) :
        MvPolynomial.eval₂
            (Polynomial.evalRingHom r) w
            (MvPolynomial.optionEquivRight ℝ
              (σ ⊕ Option ι) Q) =
          MvPolynomial.eval
            (parameterizedLiftAssignment r w) Q := by
      rw [GateGOptionRelativeGerm.eval₂_optionEquivRight]
      have helim :
          (fun o => o.elim r w) =
            parameterizedLiftAssignment r w := by
        funext o
        cases o <;> rfl
      rw [helim]
    have hlocal :=
      isLocalExtrOn_triangularLexObjectives
        Ppos τpos x₀
        (squaredRadius x₀ (approach n))
        (lift n)
        (hliftClosure n) (hliftStrict n)
        (hscoreMax n)
        (hcoordinateLex n)
        j
    simpa only [relativeObjective, relativeEquation,
      heval, hnone, hsome] using hlocal
  have hchartLex :
      ∀ j :
          Fin
            (Fintype.card
              (σ ⊕ Option ι) + 1),
        ∀ᶠ n in
            (sequenceUltrafilter : Filter ℕ),
          IsLocalExtrOn
            (GateGRelativeLexAlgebraicity.presentationObjective
              chartPresentation
              (source n none)
              (objectiveValue j))
            (GateGRelativeLexAlgebraicity.presentationFiber
                chartPresentation
                (source n none)
                (canonicalChartSequence n) ∩
              GateGLexIsolationScratch.previousObjectiveLevelSet
                (fun l z =>
                  GateGRelativeLexAlgebraicity.presentationObjective
                    chartPresentation
                    (source n none)
                    (objectiveValue l) z)
                (canonicalChartSequence n) j)
            (canonicalChartSequence n) := by
    intro j
    filter_upwards
      [hcanonicalRelations, hcanonicalSection] with
        n hnrelations hnsection
    have hpull :=
      isLocalExtrOn_presentationFiber_previous_relative
        chartPresentation
        (source n none) relativeCoordinate
        relativeEquation hrelativeEquation
        relativeObjective objectiveValue
        hrelativeObjective
        (canonicalChartSequence n)
        (fun v => source n (some v))
        hnrelations hnsection j
        (hsourceLex n j)
    exact hpull
  have hseparable :
      let K := FractionRing (Polynomial ℝ)
      letI : Algebra K GermField :=
        parameterFractionRingGermAlgebra
          source none hsourceAnti.injective
      ∀ s : S,
        IsAlgebraic K (φ s) →
        ∃ Q : Polynomial (Polynomial ℝ),
          Q ≠ 0 ∧
          Polynomial.aeval s Q = 0 ∧
          (∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            bivEval Q.derivative
                (source n none)
                (GateGRelativeLexAlgebraicity.presentationObjective
                  chartPresentation
                  (source n none) s
                  (canonicalChartSequence n)) ≠ 0) := by
    dsimp only
    intro s hs
    exact
      exists_localized_relation_eventually_presentationObjective_derivative_ne_zero
        source none hsourceAnti.injective
        J g hg (mem_sequenceGermIdeal_iff source)
        chartPresentation s hs
  have halgebraicObjectives :
      let K := FractionRing (Polynomial ℝ)
      letI : Algebra K GermField :=
        parameterFractionRingGermAlgebra
          source none hsourceAnti.injective
      ∀ j :
          Fin
            (Fintype.card
              (σ ⊕ Option ι) + 1),
        IsAlgebraic K (φ (objectiveValue j)) := by
    exact
      all_isAlgebraic_of_lex_and_separable_step
        source none hsourceAnti.injective
        φ chart hbase objectiveValue hchartLex
        hseparable
  let K := FractionRing (Polynomial ℝ)
  letI : Algebra K GermField :=
    parameterFractionRingGermAlgebra
      source none hsourceAnti.injective
  have hcoordinateAlgebraic :
      ∀ v : σ ⊕ Option ι,
        IsAlgebraic K
          (((fun n => source n (some v)) :
            ℕ → ℝ) : GermField) := by
    intro v
    let k :
        Fin (Fintype.card (σ ⊕ Option ι)) :=
      Fintype.equivFin (σ ⊕ Option ι) v
    have h :=
      halgebraicObjectives k.succ
    have hvalue :=
      localizedGermParameterAlgHom_eval₂_optionEquivRight
        source J g hg
        (mem_sequenceGermIdeal_iff source)
        (triangularLexObjectivePolynomial τpos k.succ)
    change
      φ (objectiveValue k.succ) =
        ((fun n =>
          MvPolynomial.eval (source n)
            (triangularLexObjectivePolynomial
              τpos k.succ)) : GermField)
        at hvalue
    rw [hvalue] at h
    simpa [triangularLexObjectivePolynomial, k] using h
  choose relation hrelationNe hrelationRoot hrelationDeriv using
    fun v =>
      exists_bivariateRelation_eventually
        source none hsourceAnti.injective
        (fun n => source n (some v))
        (hcoordinateAlgebraic v)
  exact
    positiveCoordinateArc_of_eventual_source_relations_some
      P τ coordinate x₀ hcoordinate₀
      source hsourceCell hsourcePos hsourceLim
      relation hrelationNe hrelationRoot

end GateGSelectionCapstone
end Math
