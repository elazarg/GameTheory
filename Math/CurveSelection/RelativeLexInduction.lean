import Math.CurveSelection.RelativeLexAlgebraicity

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

noncomputable section

open Filter Set

namespace Math
namespace CurveSelection.RelativeLexInduction

open CurveSelection.GermChart
open CurveSelection.GermComponentScratch
open CurveSelection.LexIsolationScratch
open CurveSelection.RelativeLexAlgebraicity
open CurveSelection.RelativePresentation
open CurveSelection.RelativePresentationGerm

/--
Finite lexicographic algebraicity induction.

At a given stage, separable relations for the already algebraic preceding
objectives make their level constraints locally redundant.  The one-object
relative Lagrange theorem then proves algebraicity of the current objective.
Strong induction over the finite objective list closes the construction.
-/
theorem all_isAlgebraic_of_lex_and_separable_step
    {S ι κ σ : Type*} {d : ℕ}
    [CommRing S] [Algebra (Polynomial ℝ) S]
    [Algebra (Polynomial ℝ) GermField]
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (source : ℕ → (σ → ℝ))
    (parameter : σ)
    (hinjective :
      Function.Injective
        (fun n => source n parameter))
    (φ : S →ₐ[Polynomial ℝ] GermField)
    (P :
      Algebra.SubmersivePresentation
        (Polynomial ℝ) S ι κ)
    (hbase :
      ∀ p : Polynomial ℝ,
        algebraMap (Polynomial ℝ) GermField p =
          ((fun n =>
            p.eval (source n parameter)) :
            GermField))
    (objective : Fin d → S)
    (hlex :
      ∀ j : Fin d,
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          IsLocalExtrOn
            (presentationObjective
              P.toPreSubmersivePresentation.toPresentation
              (source n parameter) (objective j))
            (presentationFiber
                P.toPreSubmersivePresentation.toPresentation
                (source n parameter)
                (relativePresentationSequence φ
                  P.toPreSubmersivePresentation.toPresentation n) ∩
              previousObjectiveLevelSet
                (fun l z =>
                  presentationObjective
                    P.toPreSubmersivePresentation.toPresentation
                    (source n parameter)
                    (objective l) z)
                (relativePresentationSequence φ
                  P.toPreSubmersivePresentation.toPresentation n)
                j)
            (relativePresentationSequence φ
              P.toPreSubmersivePresentation.toPresentation n))
    (separableStep :
      let K := FractionRing (Polynomial ℝ)
      letI : Algebra K GermField :=
        parameterFractionRingGermAlgebra
          source parameter hinjective
      ∀ s : S,
        IsAlgebraic K (φ s) →
        ∃ Q : Polynomial (Polynomial ℝ),
          Q ≠ 0 ∧
          Polynomial.aeval s Q = 0 ∧
          (∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            bivEval Q.derivative
                (source n parameter)
                (presentationObjective
                  P.toPreSubmersivePresentation.toPresentation
                  (source n parameter) s
                  (relativePresentationSequence φ
                    P.toPreSubmersivePresentation.toPresentation n)) ≠
              0)) :
    let K := FractionRing (Polynomial ℝ)
    letI : Algebra K GermField :=
      parameterFractionRingGermAlgebra
        source parameter hinjective
    ∀ j : Fin d,
      IsAlgebraic K (φ (objective j)) := by
  dsimp only
  let K := FractionRing (Polynomial ℝ)
  letI : Algebra K GermField :=
    parameterFractionRingGermAlgebra
      source parameter hinjective
  let P₁ :=
    P.toPreSubmersivePresentation.toPresentation
  let a : ℕ → (ι → ℝ) :=
    relativePresentationSequence φ P₁
  have hrelations :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        ∀ i : κ,
          MvPolynomial.eval₂
            (Polynomial.evalRingHom
              (source n parameter))
            (a n) (P.relation i) = 0 := by
    exact
      Filter.eventually_all.mpr fun i =>
        eventually_eval₂_relativeRelation
          φ P₁ (fun n => source n parameter)
          hbase i
  have step :
      ∀ j : Fin d,
        (∀ l : Fin d, l < j →
          IsAlgebraic K (φ (objective l))) →
        IsAlgebraic K (φ (objective j)) := by
    intro j hprior
    have hpriorSubtype :
        ∀ l : {l : Fin d // l < j},
          IsAlgebraic K (φ (objective l.1)) :=
      fun l => hprior l.1 l.2
    choose relation hrelationNe hrelationS hderiv using
      fun l => separableStep
        (objective l.1) (hpriorSubtype l)
    have hderivAll :
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          ∀ l : {l : Fin d // l < j},
            bivEval (relation l).derivative
                (source n parameter)
                (presentationObjective
                  P₁ (source n parameter)
                  (objective l.1) (a n)) ≠ 0 :=
      Filter.eventually_all.mpr hderiv
    have hlocal :
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          IsLocalExtrOn
            (presentationObjective
              P₁ (source n parameter) (objective j))
            (presentationFiber
              P₁ (source n parameter) (a n))
            (a n) := by
      filter_upwards
        [hrelations, hderivAll, hlex j] with
          n hnrelations hnderiv hnlex
      let stageRelation :
          Fin d → Polynomial (Polynomial ℝ) :=
        fun l =>
          if hl : l < j then
            relation ⟨l, hl⟩
          else 0
      apply
        isLocalExtrOn_base_of_separablePreviousRelations
          stageRelation
          (fun _ : ι → ℝ => source n parameter)
          (fun l z =>
            presentationObjective
              P₁ (source n parameter)
              (objective l) z)
          (presentationFiber
            P₁ (source n parameter) (a n))
          (a n) j
      · intro l
        exact
          (MvPolynomial.continuous_eval
            (specializeParameterPolynomial
              (source n parameter)
              (P.σ (objective l)))).continuousAt
      · intro z hz
        rfl
      · intro l z hz
        by_cases hl : l < j
        · simpa [stageRelation, hl] using
            bivEval_presentationObjective_eq_zero_of_mem_fiber
              P₁ (source n parameter) (a n) z
              hnrelations hz (objective l)
              (relation ⟨l, hl⟩)
              (hrelationS ⟨l, hl⟩)
        · simp [stageRelation, hl, bivEval]
      · intro l
        simpa [stageRelation, l.2] using hnderiv l
      · exact hnlex
    let oneObjective : Fin 1 → S :=
      fun _ => objective j
    let emptyRelation :
        ∀ q : Fin 1,
          {l : Fin 1 // l < q} →
            Polynomial (Polynomial ℝ) :=
      fun _ _ => 0
    have hemptyS :
        ∀ (q : Fin 1)
            (l : {l : Fin 1 // l < q}),
          Polynomial.aeval
            (oneObjective l.1)
            (emptyRelation q l) = 0 := by
      intro q l
      have hq : q = 0 := Subsingleton.elim _ _
      subst q
      exact (Nat.not_lt_zero _ l.2).elim
    have hemptyDeriv :
        ∀ (q : Fin 1)
            (l : {l : Fin 1 // l < q}),
          ∀ᶠ n in
              (sequenceUltrafilter : Filter ℕ),
            bivEval (emptyRelation q l).derivative
                (source n parameter)
                (presentationObjective
                  P₁ (source n parameter)
                  (oneObjective l.1) (a n)) ≠
              0 := by
      intro q l
      have hq : q = 0 := Subsingleton.elim _ _
      subst q
      exact (Nat.not_lt_zero _ l.2).elim
    have honeLex :
        ∀ q : Fin 1,
          ∀ᶠ n in
              (sequenceUltrafilter : Filter ℕ),
            IsLocalExtrOn
              (presentationObjective
                P₁ (source n parameter)
                (oneObjective q))
              (presentationFiber
                  P₁ (source n parameter) (a n) ∩
                previousObjectiveLevelSet
                  (fun l z =>
                    presentationObjective
                      P₁ (source n parameter)
                      (oneObjective l) z)
                  (a n) q)
              (a n) := by
      intro q
      have hq : q = 0 := Subsingleton.elim _ _
      subst q
      filter_upwards [hlocal] with n hn
      simpa [oneObjective, previousObjectiveLevelSet] using hn
    obtain ⟨_Λ, _hcritical, halgebraic⟩ :=
      exists_eventually_relativeNormalMultipliers_and_isAlgebraic_of_lex
        source parameter hinjective φ P hbase
        oneObjective emptyRelation hemptyS
        hemptyDeriv honeLex
    simpa [oneObjective] using halgebraic 0
  have claim :
      ∀ (n : ℕ) (hn : n < d),
        IsAlgebraic K
          (φ (objective ⟨n, hn⟩)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn
        apply step ⟨n, hn⟩
        intro l hl
        have halg :=
          ih l.val hl l.isLt
        simpa using halg
  intro j
  simpa using claim j.val j.isLt

end CurveSelection.RelativeLexInduction
end Math
