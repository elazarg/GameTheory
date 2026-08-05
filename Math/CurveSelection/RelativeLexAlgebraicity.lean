import Math.CurveSelection.LexIsolation
import Math.CurveSelection.RelativePresentation
import Math.CurveSelection.RelativePresentationGerm
import Math.CurveSelection.RelativeSequenceCriticalAlgebraicity

/-!
Relative smooth-chart Lagrange multipliers for a finite lexicographic
objective list, and the resulting algebraicity in the parameter germ field.
-/

noncomputable section

open Filter Set

namespace Math
namespace CurveSelection.RelativeLexAlgebraicity

open CurveSelection.LexIsolationScratch
open CurveSelection.RelativePresentation
open CurveSelection.RelativePresentationGerm
open CurveSelection.RelativeSequenceCriticalAlgebraicity
open CurveSelection.GermChart
open CurveSelection.GermComponentScratch

/-- The fixed-parameter real fiber of a relative presentation. -/
def presentationFiber
    {S ι κ : Type*}
    [CommRing S] [Algebra (Polynomial ℝ) S]
    (P : Algebra.Presentation (Polynomial ℝ) S ι κ)
    (t : ℝ) (x : ι → ℝ) : Set (ι → ℝ) :=
  {z |
    ∀ i : κ,
      MvPolynomial.eval z
          (specializeParameterPolynomial t
            (P.relation i)) =
        MvPolynomial.eval x
          (specializeParameterPolynomial t
            (P.relation i))}

/-- Evaluation of the chosen presentation representative of an element. -/
def presentationObjective
    {S ι κ : Type*}
    [CommRing S] [Algebra (Polynomial ℝ) S]
    (P : Algebra.Presentation (Polynomial ℝ) S ι κ)
    (t : ℝ) (s : S) (z : ι → ℝ) : ℝ :=
  MvPolynomial.eval z
    (specializeParameterPolynomial t (P.σ s))

/--
A bivariate polynomial identity in the presented algebra holds at every
real point of every specialized presentation fiber.
-/
theorem bivEval_presentationObjective_eq_zero
    {S ι κ : Type*}
    [CommRing S] [Algebra (Polynomial ℝ) S]
    (P : Algebra.Presentation (Polynomial ℝ) S ι κ)
    (t : ℝ) (z : ι → ℝ)
    (hrelation :
      ∀ i : κ,
        MvPolynomial.eval₂
          (Polynomial.evalRingHom t) z
          (P.relation i) = 0)
    (s : S) (R : Polynomial (Polynomial ℝ))
    (hR : Polynomial.aeval s R = 0) :
    bivEval R t (presentationObjective P t s z) = 0 := by
  let ψ : S →+* ℝ :=
    presentationPointRingHom
      P (Polynomial.evalRingHom t) z hrelation
  have hψbase :
      ψ.comp (algebraMap (Polynomial ℝ) S) =
        Polynomial.evalRingHom t := by
    apply DFunLike.ext _ _
    intro p
    exact
      presentationPointRingHom_algebraMap
        P (Polynomial.evalRingHom t) z
        hrelation p
  have hψs :
      ψ s = presentationObjective P t s z := by
    rw [presentationPointRingHom_apply]
    exact
      (eval_specializeParameterPolynomial
        (P.σ s) t z).symm
  calc
    bivEval R t (presentationObjective P t s z) =
        Polynomial.eval₂
          (ψ.comp (algebraMap (Polynomial ℝ) S))
          (ψ s) R := by
            simp [bivEval, hψbase, hψs]
    _ = ψ (Polynomial.aeval s R) := by
          rw [Polynomial.aeval_def,
            Polynomial.hom_eval₂]
    _ = 0 := by rw [hR, map_zero]

/--
Version of `bivEval_presentationObjective_eq_zero` whose point is given as
membership in the fixed-level presentation fiber.
-/
theorem bivEval_presentationObjective_eq_zero_of_mem_fiber
    {S ι κ : Type*}
    [CommRing S] [Algebra (Polynomial ℝ) S]
    (P : Algebra.Presentation (Polynomial ℝ) S ι κ)
    (t : ℝ) (x z : ι → ℝ)
    (hx :
      ∀ i : κ,
        MvPolynomial.eval₂
          (Polynomial.evalRingHom t) x
          (P.relation i) = 0)
    (hz : z ∈ presentationFiber P t x)
    (s : S) (R : Polynomial (Polynomial ℝ))
    (hR : Polynomial.aeval s R = 0) :
    bivEval R t (presentationObjective P t s z) = 0 := by
  apply bivEval_presentationObjective_eq_zero
    P t z _ s R hR
  intro i
  rw [← eval_specializeParameterPolynomial]
  exact
    (hz i).trans
      (by
        rw [eval_specializeParameterPolynomial]
        exact hx i)

/--
Separable relations in the presented algebra make every preceding
lexicographic level condition locally redundant.  The conclusion is
eventual because relation exactness and derivative nonvanishing are only
needed along the selected sequence.
-/
theorem eventually_isLocalExtrOn_presentationFiber_of_lex
    {S ι κ : Type*} {d : ℕ}
    [CommRing S] [Algebra (Polynomial ℝ) S]
    [Finite ι]
    (P : Algebra.Presentation (Polynomial ℝ) S ι κ)
    (t : ℕ → ℝ) (a : ℕ → (ι → ℝ))
    (objective : Fin d → S)
    (relation :
      ∀ j : Fin d,
        {l : Fin d // l < j} →
          Polynomial (Polynomial ℝ))
    (hrelationS :
      ∀ (j : Fin d) (l : {l : Fin d // l < j}),
        Polynomial.aeval (objective l.1)
          (relation j l) = 0)
    (hrelations :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        ∀ i : κ,
          MvPolynomial.eval₂
            (Polynomial.evalRingHom (t n))
            (a n) (P.relation i) = 0)
    (hderiv :
      ∀ (j : Fin d) (l : {l : Fin d // l < j}),
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          bivEval (relation j l).derivative
              (t n)
              (presentationObjective
                P (t n) (objective l.1) (a n)) ≠
            0)
    (hlex :
      ∀ j : Fin d,
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          IsLocalExtrOn
            (presentationObjective
              P (t n) (objective j))
            (presentationFiber P (t n) (a n) ∩
              previousObjectiveLevelSet
                (fun l z =>
                  presentationObjective
                    P (t n) (objective l) z)
                (a n) j)
            (a n)) :
    ∀ j : Fin d,
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        IsLocalExtrOn
          (presentationObjective
            P (t n) (objective j))
          (presentationFiber P (t n) (a n))
          (a n) := by
  letI : Fintype ι := Fintype.ofFinite ι
  intro j
  have hderivAll :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        ∀ l : {l : Fin d // l < j},
          bivEval (relation j l).derivative
              (t n)
              (presentationObjective
                P (t n) (objective l.1) (a n)) ≠
            0 :=
    Filter.eventually_all.mpr (hderiv j)
  filter_upwards
    [hrelations, hderivAll, hlex j] with
      n hnrelations hnderiv hnlex
  let stageRelation :
      Fin d → Polynomial (Polynomial ℝ) :=
    fun l =>
      if hl : l < j then relation j ⟨l, hl⟩ else 0
  apply
    isLocalExtrOn_base_of_separablePreviousRelations
      stageRelation
      (fun _ : ι → ℝ => t n)
      (fun l z =>
        presentationObjective
          P (t n) (objective l) z)
      (presentationFiber P (t n) (a n))
      (a n) j
  · intro l
    exact
      (MvPolynomial.continuous_eval
        (specializeParameterPolynomial (t n)
          (P.σ (objective l)))).continuousAt
  · intro z hz
    rfl
  · intro l z hz
    by_cases hl : l < j
    · simpa [stageRelation, hl] using
        bivEval_presentationObjective_eq_zero_of_mem_fiber
          P (t n) (a n) z hnrelations hz
          (objective l) (relation j ⟨l, hl⟩)
          (hrelationS j ⟨l, hl⟩)
    · simp [stageRelation, hl, bivEval]
  · intro l
    simpa [stageRelation, l.2] using hnderiv l
  · exact hnlex

/-- All normalized critical equations for a finite objective list at one
specialized presentation point. -/
def RelativeNormalCriticalAt
    {S ι κ : Type*} {d : ℕ}
    [CommRing S] [Algebra (Polynomial ℝ) S]
    [Fintype κ]
    (P : Algebra.Presentation (Polynomial ℝ) S ι κ)
    (t : ℝ) (a : ι → ℝ)
    (objective : Fin d → S)
    (Λ : Fin d → κ → ℝ) : Prop :=
  ∀ (j : Fin d) (k : ι),
    MvPolynomial.eval₂
        (Polynomial.evalRingHom t) a
        (MvPolynomial.pderiv k
          (P.σ (objective j))) =
      ∑ i : κ,
        Λ j i *
          MvPolynomial.eval₂
            (Polynomial.evalRingHom t) a
            (MvPolynomial.pderiv k
              (P.relation i))

/--
Eventual regularity plus separable lexicographic isolation produces one
simultaneous sequence of normalized multipliers for all objectives.
-/
theorem exists_eventually_relativeNormalMultipliers_of_lex
    {S ι κ : Type*} {d : ℕ}
    [CommRing S] [Algebra (Polynomial ℝ) S]
    [Finite ι]
    [Fintype κ] [DecidableEq κ]
    (P :
      Algebra.PreSubmersivePresentation
        (Polynomial ℝ) S ι κ)
    (t : ℕ → ℝ) (a : ℕ → (ι → ℝ))
    (objective : Fin d → S)
    (relation :
      ∀ j : Fin d,
        {l : Fin d // l < j} →
          Polynomial (Polynomial ℝ))
    (hrelationS :
      ∀ (j : Fin d) (l : {l : Fin d // l < j}),
        Polynomial.aeval (objective l.1)
          (relation j l) = 0)
    (hrelations :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        ∀ i : κ,
          MvPolynomial.eval₂
            (Polynomial.evalRingHom (t n))
            (a n) (P.relation i) = 0)
    (hdet :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        (evaluatedJacobiMatrix P (t n) (a n)).det ≠ 0)
    (hderiv :
      ∀ (j : Fin d) (l : {l : Fin d // l < j}),
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          bivEval (relation j l).derivative
              (t n)
              (presentationObjective
                P.toPresentation (t n)
                (objective l.1) (a n)) ≠
            0)
    (hlex :
      ∀ j : Fin d,
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          IsLocalExtrOn
            (presentationObjective
              P.toPresentation (t n) (objective j))
            (presentationFiber
                P.toPresentation (t n) (a n) ∩
              previousObjectiveLevelSet
                (fun l z =>
                  presentationObjective
                    P.toPresentation (t n)
                    (objective l) z)
                (a n) j)
            (a n)) :
    ∃ Λ : ℕ → Fin d → κ → ℝ,
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        RelativeNormalCriticalAt
          P.toPresentation (t n) (a n)
          objective (Λ n) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hlocal :
      ∀ j : Fin d,
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          IsLocalExtrOn
            (presentationObjective
              P.toPresentation (t n) (objective j))
            (presentationFiber
              P.toPresentation (t n) (a n))
            (a n) :=
    eventually_isLocalExtrOn_presentationFiber_of_lex
      P.toPresentation t a objective
      relation hrelationS hrelations hderiv hlex
  have hlocalAll :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        ∀ j : Fin d,
          IsLocalExtrOn
            (presentationObjective
              P.toPresentation (t n) (objective j))
            (presentationFiber
              P.toPresentation (t n) (a n))
            (a n) :=
    Filter.eventually_all.mpr hlocal
  have hex :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        ∃ L : Fin d → κ → ℝ,
          RelativeNormalCriticalAt
            P.toPresentation (t n) (a n)
            objective L := by
    filter_upwards [hlocalAll, hdet] with n hnlocal hndet
    have hstage :
        ∀ j : Fin d,
          ∃ c : κ → ℝ,
            ∀ k : ι,
              MvPolynomial.eval₂
                  (Polynomial.evalRingHom (t n)) (a n)
                  (MvPolynomial.pderiv k
                    (P.σ (objective j))) =
                ∑ i : κ,
                  c i *
                    MvPolynomial.eval₂
                      (Polynomial.evalRingHom (t n))
                      (a n)
                      (MvPolynomial.pderiv k
                        (P.relation i)) := by
      intro j
      exact
        exists_multipliers_of_localExtrOn_presentationFiber
          P (t n) (a n) (P.σ (objective j))
          (by
            have hjlocal := hnlocal j
            unfold presentationObjective
              presentationFiber at hjlocal
            exact hjlocal)
          hndet
    choose L hL using hstage
    exact ⟨L, hL⟩
  have hall :
      ∀ n : ℕ,
        ∃ L : Fin d → κ → ℝ,
          (∃ L' : Fin d → κ → ℝ,
              RelativeNormalCriticalAt
                P.toPresentation (t n) (a n)
                objective L') →
            RelativeNormalCriticalAt
              P.toPresentation (t n) (a n)
              objective L := by
    intro n
    by_cases hn :
        ∃ L : Fin d → κ → ℝ,
          RelativeNormalCriticalAt
            P.toPresentation (t n) (a n)
            objective L
    · exact ⟨Classical.choose hn,
        fun _ => Classical.choose_spec hn⟩
    · exact ⟨0, fun h => (hn h).elim⟩
  choose Λ hΛ using hall
  refine ⟨Λ, ?_⟩
  filter_upwards [hex] with n hn
  exact hΛ n hn

/--
Canonical relative-presentation capstone for a finite lexicographic
objective list.

The selected presentation sequence is supplied by the germ chart itself.
Submersivity gives eventual real Jacobian regularity, separable relations
remove all preceding lexicographic level conditions, and normalized
Lagrange multipliers make every objective germ algebraic over `ℝ(t)`.
-/
theorem exists_eventually_relativeNormalMultipliers_and_isAlgebraic_of_lex
    {S ι κ σ : Type*} {d : ℕ}
    [CommRing S] [Algebra (Polynomial ℝ) S]
    [Algebra (Polynomial ℝ) GermField]
    [Finite ι]
    [Fintype κ]
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
    (relation :
      ∀ j : Fin d,
        {l : Fin d // l < j} →
          Polynomial (Polynomial ℝ))
    (hrelationS :
      ∀ (j : Fin d) (l : {l : Fin d // l < j}),
        Polynomial.aeval (objective l.1)
          (relation j l) = 0)
    (hderiv :
      ∀ (j : Fin d) (l : {l : Fin d // l < j}),
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          bivEval (relation j l).derivative
              (source n parameter)
              (presentationObjective
                P.toPreSubmersivePresentation.toPresentation
                (source n parameter)
                (objective l.1)
                (relativePresentationSequence φ
                  P.toPreSubmersivePresentation.toPresentation n)) ≠
            0)
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
              P.toPreSubmersivePresentation.toPresentation n)) :
    let K := FractionRing (Polynomial ℝ)
    letI : Algebra K GermField :=
      parameterFractionRingGermAlgebra
        source parameter hinjective
    ∃ Λ : ℕ → Fin d → κ → ℝ,
      (∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        RelativeNormalCriticalAt
          P.toPreSubmersivePresentation.toPresentation
          (source n parameter)
          (relativePresentationSequence φ
            P.toPreSubmersivePresentation.toPresentation n)
          objective (Λ n)) ∧
      ∀ j : Fin d,
        IsAlgebraic K (φ (objective j)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  dsimp only
  let K := FractionRing (Polynomial ℝ)
  letI : Algebra K GermField :=
    parameterFractionRingGermAlgebra
      source parameter hinjective
  let t : ℕ → ℝ := fun n => source n parameter
  let P₀ :=
    P.toPreSubmersivePresentation
  let P₁ :=
    P.toPreSubmersivePresentation.toPresentation
  let a : ℕ → (ι → ℝ) :=
    relativePresentationSequence φ P₁
  have hrelations :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        ∀ i : κ,
          MvPolynomial.eval₂
            (Polynomial.evalRingHom (t n))
            (a n) (P.relation i) = 0 := by
    exact
      Filter.eventually_all.mpr fun i =>
        eventually_eval₂_relativeRelation
          φ P₁ t hbase i
  have hdet :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        (evaluatedJacobiMatrix
          P₀ (t n) (a n)).det ≠ 0 := by
    exact
      eventually_det_evaluatedJacobiMatrix_ne_zero
        φ P t hbase
  obtain ⟨Λ, hcritical⟩ :=
    exists_eventually_relativeNormalMultipliers_of_lex
      P₀ t a objective relation hrelationS
      hrelations hdet hderiv hlex
  refine ⟨Λ, hcritical, ?_⟩
  intro j
  have hcriticalj :
      ∀ k : ι,
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          MvPolynomial.eval₂
              (Polynomial.evalRingHom (t n))
              (a n)
              (MvPolynomial.pderiv k
                (P.σ (objective j))) =
            ∑ i : κ,
              Λ n j i *
                MvPolynomial.eval₂
                  (Polynomial.evalRingHom (t n))
                  (a n)
                  (MvPolynomial.pderiv k
                    (P.relation i)) := by
    intro k
    filter_upwards [hcritical] with n hn
    exact hn j k
  have halgebraic :
      IsAlgebraic K
        (((fun n =>
          MvPolynomial.eval₂
            (Polynomial.evalRingHom (t n))
            (a n) (P.σ (objective j))) :
          ℕ → ℝ) : GermField) := by
    exact
      isAlgebraic_objectiveGerm_of_eventually_relativeNormalCriticality
        source parameter hinjective a
        (fun i => P.relation i)
        (P.σ (objective j))
        (fun n i => Λ n j i)
        (fun i => by
          filter_upwards [hrelations] with n hn
          exact hn i)
        hcriticalj
  have hsection :
      (((fun n =>
          MvPolynomial.eval₂
            (Polynomial.evalRingHom (t n))
            (a n) (P.σ (objective j))) :
          ℕ → ℝ) : GermField) =
        φ (objective j) := by
    simpa [a, P₁, t, P.aeval_val_σ] using
      coe_eval₂_relativePresentationSequence
        φ P₁ t hbase (P.σ (objective j))
  rw [hsection] at halgebraic
  exact halgebraic

end CurveSelection.RelativeLexAlgebraicity
end Math
