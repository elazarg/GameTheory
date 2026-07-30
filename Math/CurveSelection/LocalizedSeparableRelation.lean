import Math.CurveSelection.AlgebraicRelation
import Math.CurveSelection.GermAlgebraicRelation
import Math.CurveSelection.RelativeLexAlgebraicity

set_option autoImplicit false

noncomputable section

open Filter

namespace Math
namespace CurveSelection.LocalizedSeparableRelation

open CurveSelection.AlgebraicRelation
open CurveSelection.GermAlgebraicRelation
open CurveSelection.GermChart
open CurveSelection.GermComponentScratch
open CurveSelection.RelativeLexAlgebraicity
open CurveSelection.RelativePresentation
open CurveSelection.RelativePresentationGerm

/--
The generic-point map from a localized prime germ is injective.  Exact
ultrafilter detection makes the quotient map injective, and localization
does not introduce a new kernel because its defining lift agrees with that
quotient map on the base algebra.
-/
theorem localizedGermParameterAlgHom_injective
    {σ : Type*}
    (source : ℕ → (σ → ℝ))
    (J : Ideal (MvPolynomial σ ℝ))
    (parameter : σ)
    (g : MvPolynomial σ ℝ)
    (hg : g ∉ J)
    (hJmem :
      ∀ Q : MvPolynomial σ ℝ,
        Q ∈ J ↔
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (source n) Q = 0) :
    letI : Algebra (Polynomial ℝ)
        (MvPolynomial σ ℝ ⧸ J) :=
      CurveSelection.FunctionField.parameterPolynomialAlgebra
        J parameter
    letI : Algebra (Polynomial ℝ) GermField :=
      parameterGermAlgebra source parameter
    Function.Injective
      (localizedGermParameterAlgHom
        source J parameter g hg hJmem) := by
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial σ ℝ ⧸ J) :=
    CurveSelection.FunctionField.parameterPolynomialAlgebra
      J parameter
  letI : Algebra (Polynomial ℝ) GermField :=
    parameterGermAlgebra source parameter
  rw [localizedGermParameterAlgHom]
  apply (IsLocalization.lift_injective_iff _).2
  intro a b
  constructor
  · intro hab
    have h :=
      congrArg
        (IsLocalization.lift
          (M :=
            Submonoid.powers
              (Ideal.Quotient.mk J g))
          (S :=
            Localization.Away
              (Ideal.Quotient.mk J g))
          (g :=
            (quotientGermParameterAlgHom
              source J parameter hJmem).toRingHom)
          (fun s => by
            obtain ⟨n, hn⟩ := s.property
            rw [← hn, map_pow]
            apply IsUnit.pow
            rw [isUnit_iff_ne_zero]
            intro hzero
            apply Ideal.Quotient.eq_zero_iff_mem.not.mpr hg
            apply quotientGermAlgHom_injective
              source J hJmem
            simpa [quotientGermParameterAlgHom]
              using hzero))
        hab
    simpa only [IsLocalization.lift_eq] using h
  · intro hab
    have hab' :
        quotientGermAlgHom source J hJmem a =
          quotientGermAlgHom source J hJmem b := by
      simpa [quotientGermParameterAlgHom] using hab
    have := quotientGermAlgHom_injective
      source J hJmem hab'
    subst b
    rfl

/--
Algebraicity over `ℝ(t)` descends through an injective localized
coordinate-algebra map to an exact polynomial relation in that algebra.
The separable derivative remains nonzero eventually along any chosen real
representative of the same germ.

The `ℝ[t]`-algebra structure on the germ field is deliberately fixed here
to evaluation at the distinguished parameter sequence.
-/
theorem exists_exact_relation_eventually_derivative_ne_zero
    {σ S : Type*}
    [CommRing S] [Algebra (Polynomial ℝ) S]
    (source : ℕ → (σ → ℝ))
    (parameter : σ)
    (hinjective :
      Function.Injective
        (fun n => source n parameter)) :
    letI : Algebra (Polynomial ℝ) GermField :=
      parameterGermAlgebra source parameter
    ∀ (φ : S →ₐ[Polynomial ℝ] GermField),
      Function.Injective φ →
      ∀ (s : S) (value : ℕ → ℝ),
        ((value : ℕ → ℝ) : GermField) = φ s →
        (letI : Algebra
            (FractionRing (Polynomial ℝ)) GermField :=
          parameterFractionRingGermAlgebra
            source parameter hinjective
         IsAlgebraic
           (FractionRing (Polynomial ℝ)) (φ s)) →
        ∃ Q : Polynomial (Polynomial ℝ),
          Q ≠ 0 ∧
          Polynomial.aeval s Q = 0 ∧
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            bivEval Q.derivative
              (source n parameter) (value n) ≠
              0 := by
  letI : Algebra (Polynomial ℝ) GermField :=
    parameterGermAlgebra source parameter
  intro φ hφ s value hvalue halgebraic
  let K := FractionRing (Polynomial ℝ)
  letI : Algebra K GermField :=
    parameterFractionRingGermAlgebra
      source parameter hinjective
  obtain ⟨Q, hQne, hroot, hderiv⟩ :=
    exists_base_relation_derivative_ne_zero
      (R := Polynomial ℝ) (K := K)
      (L := GermField) (φ s) halgebraic
  have hbase :
      (algebraMap K GermField).comp
          (algebraMap (Polynomial ℝ) K) =
        algebraMap (Polynomial ℝ) GermField := by
    apply DFunLike.ext _ _
    intro p
    change
      parameterFractionRingGermHom
          source parameter hinjective
          (algebraMap (Polynomial ℝ) K p) =
        parameterGermEval source parameter p
    exact
      parameterFractionRingGermHom_algebraMap
        source parameter hinjective p
  have hrootDirect :
      Polynomial.aeval (φ s) Q = 0 := by
    rw [Polynomial.aeval_eq_aeval_map hbase]
    exact hroot
  have hrootS :
      Polynomial.aeval s Q = 0 := by
    apply hφ
    rw [map_zero, ← Polynomial.aeval_algHom_apply]
    exact hrootDirect
  have hvalueRepresentative :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        value n =
          germRepresentative (φ s) n := by
    apply Filter.Germ.coe_eq.mp
    exact
      hvalue.trans
        (coe_germRepresentative (φ s)).symm
  refine ⟨Q, hQne, hrootS, ?_⟩
  rw [Ultrafilter.eventually_not]
  intro heventuallyZero
  apply hderiv
  rw [← coe_bivEval_germRepresentative
    source parameter hinjective (φ s) Q.derivative]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards
    [heventuallyZero, hvalueRepresentative] with
      n hnzero hnvalue
  simpa [hnvalue] using hnzero

/--
Localized-chart specialization of
`exists_exact_relation_eventually_derivative_ne_zero`.

For an algebraic localized element, the returned separable relation is an
exact identity already in the localized algebra, and its value derivative
is eventually nonzero on the canonical real presentation objectives.
-/
theorem
    exists_localized_relation_eventually_presentationObjective_derivative_ne_zero
    {σ ι κ : Type*}
    (source : ℕ → (σ → ℝ))
    (parameter : σ)
    (hinjective :
      Function.Injective
        (fun n => source n parameter))
    (J : Ideal (MvPolynomial σ ℝ))
    (g : MvPolynomial σ ℝ)
    (hg : g ∉ J)
    (hJmem :
      ∀ Q : MvPolynomial σ ℝ,
        Q ∈ J ↔
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (source n) Q = 0) :
    letI : Algebra (Polynomial ℝ)
        (MvPolynomial σ ℝ ⧸ J) :=
      CurveSelection.FunctionField.parameterPolynomialAlgebra
        J parameter
    letI : Algebra (Polynomial ℝ) GermField :=
      parameterGermAlgebra source parameter
    let φ :
        Localization.Away
            (Ideal.Quotient.mk J g) →ₐ[Polynomial ℝ]
          GermField :=
      localizedGermParameterAlgHom
        source J parameter g hg hJmem
    ∀ (P :
        Algebra.Presentation
          (Polynomial ℝ)
          (Localization.Away
            (Ideal.Quotient.mk J g))
          ι κ)
      (s :
        Localization.Away
          (Ideal.Quotient.mk J g)),
      (let K := FractionRing (Polynomial ℝ)
       letI : Algebra K GermField :=
         parameterFractionRingGermAlgebra
           source parameter hinjective
       IsAlgebraic K (φ s)) →
      ∃ Q : Polynomial (Polynomial ℝ),
        Q ≠ 0 ∧
        Polynomial.aeval s Q = 0 ∧
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          bivEval Q.derivative
              (source n parameter)
              (presentationObjective
                P (source n parameter) s
             (relativePresentationSequence
                   φ P n)) ≠
              0 := by
  simp only
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial σ ℝ ⧸ J) :=
    CurveSelection.FunctionField.parameterPolynomialAlgebra
      J parameter
  letI : Algebra (Polynomial ℝ) GermField :=
    parameterGermAlgebra source parameter
  intro P s halgebraic
  let φ :
      Localization.Away
          (Ideal.Quotient.mk J g) →ₐ[Polynomial ℝ]
        GermField :=
    localizedGermParameterAlgHom
      source J parameter g hg hJmem
  let value : ℕ → ℝ :=
    fun n =>
      presentationObjective
        P (source n parameter) s
        (relativePresentationSequence φ P n)
  have hbase :
      ∀ p : Polynomial ℝ,
        algebraMap (Polynomial ℝ) GermField p =
          ((fun n =>
            p.eval (source n parameter)) :
            GermField) :=
    parameterGermAlgebra_algebraMap_apply
      source parameter
  have hvalue :
      ((value : ℕ → ℝ) : GermField) =
        φ s := by
    rw [← coe_germRepresentative (φ s)]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards
      [eventually_eval₂_relativeSection
        φ P (fun n => source n parameter)
        hbase s] with n hn
    simpa [value, presentationObjective,
      eval_specializeParameterPolynomial] using hn
  exact
    exists_exact_relation_eventually_derivative_ne_zero
      source parameter hinjective
      φ
      (localizedGermParameterAlgHom_injective
        source J parameter g hg hJmem)
      s value hvalue halgebraic

end CurveSelection.LocalizedSeparableRelation
end Math
