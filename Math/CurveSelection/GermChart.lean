/- Generic-point evaluation of a prime sequence germ on an affine chart. -/
import Math.CurveSelection.FunctionField
import Math.CurveSelection.GermComponent
import Math.CurveSelection.RelativeSmoothGerm

set_option autoImplicit false

noncomputable section

open Filter

namespace Math
namespace CurveSelection.GermChart

open CurveSelection.FunctionField
open CurveSelection.GermComponentScratch

/-- The ultraproduct of the real field along the fixed free ultrafilter. -/
abbrev GermField :=
  Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ

instance germRealAlgebra : Algebra ℝ GermField :=
  germConstRingHom.toAlgebra

/-- The generic point of a prime sequence germ, valued in the ultrafilter
germ field. -/
def quotientGermAlgHom
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (J : Ideal (MvPolynomial σ ℝ))
    (hJmem :
      ∀ Q : MvPolynomial σ ℝ,
        Q ∈ J ↔
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (x n) Q = 0) :
    (MvPolynomial σ ℝ ⧸ J) →ₐ[ℝ] GermField :=
  Ideal.Quotient.liftₐ J (sequenceGermEval x) fun Q hQ => by
    rw [sequenceGermEval_apply]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [(hJmem Q).mp hQ] with n hn
    exact hn

theorem quotientGermAlgHom_injective
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (J : Ideal (MvPolynomial σ ℝ))
    (hJmem :
      ∀ Q : MvPolynomial σ ℝ,
        Q ∈ J ↔
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (x n) Q = 0) :
    Function.Injective (quotientGermAlgHom x J hJmem) := by
  intro a b hab
  rw [← sub_eq_zero]
  obtain ⟨Q, hQ⟩ :=
    Ideal.Quotient.mk_surjective (a - b)
  rw [← hQ]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (hJmem Q).mpr
  have hgerm :
      sequenceGermEval x Q = 0 := by
    change quotientGermAlgHom x J hJmem
      (Ideal.Quotient.mk J Q) = 0
    rw [hQ, map_sub, hab, sub_self]
  rw [sequenceGermEval_apply] at hgerm
  exact Filter.Germ.coe_eq.mp hgerm

/-- The generic-point embedding extends across every basic open that does
not vanish on the prime germ. -/
def localizedGermAlgHom
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (J : Ideal (MvPolynomial σ ℝ))
    (g : MvPolynomial σ ℝ)
    (hg : g ∉ J)
    (hJmem :
      ∀ Q : MvPolynomial σ ℝ,
        Q ∈ J ↔
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (x n) Q = 0) :
    Localization.Away (Ideal.Quotient.mk J g) →ₐ[ℝ]
      GermField := by
  let f := quotientGermAlgHom x J hJmem
  refine IsLocalization.liftAlgHom
    (M := Submonoid.powers (Ideal.Quotient.mk J g))
    (S := Localization.Away (Ideal.Quotient.mk J g))
    (f := f) ?_
  intro s
  obtain ⟨n, hn⟩ := s.property
  rw [← hn, map_pow]
  apply IsUnit.pow
  rw [isUnit_iff_ne_zero]
  intro hzero
  apply Ideal.Quotient.eq_zero_iff_mem.not.mpr hg
  apply quotientGermAlgHom_injective x J hJmem
  simpa [f] using hzero

/-- The germ field as an algebra over `ℝ[t]`, with `t` evaluated at the
distinguished parameter sequence. -/
@[reducible] def parameterGermAlgebra
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (parameter : σ) :
    Algebra (Polynomial ℝ) GermField :=
  (parameterGermEval x parameter).toAlgebra

/-- Embed the rational function field `ℝ(t)` into the ultrafilter germ
field using a sequence with pairwise distinct parameter values. -/
def parameterFractionRingGermHom
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (parameter : σ)
    (hinjective :
      Function.Injective (fun n => x n parameter)) :
    FractionRing (Polynomial ℝ) →+* GermField :=
  IsFractionRing.lift
    (parameterGermEval_injective_of_injective
      x parameter hinjective)

theorem parameterFractionRingGermHom_injective
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (parameter : σ)
    (hinjective :
      Function.Injective (fun n => x n parameter)) :
    Function.Injective
      (parameterFractionRingGermHom
        x parameter hinjective) :=
  (parameterFractionRingGermHom
    x parameter hinjective).injective

/-- The germ field as an algebra over `ℝ(t)`. -/
@[reducible] def parameterFractionRingGermAlgebra
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (parameter : σ)
    (hinjective :
      Function.Injective (fun n => x n parameter)) :
    Algebra (FractionRing (Polynomial ℝ)) GermField :=
  (parameterFractionRingGermHom
    x parameter hinjective).toAlgebra

theorem parameterFractionRingGermHom_algebraMap
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (parameter : σ)
    (hinjective :
      Function.Injective (fun n => x n parameter))
    (p : Polynomial ℝ) :
    parameterFractionRingGermHom x parameter hinjective
        (algebraMap (Polynomial ℝ)
          (FractionRing (Polynomial ℝ)) p) =
      parameterGermEval x parameter p := by
  rw [parameterFractionRingGermHom,
    IsFractionRing.lift_algebraMap]
  rfl

/-- The generic-point embedding respects the `ℝ[t]`-algebra structures
defined by the distinguished parameter. -/
def quotientGermParameterAlgHom
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (J : Ideal (MvPolynomial σ ℝ))
    (parameter : σ)
    (hJmem :
      ∀ Q : MvPolynomial σ ℝ,
        Q ∈ J ↔
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (x n) Q = 0) :
    letI : Algebra (Polynomial ℝ)
        (MvPolynomial σ ℝ ⧸ J) :=
      parameterPolynomialAlgebra J parameter
    letI : Algebra (Polynomial ℝ) GermField :=
      parameterGermAlgebra x parameter
    (MvPolynomial σ ℝ ⧸ J) →ₐ[Polynomial ℝ]
      GermField := by
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial σ ℝ ⧸ J) :=
    parameterPolynomialAlgebra J parameter
  letI : Algebra (Polynomial ℝ) GermField :=
    parameterGermAlgebra x parameter
  exact
    { quotientGermAlgHom x J hJmem with
      commutes' := fun p => rfl }

/-- Relative-to-parameter version of `localizedGermAlgHom`. -/
def localizedGermParameterAlgHom
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (J : Ideal (MvPolynomial σ ℝ))
    (parameter : σ)
    (g : MvPolynomial σ ℝ)
    (hg : g ∉ J)
    (hJmem :
      ∀ Q : MvPolynomial σ ℝ,
        Q ∈ J ↔
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (x n) Q = 0) :
    letI : Algebra (Polynomial ℝ)
        (MvPolynomial σ ℝ ⧸ J) :=
      parameterPolynomialAlgebra J parameter
    letI : Algebra (Polynomial ℝ) GermField :=
      parameterGermAlgebra x parameter
    Localization.Away (Ideal.Quotient.mk J g) →ₐ[Polynomial ℝ]
      GermField := by
  letI : Algebra (Polynomial ℝ)
      (MvPolynomial σ ℝ ⧸ J) :=
    parameterPolynomialAlgebra J parameter
  letI : Algebra (Polynomial ℝ) GermField :=
    parameterGermAlgebra x parameter
  let f :=
    quotientGermParameterAlgHom
      x J parameter hJmem
  refine IsLocalization.liftAlgHom
    (M := Submonoid.powers (Ideal.Quotient.mk J g))
    (S := Localization.Away (Ideal.Quotient.mk J g))
    (f := f) ?_
  intro s
  obtain ⟨n, hn⟩ := s.property
  rw [← hn, map_pow]
  apply IsUnit.pow
  rw [isUnit_iff_ne_zero]
  intro hzero
  apply Ideal.Quotient.eq_zero_iff_mem.not.mpr hg
  apply quotientGermAlgHom_injective x J hJmem
  simpa [f, quotientGermParameterAlgHom] using hzero

/-- A chosen real sequence representing an element of the ultrafilter germ
field. -/
def germRepresentative (z : GermField) : ℕ → ℝ :=
  Quotient.out z

theorem coe_germRepresentative (z : GermField) :
    ((germRepresentative z : ℕ → ℝ) : GermField) = z := by
  exact Quotient.out_eq z

theorem eventually_germRepresentative_zero :
    ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
      germRepresentative (0 : GermField) n = 0 := by
  apply Filter.Germ.coe_eq.mp
  exact coe_germRepresentative 0

/-- Evaluate each generator of a finite presentation at the generic germ
and choose simultaneous real representatives. -/
def presentationSequence
    {S ι κ : Type*}
    [CommRing S] [Algebra ℝ S]
    (φ : S →ₐ[ℝ] GermField)
    (P : Algebra.Presentation ℝ S ι κ) :
    ℕ → (ι → ℝ) :=
  fun n i => germRepresentative (φ (P.val i)) n

theorem sequenceGermEval_presentationSequence
    {S ι κ : Type*}
    [CommRing S] [Algebra ℝ S]
    (φ : S →ₐ[ℝ] GermField)
    (P : Algebra.Presentation ℝ S ι κ) :
    sequenceGermEval (presentationSequence φ P) =
      φ.comp (MvPolynomial.aeval P.val) := by
  ext i
  simp [presentationSequence, sequenceGermEval,
    coe_germRepresentative]

/-- Every polynomial identity in the presented algebra holds eventually
on the chosen real representative sequence. -/
theorem eventually_eval_presentationPolynomial
    {S ι κ : Type*}
    [CommRing S] [Algebra ℝ S]
    (φ : S →ₐ[ℝ] GermField)
    (P : Algebra.Presentation ℝ S ι κ)
    (Q : MvPolynomial ι ℝ) :
    ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
      MvPolynomial.eval (presentationSequence φ P n) Q =
        germRepresentative
          (φ (MvPolynomial.aeval P.val Q)) n := by
  apply Filter.Germ.coe_eq.mp
  rw [← sequenceGermEval_apply]
  rw [sequenceGermEval_presentationSequence]
  exact (coe_germRepresentative _).symm

theorem eventually_eval_relation
    {S ι κ : Type*}
    [CommRing S] [Algebra ℝ S]
    (φ : S →ₐ[ℝ] GermField)
    (P : Algebra.Presentation ℝ S ι κ)
    (j : κ) :
    ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
      MvPolynomial.eval
        (presentationSequence φ P n) (P.relation j) = 0 := by
  filter_upwards
    [eventually_eval_presentationPolynomial
      φ P (P.relation j),
      eventually_germRepresentative_zero] with n hn hnzero
  rw [P.aeval_val_relation, map_zero] at hn
  exact hn.trans hnzero

theorem eventually_eval_section
    {S ι κ : Type*}
    [CommRing S] [Algebra ℝ S]
    (φ : S →ₐ[ℝ] GermField)
    (P : Algebra.Presentation ℝ S ι κ)
    (s : S) :
    ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
      MvPolynomial.eval
        (presentationSequence φ P n) (P.σ s) =
          germRepresentative (φ s) n := by
  simpa [P.aeval_val_σ] using
    eventually_eval_presentationPolynomial φ P (P.σ s)

end CurveSelection.GermChart
end Math
