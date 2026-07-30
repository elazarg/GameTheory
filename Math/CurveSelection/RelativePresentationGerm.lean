/- Real representatives of a relative standard-smooth germ chart. -/
import Math.CurveSelection.RelativePresentation

set_option autoImplicit false

noncomputable section

open Filter

namespace Math
namespace CurveSelection.RelativePresentationGerm

open CurveSelection.GermChart
open CurveSelection.GermComponentScratch
open CurveSelection.RelativePresentation

/-- Choose simultaneous real representatives of the images of the
generators of a presentation over `ℝ[t]`. -/
def relativePresentationSequence
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Algebra (Polynomial ℝ) GermField]
    (φ : S →ₐ[Polynomial ℝ] GermField)
    (P : Algebra.Presentation (Polynomial ℝ) S ι κ) :
    ℕ → (ι → ℝ) :=
  fun n i => germRepresentative (φ (P.val i)) n

theorem coe_relativePresentationSequence
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Algebra (Polynomial ℝ) GermField]
    (φ : S →ₐ[Polynomial ℝ] GermField)
    (P : Algebra.Presentation (Polynomial ℝ) S ι κ)
    (i : ι) :
    ((fun n => relativePresentationSequence φ P n i) :
        GermField) =
      φ (P.val i) := by
  exact coe_germRepresentative _

/-- Under the parameter-germ algebra structure, the scalar polynomial
`p` is represented by the sequence `n ↦ p (x n parameter)`. -/
theorem parameterGermAlgebra_algebraMap_apply
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (parameter : σ)
    (p : Polynomial ℝ) :
    letI : Algebra (Polynomial ℝ) GermField :=
      parameterGermAlgebra x parameter
    algebraMap (Polynomial ℝ) GermField p =
      ((fun n => p.eval (x n parameter)) :
        GermField) := by
  change parameterGermEval x parameter p =
    ((fun n => p.eval (x n parameter)) : GermField)
  exact parameterGermEval_apply x parameter p

/--
Evaluation of a relative presentation polynomial on the chosen real
representatives, with its coefficients specialized at the real parameter
sequence, represents evaluation at the generic germ.
-/
theorem coe_eval₂_relativePresentationSequence
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Algebra (Polynomial ℝ) GermField]
    (φ : S →ₐ[Polynomial ℝ] GermField)
    (P : Algebra.Presentation (Polynomial ℝ) S ι κ)
    (t : ℕ → ℝ)
    (hbase :
      ∀ p : Polynomial ℝ,
        algebraMap (Polynomial ℝ) GermField p =
          ((fun n => p.eval (t n)) : GermField))
    (Q : MvPolynomial ι (Polynomial ℝ)) :
    ((fun n =>
        MvPolynomial.eval₂
          (Polynomial.evalRingHom (t n))
          (relativePresentationSequence φ P n) Q) :
        GermField) =
      φ (MvPolynomial.aeval P.val Q) := by
  induction Q using MvPolynomial.induction_on with
  | C p =>
      simp only [MvPolynomial.eval₂_C,
        MvPolynomial.aeval_C,
        Polynomial.coe_evalRingHom]
      rw [← hbase p, φ.commutes]
  | add Q R hQ hR =>
      have heval :
          ((fun n =>
            MvPolynomial.eval₂
              (Polynomial.evalRingHom (t n))
              (relativePresentationSequence φ P n)
              (Q + R)) : GermField) =
            ((fun n =>
              MvPolynomial.eval₂
                  (Polynomial.evalRingHom (t n))
                  (relativePresentationSequence φ P n) Q +
                MvPolynomial.eval₂
                  (Polynomial.evalRingHom (t n))
                  (relativePresentationSequence φ P n) R) :
              GermField) := by
        apply Filter.Germ.coe_eq.mpr
        exact Eventually.of_forall fun n => by
          change
            MvPolynomial.eval₂
                (Polynomial.evalRingHom (t n))
                (relativePresentationSequence φ P n)
                (Q + R) =
              MvPolynomial.eval₂
                  (Polynomial.evalRingHom (t n))
                  (relativePresentationSequence φ P n) Q +
                MvPolynomial.eval₂
                  (Polynomial.evalRingHom (t n))
                  (relativePresentationSequence φ P n) R
          exact MvPolynomial.eval₂_add
            (f := Polynomial.evalRingHom (t n))
            (g := relativePresentationSequence φ P n)
            (p := Q) (q := R)
      rw [heval]
      change
        ((((fun n =>
            MvPolynomial.eval₂
              (Polynomial.evalRingHom (t n))
              (relativePresentationSequence φ P n) Q) +
          (fun n =>
            MvPolynomial.eval₂
              (Polynomial.evalRingHom (t n))
              (relativePresentationSequence φ P n) R)) :
            ℕ → ℝ) : GermField) =
          φ (MvPolynomial.aeval P.val (Q + R))
      rw [Filter.Germ.coe_add, hQ, hR]
      simp only [map_add]
  | mul_X Q i hQ =>
      have heval :
          ((fun n =>
            MvPolynomial.eval₂
              (Polynomial.evalRingHom (t n))
              (relativePresentationSequence φ P n)
              (Q * MvPolynomial.X i)) : GermField) =
            ((fun n =>
              MvPolynomial.eval₂
                  (Polynomial.evalRingHom (t n))
                  (relativePresentationSequence φ P n) Q *
                relativePresentationSequence φ P n i) :
              GermField) := by
        apply Filter.Germ.coe_eq.mpr
        exact Eventually.of_forall fun n => by
          change
            MvPolynomial.eval₂
                (Polynomial.evalRingHom (t n))
                (relativePresentationSequence φ P n)
                (Q * MvPolynomial.X i) =
              MvPolynomial.eval₂
                  (Polynomial.evalRingHom (t n))
                  (relativePresentationSequence φ P n) Q *
                relativePresentationSequence φ P n i
          rw [MvPolynomial.eval₂_mul,
            MvPolynomial.eval₂_X]
      rw [heval]
      change
        ((((fun n =>
            MvPolynomial.eval₂
              (Polynomial.evalRingHom (t n))
              (relativePresentationSequence φ P n) Q) *
          (fun n =>
            relativePresentationSequence φ P n i)) :
            ℕ → ℝ) : GermField) =
          φ
            (MvPolynomial.aeval P.val
              (Q * MvPolynomial.X i))
      rw [Filter.Germ.coe_mul, hQ,
        coe_relativePresentationSequence]
      simp only [map_mul, MvPolynomial.aeval_X]

/-- Pointwise evaluation agrees eventually with a chosen representative of
the corresponding element of the germ field. -/
theorem eventually_eval₂_relativePresentationPolynomial
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Algebra (Polynomial ℝ) GermField]
    (φ : S →ₐ[Polynomial ℝ] GermField)
    (P : Algebra.Presentation (Polynomial ℝ) S ι κ)
    (t : ℕ → ℝ)
    (hbase :
      ∀ p : Polynomial ℝ,
        algebraMap (Polynomial ℝ) GermField p =
          ((fun n => p.eval (t n)) : GermField))
    (Q : MvPolynomial ι (Polynomial ℝ)) :
    ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
      MvPolynomial.eval₂
          (Polynomial.evalRingHom (t n))
          (relativePresentationSequence φ P n) Q =
        germRepresentative
          (φ (MvPolynomial.aeval P.val Q)) n := by
  apply Filter.Germ.coe_eq.mp
  rw [coe_eval₂_relativePresentationSequence
    φ P t hbase Q]
  exact (coe_germRepresentative _).symm

/-- Every relation of the relative presentation holds eventually on the
chosen real representative sequence. -/
theorem eventually_eval₂_relativeRelation
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Algebra (Polynomial ℝ) GermField]
    (φ : S →ₐ[Polynomial ℝ] GermField)
    (P : Algebra.Presentation (Polynomial ℝ) S ι κ)
    (t : ℕ → ℝ)
    (hbase :
      ∀ p : Polynomial ℝ,
        algebraMap (Polynomial ℝ) GermField p =
          ((fun n => p.eval (t n)) : GermField))
    (j : κ) :
    ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
      MvPolynomial.eval₂
          (Polynomial.evalRingHom (t n))
          (relativePresentationSequence φ P n)
          (P.relation j) =
        0 := by
  filter_upwards
    [eventually_eval₂_relativePresentationPolynomial
      φ P t hbase (P.relation j),
      eventually_germRepresentative_zero] with n hn hnzero
  rw [P.aeval_val_relation, map_zero] at hn
  exact hn.trans hnzero

/-- The designated polynomial section of every algebra element is
represented by the same real sequence after eventual evaluation. -/
theorem eventually_eval₂_relativeSection
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Algebra (Polynomial ℝ) GermField]
    (φ : S →ₐ[Polynomial ℝ] GermField)
    (P : Algebra.Presentation (Polynomial ℝ) S ι κ)
    (t : ℕ → ℝ)
    (hbase :
      ∀ p : Polynomial ℝ,
        algebraMap (Polynomial ℝ) GermField p =
          ((fun n => p.eval (t n)) : GermField))
    (s : S) :
    ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
      MvPolynomial.eval₂
          (Polynomial.evalRingHom (t n))
          (relativePresentationSequence φ P n)
          (P.σ s) =
        germRepresentative (φ s) n := by
  simpa [P.aeval_val_σ] using
    eventually_eval₂_relativePresentationPolynomial
      φ P t hbase (P.σ s)

/--
The Jacobian unit of a submersive presentation specializes to a nonzero
real determinant eventually along the representative sequence.
-/
theorem eventually_eval₂_jacobiMatrix_det_ne_zero
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Algebra (Polynomial ℝ) GermField]
    [Fintype κ] [DecidableEq κ]
    (φ : S →ₐ[Polynomial ℝ] GermField)
    (P :
      Algebra.SubmersivePresentation
        (Polynomial ℝ) S ι κ)
    (t : ℕ → ℝ)
    (hbase :
      ∀ p : Polynomial ℝ,
        algebraMap (Polynomial ℝ) GermField p =
          ((fun n => p.eval (t n)) : GermField)) :
    ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
      MvPolynomial.eval₂
          (Polynomial.evalRingHom (t n))
          (relativePresentationSequence φ
            P.toPreSubmersivePresentation.toPresentation n)
          P.jacobiMatrix.det ≠ 0 := by
  have hcoe :
      ((fun n =>
          MvPolynomial.eval₂
            (Polynomial.evalRingHom (t n))
            (relativePresentationSequence φ
              P.toPreSubmersivePresentation.toPresentation n)
            P.jacobiMatrix.det) :
          GermField) =
        φ P.jacobian := by
    calc
      ((fun n =>
          MvPolynomial.eval₂
            (Polynomial.evalRingHom (t n))
            (relativePresentationSequence φ
              P.toPreSubmersivePresentation.toPresentation n)
            P.jacobiMatrix.det) : GermField) =
        φ
          (MvPolynomial.aeval P.val
            P.jacobiMatrix.det) :=
        coe_eval₂_relativePresentationSequence
          φ P.toPreSubmersivePresentation.toPresentation
          t hbase P.jacobiMatrix.det
      _ = φ P.jacobian := by
        rw [P.jacobian_eq_jacobiMatrix_det,
          P.algebraMap_apply]
  have hne : φ P.jacobian ≠ 0 := by
    exact (isUnit_iff_ne_zero.mp
      (P.jacobian_isUnit.map φ))
  rw [Ultrafilter.eventually_not]
  intro hzero
  apply hne
  rw [← hcoe]
  exact Filter.Germ.coe_eq.mpr hzero

/-- Matrix form of
`eventually_eval₂_jacobiMatrix_det_ne_zero`, matching the real chart API. -/
theorem eventually_det_evaluatedJacobiMatrix_ne_zero
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Algebra (Polynomial ℝ) GermField]
    [Fintype κ] [DecidableEq κ]
    (φ : S →ₐ[Polynomial ℝ] GermField)
    (P :
      Algebra.SubmersivePresentation
        (Polynomial ℝ) S ι κ)
    (t : ℕ → ℝ)
    (hbase :
      ∀ p : Polynomial ℝ,
        algebraMap (Polynomial ℝ) GermField p =
          ((fun n => p.eval (t n)) : GermField)) :
    ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
      (evaluatedJacobiMatrix
          P.toPreSubmersivePresentation (t n)
          (relativePresentationSequence φ
            P.toPreSubmersivePresentation.toPresentation n)).det ≠
        0 := by
  filter_upwards
    [eventually_eval₂_jacobiMatrix_det_ne_zero
      φ P t hbase] with n hn
  rw [det_evaluatedJacobiMatrix]
  exact hn

/--
A single real representative of a relative submersive germ chart on which
all defining relations and the selected Jacobian minor are eventually
valid.  Every designated section is represented eventually as well.
-/
theorem exists_eventually_regular_relativePresentationSequence
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Algebra (Polynomial ℝ) GermField]
    [Fintype κ] [DecidableEq κ]
    (φ : S →ₐ[Polynomial ℝ] GermField)
    (P :
      Algebra.SubmersivePresentation
        (Polynomial ℝ) S ι κ)
    (t : ℕ → ℝ)
    (hbase :
      ∀ p : Polynomial ℝ,
        algebraMap (Polynomial ℝ) GermField p =
          ((fun n => p.eval (t n)) : GermField)) :
    ∃ a : ℕ → (ι → ℝ),
      (∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        (∀ j : κ,
          MvPolynomial.eval₂
              (Polynomial.evalRingHom (t n))
              (a n) (P.relation j) =
            0) ∧
          MvPolynomial.eval₂
              (Polynomial.evalRingHom (t n))
              (a n) P.jacobiMatrix.det ≠ 0) ∧
      (∀ s : S,
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          MvPolynomial.eval₂
              (Polynomial.evalRingHom (t n))
              (a n) (P.σ s) =
            germRepresentative (φ s) n) := by
  refine ⟨relativePresentationSequence φ
    P.toPreSubmersivePresentation.toPresentation, ?_, ?_⟩
  · filter_upwards
      [Filter.eventually_all.mpr fun j =>
        eventually_eval₂_relativeRelation
          φ P.toPreSubmersivePresentation.toPresentation
          t hbase j,
        eventually_eval₂_jacobiMatrix_det_ne_zero
          φ P t hbase] with n hrelation hdet
    exact ⟨hrelation, hdet⟩
  · intro s
    exact eventually_eval₂_relativeSection
      φ P.toPreSubmersivePresentation.toPresentation
      t hbase s

/--
Exact matrix form of the regular representative capstone.  This is the
form consumed by the fixed-parameter real chart and Lagrange arguments.
-/
theorem exists_eventually_regular_evaluatedPresentationSequence
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Algebra (Polynomial ℝ) GermField]
    [Fintype κ] [DecidableEq κ]
    (φ : S →ₐ[Polynomial ℝ] GermField)
    (P :
      Algebra.SubmersivePresentation
        (Polynomial ℝ) S ι κ)
    (t : ℕ → ℝ)
    (hbase :
      ∀ p : Polynomial ℝ,
        algebraMap (Polynomial ℝ) GermField p =
          ((fun n => p.eval (t n)) : GermField)) :
    ∃ a : ℕ → (ι → ℝ),
      (∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        (∀ j : κ,
          MvPolynomial.eval₂
              (Polynomial.evalRingHom (t n))
              (a n) (P.relation j) =
            0) ∧
          (evaluatedJacobiMatrix
            P.toPreSubmersivePresentation
            (t n) (a n)).det ≠
            0) ∧
      (∀ s : S,
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          MvPolynomial.eval₂
              (Polynomial.evalRingHom (t n))
              (a n) (P.σ s) =
            germRepresentative (φ s) n) := by
  obtain ⟨a, hregular, hsection⟩ :=
    exists_eventually_regular_relativePresentationSequence
      φ P t hbase
  refine ⟨a, ?_, hsection⟩
  filter_upwards [hregular] with n hn
  refine ⟨hn.1, ?_⟩
  rw [det_evaluatedJacobiMatrix]
  exact hn.2

end CurveSelection.RelativePresentationGerm
end Math
