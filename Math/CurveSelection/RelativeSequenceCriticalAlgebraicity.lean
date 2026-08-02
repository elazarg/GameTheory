import Math.CurveSelection.AmbientCriticalAlgebraicity
import Math.CurveSelection.GermChart

set_option autoImplicit false

noncomputable section

open Filter

namespace Math
namespace CurveSelection.RelativeSequenceCriticalAlgebraicity

open CurveSelection.AmbientCriticalAlgebraicity
open CurveSelection.GermChart
open CurveSelection.GermComponentScratch

/-- Evaluation of an `ℝ[t]`-polynomial on a varying real parameter and a
real sequence agrees with evaluation in the ultrafilter germ field after
extending coefficients to `ℝ(t)`. -/
theorem eval₂_map_parameterFractionRing_germ
    {σ ι : Type*}
    (x : ℕ → (σ → ℝ))
    (parameter : σ)
    (hinjective :
      Function.Injective (fun n => x n parameter))
    (y : ℕ → (ι → ℝ))
    (Q : MvPolynomial ι (Polynomial ℝ)) :
    let K := FractionRing (Polynomial ℝ)
    letI : Algebra K GermField :=
      parameterFractionRingGermAlgebra
        x parameter hinjective
    MvPolynomial.eval₂
        (algebraMap K GermField)
        (fun i => ((fun n => y n i) : GermField))
        (Q.map
          (algebraMap (Polynomial ℝ) K)) =
      (((fun n =>
          MvPolynomial.eval₂
            (Polynomial.evalRingHom (x n parameter))
            (y n) Q) : ℕ → ℝ) :
        GermField) := by
  dsimp only
  let K := FractionRing (Polynomial ℝ)
  letI : Algebra K GermField :=
    parameterFractionRingGermAlgebra
      x parameter hinjective
  rw [MvPolynomial.eval₂_map]
  have hcoeff :
      (algebraMap K GermField).comp
          (algebraMap (Polynomial ℝ) K) =
        (parameterGermEval x parameter).toRingHom := by
    apply DFunLike.ext _ _
    intro p
    change
      parameterFractionRingGermHom x parameter hinjective
          (algebraMap (Polynomial ℝ)
            (FractionRing (Polynomial ℝ)) p) =
        parameterGermEval x parameter p
    exact parameterFractionRingGermHom_algebraMap
      x parameter hinjective p
  rw [hcoeff]
  induction Q using MvPolynomial.induction_on with
  | C p =>
      simp only [MvPolynomial.eval₂_C,
        Polynomial.coe_evalRingHom]
      exact parameterGermEval_apply x parameter p
  | add P Q hP hQ =>
      simp only [MvPolynomial.eval₂_add]
      rw [hP, hQ, ← Filter.Germ.coe_add]
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall (fun _ => rfl)
  | mul_X P i hP =>
      simp only [MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X]
      rw [hP, ← Filter.Germ.coe_mul]
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall (fun _ => rfl)

/--
An eventual normalized critical equation for `ℝ[t]`-polynomials makes the
objective-value germ algebraic over `ℝ(t)`.

Unlike the flattened real-polynomial adapter, the parameter is a coefficient
here, so no spurious critical equation in the parameter direction is needed.
-/
theorem isAlgebraic_objectiveGerm_of_eventually_relativeNormalCriticality
    {σ ι I : Type*} [Finite ι] [Fintype I]
    (x : ℕ → (σ → ℝ))
    (parameter : σ)
    (hinjective :
      Function.Injective (fun n => x n parameter))
    (y : ℕ → (ι → ℝ))
    (P : I → MvPolynomial ι (Polynomial ℝ))
    (Q : MvPolynomial ι (Polynomial ℝ))
    (Λ : ℕ → I → ℝ)
    (hzero :
      ∀ i,
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          MvPolynomial.eval₂
            (Polynomial.evalRingHom (x n parameter))
            (y n) (P i) = 0)
    (hcritical :
      ∀ k,
        ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
          MvPolynomial.eval₂
              (Polynomial.evalRingHom (x n parameter))
              (y n) (MvPolynomial.pderiv k Q) =
            ∑ i : I,
              Λ n i *
                MvPolynomial.eval₂
                  (Polynomial.evalRingHom (x n parameter))
                  (y n)
                  (MvPolynomial.pderiv k (P i))) :
    let K := FractionRing (Polynomial ℝ)
    letI : Algebra K GermField :=
      parameterFractionRingGermAlgebra
        x parameter hinjective
    IsAlgebraic K
      (((fun n =>
          MvPolynomial.eval₂
            (Polynomial.evalRingHom (x n parameter))
            (y n) Q) : ℕ → ℝ) :
        GermField) := by
  letI : Fintype ι := Fintype.ofFinite ι
  dsimp only
  let K := FractionRing (Polynomial ℝ)
  letI : Algebra K GermField :=
    parameterFractionRingGermAlgebra
      x parameter hinjective
  let yg : ι → GermField :=
    fun k => ((fun n => y n k) : GermField)
  let Λg : I → GermField :=
    fun i => ((fun n => Λ n i) : GermField)
  let PK : I → MvPolynomial ι K :=
    fun i => (P i).map
      (algebraMap (Polynomial ℝ) K)
  let QK : MvPolynomial ι K :=
    Q.map (algebraMap (Polynomial ℝ) K)
  have hzeroG :
      ∀ i,
        MvPolynomial.eval₂
            (algebraMap K GermField) yg (PK i) = 0 := by
    intro i
    rw [eval₂_map_parameterFractionRing_germ
      x parameter hinjective y (P i)]
    apply Filter.Germ.coe_eq.mpr
    exact hzero i
  have hcriticalG :
      ∀ k,
        MvPolynomial.eval₂
            (algebraMap K GermField) yg
            (MvPolynomial.pderiv k QK) =
          ∑ i : I,
            Λg i *
              MvPolynomial.eval₂
                (algebraMap K GermField) yg
                (MvPolynomial.pderiv k (PK i)) := by
    intro k
    simp only [QK, PK, MvPolynomial.pderiv_map]
    rw [eval₂_map_parameterFractionRing_germ
      x parameter hinjective y
      (MvPolynomial.pderiv k Q)]
    have hPi :
        ∀ i : I,
          MvPolynomial.eval₂
              (algebraMap K GermField) yg
              ((MvPolynomial.pderiv k (P i)).map
                (algebraMap (Polynomial ℝ) K)) =
            (((fun n =>
                MvPolynomial.eval₂
                  (Polynomial.evalRingHom (x n parameter))
                  (y n)
                  (MvPolynomial.pderiv k (P i))) :
              ℕ → ℝ) : GermField) := by
      intro i
      exact eval₂_map_parameterFractionRing_germ
        x parameter hinjective y
        (MvPolynomial.pderiv k (P i))
    simp_rw [hPi]
    let φ :
        (ℕ → ℝ) →+* GermField :=
      Filter.Germ.coeRingHom
        (sequenceUltrafilter : Filter ℕ)
    change
      φ (fun n =>
          MvPolynomial.eval₂
            (Polynomial.evalRingHom (x n parameter))
            (y n) (MvPolynomial.pderiv k Q)) =
        ∑ i : I,
          φ (fun n => Λ n i) *
            φ (fun n =>
              MvPolynomial.eval₂
                (Polynomial.evalRingHom (x n parameter))
                (y n)
                (MvPolynomial.pderiv k (P i)))
    simp_rw [← map_mul]
    rw [← map_sum]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hcritical k] with n hn
    simpa only [Finset.sum_apply, Pi.mul_apply] using hn
  have halgebraic :
      IsAlgebraic K
        (MvPolynomial.eval₂
          (algebraMap K GermField) yg QK) :=
    isAlgebraic_of_equations_and_normalCriticality_in_ambient
      yg PK hzeroG QK Λg hcriticalG
  rw [eval₂_map_parameterFractionRing_germ
    x parameter hinjective y Q] at halgebraic
  exact halgebraic

end CurveSelection.RelativeSequenceCriticalAlgebraicity
end Math
