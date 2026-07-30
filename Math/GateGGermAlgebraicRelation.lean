/- Fixed separable bivariate relations for algebraic ultrafilter germs. -/
import Math.GateGAlgebraicRelation
import Math.GateGGermChart
import Math.GateGLocalRootIsolation

set_option autoImplicit false

noncomputable section

open Filter

namespace Math
namespace GateGGermAlgebraicRelation

open GateGAlgebraicRelation
open GateGGermChart
open GateGGermComponentScratch

/-- Evaluating a real bivariate polynomial on representative sequences
gives the same germ as evaluating it algebraically over `ℝ(t)`. -/
theorem coe_bivEval_germRepresentative
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (parameter : σ)
    (hinjective :
      Function.Injective (fun n => x n parameter))
    (q : GermField)
    (Q : Polynomial (Polynomial ℝ)) :
    letI : Algebra (FractionRing (Polynomial ℝ)) GermField :=
      parameterFractionRingGermAlgebra
        x parameter hinjective
    ((fun n =>
        bivEval Q (x n parameter)
          (germRepresentative q n)) : GermField) =
      Polynomial.aeval q
        (Q.map
          (algebraMap (Polynomial ℝ)
            (FractionRing (Polynomial ℝ)))) := by
  letI : Algebra (FractionRing (Polynomial ℝ)) GermField :=
    parameterFractionRingGermAlgebra
      x parameter hinjective
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Polynomial.map_add, map_add, ← hP, ← hQ]
      apply Filter.Germ.coe_eq.mpr
      exact Eventually.of_forall fun n => by
        simp [bivEval]
  | monomial n p =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [Polynomial.map_mul, Polynomial.map_C,
        Polynomial.aeval_def, Polynomial.eval₂_C,
        Polynomial.eval₂_mul]
      simp only [Polynomial.map_pow, Polynomial.map_X,
        Polynomial.eval₂_pow, Polynomial.eval₂_X]
      rw [show
        (algebraMap
          (FractionRing (Polynomial ℝ)) GermField) =
            parameterFractionRingGermHom
              x parameter hinjective by
        exact RingHom.algebraMap_toAlgebra _]
      rw [parameterFractionRingGermHom_algebraMap
        x parameter hinjective p]
      change
        ((fun m =>
          bivEval (Polynomial.C p * Polynomial.X ^ n)
            (x m parameter) (germRepresentative q m)) :
            GermField) =
          parameterGermEval x parameter p * q ^ n
      calc
        ((fun m =>
          bivEval (Polynomial.C p * Polynomial.X ^ n)
            (x m parameter) (germRepresentative q m)) :
            GermField) =
            ((fun m =>
              p.eval (x m parameter) *
                germRepresentative q m ^ n) :
              GermField) := by
                apply Filter.Germ.coe_eq.mpr
                exact Eventually.of_forall fun m => by
                  simp [bivEval]
        _ =
            ((fun m => p.eval (x m parameter)) :
                GermField) *
              ((germRepresentative q : ℕ → ℝ) :
                GermField) ^ n := rfl
        _ =
            parameterGermEval x parameter p *
              ((germRepresentative q : ℕ → ℝ) :
                GermField) ^ n := by
                  rw [parameterGermEval_apply]
        _ = parameterGermEval x parameter p * q ^ n := by
              rw [coe_germRepresentative]

/-- Algebraicity of a germ over `ℝ(t)` yields one fixed real bivariate
relation whose value derivative is nonzero at almost every representative
point. -/
theorem exists_eventually_separable_bivariateRelation
    {σ : Type*}
    (x : ℕ → (σ → ℝ))
    (parameter : σ)
    (hinjective :
      Function.Injective (fun n => x n parameter))
    (q : GermField)
    (hq :
      letI : Algebra
          (FractionRing (Polynomial ℝ)) GermField :=
        parameterFractionRingGermAlgebra
          x parameter hinjective
      IsAlgebraic (FractionRing (Polynomial ℝ)) q) :
    ∃ Q : Polynomial (Polynomial ℝ),
      Q ≠ 0 ∧
      (∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        bivEval Q (x n parameter)
          (germRepresentative q n) = 0) ∧
      (∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        bivEval Q.derivative (x n parameter)
          (germRepresentative q n) ≠ 0) := by
  letI : Algebra
      (FractionRing (Polynomial ℝ)) GermField :=
    parameterFractionRingGermAlgebra
      x parameter hinjective
  obtain ⟨Q, hQ, hroot, hderiv⟩ :=
    exists_base_relation_derivative_ne_zero
      (R := Polynomial ℝ)
      (K := FractionRing (Polynomial ℝ))
      (L := GermField) q hq
  refine ⟨Q, hQ, ?_, ?_⟩
  · apply Filter.Germ.coe_eq.mp
    rw [coe_bivEval_germRepresentative
      x parameter hinjective q Q]
    exact hroot
  · rw [Ultrafilter.eventually_not]
    intro heventuallyZero
    apply hderiv
    rw [← coe_bivEval_germRepresentative
      x parameter hinjective q Q.derivative]
    exact Filter.Germ.coe_eq.mpr heventuallyZero

end GateGGermAlgebraicRelation
end Math
