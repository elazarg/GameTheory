import Math.GateGAmbientCriticalAlgebraicity
import Math.GateGAlgebraicRelation
import Math.GateGGermChart
import Math.AlgebraicSelection

set_option autoImplicit false

noncomputable section

open Filter

namespace Math
namespace GateGAmbientGermRelation

open GateGAlgebraicRelation
open GateGGermChart
open GateGGermComponentScratch

/-- Pointwise bivariate evaluation, passed to the ultrafilter germ field,
is polynomial evaluation at the parameter and value germs. -/
theorem coe_bivEval
    {σ : Type*}
    (x : ℕ → (σ → ℝ)) (parameter : σ)
    (value : ℕ → ℝ)
    (Q : Polynomial (Polynomial ℝ)) :
    ((fun n =>
        bivEval Q (x n parameter) (value n)) :
      GermField) =
      Polynomial.eval₂
        (parameterGermEval x parameter).toRingHom
        ((value : ℕ → ℝ) : GermField) Q := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
      calc
        ((fun n =>
            bivEval (P + Q) (x n parameter) (value n)) :
          GermField) =
            ((fun n =>
                bivEval P (x n parameter) (value n) +
                  bivEval Q (x n parameter) (value n)) :
              GermField) := by
                congr
                funext n
                simp [bivEval]
        _ =
            ((fun n =>
                bivEval P (x n parameter) (value n)) :
              GermField) +
            ((fun n =>
                bivEval Q (x n parameter) (value n)) :
              GermField) := by
                rw [← Filter.Germ.coe_add]
                apply Filter.Germ.coe_eq.mpr
                exact Eventually.of_forall fun n => rfl
        _ = _ := by
          rw [hP, hQ, Polynomial.eval₂_add]
  | monomial n p =>
      calc
        ((fun m =>
            bivEval (Polynomial.monomial n p)
              (x m parameter) (value m)) :
          GermField) =
            ((fun m =>
                p.eval (x m parameter) * value m ^ n) :
              GermField) := by
                congr
                funext m
                simp [bivEval]
        _ =
            ((fun m => p.eval (x m parameter)) :
              GermField) *
            (((value : ℕ → ℝ) : GermField) ^ n) := by
                rw [← Filter.Germ.coe_pow,
                  ← Filter.Germ.coe_mul]
                apply Filter.Germ.coe_eq.mpr
                exact Eventually.of_forall fun m => rfl
        _ =
            parameterGermEval x parameter p *
              (((value : ℕ → ℝ) : GermField) ^ n) := by
                rw [parameterGermEval_apply]
        _ = _ := by
          simp

/-- Evaluation after extending coefficients from `ℝ[t]` to `ℝ(t)` agrees
with pointwise evaluation at the parameter sequence in the germ field. -/
theorem coe_bivEval_eq_aeval_map
    {σ : Type*}
    (x : ℕ → (σ → ℝ)) (parameter : σ)
    (hinjective :
      Function.Injective (fun n => x n parameter))
    (value : ℕ → ℝ)
    (Q : Polynomial (Polynomial ℝ)) :
    let K := FractionRing (Polynomial ℝ)
    letI : Algebra K GermField :=
      parameterFractionRingGermAlgebra
        x parameter hinjective
    ((fun n =>
        bivEval Q (x n parameter) (value n)) :
      GermField) =
      Polynomial.aeval
        ((value : ℕ → ℝ) : GermField)
        (Q.map (algebraMap (Polynomial ℝ) K)) := by
  dsimp only
  let K := FractionRing (Polynomial ℝ)
  letI : Algebra K GermField :=
    parameterFractionRingGermAlgebra
      x parameter hinjective
  rw [coe_bivEval]
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  apply DFunLike.ext _ _
  intro p
  exact
    (parameterFractionRingGermHom_algebraMap
      x parameter hinjective p).symm

/-- Algebraicity of a real-valued sequence germ over the rational
parameter field gives one fixed separable bivariate relation on an
ultrafilter-large set of indices. -/
theorem exists_bivariateRelation_eventually
    {σ : Type*}
    (x : ℕ → (σ → ℝ)) (parameter : σ)
    (hinjective :
      Function.Injective (fun n => x n parameter))
    (value : ℕ → ℝ)
    (halgebraic :
      let K := FractionRing (Polynomial ℝ)
      letI : Algebra K GermField :=
        parameterFractionRingGermAlgebra
          x parameter hinjective
      IsAlgebraic K
        ((value : ℕ → ℝ) : GermField)) :
    ∃ Q : Polynomial (Polynomial ℝ),
      Q ≠ 0 ∧
      (∀ᶠ n in
          (sequenceUltrafilter : Filter ℕ),
        bivEval Q (x n parameter) (value n) = 0) ∧
      (∀ᶠ n in
          (sequenceUltrafilter : Filter ℕ),
        bivEval Q.derivative
          (x n parameter) (value n) ≠ 0) := by
  let K := FractionRing (Polynomial ℝ)
  letI : Algebra K GermField :=
    parameterFractionRingGermAlgebra
      x parameter hinjective
  obtain ⟨Q, hQne, hroot, hderiv⟩ :=
    exists_base_relation_derivative_ne_zero
      (R := Polynomial ℝ) (K := K)
      (L := GermField)
      (((value : ℕ → ℝ) : GermField))
      halgebraic
  refine ⟨Q, hQne, ?_, ?_⟩
  · have heq :
        ((fun n =>
            bivEval Q (x n parameter) (value n)) :
          GermField) = 0 := by
      rw [coe_bivEval_eq_aeval_map
        x parameter hinjective value Q]
      exact hroot
    rw [← Filter.Germ.coe_zero] at heq
    exact Filter.Germ.coe_eq.mp heq
  · by_contra hnot
    let Z : Set ℕ :=
      {n |
        bivEval Q.derivative
          (x n parameter) (value n) = 0}
    have hZnot :
        Z ∉ sequenceUltrafilter := by
      intro hZ
      apply hderiv
      rw [← coe_bivEval_eq_aeval_map
        x parameter hinjective value Q.derivative]
      exact Filter.Germ.coe_eq.mpr hZ
    have hZc :
        Zᶜ ∈ sequenceUltrafilter :=
      (Ultrafilter.compl_mem_iff_notMem).2 hZnot
    apply hnot
    filter_upwards [hZc] with n hn
    simpa [Z] using hn

end GateGAmbientGermRelation
end Math
