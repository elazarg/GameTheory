import Math.GateGProjection
import Math.GateGSquareLift

set_option autoImplicit false

noncomputable section

open Math.PolynomialSignCell

namespace Math
namespace GateGSourceCell

open GateGSquareLiftScratch

/-- Permanent parameterized square-lift equations, together with strict
positivity of the squared slack score. -/
abbrev SourceConstraint
    {ι : Type*} (τ : SignPattern ι) :=
  ParameterizedSquareLiftEquation τ ⊕ Unit

def sourcePolynomial
    {ι σ : Type*} [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (x₀ : Assignment σ) :
    SourceConstraint τ →
      MvPolynomial (Option (σ ⊕ ι)) ℝ
  | .inl e => parameterizedSquareLiftPolynomial P τ x₀ e
  | .inr () => parameterizedStrictScorePolynomial (σ := σ) τ

def sourceSignPattern
    {ι : Type*} (τ : SignPattern ι) :
    SignPattern (SourceConstraint τ)
  | .inl _ => 0
  | .inr () => 1

/-- Forget the explicit squared-radius parameter and every slack coordinate,
retaining only the original assignment variables. -/
def sourceProjection
    {ι σ : Type*} [Fintype σ] [Fintype ι] :
    Assignment (Option (σ ⊕ ι)) →L[ℝ]
      Assignment σ :=
  ContinuousLinearMap.pi fun v =>
    (ContinuousLinearMap.proj
      (some (Sum.inl v)) :
        Assignment (Option (σ ⊕ ι)) →L[ℝ] ℝ)

@[simp]
theorem sourceProjection_apply
    {ι σ : Type*} [Fintype σ] [Fintype ι]
    (u : Assignment (Option (σ ⊕ ι)))
    (v : σ) :
    sourceProjection u v = u (some (Sum.inl v)) :=
  rfl

/-- The equation/strict-score form used by the selected sequence is exactly
membership in the source sign cell. -/
theorem mem_sourceCell_of_equations_of_strictSlackProduct_ne_zero
    {ι σ : Type*} [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (x₀ : Assignment σ)
    (r : ℝ) (y : Assignment (σ ⊕ ι))
    (hequation :
      ∀ e : ParameterizedSquareLiftEquation τ,
        MvPolynomial.eval
          (parameterizedLiftAssignment r y)
          (parameterizedSquareLiftPolynomial P τ x₀ e) = 0)
    (hstrict : strictSlackProduct τ y ≠ 0) :
    parameterizedLiftAssignment r y ∈
      signCell
        (sourcePolynomial P τ x₀)
        (sourceSignPattern τ) := by
  funext c
  cases c with
  | inl e =>
      apply sign_eq_zero_iff.mpr
      simpa [sourcePolynomial] using hequation e
  | inr u =>
      rcases u with ⟨⟩
      apply sign_eq_one_iff.mpr
      have hsquare : 0 < strictSlackProduct τ y ^ 2 :=
        sq_pos_of_ne_zero hstrict
      simpa [sourcePolynomial] using hsquare

/-- Every point of the source sign cell projects into the original complete
sign cell.  The positive score rules out every wrong square-root sign. -/
theorem sourceProjection_mem_signCell
    {ι σ : Type*} [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (x₀ : Assignment σ)
    {u : Assignment (Option (σ ⊕ ι))}
    (hu :
      u ∈ signCell
        (sourcePolynomial P τ x₀)
        (sourceSignPattern τ)) :
    sourceProjection u ∈ signCell P τ := by
  classical
  let r : ℝ := u none
  let y : Assignment (σ ⊕ ι) :=
    fun v => u (some v)
  have huDef :
      parameterizedLiftAssignment r y = u := by
    funext o
    cases o <;> rfl
  have huEq :
      ∀ e : ParameterizedSquareLiftEquation τ,
        MvPolynomial.eval
          (parameterizedLiftAssignment r y)
          (parameterizedSquareLiftPolynomial P τ x₀ e) = 0 := by
    intro e
    have he := congrFun hu (Sum.inl e)
    have hzero :
        MvPolynomial.eval u
          (sourcePolynomial P τ x₀ (Sum.inl e)) = 0 :=
      sign_eq_zero_iff.mp (by
        simpa [polynomialSignPattern,
          sourceSignPattern] using he)
    rw [huDef]
    exact hzero
  have hscorePos :
      0 <
        MvPolynomial.eval
          (parameterizedLiftAssignment r y)
          (parameterizedStrictScorePolynomial (σ := σ) τ) := by
    have hs := congrFun hu (Sum.inr ())
    have hs' :
        0 <
          MvPolynomial.eval u
            (sourcePolynomial P τ x₀ (Sum.inr ())) :=
      sign_eq_one_iff.mp (by
        simpa [polynomialSignPattern,
          sourceSignPattern] using hs)
    rw [huDef]
    exact hs'
  have hstrict : strictSlackProduct τ y ≠ 0 := by
    have hsquare : 0 < strictSlackProduct τ y ^ 2 := by
      simpa using hscorePos
    exact sq_pos_iff.mp hsquare
  have hequation :
      ∀ i,
        MvPolynomial.eval y (squareLiftPolynomial P τ i) = 0 := by
    intro i
    have hi := huEq
      (Sum.inl i : ParameterizedSquareLiftEquation τ)
    simpa [parameterizedSquareLiftPolynomial,
      MvPolynomial.eval_rename, Function.comp_def] using hi
  have hycell :
      (fun v => y (Sum.inl v)) ∈ signCell P τ :=
    project_mem_signCell_of_equations_of_strictSlackProduct_ne_zero
      P τ hequation hstrict
  simpa [sourceProjection, y] using hycell

@[simp]
theorem sourceProjection_parameterized_squareLift
    {ι σ : Type*} [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (r : ℝ) (x : Assignment σ) :
    sourceProjection
        (parameterizedLiftAssignment r
          (squareLift P τ x)) =
      x := by
  funext v
  rfl

/--
An analytic power curve in the parameterized source cell projects to the
positive-coordinate analytic arc required by the original sign cell.

The source power coordinate is the squared radius; positivity of the
original distinguished coordinate comes instead from adjoining that strict
sign before square lifting.
-/
theorem positiveCoordinateArc_of_sourcePowerCurve
    {ι σ : Type*} [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (coordinate : σ)
    (x₀ : Assignment σ)
    (hcoordinate₀ : x₀ coordinate = 0)
    (hcurve :
      let Ppos :=
        withPositiveCoordinatePolynomial P coordinate
      let τpos :=
        withPositiveCoordinateSignPattern τ
      HasAnalyticPowerCurveAt
        (signCell
          (sourcePolynomial Ppos τpos x₀)
          (sourceSignPattern τpos))
        (ContinuousLinearMap.proj none)
        (parameterizedLiftAssignment 0
          (squareLift Ppos τpos x₀))) :
    HasPositiveCoordinateAnalyticArcAt
      (signCell P τ)
      (ContinuousLinearMap.proj coordinate) x₀ := by
  dsimp only at hcurve
  apply
    GateGProjection.HasAnalyticPowerCurveAt.project_to_positiveCoordinateArc
      hcurve sourceProjection
        (ContinuousLinearMap.proj coordinate)
  · exact
      sourceProjection_parameterized_squareLift
        (withPositiveCoordinatePolynomial P coordinate)
        (withPositiveCoordinateSignPattern τ) 0 x₀
  · exact hcoordinate₀
  · intro u hu
    have huPos :
        sourceProjection u ∈
          signCell
            (withPositiveCoordinatePolynomial P coordinate)
            (withPositiveCoordinateSignPattern τ) :=
      sourceProjection_mem_signCell
        (withPositiveCoordinatePolynomial P coordinate)
        (withPositiveCoordinateSignPattern τ)
        x₀ hu
    rw [signCell_withPositiveCoordinate] at huPos
    exact huPos

end GateGSourceCell
end Math
