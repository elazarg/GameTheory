import Math.CurveSelection.LexIsolation
import Math.CurveSelection.SquareLift

noncomputable section

open Filter Set Topology
open Math.PolynomialSignCell

namespace Math
namespace CurveSelection.SourceLexExtrema

open CurveSelection.LexIsolationScratch
open CurveSelection.SquareLiftScratch

/--
The compact square-lift selection inequalities are precisely the local
lexicographic extrema needed on the fixed-radius permanent equation locus.
Stage zero is the strict-slack-score maximum; every successor stage is the
minimum of one enumerated lift coordinate after fixing all earlier stages.
-/
theorem isLocalExtrOn_triangularLexObjectives
    {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (x₀ : Assignment σ)
    (r : ℝ)
    (y : Assignment (σ ⊕ ι))
    (hy :
      y ∈ liftedCellSquaredRadiusClosure P τ x₀ r)
    (hstrict : strictSlackProduct τ y ≠ 0)
    (hmax :
      ∀ w,
        w ∈ liftedCellSquaredRadiusClosure P τ x₀ r →
        strictSlackProduct τ w ^ 2 ≤
          strictSlackProduct τ y ^ 2)
    (hlex :
      ∀ (k : Fin (Fintype.card (σ ⊕ ι))) w,
        w ∈ liftedCellSquaredRadiusClosure P τ x₀ r →
        strictSlackProduct τ w ^ 2 =
            strictSlackProduct τ y ^ 2 →
        (∀ j : Fin (Fintype.card (σ ⊕ ι)),
          j < k →
          enumeratedLiftCoordinate j w =
            enumeratedLiftCoordinate j y) →
        enumeratedLiftCoordinate k y ≤
          enumeratedLiftCoordinate k w) :
    let objective :
        Fin (Fintype.card (σ ⊕ ι) + 1) →
          Assignment (σ ⊕ ι) → ℝ :=
      fun j w =>
        MvPolynomial.eval
          (parameterizedLiftAssignment r w)
          (triangularLexObjectivePolynomial τ j)
    let permanentFiber : Set (Assignment (σ ⊕ ι)) :=
      {w |
        ∀ e : ParameterizedSquareLiftEquation τ,
          MvPolynomial.eval
            (parameterizedLiftAssignment r w)
            (parameterizedSquareLiftPolynomial P τ x₀ e) = 0}
    ∀ j,
      IsLocalExtrOn
        (objective j)
        (permanentFiber ∩
          previousObjectiveLevelSet objective y j)
        y := by
  dsimp only
  let objective :
      Fin (Fintype.card (σ ⊕ ι) + 1) →
        Assignment (σ ⊕ ι) → ℝ :=
    fun j w =>
      MvPolynomial.eval
        (parameterizedLiftAssignment r w)
        (triangularLexObjectivePolynomial τ j)
  let permanentFiber : Set (Assignment (σ ⊕ ι)) :=
    {w |
      ∀ e : ParameterizedSquareLiftEquation τ,
        MvPolynomial.eval
          (parameterizedLiftAssignment r w)
          (parameterizedSquareLiftPolynomial P τ x₀ e) = 0}
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · right
    change
      ∀ᶠ w in
        𝓝[permanentFiber ∩
          previousObjectiveLevelSet objective y 0] y,
        objective 0 w ≤ objective 0 y
    rw [eventually_nhdsWithin_iff]
    filter_upwards
      [eventually_mem_liftedCellSquaredRadiusClosure_of_parameterizedEquations
        P τ x₀ r hy hstrict] with w hw
    intro hwset
    have hwclosure :
        w ∈ liftedCellSquaredRadiusClosure P τ x₀ r :=
      hw hwset.1
    simpa [objective] using hmax w hwclosure
  · left
    change
      ∀ᶠ w in
        𝓝[permanentFiber ∩
          previousObjectiveLevelSet objective y k.succ] y,
        objective k.succ y ≤ objective k.succ w
    rw [eventually_nhdsWithin_iff]
    filter_upwards
      [eventually_mem_liftedCellSquaredRadiusClosure_of_parameterizedEquations
        P τ x₀ r hy hstrict] with w hw
    intro hwset
    have hwclosure :
        w ∈ liftedCellSquaredRadiusClosure P τ x₀ r :=
      hw hwset.1
    have hscore :
        strictSlackProduct τ w ^ 2 =
          strictSlackProduct τ y ^ 2 := by
      have h :=
        hwset.2
          ⟨0, by simp⟩
      simpa [objective] using h
    have hcoordinates :
        ∀ l : Fin (Fintype.card (σ ⊕ ι)),
          l < k →
          enumeratedLiftCoordinate l w =
            enumeratedLiftCoordinate l y := by
      intro l hl
      have h :=
        hwset.2
          ⟨l.succ, Fin.succ_lt_succ_iff.mpr hl⟩
      simpa [objective] using h
    simpa [objective] using
      hlex k w hwclosure hscore hcoordinates

end CurveSelection.SourceLexExtrema
end Math
