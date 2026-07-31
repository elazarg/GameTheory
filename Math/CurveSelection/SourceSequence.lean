import Math.CurveSelection.AlgebraicReduction
import Math.CurveSelection.SourceCell

set_option autoImplicit false

noncomputable section

open Filter Set Topology
open Math.PolynomialSignCell

namespace Math
namespace CurveSelection.SourceSequence

open CurveSelection.AlgebraicReductionScratch
open CurveSelection.SourceCell
open CurveSelection.SquareLiftScratch

/--
Construct the lexicographically selected parameterized square-lift sequence
used by analytic curve selection.

The original positive coordinate is first inserted as a strict sign.  The
new algebraic parameter is the squared radius, thinned to be strictly
decreasing.  In every radius fiber the strict-slack score is maximized and
all lift coordinates are then minimized lexicographically.
-/
theorem exists_lexSelected_source_sequence
    {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (coordinate : σ)
    (x₀ : Assignment σ)
    (hcoordinate₀ : x₀ coordinate = 0)
    (hclosure :
      x₀ ∈
        closure
          (signCell P τ ∩
            {x | 0 < x coordinate})) :
    let Ppos :=
      withPositiveCoordinatePolynomial P coordinate
    let τpos :=
      withPositiveCoordinateSignPattern τ
    ∃ (a : ℕ → Assignment σ)
        (y : ℕ → Assignment (σ ⊕ Option ι))
        (z : ℕ → Assignment σ)
        (u : ℕ →
          Assignment (Option (σ ⊕ Option ι))),
      (∀ m, a m ∈ signCell Ppos τpos) ∧
      StrictAnti
        (fun m => squaredRadius x₀ (a m)) ∧
      Tendsto a atTop (𝓝 x₀) ∧
      (∀ m,
        y m ∈
          liftedCellSquaredRadiusClosure
            Ppos τpos x₀
              (squaredRadius x₀ (a m))) ∧
      (∀ m,
        squaredRadius x₀ (z m) =
          squaredRadius x₀ (a m)) ∧
      (∀ m, y m = squareLift Ppos τpos (z m)) ∧
      (∀ m, strictSlackProduct τpos (y m) ≠ 0) ∧
      (∀ m,
        (fun v => y m (Sum.inl v)) ∈
          signCell Ppos τpos) ∧
      Tendsto y atTop
        (𝓝 (squareLift Ppos τpos x₀)) ∧
      (∀ m,
        u m =
          parameterizedLiftAssignment
            (squaredRadius x₀ (a m)) (y m)) ∧
      (∀ m,
        u m ∈
          signCell
            (sourcePolynomial Ppos τpos x₀)
            (sourceSignPattern τpos)) ∧
      (∀ m, 0 < u m none) ∧
      StrictAnti (fun m => u m none) ∧
      Tendsto u atTop
        (𝓝
          (parameterizedLiftAssignment 0
            (squareLift Ppos τpos x₀))) ∧
      (∀ m w,
        w ∈
            liftedCellSquaredRadiusClosure
              Ppos τpos x₀
                (squaredRadius x₀ (a m)) →
        strictSlackProduct τpos w ^ 2 ≤
          strictSlackProduct τpos (y m) ^ 2) ∧
      ∀ m
          (k :
            Fin
              (Fintype.card
                (σ ⊕ Option ι)))
          w,
        w ∈
            liftedCellSquaredRadiusClosure
              Ppos τpos x₀
                (squaredRadius x₀ (a m)) →
        strictSlackProduct τpos w ^ 2 =
            strictSlackProduct τpos (y m) ^ 2 →
        (∀ j :
            Fin
              (Fintype.card
                (σ ⊕ Option ι)),
          j < k →
          enumeratedLiftCoordinate j w =
            enumeratedLiftCoordinate j (y m)) →
        enumeratedLiftCoordinate k (y m) ≤
          enumeratedLiftCoordinate k w := by
  dsimp only
  let Ppos :=
    withPositiveCoordinatePolynomial P coordinate
  let τpos :=
    withPositiveCoordinateSignPattern τ
  obtain
      ⟨x, hxcell, _hxanti, hxpositive, hxlim,
        _hxparameter⟩ :=
    exists_strictAnti_parameter_approach
      hcoordinate₀ hclosure
  have hxne : ∀ m, x m ≠ x₀ := by
    intro m hm
    have hp := hxpositive m
    rw [hm, hcoordinate₀] at hp
    exact (lt_irrefl 0 hp).elim
  obtain ⟨a, harange, haanti, halim⟩ :=
    exists_strictAnti_squaredRadius_subsequence
      x x₀ hxne hxlim
  have hacell :
      ∀ m, a m ∈ signCell Ppos τpos := by
    intro m
    obtain ⟨n, hn⟩ := harange m
    rw [← hn]
    rw [signCell_withPositiveCoordinate]
    exact ⟨hxcell n, hxpositive n⟩
  obtain
      ⟨y, z, hyS, hzRadius, hyEq, hystrict,
        hycell, _hzlim, hylim, hymax, hylex⟩ :=
    exists_lexSelected_squaredRadius_sequence
      Ppos τpos x₀ a hacell halim
      (Fintype.card (σ ⊕ Option ι))
      (enumeratedLiftCoordinate
        (σ := σ) (ι := Option ι))
      (continuous_enumeratedLiftCoordinate
        (σ := σ) (ι := Option ι))
  let u : ℕ →
      Assignment (Option (σ ⊕ Option ι)) :=
    fun m =>
      parameterizedLiftAssignment
        (squaredRadius x₀ (a m)) (y m)
  have huequation :
      ∀ m e,
        MvPolynomial.eval (u m)
          (parameterizedSquareLiftPolynomial
            Ppos τpos x₀ e) = 0 := by
    intro m e
    have hzcell :
        z m ∈ signCell Ppos τpos := by
      simpa [hyEq m] using hycell m
    have he :=
      eval_parameterizedSquareLiftPolynomial_eq_zero
        Ppos τpos x₀ hzcell e
    rw [hzRadius m] at he
    simpa [u, hyEq m] using he
  have husource :
      ∀ m,
        u m ∈
          signCell
            (sourcePolynomial Ppos τpos x₀)
            (sourceSignPattern τpos) := by
    intro m
    exact
      mem_sourceCell_of_equations_of_strictSlackProduct_ne_zero
        Ppos τpos x₀
        (squaredRadius x₀ (a m)) (y m)
        (huequation m) (hystrict m)
  have hapos :
      ∀ m, 0 < squaredRadius x₀ (a m) := by
    intro m
    apply squaredRadius_pos
    intro hm
    have hmcell := hacell m
    rw [signCell_withPositiveCoordinate] at hmcell
    have hp := hmcell.2
    rw [hm] at hp
    change 0 < x₀ coordinate at hp
    rw [hcoordinate₀] at hp
    exact (lt_irrefl 0 hp).elim
  have hrlim :
      Tendsto (fun m => squaredRadius x₀ (a m))
        atTop (𝓝 0) := by
    have h :=
      (continuous_squaredRadius x₀).continuousAt.tendsto.comp
        halim
    change
      Tendsto (squaredRadius x₀ ∘ a)
        atTop (𝓝 0)
    simpa only [squaredRadius_self] using h
  have hulim :
      Tendsto u atTop
        (𝓝
          (parameterizedLiftAssignment 0
            (squareLift Ppos τpos x₀))) := by
    rw [tendsto_pi_nhds]
    intro o
    cases o with
    | none =>
        simpa [u] using hrlim
    | some v =>
        simpa [u] using
          (tendsto_pi_nhds.mp hylim v)
  refine
    ⟨a, y, z, u, hacell, haanti, halim,
      hyS, hzRadius, hyEq, hystrict, hycell,
      hylim, fun m => rfl, husource, ?_, ?_,
      hulim, hymax, hylex⟩
  · intro m
    simpa [u] using hapos m
  · simpa [u] using haanti

end CurveSelection.SourceSequence
end Math
