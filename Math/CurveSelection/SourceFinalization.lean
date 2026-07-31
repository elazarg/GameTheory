import Math.CurveSelection.AlgebraicApproach
import Math.CurveSelection.SourceCell
import Math.CurveSelection.UltrafilterSubsequence

set_option autoImplicit false

noncomputable section

open Filter Set Topology
open Math.PolynomialSignCell

namespace Math
namespace CurveSelection.SourceFinalization

open CurveSelection.AlgebraicReductionScratch
open CurveSelection.SourceCell
open CurveSelection.SquareLiftScratch
open CurveSelection.UltrafilterSubsequence

/--
Ultrafilter-eventual algebraic relations for every nonparameter coordinate
of the source sequence are enough to finish the germ construction's analytic selection
step.  Finiteness synchronizes the relations, a strictly increasing
subsequence turns the ultrafilter identities into pointwise identities, and
the resulting source-cell power curve projects to the required positive
coordinate arc.
-/
theorem positiveCoordinateArc_of_eventual_source_relations
    {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (coordinate : σ)
    (x₀ : Assignment σ)
    (hcoordinate₀ : x₀ coordinate = 0)
    (u : ℕ → Assignment (Option (σ ⊕ Option ι)))
    (hucell :
      ∀ n,
        u n ∈
          signCell
            (sourcePolynomial
              (withPositiveCoordinatePolynomial P coordinate)
              (withPositiveCoordinateSignPattern τ) x₀)
            (sourceSignPattern
              (withPositiveCoordinateSignPattern τ)))
    (hupos : ∀ n, 0 < u n none)
    (hulim :
      Tendsto u atTop
        (𝓝
          (parameterizedLiftAssignment 0
            (squareLift
              (withPositiveCoordinatePolynomial P coordinate)
              (withPositiveCoordinateSignPattern τ) x₀))))
    (relation :
      {j : Option (σ ⊕ Option ι) // j ≠ none} →
        Polynomial (Polynomial ℝ))
    (hrelation : ∀ j, relation j ≠ 0)
    (hroot :
      ∀ j,
        ∀ᶠ n in (CurveSelection.GermComponentScratch.sequenceUltrafilter :
          Filter ℕ),
          bivEval (relation j) (u n none) (u n j.1) = 0) :
    HasPositiveCoordinateAnalyticArcAt
      (signCell P τ)
      (ContinuousLinearMap.proj coordinate) x₀ := by
  classical
  let good : ℕ → Prop :=
    fun n => ∀ j,
      bivEval (relation j) (u n none) (u n j.1) = 0
  have hgood :
      ∀ᶠ n in
          (CurveSelection.GermComponentScratch.sequenceUltrafilter : Filter ℕ),
        good n := by
    apply Filter.eventually_all.2
    intro j
    exact hroot j
  obtain ⟨ns, hns, hnsgood⟩ :=
    exists_strictMono_subsequence_of_eventually good hgood
  let v : ℕ → Assignment (Option (σ ⊕ Option ι)) :=
    fun n => u (ns n)
  have hnstendsto : Tendsto ns atTop atTop :=
    hns.tendsto_atTop
  have hvcell :
      ∀ n,
        v n ∈
          signCell
            (sourcePolynomial
              (withPositiveCoordinatePolynomial P coordinate)
              (withPositiveCoordinateSignPattern τ) x₀)
            (sourceSignPattern
              (withPositiveCoordinateSignPattern τ)) :=
    fun n => hucell (ns n)
  have hvpos : ∀ n, 0 < v n none :=
    fun n => hupos (ns n)
  have hvlim :
      Tendsto v atTop
        (𝓝
          (parameterizedLiftAssignment 0
            (squareLift
              (withPositiveCoordinatePolynomial P coordinate)
              (withPositiveCoordinateSignPattern τ) x₀))) :=
    hulim.comp hnstendsto
  have hvroot :
      ∀ n j,
        bivEval (relation j) (v n none) (v n j.1) = 0 := by
    intro n j
    exact hnsgood n j
  have hpower :
      HasAnalyticPowerCurveAt
        (signCell
          (sourcePolynomial
            (withPositiveCoordinatePolynomial P coordinate)
            (withPositiveCoordinateSignPattern τ) x₀)
          (sourceSignPattern
            (withPositiveCoordinateSignPattern τ)))
        (ContinuousLinearMap.proj none)
        (parameterizedLiftAssignment 0
          (squareLift
            (withPositiveCoordinatePolynomial P coordinate)
            (withPositiveCoordinateSignPattern τ) x₀)) := by
    apply
      Math.CurveSelection.AlgebraicApproach.hasAnalyticPowerCurveAt_signCell_of_algebraic_approach
          (sourcePolynomial
            (withPositiveCoordinatePolynomial P coordinate)
            (withPositiveCoordinateSignPattern τ) x₀)
          (sourceSignPattern
            (withPositiveCoordinateSignPattern τ))
          none
          (parameterizedLiftAssignment 0
            (squareLift
              (withPositiveCoordinatePolynomial P coordinate)
              (withPositiveCoordinateSignPattern τ) x₀))
          (by rfl)
          v relation hvcell hvpos hvlim hrelation hvroot
  exact
    positiveCoordinateArc_of_sourcePowerCurve
      P τ coordinate x₀ hcoordinate₀ hpower

/--
Convenient option-indexed form: it is enough to provide relations directly
for the coordinates under `some`.  These are exactly all nonparameter
coordinates of the source assignment.
-/
theorem positiveCoordinateArc_of_eventual_source_relations_some
    {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (coordinate : σ)
    (x₀ : Assignment σ)
    (hcoordinate₀ : x₀ coordinate = 0)
    (u : ℕ → Assignment (Option (σ ⊕ Option ι)))
    (hucell :
      ∀ n,
        u n ∈
          signCell
            (sourcePolynomial
              (withPositiveCoordinatePolynomial P coordinate)
              (withPositiveCoordinateSignPattern τ) x₀)
            (sourceSignPattern
              (withPositiveCoordinateSignPattern τ)))
    (hupos : ∀ n, 0 < u n none)
    (hulim :
      Tendsto u atTop
        (𝓝
          (parameterizedLiftAssignment 0
            (squareLift
              (withPositiveCoordinatePolynomial P coordinate)
              (withPositiveCoordinateSignPattern τ) x₀))))
    (relation :
      (σ ⊕ Option ι) → Polynomial (Polynomial ℝ))
    (hrelation : ∀ v, relation v ≠ 0)
    (hroot :
      ∀ v,
        ∀ᶠ n in (CurveSelection.GermComponentScratch.sequenceUltrafilter :
          Filter ℕ),
          bivEval (relation v) (u n none) (u n (some v)) = 0) :
    HasPositiveCoordinateAnalyticArcAt
      (signCell P τ)
      (ContinuousLinearMap.proj coordinate) x₀ := by
  let unsome :
      {j : Option (σ ⊕ Option ι) // j ≠ none} →
        (σ ⊕ Option ι) :=
    fun j =>
      j.1.get (Option.isSome_iff_ne_none.mpr j.2)
  have hsome :
      ∀ j : {j : Option (σ ⊕ Option ι) // j ≠ none},
        some (unsome j) = j.1 := by
    intro j
    exact Option.some_get
      (Option.isSome_iff_ne_none.mpr j.2)
  apply
    positiveCoordinateArc_of_eventual_source_relations
      P τ coordinate x₀ hcoordinate₀ u
      hucell hupos hulim
      (fun j => relation (unsome j))
  · intro j
    exact hrelation (unsome j)
  · intro j
    filter_upwards [hroot (unsome j)] with n hn
    simpa [hsome j] using hn

end CurveSelection.SourceFinalization
end Math
