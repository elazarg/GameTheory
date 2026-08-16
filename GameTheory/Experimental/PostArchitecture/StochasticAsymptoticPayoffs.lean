/-
# EXP-108: distinct stochastic asymptotic payoff aggregations

This file exposes the three order-of-limits notions over an arbitrary path
measure.  It deliberately does not identify them, add an expectation wrapper,
or introduce an equilibrium notion.  Integrability and measurability remain
the hypotheses of the theorems that use them; they are not stored in these
definitions.
-/

import GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure
import GameTheory.Experimental.PostArchitecture.AsymptoticOscillatingSequence
import GameTheory.Experimental.PostArchitecture.CountablePMFExpectation

noncomputable section

open scoped BigOperators
open scoped Topology
open Filter

namespace GameTheory.Experimental.PostArchitecture

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The finite Cesaro average of a path's stage-payoff sequence. -/
def pathwiseAverage (stage : Ω → ℕ → ℝ) (ω : Ω) (n : ℕ) : ℝ :=
  cesaroAverage (stage ω) n

/--
`E[liminf Aₙ]`: pathwise liminf before integration.

This is a total Bochner integral, so it represents an expectation only when
the integrand is measurable and integrable (or under hypotheses implying
those properties).
-/
def expectedPathwiseLiminf (μ : Measure Ω) (stage : Ω → ℕ → ℝ) : ℝ :=
  ∫ ω, Filter.liminf (fun n => pathwiseAverage stage ω n) atTop ∂μ

/--
`E[limsup Aₙ]`: pathwise limsup before integration.

This is a total Bochner integral, so it represents an expectation only when
the integrand is measurable and integrable (or under hypotheses implying
those properties).
-/
def expectedPathwiseLimsup (μ : Measure Ω) (stage : Ω → ℕ → ℝ) : ℝ :=
  ∫ ω, Filter.limsup (fun n => pathwiseAverage stage ω n) atTop ∂μ

/--
The total Bochner integral encoding the expected finite Cesaro average at one
horizon.  It represents an expectation only under the relevant measurability
and integrability hypotheses.
-/
def expectedFiniteAverage (μ : Measure Ω) (stage : Ω → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∫ ω, pathwiseAverage stage ω n ∂μ

/--
`limₙ E[Aₙ]`, stated as convergence to an explicit value.  The sequence uses
the total Bochner integrals above; expectation semantics require the relevant
measurability and integrability hypotheses.
-/
def HasExpectedFiniteAverageLimit (μ : Measure Ω)
    (stage : Ω → ℕ → ℝ) (value : ℝ) : Prop :=
  Tendsto (fun n => expectedFiniteAverage μ stage n) atTop (𝓝 value)

omit [MeasurableSpace Ω] in
@[simp]
theorem pathwiseAverage_def (stage : Ω → ℕ → ℝ) (ω : Ω) (n : ℕ) :
    pathwiseAverage stage ω n = cesaroAverage (stage ω) n :=
  rfl

theorem expectedPathwiseLiminf_eq_integral (μ : Measure Ω)
    (stage : Ω → ℕ → ℝ) :
    expectedPathwiseLiminf μ stage =
      ∫ ω, Filter.liminf (fun n => cesaroAverage (stage ω) n) atTop ∂μ :=
  rfl

theorem expectedPathwiseLimsup_eq_integral (μ : Measure Ω)
    (stage : Ω → ℕ → ℝ) :
    expectedPathwiseLimsup μ stage =
      ∫ ω, Filter.limsup (fun n => cesaroAverage (stage ω) n) atTop ∂μ :=
  rfl

theorem expectedFiniteAverage_eq_integral (μ : Measure Ω)
    (stage : Ω → ℕ → ℝ) (n : ℕ) :
    expectedFiniteAverage μ stage n =
      ∫ ω, cesaroAverage (stage ω) n ∂μ :=
  rfl

/-! ## The countable discrete bridge -/

open GameTheory.Math.Probability

/--
On a countable discrete carrier, the total Bochner integral used by
`expectedFiniteAverage` agrees with `FinDist.expect` under an explicit
pointwise bound.
-/
theorem finDistMeasure_integral_eq_expect_of_bound {α : Type*}
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : FinDist α) (f : α → ℝ) {C : ℝ}
    (hbound : ∀ a, ‖f a‖ ≤ C) :
    (∫ a, f a ∂StochasticInfinitePlayMeasure.finDistMeasure μ) =
      μ.expect f := by
  exact CountablePMFExpectation.finDist_integral_eq_expect_of_bound
    μ f hbound

theorem hasExpectedFiniteAverageLimit_iff (μ : Measure Ω)
    (stage : Ω → ℕ → ℝ) (value : ℝ) :
    HasExpectedFiniteAverageLimit μ stage value ↔
      Tendsto (fun n => ∫ ω, pathwiseAverage stage ω n ∂μ)
        atTop (𝓝 value) :=
  Iff.rfl

theorem hasExpectedFiniteAverageLimit_const
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c value : ℝ)
    (hvalue : value = c) :
    HasExpectedFiniteAverageLimit μ (fun _ _ => c) value := by
  subst value
  rw [HasExpectedFiniteAverageLimit]
  convert tendsto_const_nhds using 1
  funext n
  simp [expectedFiniteAverage, pathwiseAverage, cesaroAverage,
    integral_const, smul_eq_mul]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-! ## A countable two-point hostile consumer -/

/-- The fair selector law on the countable carrier `Bool`. -/
def fairSelectorLaw : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure true) (FinDist.pure false)

/-- Select a stage sequence or its pointwise unit complement. -/
def fairSelectorStage (stage : ℕ → ℝ) : Bool → ℕ → ℝ
  | true => stage
  | false => complementSequence stage

theorem fairSelectorStage_average_bound (stage : ℕ → ℝ)
    (hstage : ∀ n, ‖cesaroAverage stage n‖ ≤ 1)
    (hcomplement : ∀ n,
      ‖cesaroAverage (complementSequence stage) n‖ ≤ 1) :
    ∀ b n, ‖pathwiseAverage (fairSelectorStage stage) b n‖ ≤ 1 := by
  intro b n
  cases b with
  | false => exact hcomplement n
  | true => exact hstage n

theorem fairSelectorStage_liminf_bound (stage : ℕ → ℝ)
    (hstage_liminf :
      Filter.liminf (fun n => cesaroAverage stage n) atTop = 0)
    (hcomplement_liminf :
      Filter.liminf
          (fun n => cesaroAverage (complementSequence stage) n) atTop = 0) :
    ∀ b, ‖Filter.liminf
        (fun n => pathwiseAverage (fairSelectorStage stage) b n) atTop‖ ≤ 1 := by
  intro b
  cases b with
  | false =>
      simp only [fairSelectorStage, pathwiseAverage]
      rw [hcomplement_liminf]
      norm_num
  | true =>
      simp only [fairSelectorStage, pathwiseAverage]
      rw [hstage_liminf]
      norm_num

theorem fairSelectorStage_limsup_bound (stage : ℕ → ℝ)
    (hstage_limsup :
      Filter.limsup (fun n => cesaroAverage stage n) atTop = 1)
    (hcomplement_limsup :
      Filter.limsup
          (fun n => cesaroAverage (complementSequence stage) n) atTop = 1) :
    ∀ b, ‖Filter.limsup
        (fun n => pathwiseAverage (fairSelectorStage stage) b n) atTop‖ ≤ 1 := by
  intro b
  cases b with
  | false =>
      simp only [fairSelectorStage, pathwiseAverage]
      rw [hcomplement_limsup]
      norm_num
  | true =>
      simp only [fairSelectorStage, pathwiseAverage]
      rw [hstage_limsup]
      norm_num

/--
Given the endpoint facts and explicit finite-average bounds, the countable
selector version realizes the three distinct values `0`, `1 / 2`, and `1`
for the exact Bochner-integral definitions above.
-/
theorem fair_selector_order_limits_measure (stage : ℕ → ℝ)
    (hstage_liminf :
      Filter.liminf (fun n => cesaroAverage stage n) atTop = 0)
    (hstage_limsup :
      Filter.limsup (fun n => cesaroAverage stage n) atTop = 1)
    (hcomplement_liminf :
      Filter.liminf
          (fun n => cesaroAverage (complementSequence stage) n) atTop = 0)
    (hcomplement_limsup :
      Filter.limsup
          (fun n => cesaroAverage (complementSequence stage) n) atTop = 1)
    (hstage_bound : ∀ n, ‖cesaroAverage stage n‖ ≤ 1)
    (hcomplement_bound : ∀ n,
      ‖cesaroAverage (complementSequence stage) n‖ ≤ 1) :
    expectedPathwiseLiminf
          (StochasticInfinitePlayMeasure.finDistMeasure (fairSelectorLaw))
          (fairSelectorStage stage) = 0 ∧
      (∀ n, expectedFiniteAverage
          (StochasticInfinitePlayMeasure.finDistMeasure (fairSelectorLaw))
          (fairSelectorStage stage) n = (1 / 2 : ℝ)) ∧
      HasExpectedFiniteAverageLimit
          (StochasticInfinitePlayMeasure.finDistMeasure (fairSelectorLaw))
          (fairSelectorStage stage) (1 / 2 : ℝ) ∧
      expectedPathwiseLimsup
          (StochasticInfinitePlayMeasure.finDistMeasure (fairSelectorLaw))
          (fairSelectorStage stage) = 1 := by
  have hliminf_bound := fairSelectorStage_liminf_bound stage
    hstage_liminf hcomplement_liminf
  have hlimsup_bound := fairSelectorStage_limsup_bound stage
    hstage_limsup hcomplement_limsup
  have havg_bound := fairSelectorStage_average_bound stage
    hstage_bound hcomplement_bound
  have hLiminf := finDistMeasure_integral_eq_expect_of_bound
    fairSelectorLaw
    (fun b => Filter.liminf
      (fun n => pathwiseAverage (fairSelectorStage stage) b n) atTop)
    hliminf_bound
  have hLimsup := finDistMeasure_integral_eq_expect_of_bound
    fairSelectorLaw
    (fun b => Filter.limsup
      (fun n => pathwiseAverage (fairSelectorStage stage) b n) atTop)
    hlimsup_bound
  have hLiminfValue :
      expectedPathwiseLiminf
          (StochasticInfinitePlayMeasure.finDistMeasure (fairSelectorLaw))
          (fairSelectorStage stage) = 0 := by
    unfold expectedPathwiseLiminf
    rw [hLiminf, fairSelectorLaw, FinDist.expect_mix,
      FinDist.expect_pure, FinDist.expect_pure]
    simp only [fairSelectorStage, pathwiseAverage]
    rw [hstage_liminf, hcomplement_liminf]
    norm_num
  have hLimsupValue :
      expectedPathwiseLimsup
          (StochasticInfinitePlayMeasure.finDistMeasure (fairSelectorLaw))
          (fairSelectorStage stage) = 1 := by
    unfold expectedPathwiseLimsup
    rw [hLimsup, fairSelectorLaw, FinDist.expect_mix,
      FinDist.expect_pure, FinDist.expect_pure]
    simp only [fairSelectorStage, pathwiseAverage]
    rw [hstage_limsup, hcomplement_limsup]
    norm_num
  have havg_value : ∀ n, expectedFiniteAverage
      (StochasticInfinitePlayMeasure.finDistMeasure (fairSelectorLaw))
      (fairSelectorStage stage) n = (1 / 2 : ℝ) := by
    intro n
    unfold expectedFiniteAverage
    have h := finDistMeasure_integral_eq_expect_of_bound
      fairSelectorLaw (fun b => pathwiseAverage
        (fairSelectorStage stage) b n) (havg_bound · n)
    rw [h, fairSelectorLaw, FinDist.expect_mix,
      FinDist.expect_pure, FinDist.expect_pure]
    simp only [fairSelectorStage, pathwiseAverage]
    rw [cesaroAverage_complement]
    ring
  refine ⟨hLiminfValue, havg_value, ?_, hLimsupValue⟩
  rw [HasExpectedFiniteAverageLimit]
  convert tendsto_const_nhds using 1
  funext n
  exact havg_value n

/-- The machine-checked alternating-block path realizes the hostile slice. -/
theorem alternatingBlockStage_order_limits_measure :
    expectedPathwiseLiminf
          (StochasticInfinitePlayMeasure.finDistMeasure (fairSelectorLaw))
          (fairSelectorStage alternatingBlockStage) = 0 ∧
      (∀ n, expectedFiniteAverage
          (StochasticInfinitePlayMeasure.finDistMeasure (fairSelectorLaw))
          (fairSelectorStage alternatingBlockStage) n = (1 / 2 : ℝ)) ∧
      HasExpectedFiniteAverageLimit
          (StochasticInfinitePlayMeasure.finDistMeasure (fairSelectorLaw))
          (fairSelectorStage alternatingBlockStage) (1 / 2 : ℝ) ∧
      expectedPathwiseLimsup
          (StochasticInfinitePlayMeasure.finDistMeasure (fairSelectorLaw))
          (fairSelectorStage alternatingBlockStage) = 1 := by
  have hstage_bound : ∀ n,
      ‖cesaroAverage alternatingBlockStage n‖ ≤ 1 := by
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (alternatingCesaro_bounded n).1]
    exact (alternatingCesaro_bounded n).2
  have hcomplement_bound : ∀ n,
      ‖cesaroAverage (complementSequence alternatingBlockStage) n‖ ≤ 1 := by
    intro n
    rw [cesaroAverage_complement]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · linarith [(alternatingCesaro_bounded n).1]
    · linarith [(alternatingCesaro_bounded n).2]
  exact fair_selector_order_limits_measure alternatingBlockStage
    cesaroAverage_alternating_liminf_limsup.1
    cesaroAverage_alternating_liminf_limsup.2
    cesaroAverage_complement_alternating_liminf_limsup.1
    cesaroAverage_complement_alternating_liminf_limsup.2
    hstage_bound hcomplement_bound

end GameTheory.Experimental.PostArchitecture
