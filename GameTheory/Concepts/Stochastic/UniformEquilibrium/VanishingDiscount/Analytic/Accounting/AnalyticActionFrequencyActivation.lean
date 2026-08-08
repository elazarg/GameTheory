/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.PublicActionFrequencyResponse
import Math.OnlineLearning.CompletedEpochCalendar
import Math.Probability.ResetActivation
import Math.Probability.StitchedMartingale
import Math.OnlineLearning.AnytimeCalendarLimits

/-!
# Horizon-free activation of analytic public action responses

An analytic stage response supplies one fixed public action-frequency score.
The universal logarithmic calendar evaluates that score at successively
smaller Bellman parameters without knowing the response's finite analytic
order.

This file separates the two honest parts of statistical activation.

* The analytic response is compiled to a centered, bounded score with a
  power-law pure-comparison drift at every sufficiently late calendar epoch.
* A generic cumulative-score process is tested against the existing
  geometric stitched boundary. Under the baseline law, the probability of
  any activation is at most the chosen error budget. Under a comparison law,
  activation fails with at most the same budget once its deterministic signal
  dominates twice the boundary.

The second part deliberately takes the cumulative signal comparison as data.
It is the minimal predictable-process interface: converting the one-step
analytic drift into that cumulative inequality depends on the concrete play
law, history contexts, and reset convention. No punishment or target-payoff
closure is asserted here.
-/

noncomputable section

open scoped ENNReal Topology

namespace GameTheory
namespace StochasticGame

open Filter Math Math.OnlineLearning Math.PMFProduct Math.Probability
  MeasureTheory Set
open ProbabilityTheory

variable {ι : Type} {G : StochasticGame ι}

namespace AnalyticFinkStagePublicResponse

/-- The universal calendar eventually exposes the complete operational
action-frequency detector furnished by an analytic stage response. The
algorithm does not use `R.order`; the order occurs only in the proved drift
lower bound. -/
theorem eventually_universalEpochActionFrequencyDetector
    [Fintype G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
    {germ : G.AnalyticBellmanGerm}
    {response : Σ owner : ι, G.State × G.Act owner}
    (R : AnalyticFinkStagePublicResponse germ response)
    {U : ℝ} (hU : 0 < U)
    (hpay : ∀ s a owner, |G.stagePayoff s a owner| ≤ U) :
    ∀ᶠ k : ℕ in atTop,
      ∀ hk :
          universalEpochScale k ∈
            Ioo (0 : ℝ) germ.radius,
        expect
            (pmfPi
              (G.finkProfile
                (germ.finkPointAt hk) response.2.1))
            (G.publicActionFrequencyScore
              response.1
              (G.finkProfile
                (germ.finkPointAt hk) response.2.1 response.1)
              response.2.2) = 0 ∧
          R.margin / (2 * U) *
                universalEpochScale k ^ R.order ≤
            expect
              (pmfPi
                (Function.update
                  (G.finkProfile
                    (germ.finkPointAt hk) response.2.1)
                  response.1 (PMF.pure response.2.2)))
              (G.publicActionFrequencyScore
                response.1
                (G.finkProfile
                  (germ.finkPointAt hk) response.2.1 response.1)
                response.2.2) ∧
          ∀ jointAction,
            |G.publicActionFrequencyScore
                response.1
                (G.finkProfile
                  (germ.finkPointAt hk) response.2.1 response.1)
                response.2.2 jointAction| ≤ 1 := by
  have hscale :
      Tendsto universalEpochScale atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact
      ⟨tendsto_universalEpochScale,
        Filter.Eventually.of_forall universalEpochScale_pos⟩
  exact hscale.eventually
    (R.eventually_actionFrequencyDetector hU hpay)

end AnalyticFinkStagePublicResponse

section StitchedActivation

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω]
  {baselineLaw comparisonLaw : Measure Ω}

/-- The canonical horizon-free activation boundary for increments bounded
by `L` and total false-activation budget `alpha`. -/
def publicDetectorBoundary (L alpha : ℝ) (n : ℕ) : ℝ :=
  stitchedBoundary (boundedIncrementVariance L)
    inverseSqrtDyadicRate (geometricBlockBudget alpha) n

/-- A cumulative public score activates once it crosses its stitched
boundary at any positive time. -/
def publicDetectorActivation
    (cumulative : ℕ → Ω → ℝ) (L alpha : ℝ) : Set Ω :=
  {ω | ∃ n, 0 < n ∧
    publicDetectorBoundary L alpha n ≤ cumulative n ω}

/-- Minimal honest predictable-process interface for a horizon-free public
detector.

`cumulative` is the observed score. It is a bounded-increment martingale
under the baseline law. Under the comparison law, `adverseNoise` is the
centered adverse fluctuation, and `comparisonLower` says that observed score
is at least deterministic signal minus that fluctuation. The final eventual
inequality is the deterministic calendar calculation required for
activation. -/
structure HorizonFreePublicDetector
    (baselineLaw comparisonLaw : Measure Ω) where
  cumulative : ℕ → Ω → ℝ
  adverseNoise : ℕ → Ω → ℝ
  filtration : Filtration ℕ ‹MeasurableSpace Ω›
  adverseFiltration : Filtration ℕ ‹MeasurableSpace Ω›
  incrementBound : ℝ
  alpha : ℝ
  alpha_pos : 0 < alpha
  baseline_probability : IsProbabilityMeasure baselineLaw
  comparison_probability : IsProbabilityMeasure comparisonLaw
  baseline_martingale :
    Martingale cumulative filtration baselineLaw
  baseline_zero : ∀ ω, cumulative 0 ω = 0
  baseline_increment_bound :
    ∀ n ω,
      processIncrement cumulative n ω ∈
        Icc (-incrementBound) incrementBound
  adverse_martingale :
    Martingale adverseNoise adverseFiltration comparisonLaw
  adverse_zero : ∀ ω, adverseNoise 0 ω = 0
  adverse_increment_bound :
    ∀ n ω,
      processIncrement adverseNoise n ω ∈
        Icc (-incrementBound) incrementBound
  signal : ℕ → ℝ
  comparisonLower :
    ∀ n ω, signal n - adverseNoise n ω ≤ cumulative n ω
  eventually_signal_dominates :
    ∀ᶠ n in atTop,
      0 < n ∧
        2 * publicDetectorBoundary incrementBound alpha n <
          signal n

namespace HorizonFreePublicDetector

variable [StandardBorelSpace Ω]

/-- Under the baseline law, the probability of any false activation is at
most the chosen budget. -/
theorem baseline_falseActivation_le
    (D : HorizonFreePublicDetector baselineLaw comparisonLaw) :
    baselineLaw
        (publicDetectorActivation
          D.cumulative D.incrementBound D.alpha) ≤
      ENNReal.ofReal D.alpha := by
  letI : IsProbabilityMeasure baselineLaw :=
    D.baseline_probability
  exact
    measure_exists_geometricStitchedBoundary_le_of_boundedIncrements
      D.baseline_martingale D.baseline_zero D.alpha_pos
      D.baseline_increment_bound

omit [StandardBorelSpace Ω] in
/-- If the comparison signal eventually dominates twice the boundary, then
failure to activate forces the adverse martingale to cross that same
boundary. -/
theorem compl_activation_subset_adverseCrossing
    (D : HorizonFreePublicDetector baselineLaw comparisonLaw) :
    (publicDetectorActivation
        D.cumulative D.incrementBound D.alpha)ᶜ ⊆
      publicDetectorActivation
        D.adverseNoise D.incrementBound D.alpha := by
  intro ω hnoActivation
  obtain ⟨n, hn, hdominates⟩ :=
    D.eventually_signal_dominates.exists
  by_contra hnoAdverse
  have hadverse :
      D.adverseNoise n ω <
        publicDetectorBoundary D.incrementBound D.alpha n := by
    by_contra hnot
    apply hnoAdverse
    exact ⟨n, hn, le_of_not_gt hnot⟩
  apply hnoActivation
  refine ⟨n, hn, ?_⟩
  have hlower := D.comparisonLower n ω
  linarith

/-- Under the comparison law, the probability of never activating is at
most the adverse-noise budget. -/
theorem comparison_missedActivation_le
    (D : HorizonFreePublicDetector baselineLaw comparisonLaw) :
    comparisonLaw
        (publicDetectorActivation
          D.cumulative D.incrementBound D.alpha)ᶜ ≤
      ENNReal.ofReal D.alpha := by
  letI : IsProbabilityMeasure comparisonLaw :=
    D.comparison_probability
  calc
    comparisonLaw
        (publicDetectorActivation
          D.cumulative D.incrementBound D.alpha)ᶜ ≤
        comparisonLaw
          (publicDetectorActivation
            D.adverseNoise D.incrementBound D.alpha) :=
      measure_mono D.compl_activation_subset_adverseCrossing
    _ ≤ ENNReal.ofReal D.alpha :=
      measure_exists_geometricStitchedBoundary_le_of_boundedIncrements
        D.adverse_martingale D.adverse_zero D.alpha_pos
        D.adverse_increment_bound

/-- Summable epoch budgets give a familywise baseline false-activation
bound for a countable horizon-free detector family. -/
theorem measure_iUnion_baseline_falseActivation_le
    (detector :
      ℕ → HorizonFreePublicDetector baselineLaw comparisonLaw)
    (delta : ℝ≥0∞)
    (hbudget :
      ∑' k, ENNReal.ofReal (detector k).alpha ≤ delta) :
    baselineLaw
        (⋃ k,
          publicDetectorActivation
            (detector k).cumulative
            (detector k).incrementBound
            (detector k).alpha) ≤
      delta := by
  apply measure_iUnion_failure_le
    (fun k =>
      publicDetectorActivation
        (detector k).cumulative
        (detector k).incrementBound
        (detector k).alpha)
    (fun k => ENNReal.ofReal (detector k).alpha)
    delta
  · exact fun k => (detector k).baseline_falseActivation_le
  · exact hbudget

/-- If comparison missed-activation budgets are summable, almost every
comparison path activates in every sufficiently late detector epoch. No
independence between epochs is required. -/
theorem ae_eventually_comparison_activates_of_budget
    (detector :
      ℕ → HorizonFreePublicDetector baselineLaw comparisonLaw)
    (hbudget :
      ∑' k, ENNReal.ofReal (detector k).alpha ≠ ∞) :
    ∀ᵐ ω ∂comparisonLaw,
      ∀ᶠ k in atTop,
        ω ∈ publicDetectorActivation
          (detector k).cumulative
          (detector k).incrementBound
          (detector k).alpha := by
  have hfailure :
      ∀ k,
        comparisonLaw
            (publicDetectorActivation
              (detector k).cumulative
              (detector k).incrementBound
              (detector k).alpha)ᶜ ≤
          ENNReal.ofReal (detector k).alpha :=
    fun k => (detector k).comparison_missedActivation_le
  have hnot :=
    ae_eventually_not_mem_failure_of_budget
      (μ := comparisonLaw)
      (fun k =>
        (publicDetectorActivation
          (detector k).cumulative
          (detector k).incrementBound
          (detector k).alpha)ᶜ)
      (fun k => ENNReal.ofReal (detector k).alpha)
      hfailure hbudget
  filter_upwards [hnot] with ω hω
  filter_upwards [hω] with k hk
  simpa only [mem_compl_iff, not_not] using hk

end HorizonFreePublicDetector

/-! ## Optional stopping-time resets -/

/-- Exact assumptions needed to restart one detector at a stopping time.
They are intentionally the same assumptions consumed by the existing
post-reset stitched theorem. -/
structure PostResetPublicDetector
    [StandardBorelSpace Ω]
    (law : Measure Ω) where
  process : ℕ → Ω → ℝ
  filtration : Filtration ℕ ‹MeasurableSpace Ω›
  reset : Ω → ℕ
  reset_stopping :
    IsStoppingTime filtration (fun ω => (reset ω : ℕ∞))
  postFiltration : Filtration ℕ ‹MeasurableSpace Ω›
  incrementBound : ℝ
  alpha : ℝ
  alpha_pos : 0 < alpha
  probability : IsProbabilityMeasure law
  post_measurable :
    ∀ n, Measurable
      (postResetIncrement process reset n)
  post_martingale :
    ∀ᵐ root ∂law.trim reset_stopping.measurableSpace_le,
      Martingale
        (postResetIncrement process reset)
        postFiltration
        (condExpKernel law
          reset_stopping.measurableSpace root)
  post_increment_bound :
    ∀ n ω,
      processIncrement
          (postResetIncrement process reset) n ω ∈
        Icc (-incrementBound) incrementBound

namespace PostResetPublicDetector

variable [StandardBorelSpace Ω]

/-- A detector restarted at an adaptive stopping time retains the same
unconditional anytime false-activation budget. -/
theorem falseActivation_le
    (D : PostResetPublicDetector (Ω := Ω) baselineLaw) :
    baselineLaw
        {ω | ∃ n, 0 < n ∧
          publicDetectorBoundary
              D.incrementBound D.alpha n ≤
            postResetIncrement
              D.process D.reset n ω} ≤
      ENNReal.ofReal D.alpha := by
  letI : IsProbabilityMeasure baselineLaw :=
    D.probability
  simpa only [publicDetectorBoundary] using
    (measure_exists_geometricStitchedBoundary_postReset_le
      (μ := baselineLaw) (M := D.process)
      (𝒢 := D.filtration) (reset := D.reset)
      D.reset_stopping D.postFiltration D.alpha_pos
      D.post_measurable D.post_martingale
      D.post_increment_bound)

/-- Summable budgets control false activation across an arbitrary countable
family of stopping-time resets; independence is not required. -/
theorem measure_iUnion_falseActivation_le
    (detector :
      ℕ → PostResetPublicDetector (Ω := Ω) baselineLaw)
    (delta : ℝ≥0∞)
    (hbudget :
      ∑' k, ENNReal.ofReal (detector k).alpha ≤ delta) :
    baselineLaw
        (⋃ k,
          {ω | ∃ n, 0 < n ∧
            publicDetectorBoundary
                (detector k).incrementBound
                (detector k).alpha n ≤
              postResetIncrement
                (detector k).process
                (detector k).reset n ω}) ≤
      delta := by
  apply measure_iUnion_failure_le
    (fun k =>
      {ω | ∃ n, 0 < n ∧
        publicDetectorBoundary
            (detector k).incrementBound
            (detector k).alpha n ≤
          postResetIncrement
            (detector k).process
            (detector k).reset n ω})
    (fun k => ENNReal.ofReal (detector k).alpha)
    delta
  · exact fun k => (detector k).falseActivation_le
  · exact hbudget

end PostResetPublicDetector

end StitchedActivation

end StochasticGame
end GameTheory
