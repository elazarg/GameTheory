/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.OnlineLearning.CompletedEpochCalendar
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Limits of the anytime logarithmic calendar

The epoch containing a calendar time tends to infinity, so the universal
scale read at every calendar time — not only at epoch indices — tends to
zero while staying positive.  Consequently any implementation cost vanishing
with the analytic parameter has vanishing calendar average, including over
unfinished epochs.
-/

noncomputable section

open scoped Topology

namespace Math
namespace OnlineLearning

open Filter

/-- The epoch containing calendar time `t` tends to infinity. -/
theorem tendsto_anytimeEpochIndex :
    Tendsto anytimeEpochIndex atTop atTop := by
  refine tendsto_atTop.2 fun K => ?_
  filter_upwards
    [eventually_ge_atTop
      (epochStart anytimeEpochLength K)] with t ht
  exact anytimeEpochIndex_ge_of_start_le ht

/-- The universal scale also tends to zero when read at every calendar time,
not just at epoch indices. -/
theorem tendsto_universalEpochScale_anytimeEpochIndex :
    Tendsto
      (fun t => universalEpochScale (anytimeEpochIndex t))
      atTop (𝓝 0) :=
  tendsto_universalEpochScale.comp tendsto_anytimeEpochIndex

/-- The calendar scale stays positive at every calendar time. -/
theorem universalEpochScale_anytimeEpochIndex_pos (t : ℕ) :
    0 < universalEpochScale (anytimeEpochIndex t) :=
  universalEpochScale_pos _

/-- Average implementation cost accumulated by the universal calendar. -/
def universalCalendarImplementationCostAverage
    (cost : ℝ → ℝ) (T : ℕ) : ℝ :=
  (T : ℝ)⁻¹ *
    ∑ t ∈ Finset.range T,
      cost (universalEpochScale (anytimeEpochIndex t))

/-- Any implementation cost which vanishes with the analytic parameter has
vanishing average cost at every calendar horizon, including unfinished
epochs. -/
theorem tendsto_universalCalendarImplementationCostAverage
    (cost : ℝ → ℝ)
    (hcost : Tendsto cost (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto
      (universalCalendarImplementationCostAverage cost)
      atTop (𝓝 0) := by
  have hscale :
      Tendsto
        (fun t => universalEpochScale (anytimeEpochIndex t))
        atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact
      ⟨tendsto_universalEpochScale_anytimeEpochIndex,
        Filter.Eventually.of_forall
          universalEpochScale_anytimeEpochIndex_pos⟩
  have hperRound :
      Tendsto
        (fun t =>
          cost (universalEpochScale (anytimeEpochIndex t)))
        atTop (𝓝 0) :=
    hcost.comp hscale
  change
    Tendsto
      (fun T : ℕ =>
        (T : ℝ)⁻¹ *
          ∑ t ∈ Finset.range T,
            cost (universalEpochScale (anytimeEpochIndex t)))
      atTop (𝓝 0)
  exact hperRound.cesaro

end OnlineLearning
end Math
