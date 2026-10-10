/-
# Stability of discrete laws in statistical distance

Pointwise convergence to a normalized PMF is equivalent to convergence in
statistical distance, without finiteness or countability of the carrier.
Pointwise domination gives the distance bound from missing normalization mass.
-/

import GameTheory.Math.Probability.StatisticalDistance
import GameTheory.Math.Probability.Domination

noncomputable section

namespace GameTheory.Math.Probability
open Filter

/-- On discrete probability laws, pointwise convergence implies vanishing total variation. -/
theorem PMFConvergesPointwise.statisticalDistance_tendsto {α : Type*}
    {sequence : ℕ → PMF α} {target : PMF α} (converges : PMFConvergesPointwise sequence target) :
    Filter.Tendsto (fun n => statisticalDistance (sequence n) target) Filter.atTop (nhds 0) := by
  have limit := Filter.Tendsto.sub (f := fun _ : ℕ => (1 : ℝ)) tendsto_const_nhds
    (pmf_overlap_tendsto converges)
  simpa only [statisticalDistance_eq_one_sub_overlap, sub_self] using limit

/-- Native pointwise convergence and vanishing statistical distance agree. -/
theorem pmfConvergesPointwise_iff_statisticalDistance_tendsto {α : Type*}
    {sequence : ℕ → PMF α} {target : PMF α} :
    PMFConvergesPointwise sequence target ↔
      Tendsto (fun n => statisticalDistance (sequence n) target) atTop (nhds 0) := by
  constructor
  · exact PMFConvergesPointwise.statisticalDistance_tendsto
  · intro converges
    apply pmfConvergesPointwise_iff_toReal.mpr
    intro a
    have lower : Tendsto (fun n => (target a).toReal - statisticalDistance (sequence n) target)
        atTop (nhds (target a).toReal) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub converges
    have upper : Tendsto (fun n => (target a).toReal + statisticalDistance (sequence n) target)
        atTop (nhds (target a).toReal) := by
      simpa only [add_zero] using tendsto_const_nhds.add converges
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le lower upper
    · intro n
      have bound := (abs_le.mp (abs_mass_sub_le_statisticalDistance (sequence n) target a)).1
      linarith
    · intro n
      have bound := (abs_le.mp (abs_mass_sub_le_statisticalDistance (sequence n) target a)).2
      linarith

/-- Keeping a fraction of another law loses at most its missing normalization mass. -/
theorem statisticalDistance_le_of_domination {α : Type*} (source target : PMF α)
    (factor : ℝ) (small : factor ≤ 1)
    (lower : ∀ a, factor * (source a).toReal ≤ (target a).toReal) :
    statisticalDistance source target ≤ 1 - factor := by
  apply (statisticalDistance_le_iff _ _ _).mpr
  intro event
  have first := probOf_domination source target factor lower event
  have second := probOf_domination_excess source target factor lower event
  have atMostOne : (source.toOuterMeasure event).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using outerMeasure_le_one source event)
  have missing : (1 - factor) * (source.toOuterMeasure event).toReal ≤ 1 - factor :=
    mul_le_of_le_one_right (sub_nonneg.mpr small) atMostOne
  have scaled : factor * (source.toOuterMeasure event).toReal ≤
      (source.toOuterMeasure event).toReal :=
    mul_le_of_le_one_left ENNReal.toReal_nonneg small
  exact abs_le.mpr ⟨by linarith, by linarith⟩


end GameTheory.Math.Probability
