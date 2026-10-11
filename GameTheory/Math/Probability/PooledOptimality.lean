import GameTheory.Math.Probability.ExpectationAlgebra
import Mathlib.Tactic.Linarith
/-! # Individual bounds from aggregate comparisons

When members share a near-maximizing action, an aggregate payoff comparison
bounds each member's weighted regret. Nonnegative weights may vanish, so only
positive-weight members yield an unweighted rationality bound. The aggregate
comparison may itself have an error. The action space is arbitrary and only
the compared response means require integrability.
-/

noncomputable section
namespace GameTheory.Math.Probability

/-- A common near-maximizer and an aggregate comparison bound control each member's
weighted regret. Only the compared means must be integrable; actions may be infinite.
Zero member weights impose no individual rationality claim. -/
theorem weighted_member_gain_le_of_common_best {Member Part : Type*}
    (members : Finset Member) (weight : Member → ℝ) (value : Member → Part → ℝ)
    (current : PMF Part) (best : Part) (error tolerance : ℝ)
    (nonnegative : ∀ member ∈ members, 0 ≤ weight member)
    (currentIntegrable : ∀ member ∈ members, PayoffIntegrable current (value member))
    (nearBest : ∀ member ∈ members, ∀ part, value member part ≤ value member best + error)
    (aggregate : ∑ member ∈ members,
      weight member * (value member best - expect current (value member)) ≤ tolerance)
    {chosen : Member} (present : chosen ∈ members) (alternative : PMF Part)
    (alternativeIntegrable : PayoffIntegrable alternative (value chosen)) :
    weight chosen * (expect alternative (value chosen) - expect current (value chosen)) ≤
      tolerance + (∑ member ∈ members, weight member) * error := by
  classical
  let gap (member : Member) := value member best + error - expect current (value member)
  have gapNonnegative (member : Member) (inside : member ∈ members) : 0 ≤ gap member :=
    sub_nonneg.mpr (expect_le_const current _ (currentIntegrable member inside) _
      (fun part _ => nearBest member inside part))
  have alternativeBound : expect alternative (value chosen) ≤ value chosen best + error :=
    expect_le_const alternative _ alternativeIntegrable _ (fun part _ => nearBest chosen present part)
  have single : weight chosen * gap chosen ≤ ∑ member ∈ members, weight member * gap member :=
    Finset.single_le_sum (fun member inside => mul_nonneg (nonnegative member inside)
      (gapNonnegative member inside)) present
  have total : (∑ member ∈ members, weight member * gap member) =
      (∑ member ∈ members, weight member * (value member best - expect current (value member))) +
        (∑ member ∈ members, weight member) * error := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro member _
    dsimp only [gap]
    ring
  have individual := mul_le_mul_of_nonneg_left
    (sub_le_sub_right alternativeBound (expect current (value chosen))) (nonnegative chosen present)
  exact individual.trans (single.trans (total.le.trans (add_le_add aggregate le_rfl)))

/-- Unit member weights specialize the weighted bound to cardinality times common-action error. -/
theorem member_gain_le_of_common_best {Member Part : Type*}
    (members : Finset Member) (value : Member → Part → ℝ) (current : PMF Part)
    (best : Part) (error tolerance : ℝ)
    (currentIntegrable : ∀ member ∈ members, PayoffIntegrable current (value member))
    (nearBest : ∀ member ∈ members, ∀ part, value member part ≤ value member best + error)
    (aggregate : ∑ member ∈ members,
      (value member best - expect current (value member)) ≤ tolerance)
    {chosen : Member} (present : chosen ∈ members) (alternative : PMF Part)
    (alternativeIntegrable : PayoffIntegrable alternative (value chosen)) :
    expect alternative (value chosen) - expect current (value chosen) ≤
      tolerance + members.card * error := by
  have bound := weighted_member_gain_le_of_common_best members (fun _ => 1) value current best
    error tolerance (fun _ _ => zero_le_one) currentIntegrable nearBest
    (by simpa only [one_mul] using aggregate) present alternative alternativeIntegrable
  simpa only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] using bound

end GameTheory.Math.Probability
