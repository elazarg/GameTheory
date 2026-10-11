/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

import GameTheory.Math.Probability.Bounds
import GameTheory.Math.Probability.ExpectationAlgebra

/-! # Expected event penalties

A fixed real penalty on an event subtracts that event's probability times the
penalty from expected utility. The bounded charge preserves integrability;
no bound on the base utility and no finite support are required.
-/

noncomputable section
namespace GameTheory.Math.Probability
variable {Outcome : Type*}

/-- Pay the fixed utility penalty precisely on the sanction event. -/
def penalizedPayoff (base : Outcome → ℝ) (sanction : Set Outcome) (penalty : ℝ) :
    Outcome → ℝ := by
  classical
  exact fun outcome => base outcome - if outcome ∈ sanction then penalty else 0

/-- The sanction is bounded, so it preserves integrability of the base utility. -/
theorem payoffIntegrable_penalizedPayoff {law : PMF Outcome} {base : Outcome → ℝ}
    (integrable : PayoffIntegrable law base) (sanction : Set Outcome) (penalty : ℝ) :
    PayoffIntegrable law (penalizedPayoff base sanction penalty) := by
  classical
  unfold penalizedPayoff
  exact payoffIntegrable_sub integrable
    (payoffIntegrable_of_bounded _ _ (C := |penalty|) fun outcome => by split <;> simp)

theorem expect_penalizedPayoff (law : PMF Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome) (penalty : ℝ) (integrable : PayoffIntegrable law base) :
    expect law (penalizedPayoff base sanction penalty) =
      expect law base - (law.toOuterMeasure sanction).toReal * penalty := by
  classical
  unfold penalizedPayoff
  rw [expect_sub integrable
    (payoffIntegrable_of_bounded _ _ (C := |penalty|) fun outcome => by split <;> simp)]
  have amount : (fun outcome => if outcome ∈ sanction then penalty else 0) =
      (fun outcome => penalty * if outcome ∈ sanction then (1 : ℝ) else 0) := by
    funext outcome
    split <;> simp
  rw [amount, expect_const_mul, expect_indicator, mul_comm]

end GameTheory.Math.Probability
