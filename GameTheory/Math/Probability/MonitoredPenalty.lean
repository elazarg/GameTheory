/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

import GameTheory.Math.Probability.EventPenalty
import GameTheory.Math.Probability.SoundDetection

/-! # Expected penalties from randomized observations

A terminal alarm sees an observation of the outcome. Automatic collection is
an event penalty on the alarm's Boolean response; its expected charge is the
penalty multiplied by alarm probability. This specializes the existing event
penalty and does not assume finite outcome or observation carriers.
-/

noncomputable section
namespace GameTheory.Math.Probability
variable {Outcome Observation : Type*}

/-- Expected payoff after a terminal alarm and automatic collection on a true alarm. -/
abbrev monitoredPayoff (base : Outcome → ℝ) (observe : Outcome → Observation)
    (alarm : Observation → PMF Bool) (penalty : ℝ) (outcome : Outcome) : ℝ :=
  expect (alarm (observe outcome)) (penalizedPayoff (fun _ => base outcome) {true} penalty)

/-- Expected automatic collection subtracts the penalty times the alarm's probability. -/
theorem monitoredPayoff_eq (base : Outcome → ℝ) (observe : Outcome → Observation)
    (alarm : Observation → PMF Bool) (penalty : ℝ) :
    monitoredPayoff base observe alarm penalty =
      fun outcome => base outcome - ((alarm (observe outcome)) true).toReal * penalty := by
  funext outcome
  rw [monitoredPayoff, expect_penalizedPayoff _ _ _ _ (payoffIntegrable_constant _ _),
    expect_constant, PMF.toOuterMeasure_apply_singleton]

/-- The charge is bounded, so it preserves integrability of the base utility. -/
theorem payoffIntegrable_monitoredPayoff {law : PMF Outcome} {base : Outcome → ℝ}
    (integrable : PayoffIntegrable law base) (observe : Outcome → Observation)
    (alarm : Observation → PMF Bool) (penalty : ℝ) :
    PayoffIntegrable law (monitoredPayoff base observe alarm penalty) := by
  rw [monitoredPayoff_eq]
  exact payoffIntegrable_sub integrable
    (payoffIntegrable_of_bounded _ _ (C := |penalty|) fun outcome => by
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_of_le_one_left (abs_nonneg _) (pmf_toReal_apply_le_one _ _))

theorem expect_monitoredPayoff (law : PMF Outcome) (base : Outcome → ℝ)
    (observe : Outcome → Observation) (alarm : Observation → PMF Bool) (penalty : ℝ)
    (integrable : PayoffIntegrable law base) :
    expect law (monitoredPayoff base observe alarm penalty) =
      expect law base - (((law.map observe).bind alarm) true).toReal * penalty := by
  rw [monitoredPayoff_eq, expect_sub integrable
    (payoffIntegrable_of_bounded _ _ (C := |penalty|) fun outcome => by
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_of_le_one_left (abs_nonneg _) (pmf_toReal_apply_le_one _ _))]
  simp_rw [mul_comm _ penalty]
  rw [expect_const_mul, toReal_bind_apply, expect_map]
  rfl

end GameTheory.Math.Probability
