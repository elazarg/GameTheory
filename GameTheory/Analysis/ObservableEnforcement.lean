/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

import GameTheory.Analysis.Enforcement
import GameTheory.Math.Probability.MonitoredPenalty

/-! # Sound observable deterrence

For fixed compared laws, an automatically collected penalty with no alarms on
admitted observations deters exactly when the mass outside the admitted set
times the penalty covers the gain. A profitable comparison admits some finite
nonnegative sound deterrent exactly when that mass is positive. The admitted
set can contain every permitted strategy's observation support; this does not
construct a monitor implementation or a sequentially consistent assessment.
-/

noncomputable section
namespace GameTheory.Enforcement
open Math.Probability
variable {Outcome Observation : Type*}

/-- The optimal sound alarm deters a comparison at a specified nonnegative
penalty exactly when the detectable mass times that penalty covers the gain. -/
theorem exists_sound_alarm_for_penalty_iff (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (observe : Outcome → Observation) (admitted : Set Observation)
    (permitted : (comparison.prescribed.map observe).support ⊆ admitted)
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base)
    (penalty : ℝ) (nonnegative : 0 ≤ penalty) :
    (∃ alarm : Observation → PMF Bool,
      (∀ observation ∈ admitted, ((alarm observation) true).toReal = 0) ∧
      comparison.Holds (monitoredPayoff base observe alarm penalty)) ↔
        expect comparison.alternative base - expect comparison.prescribed base ≤
          ((comparison.alternative.map observe).toOuterMeasure admittedᶜ).toReal * penalty := by
  constructor
  · rintro ⟨alarm, sound, deters⟩
    have silent : (((comparison.prescribed.map observe).bind alarm) true).toReal = 0 :=
      (alarm_zero_iff _ alarm).mpr (fun observation supported =>
        sound observation (permitted supported))
    have bounded := mul_le_mul_of_nonneg_right
      (detection_le_outside_admitted admitted (comparison.alternative.map observe) alarm sound)
      nonnegative
    replace deters := (IncentiveComparison.holds_iff_of_integrable _ _
      (payoffIntegrable_monitoredPayoff prescribedIntegrable _ _ _)
      (payoffIntegrable_monitoredPayoff alternativeIntegrable _ _ _)).mp deters
    change expect comparison.alternative _ ≤ expect comparison.prescribed _ at deters
    rw [expect_monitoredPayoff _ _ _ _ _ alternativeIntegrable,
      expect_monitoredPayoff _ _ _ _ _ prescribedIntegrable, silent, zero_mul, sub_zero]
      at deters
    linarith
  · intro sufficient
    have silent :
        (((comparison.prescribed.map observe).bind (outsideAlarm admitted)) true).toReal = 0 :=
      (alarm_zero_iff _ _).mpr (fun observation supported =>
        outsideAlarm_sound admitted observation (permitted supported))
    refine ⟨outsideAlarm admitted, outsideAlarm_sound admitted, ?_⟩
    refine (IncentiveComparison.holds_iff_of_integrable _ _
      (payoffIntegrable_monitoredPayoff prescribedIntegrable _ _ _)
      (payoffIntegrable_monitoredPayoff alternativeIntegrable _ _ _)).mpr ?_
    rw [expect_monitoredPayoff _ _ _ _ _ alternativeIntegrable,
      expect_monitoredPayoff _ _ _ _ _ prescribedIntegrable, silent, zero_mul, sub_zero,
      outsideAlarm_probability]
    linarith

/-- For one profitable comparison, a finite nonnegative penalty and a sound
alarm can deter the deviation iff it has positive observable mass outside
the admitted set. This does not give a uniform penalty for a family of deviations. -/
theorem exists_sound_deterrent_iff (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (observe : Outcome → Observation) (admitted : Set Observation)
    (permitted : (comparison.prescribed.map observe).support ⊆ admitted)
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base)
    (profitable : expect comparison.prescribed base < expect comparison.alternative base) :
    (∃ alarm : Observation → PMF Bool, ∃ penalty : ℝ,
      0 ≤ penalty ∧
      (∀ observation ∈ admitted, ((alarm observation) true).toReal = 0) ∧
      comparison.Holds (monitoredPayoff base observe alarm penalty)) ↔
        0 < ((comparison.alternative.map observe).toOuterMeasure admittedᶜ).toReal := by
  constructor
  · rintro ⟨alarm, penalty, nonnegative, sound, deters⟩
    have silent : (((comparison.prescribed.map observe).bind alarm) true).toReal = 0 :=
      (alarm_zero_iff _ alarm).mpr (fun observation supported =>
        sound observation (permitted supported))
    have bounded := detection_le_outside_admitted admitted
      (comparison.alternative.map observe) alarm sound
    have detected_nonnegative :
        0 ≤ (((comparison.alternative.map observe).bind alarm) true).toReal :=
      ENNReal.toReal_nonneg
    replace deters := (IncentiveComparison.holds_iff_of_integrable _ _
      (payoffIntegrable_monitoredPayoff prescribedIntegrable _ _ _)
      (payoffIntegrable_monitoredPayoff alternativeIntegrable _ _ _)).mp deters
    change expect comparison.alternative _ ≤ expect comparison.prescribed _ at deters
    rw [expect_monitoredPayoff _ _ _ _ _ alternativeIntegrable,
      expect_monitoredPayoff _ _ _ _ _ prescribedIntegrable, silent, zero_mul, sub_zero]
      at deters
    have detected : 0 < (((comparison.alternative.map observe).bind alarm) true).toReal := by
      by_contra impossible
      have zero : (((comparison.alternative.map observe).bind alarm) true).toReal = 0 :=
        le_antisymm (le_of_not_gt impossible) detected_nonnegative
      rw [zero, zero_mul, sub_zero] at deters
      exact (not_le_of_gt profitable) deters
    exact detected.trans_le bounded
  · intro positive
    let gain := expect comparison.alternative base - expect comparison.prescribed base
    let probability := ((comparison.alternative.map observe).toOuterMeasure admittedᶜ).toReal
    have probability_positive : 0 < probability := positive
    have gain_positive : 0 < gain := sub_pos.mpr profitable
    have silent :
        (((comparison.prescribed.map observe).bind (outsideAlarm admitted)) true).toReal = 0 :=
      (alarm_zero_iff _ _).mpr (fun observation supported =>
        outsideAlarm_sound admitted observation (permitted supported))
    refine ⟨outsideAlarm admitted, gain / probability,
      (div_pos gain_positive probability_positive).le,
      outsideAlarm_sound admitted, ?_⟩
    refine (IncentiveComparison.holds_iff_of_integrable _ _
      (payoffIntegrable_monitoredPayoff prescribedIntegrable _ _ _)
      (payoffIntegrable_monitoredPayoff alternativeIntegrable _ _ _)).mpr ?_
    rw [expect_monitoredPayoff _ _ _ _ _ alternativeIntegrable,
      expect_monitoredPayoff _ _ _ _ _ prescribedIntegrable, silent, zero_mul, sub_zero,
      outsideAlarm_probability]
    change expect comparison.alternative base - probability * (gain / probability) ≤ _
    rw [mul_div_cancel₀ _ probability_positive.ne']
    dsimp only [gain]
    linarith

end GameTheory.Enforcement
