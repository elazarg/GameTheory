/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

import GameTheory.Math.Probability.Bounds
import GameTheory.Math.Probability.ExpectationAlgebra

/-! # Sound randomized detection

Silence under all permitted laws is silence on the union of their supports.
A sound randomized alarm can detect at most the mass outside the admitted
set. One deterministic outside-set alarm attains this bound for every law;
this is an existence result, not an executable membership test for arbitrary sets.
-/

noncomputable section
namespace GameTheory.Math.Probability
variable {Outcome Observation Index : Type*}

private theorem atom_zero_iff {α : Type*} (law : PMF α) (a : α) :
    (law a).toReal = 0 ↔ a ∉ law.support := by
  rw [← pmf_toReal_pos_iff]
  exact ⟨fun zero => by simp only [zero, lt_self_iff_false, not_false_eq_true],
    fun absent => le_antisymm (le_of_not_gt absent) ENNReal.toReal_nonneg⟩

/-- Zero false positives require the alarm to stay silent at every observation
with positive lawful probability, even when the alarm itself randomizes. -/
theorem alarm_zero_iff (lawful : PMF Outcome) (alarm : Outcome → PMF Bool) :
    ((lawful.bind alarm) true).toReal = 0 ↔
      ∀ outcome ∈ lawful.support, ((alarm outcome) true).toReal = 0 := by
  simp only [atom_zero_iff, PMF.mem_support_bind_iff]
  constructor
  · intro silent outcome supported reported
    exact silent ⟨outcome, supported, reported⟩
  · rintro silent ⟨outcome, supported, reported⟩
    exact silent outcome supported reported

/-- Soundness for all permitted laws is exactly pointwise silence on the
union of their supports. This includes all permitted choices, not just the
chosen equilibrium's observations. -/
theorem sound_for_family_iff (permitted : Index → PMF Observation)
    (alarm : Observation → PMF Bool) :
    (∀ index, (((permitted index).bind alarm) true).toReal = 0) ↔
      ∀ observation ∈ ⋃ index, (permitted index).support,
        ((alarm observation) true).toReal = 0 := by
  simp only [alarm_zero_iff, Set.mem_iUnion, forall_exists_index]
  constructor <;> intro sound first second supported <;> exact sound second first supported

/-- Detection cannot exceed the deviating mass outside the admitted set. -/
theorem detection_le_outside_admitted (admitted : Set Observation)
    (law : PMF Observation) (alarm : Observation → PMF Bool)
    (sound : ∀ observation ∈ admitted, ((alarm observation) true).toReal = 0) :
    ((law.bind alarm) true).toReal ≤ (law.toOuterMeasure admittedᶜ).toReal := by
  classical
  rw [toReal_bind_apply, ← expect_indicator]
  apply expect_mono _
    (payoffIntegrable_of_bounded _ _ (C := 1) fun observation => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact pmf_toReal_apply_le_one _ _)
    (payoffIntegrable_of_bounded _ _ (C := 1) fun observation => by split <;> simp)
  intro observation _
  by_cases allowed : observation ∈ admitted
  · rw [sound observation allowed]
    simp [allowed]
  · simp only [Set.mem_compl_iff, allowed, not_false_eq_true, ite_true]
    exact pmf_toReal_apply_le_one (alarm observation) true

/-- The deterministic alarm fires exactly outside the admitted observation set. -/
def outsideAlarm (admitted : Set Observation) (observation : Observation) : PMF Bool := by
  classical
  exact PMF.pure (decide (observation ∉ admitted))

theorem outsideAlarm_sound (admitted : Set Observation) :
    ∀ observation ∈ admitted, ((outsideAlarm admitted observation) true).toReal = 0 := by
  intro observation allowed
  simp [outsideAlarm, allowed]

theorem outsideAlarm_probability (admitted : Set Observation) (law : PMF Observation) :
    ((law.bind (outsideAlarm admitted)) true).toReal = (law.toOuterMeasure admittedᶜ).toReal := by
  classical
  rw [toReal_bind_apply, ← expect_indicator]
  apply expect_congr_on_support
  intro observation _
  by_cases allowed : observation ∈ admitted <;>
    simp [outsideAlarm, allowed]

end GameTheory.Math.Probability
