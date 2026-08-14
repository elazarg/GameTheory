/-
# Repeated-play boundary stress test

Two players repeatedly choose booleans and receive one exactly when their stage
choices agree. The hostile profile reads the last public stage and flips it, so
the native recursion is genuinely history-dependent. Its three-stage Protocol
execution is exactly the native public prefix. Separately, stationary repetition
of a stage Nash equilibrium is Nash for normalized discounted utility.
-/

import GameTheory.Repeated

noncomputable section

namespace GameTheory.Tests.Repeated

open GameTheory GameTheory.Probability
open GameTheory.Repeated

/-- A deterministic two-player coordination form. -/
@[reducible]
def coordinationForm : GameForm (Fin 2) where
  sig :=
    { Strategy := fun _ => Bool
      Outcome := Fin 2 → Bool }
  play profile := FinDist.pure profile

/-- Both players receive one when their chosen booleans agree, and zero
otherwise. -/
def coordination : UtilityGame (Fin 2) where
  form := coordinationForm
  utility profile _ := if profile 0 = profile 1 then 1 else 0

instance coordinationStrategyNonempty (i : Fin 2) :
    Nonempty (coordination.form.sig.Strategy i) :=
  ⟨false⟩

theorem coordination_play (profile : Profile coordination.form.sig) :
    coordination.form.play profile = FinDist.pure profile := rfl

@[simp]
theorem coordination_utility (profile : Fin 2 → Bool) (who : Fin 2) :
    coordination.utility profile who =
      if profile 0 = profile 1 then 1 else 0 := rfl

@[simp]
theorem coordination_expectedUtility (profile : Profile coordination.form.sig)
    (who : Fin 2) :
    expectedUtility coordination.utility who (coordination.form.play profile) =
      coordination.utility profile who := by
  rw [coordination_play]
  exact expectedUtility_pure coordination.utility who profile

def allFalse : Profile coordinationForm.sig :=
  fun _ => false

def allTrue : Profile coordinationForm.sig :=
  fun _ => true

/-- Flip player zero's action from the last public stage. The generated path
alternates between the two coordinated profiles. -/
def alternating : coordination.RepeatedProfile :=
  fun _ history =>
    match history.getLast? with
    | none => false
    | some previous => !(previous 0)

/-- The strategy is observably history-dependent. -/
theorem alternating_reads_public_history :
    alternating 0 [allFalse] = true ∧
      alternating 0 [allTrue] = false := by
  constructor <;> rfl

theorem alternating_stage_zero :
    coordination.repeatedPlay alternating 0 = allFalse := by
  rw [UtilityGame.repeatedPlay]
  funext i
  rfl

theorem alternating_stage_one :
    coordination.repeatedPlay alternating 1 = allTrue := by
  rw [UtilityGame.repeatedPlay]
  funext i
  simp [alternating, alternating_stage_zero, allFalse, allTrue]

theorem alternating_stage_two :
    coordination.repeatedPlay alternating 2 = allFalse := by
  rw [UtilityGame.repeatedPlay]
  funext i
  simp [alternating, alternating_stage_zero, alternating_stage_one,
    allFalse, allTrue]

/-- The finite Protocol compiler reproduces the native three-stage public
prefix, including the two history-dependent transitions. -/
theorem alternating_protocol_three :
    (toProtocolForm coordination 3).play
        (policyProfileOfRepeated coordination 3 alternating) =
      FinDist.pure [allFalse, allTrue, allFalse] := by
  rw [toProtocolForm_play_policyProfileOfRepeated]
  congr
  simp only [Prefix.ofPlay, List.ofFn_succ, List.ofFn_zero]
  norm_num
  rw [alternating_stage_zero, alternating_stage_one, alternating_stage_two]
  rfl

/-- Coordinating on `true` is a stage Nash equilibrium. -/
theorem allTrue_isNash :
    IsNash coordination.form (euPreference coordination.utility) allTrue := by
  rw [isNash_iff]
  intro who replacement
  rw [euPreference_apply]
  rw [coordination_expectedUtility, coordination_expectedUtility]
  fin_cases who <;> cases replacement <;>
    simp only [coordination, allTrue] <;>
    split <;> norm_num

/-- Coordination payoffs are uniformly bounded by one. -/
theorem coordination_stagePayoff_bounded :
    ∀ who : Fin 2, ∃ bound : ℝ,
      ∀ stage : Profile coordination.form.sig,
        |coordination.stagePayoff stage who| ≤ bound := by
  intro who
  refine ⟨1, fun stage => ?_⟩
  rw [UtilityGame.stagePayoff, coordination_expectedUtility]
  simp only [coordination]
  split <;> norm_num

/-- Ordinary Nash, not a repeated-specific predicate, states the discounted
equilibrium result. -/
theorem allTrue_stationary_discounted_isNash :
    IsNash coordination.repeatedForm
      (euPreference (coordination.discountedUtility (1 / 2)))
      (coordination.stationaryRepeatedProfile allTrue) := by
  exact coordination.stationaryRepeatedProfile_isNash_of_isNash_of_bounded
    (by norm_num) (by norm_num) allTrue_isNash
      coordination_stagePayoff_bounded

end GameTheory.Tests.Repeated
