/-
# Uniform-equilibrium fixture

Mutual defection in Prisoner's Dilemma is stationary uniform equilibrium.  In
contrast, stationary cooperation already fails one-stage approximate Nash at
slack one, where a permanent defection gains two.
-/

import GameTheory.Examples.Classic
import GameTheory.Repeated.Uniform

namespace GameTheory.Tests.RepeatedUniform

open GameTheory GameTheory.Examples GameTheory.Finite

theorem prisonersDilemma_defect_isUniformEquilibrium :
    prisonersDilemmaGame.IsUniformEquilibrium
      (prisonersDilemmaGame.stationaryRepeatedProfile bothDefect) :=
  prisonersDilemmaGame.stationaryRepeatedProfile_isUniformEquilibrium_of_isNash
    prisonersDilemmaGame_bothDefect_isNash

def permanentDefection : prisonersDilemmaGame.RepeatedStrategy 0 :=
  fun _ => .defect

theorem prisonersDilemma_cooperate_not_oneStageApproximateNash :
    ¬ prisonersDilemmaGame.IsεFiniteRepeatedNash 1 1
      (prisonersDilemmaGame.stationaryRepeatedProfile bothCooperate) := by
  intro happroximate
  have hdeviation :=
    (prisonersDilemmaGame.isεFiniteRepeatedNash_iff).1 happroximate
      0 permanentDefection
  rw [UtilityGame.finiteAveragePayoff_one,
    prisonersDilemmaGame.repeatedPlay_update_stationaryRepeatedProfile,
    UtilityGame.finiteAveragePayoff_one,
    prisonersDilemmaGame.repeatedPlay_stationaryRepeatedProfile] at hdeviation
  simp only [UtilityGame.stagePayoff, permanentDefection,
    prisonersDilemmaGame] at hdeviation
  rw [expectedUtility_pure, expectedUtility_pure,
    TableGame.utility_apply, TableGame.utility_apply] at hdeviation
  have hdeviationPayoff :
      prisonersDilemma.payoff
        (Profile.update bothCooperate 0 Choice.defect) 0 = 5 := by
    decide
  have hcooperationPayoff :
      prisonersDilemma.payoff bothCooperate 0 = 3 := by
    decide
  rw [hdeviationPayoff, hcooperationPayoff] at hdeviation
  norm_num at hdeviation

theorem prisonersDilemma_cooperate_not_approximateNash
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    ¬ prisonersDilemmaGame.IsεFiniteRepeatedNash horizon 1
      (prisonersDilemmaGame.stationaryRepeatedProfile bothCooperate) := by
  intro happroximate
  have hdeviation :=
    (prisonersDilemmaGame.isεFiniteRepeatedNash_iff).1 happroximate
      0 permanentDefection
  have hprofile :
      Profile.update
          (prisonersDilemmaGame.stationaryRepeatedProfile bothCooperate)
          0 permanentDefection =
        prisonersDilemmaGame.stationaryRepeatedProfile
          (Profile.update bothCooperate 0 Choice.defect) := by
    funext who history
    fin_cases who <;>
      simp [permanentDefection, UtilityGame.stationaryRepeatedProfile,
        Profile.update]
  have hdeviationPayoff :
      prisonersDilemmaGame.finiteAveragePayoff horizon
          (Profile.update
            (prisonersDilemmaGame.stationaryRepeatedProfile bothCooperate)
            0 permanentDefection) 0 = 5 := by
    rw [hprofile,
      prisonersDilemmaGame.finiteAveragePayoff_stationaryRepeatedProfile
        (by omega)]
    have hstage :
        prisonersDilemmaGame.stagePayoff
          (Profile.update bothCooperate 0 Choice.defect) 0 = 5 := by
      simp only [UtilityGame.stagePayoff, prisonersDilemmaGame]
      rw [expectedUtility_pure, TableGame.utility_apply]
      have hpayoff :
          prisonersDilemma.payoff
            (Profile.update bothCooperate 0 Choice.defect) 0 = 5 := by
        decide
      rw [hpayoff]
      norm_num
    exact hstage
  have hcooperationPayoff :
      prisonersDilemmaGame.finiteAveragePayoff horizon
          (prisonersDilemmaGame.stationaryRepeatedProfile bothCooperate) 0 = 3 := by
    rw [prisonersDilemmaGame.finiteAveragePayoff_stationaryRepeatedProfile
      (by omega)]
    simp only [UtilityGame.stagePayoff, prisonersDilemmaGame]
    rw [expectedUtility_pure, TableGame.utility_apply]
    have hpayoff : prisonersDilemma.payoff bothCooperate 0 = 3 := by
      decide
    rw [hpayoff]
    norm_num
  rw [hdeviationPayoff, hcooperationPayoff] at hdeviation
  norm_num at hdeviation

/-- Stationary cooperation fails the defining uniform approximation clause,
not merely one short truncation. -/
theorem prisonersDilemma_cooperate_not_isUniformEquilibrium :
    ¬ prisonersDilemmaGame.IsUniformEquilibrium
      (prisonersDilemmaGame.stationaryRepeatedProfile bothCooperate) := by
  intro huniform
  obtain ⟨_, happroximate⟩ := huniform
  obtain ⟨threshold, hthreshold⟩ := happroximate 1 (by norm_num)
  let horizon := max threshold 1
  exact prisonersDilemma_cooperate_not_approximateNash horizon (by
    dsimp [horizon]
    omega) (hthreshold horizon (by
      dsimp [horizon]
      omega))

end GameTheory.Tests.RepeatedUniform
