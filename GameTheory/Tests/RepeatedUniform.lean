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

end GameTheory.Tests.RepeatedUniform
