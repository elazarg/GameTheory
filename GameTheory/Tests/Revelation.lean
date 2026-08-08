/-
Hostile revelation-principle regression.

The original equilibrium plan flips a private Boolean type, so it is visibly
not truthful reporting.  The induced direct mechanism applies that plan after
the report: truth is optimal there, while the false type's opposite report
strictly lowers payoff.
-/

import GameTheory.Mechanism.Revelation

noncomputable section

namespace GameTheory.Tests.Revelation

open Probability Languages

def falseTypes : Unit → Bool := fun _ => false

def trueTypes : Unit → Bool := fun _ => true

def prior : FinDist (Unit → Bool) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure falseTypes) (FinDist.pure trueTypes)

@[reducible]
def game : BayesianGame Unit where
  Ty _ := Bool
  Act _ := Bool
  prior := prior
  payoff types actions _ := if actions () = !types () then 2 else 0

/-- The nontruthful plan that is optimal in the original game. -/
def equilibriumPlan : Profile game.signature :=
  fun _ ownType => !ownType

theorem equilibriumPlan_is_not_identity : equilibriumPlan () false = true :=
  rfl

theorem equilibriumPlan_isNash :
    IsNash game.toForm (euPreference game.utility) equilibriumPlan := by
  rw [isNash_iff]
  intro who replacement
  cases who
  rw [euPreference_apply]
  unfold expectedUtility
  rw [BayesianGame.toForm_play, FinDist.expect_map,
    BayesianGame.toForm_play, FinDist.expect_map]
  apply FinDist.expect_mono
  intro types _
  simp only [BayesianGame.utility]
  simp only [game, BayesianGame.actionsOf, equilibriumPlan,
    Profile.update_same]
  split <;> norm_num

abbrev direct := game.toDirectMechanism equilibriumPlan

theorem direct_truthful_false_chooses_true :
    direct.choose (direct.truthfulReports falseTypes) = fun _ => true := by
  funext who
  cases who
  rfl

theorem false_type_truth_strictly_beats_opposite_report :
    direct.utility falseTypes
          (direct.choose (direct.truthfulReports falseTypes)) () = 2 ∧
      direct.utility falseTypes
          (direct.choose
            (Profile.update (direct.truthfulReports falseTypes) () true)) () = 0 := by
  constructor <;> rfl

/-- The public theorem packages the induced direct mechanism through the same
canonical Bayes-Nash surface used by the original game. -/
theorem direct_truthful_isNash :
    IsNash (direct.toBayesianGame game.prior).toForm
      (euPreference (direct.toBayesianGame game.prior).utility)
      (direct.truthfulPlan game.prior) :=
  game.revelation_principle equilibriumPlan equilibriumPlan_isNash

end GameTheory.Tests.Revelation
