/-
Hostile revelation-principle regression.

The original equilibrium plan flips a private Boolean type, so it is visibly
not truthful reporting.  The induced direct mechanism applies that plan after
the report: truth is optimal there, while the false type's opposite report
strictly lowers payoff.
-/

import GameTheory.Mechanism.Revelation
import GameTheory.Core.BayesCorrelated

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

/-! ## Two-player bridge witness -/

def twoPlayerPrior : FinDist (Bool → Bool) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure fun _ => false) (FinDist.pure fun _ => true)

/-- Each player values matching its own type and coordinating with the other
player. Truthful type-contingent play maximizes the first term, while the
second term makes the opponent coordinate observable. -/
@[reducible]
def twoPlayerGame : BayesianGame Bool where
  Ty _ := Bool
  Act _ := Bool
  prior := twoPlayerPrior
  payoff types actions who :=
    (if actions who = types who then 1 else 0) +
      (if actions who = actions (!who) then 1 else 0)

def twoPlayerPlan : Profile twoPlayerGame.signature :=
  fun _ ownType => ownType

/-- The positive Bayes–Nash fixture quantifies deviations by either player;
the other player's type-contingent action remains fixed. -/
theorem twoPlayerPlan_isNash :
    IsNash twoPlayerGame.toForm (euPreference twoPlayerGame.utility)
      twoPlayerPlan := by
  rw [isNash_iff]
  intro who replacement
  rw [euPreference_apply]
  unfold expectedUtility
  rw [BayesianGame.toForm_play, FinDist.expect_map,
    BayesianGame.toForm_play, FinDist.expect_map]
  apply FinDist.expect_mono
  intro types htypes
  simp only [BayesianGame.utility]
  simp only [twoPlayerGame, BayesianGame.actionsOf, twoPlayerPlan,
    Profile.update_same]
  have htypes' : types ∈ twoPlayerPrior.support := htypes
  unfold twoPlayerPrior at htypes'
  have hcases : types = (fun _ => false) ∨ types = (fun _ => true) :=
    (FinDist.mem_support_mix_pure_iff
      (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun _ : Bool => false) (fun _ : Bool => true) types).mp htypes'
  rcases hcases with rfl | rfl <;> cases who <;>
    simp [Profile.update_of_ne, twoPlayerPlan] <;>
      split <;> norm_num

abbrev twoPlayerDirect := twoPlayerGame.toDirectMechanism twoPlayerPlan

/-- A unilateral false-player report change affects that player's compiled
action but leaves the true player's report and action untouched. This is the
`i ≠ who` branch absent from one-player revelation fixtures. -/
theorem twoPlayerDirect_preserves_nonDeviator :
    twoPlayerDirect.choose
          (Profile.update
            (twoPlayerDirect.truthfulReports (fun _ => false)) false true)
          false = true ∧
      twoPlayerDirect.choose
          (Profile.update
            (twoPlayerDirect.truthfulReports (fun _ => false)) false true)
          true = false := by
  constructor <;> rfl

theorem twoPlayerDirect_truthful_isNash :
    IsNash
      (twoPlayerDirect.toBayesianGame twoPlayerGame.prior).toForm
      (euPreference
        (twoPlayerDirect.toBayesianGame twoPlayerGame.prior).utility)
      (twoPlayerDirect.truthfulPlan twoPlayerGame.prior) :=
  twoPlayerGame.revelation_principle twoPlayerPlan twoPlayerPlan_isNash

/-- The same two-player Bayes–Nash plan crosses the deterministic BNE-to-BCE
bridge, rather than relying on a singleton-player recommendation law. -/
theorem twoPlayerRecommendation_isBayesCorrelatedEq :
    twoPlayerGame.IsBayesCorrelatedEq
      (twoPlayerGame.strategyRecommendationLaw twoPlayerPlan) :=
  twoPlayerGame.isBayesCorrelatedEq_strategyRecommendationLaw_of_isNash
    twoPlayerPlan twoPlayerPlan_isNash

end GameTheory.Tests.Revelation
