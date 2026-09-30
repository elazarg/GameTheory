/-
# Trembling perfectly correlated plans

In the entry-deterrence arena the incumbent's prescribed plans are perfectly
correlated: a fair coin chooses between two whole plans. Trembling each
coordinate independently with mass one half still leaves every choice at every
decision site with at least its share of the tremble in the behavioral reading,
because decision recall keeps the player's own record from restricting the
current coordinate. The floor is strictly positive.
-/

import GameTheory.Analysis.Protocol.SequentialOneShotTest
import GameTheory.Protocol.TremblingPlans

noncomputable section

namespace GameTheory.Tests.TremblingPlans

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Tests.SubgamePerfect GameTheory.Tests.InformationLocalization
open GameTheory.Tests.SequentialOneShot
open InformationModel

local instance : Fintype (model.InformationSite ()) := Fintype.ofFinite _

local instance (site : model.InformationSite ()) : Fintype (model.Choice () site.1) :=
  @Fintype.ofFinite _ (InformationSite.finite_choice (M := model) () site)

/-- A fair coin between the incumbent's two whole plans. -/
def correlatedPlans : PMF (model.DecisionPlan ()) :=
  (PMF.uniformOfFintype Bool).map fun heads =>
    if heads then rewardingPolicy.restrictToDecisions
    else (incumbentProfile ()).restrictToDecisions

theorem half_pos (_ : model.InformationSite ()) : (0 : ℝ) < 1 / 2 := by norm_num

theorem half_le_one (_ : model.InformationSite ()) : (1 / 2 : ℝ) ≤ 1 := by norm_num

/-- The trembled correlated plans, read behaviorally. -/
def trembled : model.MixedPolicy () :=
  trembledMixedPolicy correlatedPlans (fun _ => 1 / 2) (fun site => (half_pos site).le)
    half_le_one rewardingPolicy

theorem trembled_floor (site : model.InformationSite ())
    (choice : model.Choice () site.1) :
    (1 / 2 : ℝ) / Fintype.card (model.Choice () site.1) ≤
      ((trembled.toBehavioralWith rewardingPolicy site.1) choice).toReal :=
  div_card_le_trembledMixedPolicy_toBehavioralWith decisionRecall correlatedPlans
    (fun _ => 1 / 2) half_pos half_le_one rewardingPolicy site choice

theorem trembled_fullSupport (site : model.InformationSite ())
    (choice : model.Choice () site.1) :
    choice ∈ (trembled.toBehavioralWith rewardingPolicy site.1).support := by
  apply (PMF.mem_support_iff _ _).mpr
  intro zero
  have floor := trembled_floor site choice
  rw [zero, ENNReal.toReal_zero] at floor
  exact (floor.trans_lt' (div_pos (by norm_num)
    (Nat.cast_pos.mpr (@Fintype.card_pos _ _ (InformationSite.choice_nonempty site))))).false

end GameTheory.Tests.TremblingPlans
