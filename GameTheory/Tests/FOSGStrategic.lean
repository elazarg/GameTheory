/-
# Hostile FOSG strategic-serialization witness

Two real players choose simultaneously, but the EFG serializer must schedule
them in an explicit order.  Each player strictly prefers its own Boolean action
to be `true`.  Thus both unilateral deviation coordinates matter while neither
may observe the other's current choice.  The dominant-action equilibrium and
a profitable-deviation control are checked in the source game and across both
serialization orders.
-/

import GameTheory.Examples.FOSG
import GameTheory.Languages.Bridges.FOSGToEFGStrategic

noncomputable section

namespace GameTheory.Tests.FOSGStrategic

open GameTheory.Languages
open GameTheory.Languages.Bridges
open GameTheory.Languages.NFG.OneShotFOSG
open GameTheory.Probability
open GameTheory.Protocol

abbrev source := GameTheory.Examples.FOSG.twoBit

def trueFirst : FOSGToEFG.ExplicitOrder Bool where
  slots := 2
  player := finTwoEquiv.trans Equiv.boolNot

/-- A deterministic behavioral policy choosing one source action. -/
def actionPolicy (who : Bool) (action : Bool) :
    source.information.BehavioralPolicy who :=
  (Policy.ofAction GameTheory.Examples.FOSG.twoBitSource action).toBehavioral

/-- Lift a simultaneous Boolean action profile to behavioral FOSG play. -/
def behavioralProfile (actions : Bool → Bool) :
    (who : Bool) → source.information.BehavioralPolicy who :=
  fun who => actionPolicy who (actions who)

def allTrueActions : Bool → Bool := fun _ => true

def allFalseActions : Bool → Bool := fun _ => false

/-- Each player values its own coordinate of the simultaneous outcome. -/
def outcomeUtility
    (outcome : GameTheory.Examples.FOSG.twoBitSource.Outcome)
    (who : Bool) : ℝ :=
  if who then (if outcome.2 then 1 else 0)
  else (if outcome.1 then 1 else 0)

@[simp]
theorem outcomeUtility_twoBit (actions : Bool → Bool) (who : Bool) :
    outcomeUtility
        (GameTheory.Examples.FOSG.twoBitSource.outcome actions) who =
      if actions who then 1 else 0 := by
  cases who <;>
    simp [outcomeUtility, GameTheory.Examples.FOSG.twoBitSource]

/-- Utility is external to FOSG syntax and rewards each player's own source
action.  It is total on short histories through `utilityOfOutcome`. -/
def sourceUtility (history : source.History) (who : Bool) : ℝ :=
  utilityOfOutcome GameTheory.Examples.FOSG.twoBitSource
    outcomeUtility
    (outcomeOfState GameTheory.Examples.FOSG.twoBitSource history.state) who

/-- Updating one deterministic behavioral coordinate is the behavioral lift
of updating that player's simultaneous source action. -/
theorem behavioralProfile_update (actions : Bool → Bool)
    (who action : Bool) :
    Profile.update
        (sig := source.information.behavioralSignature)
        (behavioralProfile actions) who (actionPolicy who action) =
      behavioralProfile
        (Profile.update
          (sig := GameTheory.Examples.FOSG.twoBitSource.signature)
          actions who action) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [behavioralProfile, actionPolicy]
  · simp [behavioralProfile, actionPolicy, hplayer]

/-- A deterministic behavioral source profile realizes the utility of the
corresponding simultaneous action profile. -/
theorem expectedUtility_behavioralProfile (actions : Bool → Bool)
    (who : Bool) :
    expectedUtility sourceUtility who
        (source.information.runBehavioral (behavioralProfile actions) 1) =
      if actions who then 1 else 0 := by
  let policies := policyProfile
    GameTheory.Examples.FOSG.twoBitSource actions
  have hbehavioral :
      behavioralProfile actions = fun player => (policies player).toBehavioral :=
    rfl
  rw [hbehavioral,
    ← InformationModel.toBehavioralGameForm_play]
  calc
    expectedUtility sourceUtility who
        ((source.information.toBehavioralGameForm 1).play
          (fun player => (policies player).toBehavioral)) =
      expectedUtility sourceUtility who
        ((source.information.toGameForm 1).play policies) := by
      rw [InformationModel.toBehavioralGameForm_play_toBehavioral]
    _ = expectedUtility
        (utilityOfOutcome GameTheory.Examples.FOSG.twoBitSource
          outcomeUtility) who
        (FinDist.map
          (fun history =>
            outcomeOfState GameTheory.Examples.FOSG.twoBitSource history.state)
          ((source.information.toGameForm 1).play policies)) := by
      rw [expectedUtility_map]
      rfl
    _ = expectedUtility
        (utilityOfOutcome GameTheory.Examples.FOSG.twoBitSource
          outcomeUtility) who
        ((toProtocolForm GameTheory.Examples.FOSG.twoBitSource).play
          (policyProfile GameTheory.Examples.FOSG.twoBitSource actions)) := rfl
    _ = _ := by
      rw [toProtocolForm_play_policyProfile]
      simp only [FinDist.map_pure, expectedUtility_pure, utilityOfOutcome]
      exact outcomeUtility_twoBit actions who

/-- Choosing `true` is a behavioral Nash equilibrium for both simultaneous
players, including against randomized deviations. -/
theorem allTrue_isNash :
    IsNash (source.information.toBehavioralGameForm 1)
      (euPreference sourceUtility) (behavioralProfile allTrueActions) := by
  rw [isNash_iff]
  intro who replacement
  simp only [euPreference_apply]
  calc
    expectedUtility sourceUtility who
        (source.information.runBehavioral
          (Profile.update (behavioralProfile allTrueActions) who replacement)
          1) ≤ 1 :=
      FinDist.expect_le_of_forall _ _ 1 fun history _ => by
        rcases history with ⟨state, trace⟩
        cases state with
        | initial => simp [sourceUtility, utilityOfOutcome, outcomeOfState]
        | finished actions =>
            cases who <;>
              simp only [sourceUtility, utilityOfOutcome, outcomeOfState,
                outcomeUtility, Bool.false_eq_true, if_false, if_true]
            · split <;> norm_num
            · split <;> norm_num
    _ = expectedUtility sourceUtility who
        (source.information.runBehavioral
          (behavioralProfile allTrueActions) 1) := by
      rw [expectedUtility_behavioralProfile]
      simp [allTrueActions]

/-- The all-false control is not Nash: player `false` can change only its own
simultaneous action and raise its payoff from zero to one. -/
theorem allFalse_not_isNash :
    ¬ IsNash (source.information.toBehavioralGameForm 1)
      (euPreference sourceUtility) (behavioralProfile allFalseActions) := by
  intro hnash
  have hdeviation := (isNash_iff _).1 hnash false (actionPolicy false true)
  simp only [euPreference_apply] at hdeviation
  rw [behavioralProfile_update,
    expectedUtility_behavioralProfile,
    expectedUtility_behavioralProfile] at hdeviation
  norm_num [allFalseActions, Profile.update_same] at hdeviation

def falseFirstEquilibrium :=
  FOSGToEFG.translateBehavioral source
    GameTheory.Examples.FOSG.falseFirst
    (behavioralProfile allTrueActions)

def trueFirstEquilibrium :=
  FOSGToEFG.translateBehavioral source trueFirst
    (behavioralProfile allTrueActions)

/-- The equilibrium survives false-first serialization. -/
theorem falseFirstEquilibrium_isNash :
    IsNash
      ((FOSGToEFG.information source
        GameTheory.Examples.FOSG.falseFirst).toBehavioralGameForm 3)
      (euPreference
        (FOSGToEFG.serializedUtility source
          GameTheory.Examples.FOSG.falseFirst sourceUtility))
      falseFirstEquilibrium := by
  exact (FOSGToEFG.isNash_translateBehavioral_iff source
    GameTheory.Examples.FOSG.falseFirst sourceUtility
    (behavioralProfile allTrueActions) 1).2 allTrue_isNash

/-- Reversing the hidden selection order preserves the same source
equilibrium, rather than silently making the earlier mover observable. -/
theorem trueFirstEquilibrium_isNash :
    IsNash
      ((FOSGToEFG.information source trueFirst).toBehavioralGameForm 3)
      (euPreference
        (FOSGToEFG.serializedUtility source trueFirst sourceUtility))
      trueFirstEquilibrium := by
  exact (FOSGToEFG.isNash_translateBehavioral_iff source trueFirst
    sourceUtility (behavioralProfile allTrueActions) 1).2 allTrue_isNash

/-- For translated profiles, Nash status is independent of which explicit
serialization order is chosen. -/
theorem falseFirst_iff_trueFirst :
    IsNash
        ((FOSGToEFG.information source
          GameTheory.Examples.FOSG.falseFirst).toBehavioralGameForm 3)
        (euPreference
          (FOSGToEFG.serializedUtility source
            GameTheory.Examples.FOSG.falseFirst sourceUtility))
        falseFirstEquilibrium ↔
      IsNash
        ((FOSGToEFG.information source trueFirst).toBehavioralGameForm 3)
        (euPreference
          (FOSGToEFG.serializedUtility source trueFirst sourceUtility))
        trueFirstEquilibrium := by
  constructor
  · intro hfalse
    apply (FOSGToEFG.isNash_translateBehavioral_iff source trueFirst
      sourceUtility (behavioralProfile allTrueActions) 1).2
    apply (FOSGToEFG.isNash_translateBehavioral_iff source
      GameTheory.Examples.FOSG.falseFirst sourceUtility
      (behavioralProfile allTrueActions) 1).1
    exact hfalse
  · intro htrue
    apply (FOSGToEFG.isNash_translateBehavioral_iff source
      GameTheory.Examples.FOSG.falseFirst sourceUtility
      (behavioralProfile allTrueActions) 1).2
    apply (FOSGToEFG.isNash_translateBehavioral_iff source trueFirst
      sourceUtility (behavioralProfile allTrueActions) 1).1
    exact htrue

/-- The profitable-deviation control also crosses the serializer. -/
theorem falseFirstAllFalse_not_isNash :
    ¬ IsNash
      ((FOSGToEFG.information source
        GameTheory.Examples.FOSG.falseFirst).toBehavioralGameForm 3)
      (euPreference
        (FOSGToEFG.serializedUtility source
          GameTheory.Examples.FOSG.falseFirst sourceUtility))
      (FOSGToEFG.translateBehavioral source
        GameTheory.Examples.FOSG.falseFirst
        (behavioralProfile allFalseActions)) := by
  intro hserialized
  apply allFalse_not_isNash
  exact (FOSGToEFG.isNash_translateBehavioral_iff source
    GameTheory.Examples.FOSG.falseFirst sourceUtility
    (behavioralProfile allFalseActions) 1).1 hserialized

end GameTheory.Tests.FOSGStrategic
