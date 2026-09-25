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
open GameTheory.Math.Probability
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
    simp [outcomeUtility, GameTheory.Examples.FOSG.twoBitSource] <;>
    rfl

/-- Utility is external to FOSG syntax and rewards each player's own source
action.  It is total on short histories through `utilityOfOutcome`. -/
def sourceUtility (history : source.History) (who : Bool) : ℝ :=
  utilityOfOutcome GameTheory.Examples.FOSG.twoBitSource
    outcomeUtility
    (outcomeOfState GameTheory.Examples.FOSG.twoBitSource history.state) who

private theorem outcomeUtility_abs_le_one
    (outcome : GameTheory.Examples.FOSG.twoBitSource.Outcome) (who : Bool) :
    |outcomeUtility outcome who| ≤ 1 := by
  cases outcome with
  | mk left right =>
      cases who <;> cases left <;> cases right <;>
        norm_num [outcomeUtility]

private theorem sourceUtility_abs_le_one (history : source.History) (who : Bool) :
    |sourceUtility history who| ≤ 1 := by
  rcases history with ⟨state, trace⟩
  cases state with
  | initial => norm_num [sourceUtility, utilityOfOutcome, outcomeOfState]
  | finished actions =>
      cases who <;>
        simp only [sourceUtility, utilityOfOutcome, outcomeOfState,
          outcomeUtility, Bool.false_eq_true, ite_false, ite_true] <;>
        split <;> norm_num

theorem sourceUtility_integrable (law : PMF source.History) (who : Bool) :
    UtilityIntegrable sourceUtility who law :=
  payoffIntegrable_of_bounded law _ (C := 1)
    (fun history => by simpa using sourceUtility_abs_le_one history who)

private theorem outcomeUtility_integrable
    (law : PMF GameTheory.Examples.FOSG.twoBitSource.Outcome) (who : Bool) :
    UtilityIntegrable outcomeUtility who law :=
  payoffIntegrable_of_bounded law _ (C := 1)
    (fun outcome => outcomeUtility_abs_le_one outcome who)

private theorem optionalOutcomeUtility_integrable
    (law : PMF (Option GameTheory.Examples.FOSG.twoBitSource.Outcome))
    (who : Bool) : UtilityIntegrable
      (utilityOfOutcome GameTheory.Examples.FOSG.twoBitSource outcomeUtility)
      who law := by
  apply payoffIntegrable_of_bounded law _ (C := 1)
  intro outcome
  cases outcome with
  | none => norm_num [utilityOfOutcome]
  | some outcome => simpa [utilityOfOutcome] using
      outcomeUtility_abs_le_one outcome who

private theorem source_expectedUtility_le_one
    (law : PMF source.History) (who : Bool)
    (hintegrable : UtilityIntegrable sourceUtility who law) :
    expectedUtility sourceUtility who law hintegrable ≤ 1 := by
  have hconstant : PayoffIntegrable law (fun _ => (1 : ℝ)) :=
    payoffIntegrable_of_bounded law _ (C := 1) (fun _ => by norm_num)
  calc
    _ ≤ expect law (fun _ => 1) hconstant :=
      expect_mono (fun history _ => (abs_le.mp
        (sourceUtility_abs_le_one history who)).2) hintegrable hconstant
    _ = 1 := expect_constant law 1 hconstant

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
/-- A deterministic behavioral source profile realizes the utility of the
corresponding simultaneous action profile. -/
theorem expectedUtility_behavioralProfile (actions : Bool → Bool)
    (who : Bool) :
    expectedUtility sourceUtility who
        (source.information.runBehavioral (behavioralProfile actions) 1)
        (sourceUtility_integrable _ who) =
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
          (fun player => (policies player).toBehavioral))
        (sourceUtility_integrable _ who) =
      expectedUtility sourceUtility who
        ((source.information.toGameForm 1).play policies)
        (sourceUtility_integrable _ who) := by
      rw [InformationModel.toBehavioralGameForm_play_toBehavioral]
    _ = expectedUtility
        (utilityOfOutcome GameTheory.Examples.FOSG.twoBitSource
          outcomeUtility) who
        (PMF.map
          (fun history =>
            outcomeOfState GameTheory.Examples.FOSG.twoBitSource history.state)
          ((source.information.toGameForm 1).play policies))
        (optionalOutcomeUtility_integrable _ who) := by
      rw [expectedUtility_map]
      rfl
    _ = expectedUtility
        (utilityOfOutcome GameTheory.Examples.FOSG.twoBitSource
          outcomeUtility) who
        ((toProtocolForm GameTheory.Examples.FOSG.twoBitSource).play
          (policyProfile GameTheory.Examples.FOSG.twoBitSource actions))
        (optionalOutcomeUtility_integrable _ who) := rfl
    _ = _ := by
      rw [toProtocolForm_play_policyProfile]
      simp [PMF.pure_map, expectedUtility_pure, utilityOfOutcome]

/-- Choosing `true` is a behavioral Nash equilibrium for both simultaneous
players, including against randomized deviations. -/
theorem allTrue_isNash :
    IsNash (source.information.toBehavioralGameForm 1)
      (euPreference sourceUtility) (behavioralProfile allTrueActions) := by
  rw [isNash_iff]
  intro who replacement
  have hpreferred := sourceUtility_integrable
    (source.information.runBehavioral (behavioralProfile allTrueActions) 1) who
  have halternative := sourceUtility_integrable
    (source.information.runBehavioral
      (Profile.update (behavioralProfile allTrueActions) who replacement) 1) who
  refine ⟨hpreferred, halternative, ?_⟩
  have hpreferredValue : expectedUtility sourceUtility who
      (source.information.runBehavioral (behavioralProfile allTrueActions) 1)
      hpreferred = 1 := by
    calc
      _ = expectedUtility sourceUtility who
          (source.information.runBehavioral
            (behavioralProfile allTrueActions) 1)
          (sourceUtility_integrable _ who) :=
        expectedUtility_congr_law sourceUtility who rfl hpreferred
          (sourceUtility_integrable _ who)
      _ = 1 := by
        rw [expectedUtility_behavioralProfile]
        simp [allTrueActions]
  calc
    _ ≤ 1 := source_expectedUtility_le_one _ who halternative
    _ = expectedUtility sourceUtility who
        (source.information.runBehavioral (behavioralProfile allTrueActions) 1)
        hpreferred := hpreferredValue.symm

set_option backward.isDefEq.respectTransparency false in
/-- The all-false control is not Nash: player `false` can change only its own
simultaneous action and raise its payoff from zero to one. -/
theorem allFalse_not_isNash :
    ¬ IsNash (source.information.toBehavioralGameForm 1)
      (euPreference sourceUtility) (behavioralProfile allFalseActions) := by
  intro hnash
  rcases (isNash_iff _).1 hnash false (actionPolicy false true) with
    ⟨hpreferred, halternative, hle⟩
  let deviatedActions : Bool → Bool :=
    Profile.update (sig := GameTheory.Examples.FOSG.twoBitSource.signature)
      allFalseActions false true
  have hdeviationLaw :
      (source.information.toBehavioralGameForm 1).play
          (Profile.update (behavioralProfile allFalseActions) false
            (actionPolicy false true)) =
        source.information.runBehavioral (behavioralProfile deviatedActions) 1 := by
    rw [InformationModel.toBehavioralGameForm_play,
      behavioralProfile_update allFalseActions false true]
  have hpreferredValue := expectedUtility_behavioralProfile allFalseActions false
  have hdeviationValue := expectedUtility_behavioralProfile deviatedActions false
  have hle' : expectedUtility sourceUtility false
      (source.information.runBehavioral (behavioralProfile deviatedActions) 1)
      (payoffIntegrable_congr_law hdeviationLaw halternative) ≤
    expectedUtility sourceUtility false
      (source.information.runBehavioral (behavioralProfile allFalseActions) 1)
      hpreferred := by
    exact hle
  rw [hdeviationValue, hpreferredValue] at hle'
  norm_num [allFalseActions, deviatedActions, Profile.update_same] at hle'

def falseFirstEquilibrium :=
  FOSGToEFG.translateBehavioral source
    GameTheory.Examples.FOSG.falseFirst
    (behavioralProfile allTrueActions)

def trueFirstEquilibrium :=
  FOSGToEFG.translateBehavioral source trueFirst
    (behavioralProfile allTrueActions)

/-- One complete serialized round has exactly the source support after
erasure; the witness is stated at the public runner rather than only as a law
equality. -/
theorem falseFirst_one_round_support (sourceReached : source.History) :
    sourceReached ∈
        (source.information.runBehavioral
          (behavioralProfile allTrueActions) 1).support ↔
      ∃ targetReached ∈
          ((FOSGToEFG.information source
            GameTheory.Examples.FOSG.falseFirst).runBehavioral
            falseFirstEquilibrium 3).support,
        FOSGToEFG.eraseHistory source
          GameTheory.Examples.FOSG.falseFirst targetReached = sourceReached := by
  have hsupport := FOSGToEFG.mem_support_runBehavioral_projected_iff
    source GameTheory.Examples.FOSG.falseFirst falseFirstEquilibrium 1
    sourceReached
  unfold falseFirstEquilibrium at hsupport
  rw [FOSGToEFG.project_translate_profile] at hsupport
  unfold falseFirstEquilibrium
  simpa [GameTheory.Examples.FOSG.falseFirst, FOSGToEFG.roundWidth] using
    hsupport

/-- Supported histories after a whole serialized round are genuine source
round boundaries, so they can seed the public continuation theorem. -/
theorem falseFirst_one_round_ends_at_boundary
    {reached : (FOSGToEFG.execution source
      GameTheory.Examples.FOSG.falseFirst).History}
    (hreached : reached ∈
      ((FOSGToEFG.information source
        GameTheory.Examples.FOSG.falseFirst).runBehavioral
        falseFirstEquilibrium 3).support) :
    ∃ sourceHistory : source.History,
      reached.state = FOSGToEFG.State.stage sourceHistory 0
        (FOSGToEFG.Prefix.initial (G := source)
          (order := GameTheory.Examples.FOSG.falseFirst) sourceHistory) := by
  simpa [GameTheory.Examples.FOSG.falseFirst, FOSGToEFG.roundWidth] using
    FOSGToEFG.state_of_mem_runBehavioral_rounds source
      GameTheory.Examples.FOSG.falseFirst falseFirstEquilibrium 1
      hreached

/-- Terminal support is preserved by a complete serialized round. -/
theorem falseFirst_terminal_support_iff :
    (∃ targetReached ∈
        ((FOSGToEFG.information source
          GameTheory.Examples.FOSG.falseFirst).runBehavioral
          falseFirstEquilibrium 3).support,
      (FOSGToEFG.execution source
        GameTheory.Examples.FOSG.falseFirst).terminal targetReached.state) ↔
      ∃ sourceReached ∈
        (source.information.runBehavioral
          (behavioralProfile allTrueActions) 1).support,
        source.execution.terminal sourceReached.state := by
  have hsupport := FOSGToEFG.exists_terminal_mem_support_runBehavioral_iff
    source GameTheory.Examples.FOSG.falseFirst falseFirstEquilibrium 1
  unfold falseFirstEquilibrium at hsupport
  rw [FOSGToEFG.project_translate_profile] at hsupport
  unfold falseFirstEquilibrium
  simpa [GameTheory.Examples.FOSG.falseFirst, FOSGToEFG.roundWidth] using
    hsupport

/-- The source one-shot game has a genuinely supported terminal history after
one round. -/
theorem allTrue_has_terminal_support :
    ∃ sourceReached ∈
        (source.information.runBehavioral
          (behavioralProfile allTrueActions) 1).support,
      source.execution.terminal sourceReached.state := by
  let law := source.information.runBehavioral
    (behavioralProfile allTrueActions) 1
  obtain ⟨sourceReached, hreached⟩ := law.support_nonempty
  refine ⟨sourceReached, hreached, ?_⟩
  have hinit : ¬ source.execution.terminal
      source.execution.initHistory.state := by
    simp [source, NFG.OneShotFOSG.execution,
      ExecutionProtocol.initHistory]
  unfold law InformationModel.runBehavioral at hreached
  rw [show 1 = 0 + 1 by omega,
    source.information.runBehavioralFrom_succ_of_not_terminal
      (behavioralProfile allTrueActions) 0 hinit] at hreached
  simp only [PMF.support_bind, PMF.support_bindOnSupport,
    Set.mem_iUnion] at hreached
  obtain ⟨draw, _, target, htarget, hfinal⟩ := hreached
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_zero,
    PMF.mem_support_pure_iff] at hfinal
  subst sourceReached
  have htargetTerm : source.execution.terminal target := by
    cases target with
    | initial =>
        simp [NFG.OneShotFOSG.execution] at htarget
    | finished actions =>
        simp
  exact htargetTerm

/-- The positive terminal witness crosses the serializer; this rules out a
vacuous terminal-support equivalence. -/
theorem falseFirst_has_terminal_support :
    ∃ targetReached ∈
        ((FOSGToEFG.information source
          GameTheory.Examples.FOSG.falseFirst).runBehavioral
          falseFirstEquilibrium 3).support,
      (FOSGToEFG.execution source
        GameTheory.Examples.FOSG.falseFirst).terminal targetReached.state :=
  falseFirst_terminal_support_iff.mpr allTrue_has_terminal_support

/-- Zero target microsteps are a nearby negative control: the serialized root
is not terminal before a source round has been resolved. -/
theorem falseFirst_no_terminal_support_at_zero :
    ¬ ∃ targetReached ∈
        ((FOSGToEFG.information source
          GameTheory.Examples.FOSG.falseFirst).runBehavioral
          falseFirstEquilibrium 0).support,
      (FOSGToEFG.execution source
        GameTheory.Examples.FOSG.falseFirst).terminal targetReached.state := by
  rintro ⟨targetReached, hreached, hterm⟩
  rw [InformationModel.runBehavioral, InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_zero,
    PMF.mem_support_pure_iff] at hreached
  subst targetReached
  simp [FOSGToEFG.execution, FOSGToEFG.terminal,
    FOSGToEFG.State.history] at hterm

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
