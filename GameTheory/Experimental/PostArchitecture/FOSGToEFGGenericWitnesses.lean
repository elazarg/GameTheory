/-
# EXP-061: generic FOSG serialization witnesses

The stable bridge is instantiated on EXP-060's hostile source: two rounds,
trace-sensitive information after a merged execution state, and a privately
known inactive second-round slot.  Both exhaustive player orders must preserve
the exact two-round history law.
-/

import GameTheory.Languages.Bridges.FOSGToEFG
import GameTheory.Experimental.PostArchitecture.FOSGToEFGTwoRoundWitnesses
import Mathlib.Logic.Equiv.Bool

noncomputable section

namespace GameTheory.Experimental.FOSGToEFGGenericWitnesses

open GameTheory.Languages.Bridges
open GameTheory.Probability
open GameTheory.Experimental.FOSGToEFGTwoRound
open GameTheory.Experimental.FOSGToEFGTwoRound.Witnesses

def falseFirst : FOSGToEFG.ExplicitOrder Bool where
  slots := 2
  player := finTwoEquiv

def trueFirst : FOSGToEFG.ExplicitOrder Bool where
  slots := 2
  player := finTwoEquiv.trans Equiv.boolNot

example : ¬ Source.execution.IsTreeShaped := Source.not_treeShaped

example : GameTheory.Languages.EFG.Game Bool :=
  FOSGToEFG.toEFG Source.game falseFirst

example : GameTheory.Languages.EFG.Game Bool :=
  FOSGToEFG.toEFG Source.game trueFirst

def startChoice (action : Bool) :
    FOSGToEFG.ChoiceAt Source.game Source.execution.initHistory false :=
  ⟨some action, ⟨by simp [Source.active], Set.mem_univ _⟩⟩

def afterStartPrefix (action : Bool) :
    FOSGToEFG.Prefix Source.game falseFirst
      Source.execution.initHistory 1 :=
  (FOSGToEFG.Prefix.initial
    (G := Source.game) (order := falseFirst)
    Source.execution.initHistory).advance (by simp [falseFirst])
      (startChoice action)

/-- The later selector's generic target view does not expose the stored first
choice. -/
theorem later_selection_hides_prefix :
    FOSGToEFG.viewOfState Source.game falseFirst true
        (.stage Source.execution.initHistory 1 (afterStartPrefix false)) =
      FOSGToEFG.viewOfState Source.game falseFirst true
        (.stage Source.execution.initHistory 1 (afterStartPrefix true)) := rfl

/-- Administrative selection changes the phase but leaves the full canonical
source-information component untouched. -/
theorem selection_source_unchanged (action player : Bool) :
    (FOSGToEFG.viewOfState Source.game falseFirst player
      (.stage Source.execution.initHistory 1
        (afterStartPrefix action))).source =
    (FOSGToEFG.viewOfState Source.game falseFirst player
      (.stage Source.execution.initHistory 0
        (FOSGToEFG.Prefix.initial
          (G := Source.game) (order := falseFirst)
          Source.execution.initHistory))).source := rfl

/-- The generic target still hides whether the earlier true-player slot was
inactive or active from the false player. -/
theorem later_view_hides_hidden_activity
    (left right publicBit : Bool) :
    (FOSGToEFG.viewOfState Source.game trueFirst false
      (.stage (Source.round2History left right publicBit false) 1
        ((FOSGToEFG.Prefix.initial
          (G := Source.game) (order := trueFirst)
          (Source.round2History left right publicBit false)).advance
            (by simp [trueFirst])
            ⟨none, by
              show ¬ Source.active (.round2 publicBit false) true
              simp [Source.active]⟩))).source =
    (FOSGToEFG.viewOfState Source.game trueFirst false
      (.stage (Source.round2History left right publicBit true) 1
        ((FOSGToEFG.Prefix.initial
          (G := Source.game) (order := trueFirst)
          (Source.round2History left right publicBit true)).advance
            (by simp [trueFirst])
            ⟨some false, by
              exact ⟨by simp [Source.round2History, Source.active],
                Set.mem_univ _⟩⟩))).source := by
  simpa only [FOSGToEFG.viewOfState, FOSGToEFG.State.history] using
    Source.false_does_not_observe_hidden_activity left right publicBit

/-- Source public information is replayed at the next target boundary. -/
theorem boundary_replays_public
    (player left right hiddenActiveBit : Bool) :
    (FOSGToEFG.viewOfState Source.game falseFirst player
      (.stage (Source.round2History left right false hiddenActiveBit) 0
        (FOSGToEFG.Prefix.initial
          (G := Source.game) (order := falseFirst) _))).source ≠
    (FOSGToEFG.viewOfState Source.game falseFirst player
      (.stage (Source.round2History left right true hiddenActiveBit) 0
        (FOSGToEFG.Prefix.initial
          (G := Source.game) (order := falseFirst) _))).source := by
  simpa only [FOSGToEFG.viewOfState, FOSGToEFG.State.history] using
    Source.public_bit_is_observed player left right hiddenActiveBit

/-- Source private information is replayed at the next target boundary. -/
theorem boundary_replays_private
    (left publicBit hiddenActiveBit : Bool) :
    (FOSGToEFG.viewOfState Source.game falseFirst false
      (.stage (Source.round2History left false publicBit hiddenActiveBit) 0
        (FOSGToEFG.Prefix.initial
          (G := Source.game) (order := falseFirst) _))).source ≠
    (FOSGToEFG.viewOfState Source.game falseFirst false
      (.stage (Source.round2History left true publicBit hiddenActiveBit) 0
        (FOSGToEFG.Prefix.initial
          (G := Source.game) (order := falseFirst) _))).source := by
  simpa only [FOSGToEFG.viewOfState, FOSGToEFG.State.history] using
    Source.opponent_first_action_is_private left publicBit hiddenActiveBit

/-- Own source actions are replayed at the next target boundary. -/
theorem boundary_replays_own_action
    (right publicBit hiddenActiveBit : Bool) :
    (FOSGToEFG.viewOfState Source.game falseFirst false
      (.stage (Source.round2History false right publicBit hiddenActiveBit) 0
        (FOSGToEFG.Prefix.initial
          (G := Source.game) (order := falseFirst) _))).source ≠
    (FOSGToEFG.viewOfState Source.game falseFirst false
      (.stage (Source.round2History true right publicBit hiddenActiveBit) 0
        (FOSGToEFG.Prefix.initial
          (G := Source.game) (order := falseFirst) _))).source := by
  simpa only [FOSGToEFG.viewOfState, FOSGToEFG.State.history] using
    Source.own_first_action_is_remembered right publicBit hiddenActiveBit

/-- Observe a translated target policy through its underlying optional source
action at the canonical scheduled view. -/
def translatedFalseOptionLaw
    (source : (player : Bool) →
      Source.information.BehavioralPolicy player)
    (view : Source.View) : FinDist (Option Bool) :=
  FinDist.map Subtype.val
    (FOSGToEFG.translateBehavioral Source.game falseFirst source false
      (FOSGToEFG.scheduledView Source.game false view))

theorem translatedFalseOptionLaw_eq
    (source : (player : Bool) →
      Source.information.BehavioralPolicy player)
    (hfalse : source false = falseSignalPolicy)
    (view : Source.View) :
    translatedFalseOptionLaw source view = falseSignalOptionLaw view := by
  rw [translatedFalseOptionLaw,
    FOSGToEFG.translateBehavioral_scheduledView, hfalse,
    falseSignalOptionLaw, FinDist.map_comp]
  apply congrArg (fun f => FinDist.map f (falseSignalPolicy view))
  funext choice
  rfl

/-- Translation preserves a concrete policy's dependence on replayed public
information. -/
theorem translated_policy_reads_public
    (source : (player : Bool) →
      Source.information.BehavioralPolicy player)
    (hfalse : source false = falseSignalPolicy) :
    translatedFalseOptionLaw source (.round2 false false none false) ≠
      translatedFalseOptionLaw source (.round2 true false none false) := by
  rw [translatedFalseOptionLaw_eq source hfalse,
    translatedFalseOptionLaw_eq source hfalse]
  exact false_signal_policy_reads_public

/-- Translation preserves a concrete policy's dependence on replayed private
information. -/
theorem translated_policy_reads_private
    (source : (player : Bool) →
      Source.information.BehavioralPolicy player)
    (hfalse : source false = falseSignalPolicy) :
    translatedFalseOptionLaw source (.round2 false false none false) ≠
      translatedFalseOptionLaw source (.round2 false true none false) := by
  rw [translatedFalseOptionLaw_eq source hfalse,
    translatedFalseOptionLaw_eq source hfalse]
  exact false_signal_policy_reads_private

/-- Translation preserves a concrete policy's dependence on replayed own
actions. -/
theorem translated_policy_reads_own_action
    (source : (player : Bool) →
      Source.information.BehavioralPolicy player)
    (hfalse : source false = falseSignalPolicy) :
    translatedFalseOptionLaw source (.round2 false false none false) ≠
      translatedFalseOptionLaw source (.round2 false false none true) := by
  rw [translatedFalseOptionLaw_eq source hfalse,
    translatedFalseOptionLaw_eq source hfalse]
  exact false_signal_policy_reads_own_action

/-- On the hostile two-round source, every arbitrary serialized target policy
is recovered exactly after projection and translation, including its forced
non-owner and resolver local laws. -/
theorem falseFirst_full_profile_round_trip
    (target : (player : Bool) →
      (FOSGToEFG.information Source.game falseFirst).BehavioralPolicy player) :
    FOSGToEFG.translateBehavioral Source.game falseFirst
      (FOSGToEFG.projectBehavioral Source.game falseFirst target) = target :=
  FOSGToEFG.translate_project_profile Source.game falseFirst target

theorem falseFirst_exact
    (target : (player : Bool) →
      (FOSGToEFG.information Source.game falseFirst).BehavioralPolicy player) :
    FinDist.map (FOSGToEFG.eraseHistory Source.game falseFirst)
        ((FOSGToEFG.information Source.game falseFirst).runBehavioral target 6) =
      Source.information.runBehavioral
        (FOSGToEFG.projectBehavioral Source.game falseFirst target) 2 := by
  simpa [falseFirst, FOSGToEFG.roundWidth] using
    FOSGToEFG.map_erase_runBehavioral_eq_source Source.game falseFirst target 2

theorem trueFirst_exact
    (target : (player : Bool) →
      (FOSGToEFG.information Source.game trueFirst).BehavioralPolicy player) :
    FinDist.map (FOSGToEFG.eraseHistory Source.game trueFirst)
        ((FOSGToEFG.information Source.game trueFirst).runBehavioral target 6) =
      Source.information.runBehavioral
        (FOSGToEFG.projectBehavioral Source.game trueFirst target) 2 := by
  simpa [trueFirst, FOSGToEFG.roundWidth] using
    FOSGToEFG.map_erase_runBehavioral_eq_source Source.game trueFirst target 2

theorem translated_exact
    (source : (player : Bool) →
      Source.information.BehavioralPolicy player) :
    FinDist.map (FOSGToEFG.eraseHistory Source.game falseFirst)
        ((FOSGToEFG.information Source.game falseFirst).runBehavioral
          (FOSGToEFG.translateBehavioral Source.game falseFirst source) 6) =
      Source.information.runBehavioral source 2 := by
  simpa [falseFirst, FOSGToEFG.roundWidth] using
    FOSGToEFG.map_erase_runBehavioral_translate Source.game falseFirst source 2

theorem arbitrary_order_transport
    (target : (player : Bool) →
      (FOSGToEFG.information Source.game falseFirst).BehavioralPolicy player) :
    FinDist.map (FOSGToEFG.eraseHistory Source.game falseFirst)
        ((FOSGToEFG.information Source.game falseFirst).runBehavioral target 6) =
      FinDist.map (FOSGToEFG.eraseHistory Source.game trueFirst)
        ((FOSGToEFG.information Source.game trueFirst).runBehavioral
          (FOSGToEFG.translateBehavioral Source.game trueFirst
            (FOSGToEFG.projectBehavioral Source.game falseFirst target)) 6) := by
  simpa [falseFirst, trueFirst, FOSGToEFG.roundWidth] using
    FOSGToEFG.map_erase_runBehavioral_order_transport Source.game
      falseFirst trueFirst target 2

#print axioms FinDist.runDependent_eq_pi
#print axioms FOSGToEFG.treeShaped
#print axioms FOSGToEFG.translate_project_profile
#print axioms FOSGToEFG.map_erase_runBehavioral_eq_source
#print axioms falseFirst_full_profile_round_trip
#print axioms falseFirst_exact
#print axioms arbitrary_order_transport

end GameTheory.Experimental.FOSGToEFGGenericWitnesses
