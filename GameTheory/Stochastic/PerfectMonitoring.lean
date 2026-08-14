/-
# Perfect public monitoring for stochastic games

This named bridge drives the canonical Protocol runner. Behavioral policies
observe proof-free stochastic stage records; Protocol retains legality and
positive-support evidence internally.
-/

import GameTheory.Stochastic.Basic
import GameTheory.Protocol.Strategic

noncomputable section

namespace GameTheory.Stochastic

open Protocol Protocol.ExecutionProtocol

universe uι us ua

namespace Game

variable {ι : Type uι} (G : Game.{uι, us, ua} ι)

/-- A capability-supplied fallback used only to erase Protocol's `Option`
wrapper. Legal all-active events always contain `some`. -/
private noncomputable def fallbackAction [∀ i, Nonempty (G.Action i)]
    (i : ι) : G.Action i :=
  Classical.choice (inferInstance : Nonempty (G.Action i))

/-- Forget the `Option` wrapper of an all-active Protocol joint action. -/
private def jointAction [∀ i, Nonempty (G.Action i)]
    (joint : ∀ i, Option (G.Action i)) : ∀ i, G.Action i :=
  fun i => (joint i).getD (G.fallbackAction i)

/-- The canonical nonterminating, all-active execution from one selected
initial state. Nonempty action carriers are required exactly by Protocol's
progress law. -/
@[reducible]
noncomputable def toExecution (initial : G.State) [∀ i, Nonempty (G.Action i)] :
    ExecutionProtocol ι where
  State := G.State
  Action := G.Action
  init := initial
  active _ _ := True
  available _ _ := Set.univ
  terminal _ := False
  step state joint := G.transition state (G.jointAction joint.1)
  progress := by
    intro _ _
    refine ⟨fun i => some (G.fallbackAction i), ?_⟩
    intro i
    simp

variable {G}

@[simp]
theorem toExecution_step_some (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (state : G.State) (joint : ∀ i, G.Action i) :
    (G.toExecution initial).step state
        ⟨fun i => some (joint i), by simp [IsLegalJoint]⟩ =
      G.transition state joint := by
  rfl

/-- Erase only Protocol bookkeeping from a realized transition. -/
def stageRecordOfEvent (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (event : (G.toExecution initial).StepEvent) : G.StageRecord where
  source := event.source
  joint := G.jointAction event.joint
  target := event.target

@[simp]
theorem stageRecordOfEvent_source (initial : G.State)
    [∀ i, Nonempty (G.Action i)]
    (event : (G.toExecution initial).StepEvent) :
    (G.stageRecordOfEvent initial event).source = event.source := rfl

@[simp]
theorem stageRecordOfEvent_target (initial : G.State)
    [∀ i, Nonempty (G.Action i)]
    (event : (G.toExecution initial).StepEvent) :
    (G.stageRecordOfEvent initial event).target = event.target := rfl

/-- No action data is lost when a legal all-active Protocol event is exposed
as a stochastic stage record. -/
theorem stageRecordOfEvent_joint (initial : G.State)
    [∀ i, Nonempty (G.Action i)]
    (event : (G.toExecution initial).StepEvent) (i : ι) :
    event.joint i = some ((G.stageRecordOfEvent initial event).joint i) := by
  have hlegal := (G.toExecution initial).legalOption_of_legal event.isLegal i
  cases hchoice : event.joint i with
  | none =>
      rw [hchoice] at hlegal
      simp [LegalOption] at hlegal
  | some action =>
      simp [stageRecordOfEvent, jointAction, hchoice]

/-- Perfect public monitoring remembers every realized transition as
proof-free stochastic data. -/
@[reducible]
def perfectSignals (initial : G.State) [∀ i, Nonempty (G.Action i)] :
    InfoSignals (G.toExecution initial) where
  PublicSignal := Option G.StageRecord
  PrivateSignal := fun _ => Unit
  initialPublic := none
  initialPrivate := fun _ => ()
  publicSignal := fun event => some (G.stageRecordOfEvent initial event)
  privateSignal := fun _ _ => ()
  InfoState := fun _ => G.PublicHistory
  initInfo := fun _ _ _ => []
  pushInfo := fun _ prior _ _ signal =>
    match signal with
    | none => prior
    | some event => event :: prior

/-- Every player must choose an action at every stochastic-game state. -/
def activeMenu (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (i : ι) (_ : (G.perfectSignals initial).InfoState i) :
    Set (Option ((G.toExecution initial).Action i)) :=
  { choice | ∃ action, choice = some action }

theorem activeMenu_adequate (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (i : ι) {state : (G.toExecution initial).State}
    (trace : Trace (G.toExecution initial) state)
    (choice : Option ((G.toExecution initial).Action i)) :
    choice ∈ G.activeMenu initial i ((G.perfectSignals initial).infoOf i trace) ↔
      LegalOption (G.toExecution initial) state i choice := by
  cases choice <;> simp [activeMenu, LegalOption]

/-- Full public-history information over the canonical execution. -/
@[reducible]
def perfectMonitoring (initial : G.State) [∀ i, Nonempty (G.Action i)] :
    InformationModel (G.toExecution initial) where
  toInfoSignals := G.perfectSignals initial
  menu := G.activeMenu initial
  menu_adequate := by
    intro i _ trace choice
    exact G.activeMenu_adequate initial i trace choice

/-- Canonical Protocol behavioral profiles for a selected initial state. -/
abbrev BehaviorProfile (initial : G.State) [∀ i, Nonempty (G.Action i)] :=
  Profile (G.perfectMonitoring initial).behavioralSignature

end Game

end GameTheory.Stochastic
