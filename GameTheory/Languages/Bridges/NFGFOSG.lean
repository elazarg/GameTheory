/-
# One-shot NFG through FOSG

The source normal form compiles to `GameForm`; the target FOSG contains exactly
an execution protocol and its factored information model. The one-shot
compiler uses the real history runner and preserves the source outcome and
utility laws.
-/

import GameTheory.Languages.NFG
import GameTheory.Languages.FOSG

noncomputable section

namespace GameTheory.Languages

open GameTheory GameTheory.Protocol GameTheory.Probability
open ExecutionProtocol

universe uι

namespace NFG.OneShotFOSG

variable {ι : Type uι} (G : NFG.Game ι)

/-- The one-step target starts before the simultaneous move and finishes with
the complete realized source profile. -/
inductive State
  | initial
  | finished (actions : ∀ i, G.Action i)

namespace State

/-- Recover an action from a joint contribution certified to contain one at
every coordinate. -/
private def actionOfJoint (joint : ∀ i, Option (G.Action i))
    (hlegal : IsLegalJoint (fun _ => True) (fun _ => Set.univ) joint)
    (i : ι) : G.Action i :=
  match h : joint i with
  | some action => action
  | none => False.elim (by
      have hi := hlegal i
      rw [h] at hi
      exact hi trivial)

@[simp]
private theorem actionOfJoint_some (actions : ∀ i, G.Action i)
    (hlegal : IsLegalJoint (fun _ => True) (fun _ => Set.univ)
      (fun i => some (actions i))) (i : ι) :
    actionOfJoint G (fun i => some (actions i)) hlegal i = actions i := rfl

end State

/-- The deterministic one-step simultaneous execution. Nonempty source action
carriers are requested only here, to witness progress. -/
@[reducible]
def execution [∀ i, Nonempty (G.Action i)] : ExecutionProtocol ι where
  State := State G
  Action := G.Action
  init := .initial
  active state _ :=
    match state with
    | .initial => True
    | .finished _ => False
  available _ _ := Set.univ
  terminal state :=
    match state with
    | .initial => False
    | .finished _ => True
  step state joint :=
    match state with
    | .initial =>
        FinDist.pure (.finished (State.actionOfJoint G joint.1 joint.2.2))
    | .finished _ => False.elim (joint.2.1 trivial)
  progress := by
    intro state hterm
    cases state with
    | initial =>
        refine ⟨fun i => some (Classical.choice
          (inferInstance : Nonempty (G.Action i))), fun _ => ?_⟩
        exact ⟨trivial, Set.mem_univ _⟩
    | finished actions =>
        exact False.elim (hterm trivial)

/-- The public phase reveals only whether the simultaneous move is over. -/
inductive Phase
  | acting
  | done

/-- The policy input carries no execution state and no current action. -/
inductive View (i : ι)
  | acting
  | done

/-- The view determined by a reached execution state. -/
def viewOfState (i : ι) : State G → View i
  | .initial => .acting
  | .finished _ => .done

/-- The one-shot factored signals. No private signal reveals another player's
action; the player's own contribution is supplied separately by `pushInfo`. -/
@[reducible]
def signals [∀ i, Nonempty (G.Action i)] :
    InfoSignals (execution G) where
  PublicSignal := Phase
  PrivateSignal _ := Unit
  initialPublic := .acting
  initialPrivate _ := ()
  publicSignal event :=
    match event.target with
    | .initial => .acting
    | .finished _ => .done
  privateSignal _ _ := ()
  InfoState := View
  initInfo _ _ _ := .acting
  pushInfo _ _ _ _ publicSignalValue :=
    match publicSignalValue with
    | .acting => .acting
    | .done => .done

/-- Signal update computes exactly the local view of the reached state. -/
theorem signals_push_event [∀ i, Nonempty (G.Action i)]
    (i : ι) (prior : View i) (event : StepEvent (execution G)) :
    (signals G).pushInfo i prior (event.joint i)
        ((signals G).privateSignal i event) ((signals G).publicSignal event) =
      viewOfState G i event.target := by
  obtain ⟨source, joint, isLegal, target, realized⟩ := event
  cases target <;> rfl

/-- Every realized history leaves precisely the phase-only local view. -/
theorem infoOf_eq_viewOfState [∀ i, Nonempty (G.Action i)]
    (i : ι) {state : (execution G).State}
    (trace : Trace (execution G) state) :
    (signals G).infoOf i trace = viewOfState G i state := by
  cases trace with
  | start => rfl
  | extend prior joint isLegal realized =>
      rw [InfoSignals.infoOf_extend]
      exact signals_push_event G i _ ⟨_, joint, isLegal, _, realized⟩

/-- Initially any source action may be contributed; after the move `none` is
the unique local option. -/
def menu (i : ι) : View i → Set (Option (G.Action i))
  | .acting => { choice | ∃ action, choice = some action }
  | .done => {none}

/-- The phase-only menu agrees with execution legality after every history. -/
theorem menu_adequate [∀ i, Nonempty (G.Action i)]
    (i : ι) {state : (execution G).State}
    (trace : Trace (execution G) state)
    (choice : Option (G.Action i)) :
    choice ∈ menu G i ((signals G).infoOf i trace) ↔
      LegalOption (execution G) state i choice := by
  rw [infoOf_eq_viewOfState G i trace]
  cases state <;> cases choice <;>
    simp [menu, viewOfState, LegalOption, execution]

/-- The information model of the one-shot simultaneous move. -/
@[reducible]
def informationModel [∀ i, Nonempty (G.Action i)] :
    InformationModel (execution G) where
  toInfoSignals := signals G
  menu := menu G
  menu_adequate := by
    intro i _ trace choice
    exact menu_adequate G i trace choice

/-- The one-shot target as a genuine FOSG. -/
@[reducible]
def game [∀ i, Nonempty (G.Action i)] : FOSG.Game ι where
  execution := execution G
  information := informationModel G

namespace Policy

variable [∀ i, Nonempty (G.Action i)]

/-- Lift one source action to the corresponding information-local policy. -/
def ofAction {i : ι} (action : G.Action i) :
    (informationModel G).Policy i :=
  fun info =>
    match show View i from info with
    | .acting => ⟨some action, by simp [menu]⟩
    | .done => ⟨none, by simp [menu]⟩

end Policy

/-- Lift a complete source action profile coordinatewise. -/
def policyProfile [∀ i, Nonempty (G.Action i)]
    (profile : Profile G.signature) :
    Profile (informationModel G).strategicSignature :=
  fun i => Policy.ofAction G (profile i)

/-- The lifted profile makes every source player act at the same initial
history. -/
@[simp]
theorem policyProfile_acting [∀ i, Nonempty (G.Action i)]
    (profile : Profile G.signature) (i : ι) :
    (policyProfile G profile i).act (.acting : View i) =
      some (profile i) := rfl

/-- Every source player is active at the target's unique decision state. -/
@[simp]
theorem active_initial [∀ i, Nonempty (G.Action i)] (i : ι) :
    (execution G).active .initial i := trivial

/-- The state-indexed chooser used only to calculate the shadow of the actual
information-local run. -/
def chooserOfProfile [∀ i, Nonempty (G.Action i)]
    (profile : Profile G.signature) : (execution G).Chooser :=
  fun state hterm =>
    match state with
    | .initial =>
        ⟨fun i => some (profile i), hterm, fun _ =>
          ⟨trivial, Set.mem_univ _⟩⟩
    | .finished _ => False.elim (hterm trivial)

/-- The lifted information-local chooser is exactly the state chooser that
plays the source profile. -/
theorem historyChooser_policyProfile [∀ i, Nonempty (G.Action i)]
    (profile : Profile G.signature) :
    (informationModel G).historyChooser (policyProfile G profile) =
      (chooserOfProfile G profile).toHistoryChooser := by
  apply funext
  rintro ⟨state, trace⟩
  apply funext
  intro hterm
  apply Subtype.ext
  funext i
  show (policyProfile G profile i).act
      ((informationModel G).infoOf i trace) =
    (chooserOfProfile G profile state hterm).1 i
  have hinfo : (informationModel G).infoOf i trace =
      viewOfState G i state :=
    infoOf_eq_viewOfState G i trace
  rw [hinfo]
  cases state with
  | initial => rfl
  | finished actions =>
      exact False.elim (hterm trivial)

/-- One target step records exactly the source profile and stops. -/
theorem runFor_chooserOfProfile_one [∀ i, Nonempty (G.Action i)]
    (profile : Profile G.signature) :
    (execution G).runFor (chooserOfProfile G profile) 1 .initial =
      FinDist.pure (.finished profile) := by
  rw [ExecutionProtocol.runFor]
  simp only [execution, chooserOfProfile, ↓reduceDIte]
  rw [FinDist.pure_bind, ExecutionProtocol.runFor]
  apply congrArg FinDist.pure
  apply congrArg State.finished
  funext i
  exact State.actionOfJoint_some G profile _ i

/-- Read a source outcome from a completed target state. The optional codomain
keeps the map total on short, nonterminal histories. -/
def outcomeOfState : State G → Option G.Outcome
  | .initial => none
  | .finished actions => some (G.outcome actions)

/-- The one-shot FOSG compiled through the canonical Protocol strategic form,
with terminal histories relabeled by the source outcome. -/
@[reducible]
def toProtocolForm [∀ i, Nonempty (G.Action i)] : GameForm ι :=
  ((game G).toGameForm 1).mapOutcome
    (fun history => outcomeOfState G history.state)

/-- **T4 commuting law.** Lifting a source profile, running the actual FOSG
compiler for one step, and reading the terminal source outcome gives exactly
the direct NFG play law, embedded into the total optional codomain. -/
theorem toProtocolForm_play_policyProfile
    [∀ i, Nonempty (G.Action i)]
    (profile : Profile G.signature) :
    (toProtocolForm G).play (policyProfile G profile) =
      (G.toGameForm.play profile).map some := by
  have hshadow := map_state_runHistoryFor
    (chooserOfProfile G profile) 1 (execution G).initHistory
  rw [← historyChooser_policyProfile G profile] at hshadow
  show
    FinDist.map (fun history => outcomeOfState G history.state)
        ((informationModel G).run (policyProfile G profile) 1) =
      (FinDist.pure (G.outcome profile)).map some
  rw [InformationModel.run, InformationModel.runFrom]
  calc
    FinDist.map (fun history => outcomeOfState G history.state)
        ((execution G).runHistoryFor
          ((informationModel G).historyChooser (policyProfile G profile)) 1
          (execution G).initHistory) =
      FinDist.map (outcomeOfState G)
        (FinDist.map ExecutionProtocol.History.state
          ((execution G).runHistoryFor
            ((informationModel G).historyChooser (policyProfile G profile)) 1
            (execution G).initHistory)) := by
              rw [FinDist.map_comp]
              rfl
    _ = FinDist.map (outcomeOfState G)
        ((execution G).runFor (chooserOfProfile G profile) 1 .initial) := by
          simpa using congrArg (FinDist.map (outcomeOfState G)) hshadow
    _ = (FinDist.pure (G.outcome profile)).map some := by
          rw [runFor_chooserOfProfile_one]
          simp [outcomeOfState]

/-- Extend a source utility to the total optional outcome carrier. Its value on
short nonterminal runs is irrelevant to the horizon-one law. -/
def utilityOfOutcome (utility : G.Outcome → ι → ℝ) :
    Option G.Outcome → ι → ℝ
  | none => fun _ => 0
  | some outcome => utility outcome

/-- The frozen predecessor's utility-distribution claim follows directly from
the commuting outcome law, with utility kept outside both language syntaxes. -/
theorem toProtocolForm_utilityLaw_policyProfile
    [∀ i, Nonempty (G.Action i)]
    (utility : G.Outcome → ι → ℝ)
    (profile : Profile G.signature) :
    ((toProtocolForm G).play (policyProfile G profile)).map
        (utilityOfOutcome G utility) =
      (G.toGameForm.play profile).map utility := by
  rw [toProtocolForm_play_policyProfile, FinDist.map_comp]
  apply congrArg (fun f => (G.toGameForm.play profile).map f)
  funext outcome
  rfl

end NFG.OneShotFOSG

end GameTheory.Languages
