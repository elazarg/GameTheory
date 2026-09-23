/-
# A random mover among infinitely many players

Player zero flips a behavioral coin; every other natural-number player is
inactive. The following chance step flips a second coin through `step`.
-/

import GameTheory.Protocol.SingleMover

noncomputable section

namespace GameTheory.Tests.SingleMover

open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

inductive Stage | decision | chance (choice : Bool) | done (choice toss : Bool)
  deriving DecidableEq

def coin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

@[reducible] def protocol : ExecutionProtocol ℕ where
  State := Stage
  Action _ := Bool
  init := .decision
  active state who := state = .decision ∧ who = 0
  available _ _ := Set.univ
  terminal state := ∃ choice toss, state = .done choice toss
  step state joint := match state with
    | .decision => FinDist.pure (.chance ((joint.1 0).getD false))
    | .chance choice => coin.map (.done choice)
    | .done choice toss => FinDist.pure (.done choice toss)
  progress := by
    intro state _
    refine ⟨fun who => if state = .decision ∧ who = 0 then some false else none, ?_⟩
    intro who
    by_cases active : state = .decision ∧ who = 0 <;> simp [active]

theorem single (state : protocol.State) {first second : ℕ}
    (hfirst : protocol.active state first) (hsecond : protocol.active state second) :
    first = second := hfirst.2.trans hsecond.2.symm

@[reducible] def signals : InfoSignals protocol where
  PublicSignal := Stage
  PrivateSignal _ := Unit
  initialPublic := .decision
  initialPrivate _ := ()
  publicSignal event := event.target
  privateSignal _ _ := ()
  InfoState _ := Stage
  initInfo _ _ announced := announced
  pushInfo _ _ _ _ announced := announced

theorem infoOf_eq (who : ℕ) : ∀ {state : protocol.State} (trace : protocol.Trace state),
    signals.infoOf who trace = state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

@[reducible] def model : InformationModel protocol where
  toInfoSignals := signals
  menu who state := {choice | LegalOption protocol state who choice}
  menu_adequate := by
    intro who state trace choice
    rw [infoOf_eq who trace]
    rfl

def profile : ∀ who, model.BehavioralPolicy who := fun who state =>
  if active : state = .decision ∧ who = 0 then
    coin.map fun choice => ⟨some choice, active, Set.mem_univ _⟩
  else FinDist.pure ⟨none, active⟩

theorem initial_not_terminal : ¬ protocol.terminal protocol.initHistory.state := by
  simp [protocol, initHistory]

/-- The active coordinate retains both outcomes of its behavioral coin. -/
theorem active_marginal :
    (model.singleMoverJoint single profile protocol.initHistory initial_not_terminal).map
        (fun joint => joint.1 0) = coin.map some := by
  rw [model.singleMoverJoint_marginal]
  simp [profile, InfoSignals.infoOf, initHistory, FinDist.map_comp]
  rfl

theorem active_marginal_false_mass :
    ((model.singleMoverJoint single profile protocol.initHistory initial_not_terminal).map
      (fun joint => joint.1 0)).prob (some false) = 1 / 2 := by
  rw [active_marginal]
  rw [FinDist.prob_map_of_injective some (Option.some_injective Bool)]
  simp [coin, FinDist.prob_pure_eq_ite]

/-- An arbitrary inactive natural-number coordinate contributes nothing. -/
theorem inactive_marginal (who : ℕ) (inactive : who ≠ 0) :
    (model.singleMoverJoint single profile protocol.initHistory initial_not_terminal).map
        (fun joint => joint.1 who) = FinDist.pure none := by
  rw [model.singleMoverJoint_marginal]
  simp [profile, InfoSignals.infoOf, initHistory, inactive]

def firstJoint : {joint // protocol.Legal .decision joint} :=
  ⟨fun who => if who = 0 then some true else none,
    by
      refine ⟨by simp, ?_⟩
      intro who
      by_cases h : who = 0 <;> simp [h]⟩

def chanceHistory : protocol.History :=
  protocol.initHistory.extend firstJoint.2
    (show Stage.chance true ∈ (protocol.step .decision firstJoint).support from
      FinDist.mem_support_pure.mpr rfl)

def remaining : Stage → ℕ
  | .decision => 2
  | .chance _ => 1
  | .done _ _ => 0

theorem remaining_add_length {state : protocol.State} (trace : protocol.Trace state) :
    remaining state + trace.length = 2 := by
  induction trace with
  | start => rfl
  | @extend source target prior joint legal realized ih =>
      have decrease : remaining target + 1 = remaining source := by
        cases source with
        | decision =>
            have reached := FinDist.mem_support_pure.mp realized
            subst target
            rfl
        | chance choice =>
            rw [FinDist.support_map] at realized
            obtain ⟨toss, _, rfl⟩ := realized
            rfl
        | done choice toss => exact (legal.1 ⟨choice, toss, rfl⟩).elim
      simp only [Trace.length]
      omega

theorem bounded : protocol.BoundedHorizon 2 := by
  intro state trace enough
  have bound := remaining_add_length trace
  cases state with
  | decision => simp [remaining] at bound; omega
  | chance choice => simp [remaining] at bound; omega
  | done choice toss => exact ⟨choice, toss, rfl⟩

/-- The no-mover branch executes chance, preserving the player's retained move. -/
theorem chance_step :
    (model.runSingleMoverBehavioralFrom single profile 1 chanceHistory).map History.state =
      coin.map (Stage.done true) := by
  have running : ¬ protocol.terminal chanceHistory.state := by
    show ¬ ∃ choice toss, Stage.chance true = Stage.done choice toss
    simp
  have inactive : ¬ ∃ who, protocol.active chanceHistory.state who := by
    show ¬ ∃ who : ℕ, Stage.chance true = Stage.decision ∧ who = 0
    simp
  rw [InformationModel.runSingleMoverBehavioralFrom,
    runRandomizedFor_succ_of_not_terminal _ 0 running]
  simp only [InformationModel.singleMoverChooser, InformationModel.singleMoverJoint,
    dite_eq_right inactive, FinDist.pure_bind, FinDist.map_bindOnSupport]
  calc
    _ = (coin.map (Stage.done true)).bind FinDist.pure := by
      apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
      intro target realized
      simp only [runRandomizedFor_zero, FinDist.map_pure, History.extend_state]
    _ = _ := FinDist.bind_pure _

theorem chance_true_mass :
    ((model.runSingleMoverBehavioralFrom single profile 1 chanceHistory).map History.state).prob
      (.done true true) = 1 / 2 := by
  rw [chance_step]
  rw [FinDist.prob_map_of_injective (Stage.done true)
    (fun _ _ equal => Stage.done.inj equal |>.2)]
  simp [coin, FinDist.prob_pure_eq_ite]
  norm_num

example (policies : ∀ who, model.Policy who) (fuel : ℕ) (history : protocol.History) :
    model.runSingleMoverBehavioralFrom single (fun who => (policies who).toBehavioral)
      fuel history = model.runFrom policies fuel history :=
  model.runSingleMoverBehavioralFrom_toBehavioral single policies fuel history

end GameTheory.Tests.SingleMover
