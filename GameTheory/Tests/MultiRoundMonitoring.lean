/-
# Hostile multi-round imperfect-monitoring fixture

Two players act for two rounds.  They observe only whether their actions agree,
so player zero cannot distinguish opponent actions one and two after choosing
zero.  The information state nevertheless remembers player zero's own choice,
and a second-round policy branches on it.
-/

import GameTheory.Languages.MultiRound
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.Tests.MultiRoundMonitoring

open GameTheory GameTheory.Protocol GameTheory.Probability
open GameTheory.Languages.MultiRound
open MonitoringGame
open ExecutionProtocol

abbrev Player := Fin 2
abbrev Action := Fin 3

def actions (first second : Action) : (i : Player) → Action := fun i =>
  if i = 0 then first else second

@[reducible]
def joint (first second : Action) : (i : Player) → Option Action := fun i =>
  some (actions first second i)

/-- The public signal reports only agreement.  With three actions, observing
disagreement and remembering one's own action does not reveal the opponent. -/
@[reducible]
def fixture : MonitoringGame Player where
  Action _ := Action
  PublicSignal := Bool
  PrivateSignal _ := Unit
  horizon := 2
  initialPublic := false
  initialPrivate _ := ()
  signalLaw _ chosen :=
    FinDist.pure (decide (chosen 0 = chosen 1), fun _ => ())

instance actionNonempty (i : Player) : Nonempty (fixture.Action i) := by
  infer_instance

theorem joint_legal (first second : Action) :
    fixture.execution.Legal [] (joint first second) := by
  constructor
  · norm_num [MonitoringGame.execution, fixture]
  · intro i
    exact ⟨by norm_num [MonitoringGame.execution, fixture], Set.mem_univ _⟩

def unequalSignals : Bool × (Player → Unit) :=
  (false, fun _ => ())

def oneRound (first second : Action) : fixture.State :=
  fixture.appendRound [] (actions first second) unequalSignals

theorem step_unequal {first second : Action} (hne : first ≠ second) :
    fixture.execution.step []
        ⟨joint first second, joint_legal first second⟩ =
      FinDist.pure (oneRound first second) := by
  rw [fixture.execution_step_some [] (actions first second)
    (joint_legal first second)]
  simp [MonitoringGame.nextLaw, fixture, actions, hne, oneRound,
    unequalSignals]

def trace01 : Trace fixture.execution (oneRound 0 1) :=
  .extend .start (joint 0 1) (joint_legal 0 1) (by
    rw [step_unequal (by decide)]
    exact FinDist.mem_support_pure.mpr rfl)

def trace02 : Trace fixture.execution (oneRound 0 2) :=
  .extend .start (joint 0 2) (joint_legal 0 2) (by
    rw [step_unequal (by decide)]
    exact FinDist.mem_support_pure.mpr rfl)

def trace12 : Trace fixture.execution (oneRound 1 2) :=
  .extend .start (joint 1 2) (joint_legal 1 2) (by
    rw [step_unequal (by decide)]
    exact FinDist.mem_support_pure.mpr rfl)

/-- The hidden states differ because the opponent's realized action differs. -/
theorem hidden_states_distinct : oneRound 0 1 ≠ oneRound 0 2 := by
  intro heq
  have hrecord := congrArg List.getLast? heq
  simp [oneRound, MonitoringGame.appendRound] at hrecord
  have hplayer := congrFun hrecord 1
  have hval := congrArg Fin.val hplayer
  norm_num [actions] at hval

/-- Player zero sees the same own action and coarse signal in those distinct
hidden states, so every information-local policy must treat them alike. -/
theorem opponent_actions_hidden :
    fixture.signals.infoOf 0 trace01 =
      fixture.signals.infoOf 0 trace02 := by
  rfl

/-- Changing player zero's own action changes its information even though the
same coarse disagreement signal is emitted. -/
theorem own_previous_action_remembered :
    fixture.signals.infoOf 0 trace01 ≠
      fixture.signals.infoOf 0 trace12 := by
  intro heq
  have hrounds := congrArg (fun info => info.rounds) heq
  simp [trace01, trace12, MonitoringGame.signals, joint, actions] at hrounds

/-- The generic owner also proves the semantic recall condition used by the
canonical mixed-to-behavioral correspondence. -/
theorem fixture_perfectRecall : fixture.informationModel.PerfectRecall :=
  fixture.perfectRecall

def initialAction (i : Player) : Action :=
  if i = 0 then 1 else 2

def repeatOwnPolicy (i : Player) : fixture.informationModel.Policy i := fun info =>
  if hactive : info.rounds.length < fixture.horizon then
    let next := match info.rounds.getLast? with
      | none => initialAction i
      | some previous => previous.ownChoice.getD (initialAction i)
    ⟨some next, by simp [MonitoringGame.menu, hactive]⟩
  else
    ⟨none, by simp [MonitoringGame.menu, hactive]⟩

/-- The second-round policy actually branches on the remembered own action. -/
theorem policy_branches_on_previous_action :
    (repeatOwnPolicy 0).act (fixture.signals.infoOf 0 trace01) = some 0 ∧
      (repeatOwnPolicy 0).act (fixture.signals.infoOf 0 trace12) = some 1 := by
  constructor <;>
    rfl

/-- Locality is enforced by typing: hidden opponent actions cannot affect the
same policy when the information states coincide. -/
theorem policy_cannot_branch_on_hidden_opponent :
    (repeatOwnPolicy 0).act (fixture.signals.infoOf 0 trace01) =
      (repeatOwnPolicy 0).act (fixture.signals.infoOf 0 trace02) := by
  exact congrArg (repeatOwnPolicy 0).act opponent_actions_hidden

def repeatProfile :
    (i : Player) → fixture.informationModel.Policy i :=
  repeatOwnPolicy

/-- The joint action actually handed to Protocol in round two is the profile
reconstructed from the players' remembered own actions. -/
theorem canonical_second_round_joint :
    fixture.informationModel.jointAt repeatProfile trace12 = joint 1 2 := by
  funext i
  fin_cases i <;> rfl

/-- The public strategic form evaluates that same policy profile with the sole
history-indexed Protocol runner. -/
theorem compiled_play_is_canonical :
    fixture.toGameForm.play repeatProfile =
      fixture.informationModel.run repeatProfile fixture.horizon :=
  fixture.toGameForm_play repeatProfile

end GameTheory.Tests.MultiRoundMonitoring
