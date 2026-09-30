/-
# Sequential play with infinitely many players

Countably many agents are indexed by the natural numbers. Agent `0` votes, then
agent `1` votes, and play stops; every other agent never moves. With infinitely
many players there is no independent product of every player's local law, so
this protocol is outside the reach of a finite-player hypothesis. At most one
agent moves at each state, which is all the behavioral joint law needs.

The fixture checks that genuinely random behavioral play runs with the player
set `ℕ`: both first votes are drawable at the start, and behavioral play of a
deterministic profile is its deterministic play.
-/

import GameTheory.Protocol.Information
import GameTheory.Math.Probability.Mixture

noncomputable section

namespace GameTheory.Tests.InfiniteMovers

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol (Trace History)

/-- Before the first vote, between the votes, and after both. -/
inductive Stage | first | second (vote : Bool) | done (first second : Bool)

/-- Whether an agent must vote at a stage. -/
def Stage.Moves : Stage → ℕ → Prop
  | .first, agent => agent = 0
  | .second _, agent => agent = 1
  | .done _ _, _ => False

instance (stage : Stage) (agent : ℕ) : Decidable (stage.Moves agent) := by
  cases stage <;> unfold Stage.Moves <;> infer_instance

/-- Two agents vote in turn, drawn from countably many. -/
@[reducible]
def cascade : ExecutionProtocol ℕ where
  State := Stage
  Action _ := Bool
  init := .first
  active := Stage.Moves
  available _ _ := Set.univ
  terminal
    | .done _ _ => True
    | _ => False
  step state joint :=
    match state with
    | .first => PMF.pure (.second ((joint.1 0).getD false))
    | .second vote => PMF.pure (.done vote ((joint.1 1).getD false))
    | .done first second => PMF.pure (.done first second)
  progress := by
    rintro (_ | _ | _) hterm
    · refine ⟨fun agent => if agent = 0 then some false else none, fun agent => ?_⟩
      by_cases h : agent = 0 <;> simp [h, Stage.Moves]
    · refine ⟨fun agent => if agent = 1 then some false else none, fun agent => ?_⟩
      by_cases h : agent = 1 <;> simp [h, Stage.Moves]
    · exact absurd trivial hterm

/-- At most one agent moves at each state. -/
instance : cascade.FiniteMovers :=
  ExecutionProtocol.FiniteMovers.of_subsingleton cascade
    fun state first hfirst second hsecond => by
    cases state with
    | first => exact hfirst.trans hsecond.symm
    | second _ => exact hfirst.trans hsecond.symm
    | done _ _ => exact hfirst.elim

/-- Every agent observes the current stage. -/
@[reducible]
def signals : InfoSignals cascade where
  PublicSignal := Stage
  PrivateSignal _ := Unit
  initialPublic := .first
  initialPrivate _ := ()
  publicSignal event := event.target
  privateSignal _ _ := ()
  InfoState _ := Stage
  initInfo _ _ announced := announced
  pushInfo _ _ _ _ announced := announced

theorem infoOf_eq_state :
    ∀ {state : cascade.State} (trace : Trace cascade state) (agent : ℕ),
      signals.infoOf agent trace = state
  | _, .start, _ => rfl
  | _, .extend _ _ _ _, _ => rfl

/-- The stage determines who must vote, so the legal options are the menu. -/
@[reducible]
def model : InformationModel cascade where
  toInfoSignals := signals
  menu agent stage := {choice | LegalOption cascade stage agent choice}
  menu_adequate agent _ trace choice := by
    rw [infoOf_eq_state trace agent]
    rfl

/-- A voter who must vote tosses a fair coin; everyone else abstains. -/
def coinPolicy (agent : ℕ) : model.BehavioralPolicy agent := fun stage =>
  if hmoves : cascade.active stage agent then
    mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure ⟨some true, ⟨hmoves, Set.mem_univ _⟩⟩)
      (PMF.pure ⟨some false, ⟨hmoves, Set.mem_univ _⟩⟩)
  else PMF.pure ⟨none, hmoves⟩

/-- Agent `0` alone casts the given first vote. -/
def firstVote (vote : Bool) : ∀ agent : ℕ, Option (cascade.Action agent) :=
  fun agent => if agent = 0 then some vote else none

theorem firstVote_legal (vote : Bool) : cascade.Legal .first (firstVote vote) := by
  refine ⟨id, fun agent => ?_⟩
  by_cases h : agent = 0 <;> simp [firstVote, h, Stage.Moves]

/-- **Both first votes are drawable** by the coin-tossing profile over the
infinitely many agents. -/
theorem firstVote_mem_support_behavioralJoint (vote : Bool) :
    (⟨firstVote vote, firstVote_legal vote⟩ :
        { joint : ∀ agent, Option (cascade.Action agent) //
          cascade.Legal .first joint }) ∈
      (model.behavioralJoint coinPolicy (Trace.start : Trace cascade .first) id).support := by
  apply model.mem_support_behavioralJoint
  intro agent
  unfold coinPolicy
  split_ifs with hmoves
  · have hagent : agent = 0 := hmoves
    subst agent
    cases vote
    · exact mem_support_mix_right _ _ _ (by norm_num)
        ((PMF.mem_support_pure_iff _ _).2 (Subtype.ext rfl))
    · exact mem_support_mix_left _ _ _ (by norm_num)
        ((PMF.mem_support_pure_iff _ _).2 (Subtype.ext rfl))
  · have hagent : agent ≠ 0 := hmoves
    rw [PMF.mem_support_pure_iff]
    apply Subtype.ext
    simp [firstVote, hagent]

/-- Behavioral play of a deterministic profile over the infinitely many agents
is its deterministic play. -/
theorem runBehavioral_toBehavioral (policies : (agent : ℕ) → model.Policy agent)
    (fuel : ℕ) :
    model.runBehavioralFrom (fun agent => (policies agent).toBehavioral) fuel
        cascade.initHistory =
      model.runFrom policies fuel cascade.initHistory :=
  model.runBehavioralFrom_toBehavioral policies fuel _

end GameTheory.Tests.InfiniteMovers
