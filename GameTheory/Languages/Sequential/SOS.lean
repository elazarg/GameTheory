import GameTheory.Languages.Sequential.Syntax
import GameTheory.Model.SemanticForm
import Math.Probability

/-!
# GameTheory.Languages.Sequential.SOS

Native small-step semantics for sequential protocols.

A protocol round is executed in two phases:
- `signal`: nature samples the joint signal for the current round
- `action`: players respond with a joint action, producing the next state

This makes the protocol semantics explicit enough to compare directly with the
compiled `SM`/`InfoModel` semantics.
-/

namespace GameTheory.Sequential

open Math.Probability

variable {n : Nat} {S V A Sig : Type}

/-- Joint signal realization for one round. -/
abbrev JointSignal (n : Nat) (Sig : Type) := Fin n → Sig

/-- Joint player action for one round. -/
abbrev JointControl (n : Nat) (A : Type) := Fin n → Option A

/-- Native execution configuration for a protocol. -/
inductive Config (G : Protocol n S V A Sig) where
  | signal (round : Nat) (state : S)
  | action (round : Nat) (state : S) (sig : JointSignal n Sig)
  | terminal (state : S)
deriving Repr

namespace Config

variable {G : Protocol n S V A Sig}

/-- Underlying latent state carried by a protocol configuration. -/
def state (c : Config G) : S :=
  match c with
  | .signal _ s => s
  | .action _ s _ => s
  | .terminal s => s

/-- Current round index if the protocol has not terminated. -/
def round? (c : Config G) : Option Nat :=
  match c with
  | .signal k _ => some k
  | .action k _ _ => some k
  | .terminal _ => none

end Config

/-- Initial SOS configuration for a protocol. -/
def initialConfig (G : Protocol n S V A Sig) : Config G :=
  if G.rounds[0]? = none then
    .terminal G.init
  else
    .signal 0 G.init

/-- One native small step of a protocol. Signal phases use the all-`none`
action profile; action phases use the actual joint control. -/
inductive Step (G : Protocol n S V A Sig) : JointControl n A → Config G → Config G → Prop where
  | sample {k : Nat} {s : S} {r : Round n S V A Sig} {sig : JointSignal n Sig} :
      G.rounds[k]? = some r →
      (r.signal s) sig ≠ 0 →
      Step G (fun _ => none) (.signal k s) (.action k s sig)
  | act_more {k : Nat} {s next : S} {sig : JointSignal n Sig}
      {acts : JointControl n A} {r rNext : Round n S V A Sig} :
      G.rounds[k]? = some r →
      next = r.transition s acts →
      G.rounds[k + 1]? = some rNext →
      Step G acts (.action k s sig) (.signal (k + 1) next)
  | act_last {k : Nat} {s next : S} {sig : JointSignal n Sig}
      {acts : JointControl n A} {r : Round n S V A Sig} :
      G.rounds[k]? = some r →
      next = r.transition s acts →
      G.rounds[k + 1]? = none →
      Step G acts (.action k s sig) (.terminal next)

/-- Reachability in the native SOS semantics. -/
abbrev ReachBy (G : Protocol n S V A Sig) :=
  Semantics.Transition.ReachBy (Step G)

/-- Public execution phase for protocol configurations. -/
inductive PublicPhase where
  | signal (round : Nat)
  | action (round : Nat)
  | terminal
deriving DecidableEq, Repr

/-- Publicly visible phase information of a protocol configuration. -/
def publicPhase (c : Config G) : PublicPhase :=
  match c with
  | .signal k _ => .signal k
  | .action k _ _ => .action k
  | .terminal _ => .terminal

/-- Player-local observation available in a configuration. Players only observe
views during the action phase of a round. -/
def observe (G : Protocol n S V A Sig) (i : Fin n) : Config G → Option V
  | .signal _ _ => none
  | .terminal _ => none
  | .action k s sig =>
      match G.rounds[k]? with
      | some r => some (Round.view r i s (sig i))
      | none => none

@[simp] theorem observe_signal (G : Protocol n S V A Sig) (i : Fin n) (k : Nat) (s : S) :
    observe G i (.signal k s) = none := rfl

@[simp] theorem observe_terminal (G : Protocol n S V A Sig) (i : Fin n) (s : S) :
    observe G i (.terminal s) = none := rfl

@[simp] theorem publicPhase_signal (k : Nat) (s : S) :
    publicPhase (Config.signal (G := G) k s) = .signal k := rfl

@[simp] theorem publicPhase_action (k : Nat) (s : S) (sig : JointSignal n Sig) :
    publicPhase (Config.action (G := G) k s sig) = .action k := rfl

@[simp] theorem publicPhase_terminal (s : S) :
    publicPhase (Config.terminal (G := G) s) = .terminal := rfl

end GameTheory.Sequential
