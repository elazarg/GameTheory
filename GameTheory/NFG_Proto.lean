import GameTheory.SeqProto
import Math.Probability

/-!
# NFG → Protocol Encoding

Encodes a normal-form game (with uniform action type) as a one-round Protocol.

## Design

For games where all players share the same action type `A`, the encoding is direct:
- State = `Option Outcome` (None = not played, Some = terminal)
- View = `PUnit` (simultaneous — no observation)
- Signal = `PUnit` (no private information)
- One round: all players submit actions simultaneously

The general case (per-player action types `B i`) requires encoding into a uniform
type, e.g., via `A = Σ i, B i`. This is deferred.
-/

namespace GameTheory

open Math.Probability

variable {m : ℕ}

/-- A simple simultaneous game with uniform action type: all players choose
    from the same action set `Act`, and the outcome depends on the joint profile. -/
structure SimGame (m : ℕ) where
  Act : Type
  Outcome : Type
  outcome : (Fin m → Act) → Outcome
  utility : Outcome → Fin m → ℝ

/-- The single round of a simultaneous game Protocol. -/
noncomputable def SimGame.round (G : SimGame m) [Nonempty G.Act] :
    Round m (Option G.Outcome) PUnit G.Act PUnit where
  signal := fun _ => PMF.pure (fun _ => PUnit.unit)
  view := fun _ _ _ => PUnit.unit
  transition := fun s acts =>
    match s with
    | none =>
      -- Collect actual actions (default to first action if none submitted)
      some (G.outcome (fun i =>
        match acts i with
        | some a => a
        | none => Classical.arbitrary G.Act))
    | some o => some o

/-- One-round Protocol encoding of a simultaneous game. -/
noncomputable def SimGame.toProtocol (G : SimGame m) [Nonempty G.Act] :
    Protocol m (Option G.Outcome) PUnit G.Act PUnit where
  init := none
  rounds := [G.round]

/-- Utility function on the Protocol state space. -/
noncomputable def SimGame.protoUtility (G : SimGame m) :
    Option G.Outcome → Fin m → ℝ
  | some o => G.utility o
  | none => fun _ => 0

/-- The KernelGame derived from the Protocol encoding. -/
noncomputable def SimGame.toKernelGame (G : SimGame m) [Nonempty G.Act] :
    KernelGame (Fin m) :=
  G.toProtocol.toKernelGame G.protoUtility

end GameTheory
