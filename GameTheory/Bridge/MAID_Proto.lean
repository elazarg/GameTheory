import GameTheory.MAID.MAID
import GameTheory.Protocol.SeqProto

/-!
# MAID → Protocol Encoding

Encodes Multi-Agent Influence Diagrams into the `Protocol` abstraction.

## Encoding design

MAID evaluation (`evalAssignDist`) is a fold over the topological
order — a natural sequential unrolling.

- **State** = `Nat × TAssign S` (step index + current assignment)
- **View** = `Nat × TAssign S` (full state — perfect info)
- **Action** = `ℕ` (universal action index, interpreted modulo domain size)
- **Signal** = `PUnit` (no exogenous signals; chance is in the transition)

Each round processes the node at the current index in topological order.
Terminal steps (past the horizon) are absorbing.

## Main definitions

- `MAID.Struct.maidRound` — the one-step round
- `MAID.Struct.toProtocol` — Protocol with `topoOrder.length` rounds
-/

namespace MAID

open GameTheory

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {n : Nat}

-- ============================================================================
-- State type
-- ============================================================================

/-- State for the Protocol encoding: step index paired with current
    total assignment. -/
abbrev ProtoState (S : Struct Player n) := Nat × TAssign S

-- ============================================================================
-- The one-step round
-- ============================================================================

/-- One-step round for a MAID Protocol encoding.
    At each step, the current node in topological order is processed:
    the signal draws a value from `nodeDist`, and the transition
    uses signal player 0's relayed value to update the assignment.
    Past the horizon, the state is absorbing. -/
noncomputable def Struct.maidStochasticRound (S : Struct Player n) (sem : Sem S)
    (pol : Policy S) (m : ℕ) [NeZero m] :
    Round m (ProtoState S) (ProtoState S) ℕ ℕ where
  signal st :=
    let idx := st.1
    let a := st.2
    if h : idx < S.topoOrder.length then
      let nd := S.topoOrder[idx]
      (nodeDist S sem pol nd a).map (fun v => fun _ => v.val)
    else
      PMF.pure (fun _ => 0)
  view _i st sig := st
  transition st acts :=
    let idx := st.1
    let a := st.2
    if h : idx < S.topoOrder.length then
      let nd := S.topoOrder[idx]
      -- Read the sampled value from signal (relayed via player 0's action)
      let v_raw := (acts ⟨0, NeZero.pos m⟩).getD 0
      (idx + 1, updateAssign a nd ⟨v_raw % S.domainSize nd,
        Nat.mod_lt v_raw (S.dom_pos nd)⟩)
    else
      st

-- ============================================================================
-- Protocol construction
-- ============================================================================

/-- Protocol encoding of a MAID: `topoOrder.length` copies of `maidStochasticRound`.

    The encoding bakes in the policy and semantics — it represents one
    specific evaluation of the MAID. -/
noncomputable def Struct.toProtocol (S : Struct Player n) (sem : Sem S)
    (pol : Policy S) (m : ℕ) [NeZero m] :
    Protocol m (ProtoState S) (ProtoState S) ℕ ℕ where
  init := (0, defaultAssign S)
  rounds := List.replicate S.topoOrder.length (S.maidStochasticRound sem pol m)

end MAID
