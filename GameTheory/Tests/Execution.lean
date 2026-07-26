/-
# Hostile execution tests

RFC 9.1.6 makes it a core-invalidating failure if the selected execution
semantics needs an impossible total legal-action chooser at terminal states,
dummy probability data at chance nodes, or evaluation that silently stops at a
chance node. These are the tests that would detect it.

The protocol below is deliberately minimal and deliberately awkward: it has a
genuine chance node with no mover, a player move, and terminal states, so all
three failure modes are reachable in one example.
-/

import GameTheory.Protocol.Execution

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Probability

/-! ## Structural test: terminal states are never asked for an action

`Chooser` takes a non-terminality proof, so a total chooser is not merely
unnecessary — it is not the type the runner consumes. -/

example {ι : Type} (E : ExecutionProtocol ι) :
    E.Chooser =
      ((state : E.State) → ¬ E.terminal state →
        { joint : ∀ i, Option (E.Action i) // E.Legal state joint }) := rfl

/-- And a terminal state genuinely has no legal joint action, so a total chooser
could not be written even if the runner asked for one. -/
example {ι : Type} (E : ExecutionProtocol ι) {state : E.State}
    (hterm : E.terminal state) (joint : ∀ i, Option (E.Action i)) :
    ¬ E.Legal state joint :=
  E.terminal_no_legal hterm joint

/-! ## A coin flip followed by one decision

`chance` is a no-mover state with a fair transition law; `heads`/`tails` are
decision states for the single player; `done` is terminal. -/

/-- Execution states of the test protocol. -/
inductive Spot
  | chance
  | heads
  | tails
  | done
  deriving DecidableEq, Repr

/-- The single player's actions. -/
inductive Move
  | take
  | leave
  deriving DecidableEq, Repr

/-- One player, one coin, one decision, then stop.

Marked `@[reducible]` for the same reason `GameForm.mixed` and
`TableGame.toForm` are: without it `coinThenMove.State` does not reduce to
`Spot` at `instances` transparency, so instance search and `simp` fail on the
concrete protocol. This is the third module in which D1's bundled-structure
design has required the annotation. -/
@[reducible]
def coinThenMove : ExecutionProtocol Unit where
  State := Spot
  Action _ := Move
  init := .chance
  active state _ := state = .heads ∨ state = .tails
  available _ _ := Set.univ
  terminal state := state = .done
  terminal_inactive := by rintro state rfl i (h | h) <;> simp at h
  step state joint :=
    match state with
    | .chance => FinDist.mix (1 / 2) (by norm_num) (by norm_num)
        (FinDist.pure .heads) (FinDist.pure .tails)
    | _ => FinDist.pure .done
  progress := by
    rintro state hterm
    by_cases hactive : state = .heads ∨ state = .tails
    · exact ⟨fun _ => some .take, fun _ => ⟨hactive, Set.mem_univ _⟩⟩
    · exact ⟨fun _ => none, fun _ => hactive⟩

/-- The coin state is a chance state: execution continues and nobody moves. -/
theorem coinThenMove_chance_isChance : coinThenMove.IsChance .chance := by
  refine ⟨by simp, fun i hactive => ?_⟩
  rcases hactive with h | h <;> exact absurd h (by simp)

/-! ### Hostile test 2: the chance law is normalized and nondegenerate

Chance is carried by the transition law, not by dummy data attached to a `none`
mover. -/

theorem coinThenMove_chanceLaw_heads :
    (coinThenMove.chanceLaw coinThenMove_chance_isChance).prob .heads = 1 / 2 := by
  simp [ExecutionProtocol.chanceLaw, FinDist.prob_pure_eq_ite]

theorem coinThenMove_chanceLaw_tails :
    (coinThenMove.chanceLaw coinThenMove_chance_isChance).prob .tails = 1 / 2 := by
  simp [ExecutionProtocol.chanceLaw, FinDist.prob_pure_eq_ite]
  norm_num

/-- The two branches carry all the mass: the law is a genuine distribution, not
a degenerate placeholder. -/
theorem coinThenMove_chanceLaw_normalized :
    (coinThenMove.chanceLaw coinThenMove_chance_isChance).prob .heads +
      (coinThenMove.chanceLaw coinThenMove_chance_isChance).prob .tails = 1 := by
  rw [coinThenMove_chanceLaw_heads, coinThenMove_chanceLaw_tails]
  norm_num

/-! ### Hostile test 1: the protocol runs, and does not stop at chance

Evaluation must step *through* the chance node rather than halting there. -/

/-- A policy that always takes. -/
def alwaysTake : coinThenMove.Chooser := fun state hterm =>
  if hactive : state = Spot.heads ∨ state = Spot.tails then
    ⟨fun _ => some .take, hterm, fun _ => ⟨hactive, Set.mem_univ _⟩⟩
  else ⟨fun _ => none, hterm, fun _ => hactive⟩

/-- One step from the chance node is the coin law, not a halt. -/
theorem runFor_one_from_chance :
    coinThenMove.runFor alwaysTake 1 .chance =
      coinThenMove.chanceLaw coinThenMove_chance_isChance := by
  rw [ExecutionProtocol.runFor_succ_of_chance alwaysTake 0 coinThenMove_chance_isChance,
    show coinThenMove.runFor alwaysTake 0 = FinDist.pure from rfl, FinDist.bind_pure]

/-- Terminal states are absorbing under every policy and every fuel. -/
theorem runFor_done (fuel : ℕ) :
    coinThenMove.runFor alwaysTake fuel .done = FinDist.pure .done :=
  ExecutionProtocol.runFor_of_terminal alwaysTake fuel rfl

end GameTheory.Tests
