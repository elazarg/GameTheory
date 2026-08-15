/-
# Hostile execution tests

Execution semantics must not need an impossible total legal-action chooser at
terminal states, dummy probability data at chance nodes, or evaluation that
silently stops at a chance node. These are the tests that would detect any of
those.

The protocol below is deliberately minimal and deliberately awkward: it has a
genuine chance node with no mover, a player move whose *choice changes the
outcome*, and two distinguishable terminal states, so every failure mode is
reachable in one protocol.

The last point matters. If `step` ignored the joint action, every other test
here would still pass under a runner that discarded the chooser's answer — for
instance one that picked a legal action itself with `Classical.choice` on
`exists_legal`. `takePolicy_ne_leavePolicy` is the probe that rules that out:
two policies produce two *different* two-step laws.
-/

import GameTheory.Protocol.Execution

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

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

/-! ## A coin flip followed by one consequential decision -/

/-- Execution states. The two terminal states record *which* action was taken. -/
inductive Spot
  | chance
  | heads
  | tails
  | tookIt
  | leftIt
  deriving DecidableEq, Repr

/-- The single player's actions. -/
inductive Move
  | take
  | leave
  deriving DecidableEq, Repr

/-- Where a move leads. -/
def Move.resolve : Move → Spot
  | .take => .tookIt
  | .leave => .leftIt

/-- One player, one coin, one decision that matters, then stop.

Marked `@[reducible]` for the same reason `GameForm.mixed` and
`TableGame.toForm` are: without it `coinThenMove.State` does not reduce to
`Spot` at `instances` transparency, so instance search and `simp` fail on the
concrete protocol. Storing carriers as structure fields requires this wherever a
concrete protocol is defined. -/
@[reducible]
def coinThenMove : ExecutionProtocol Unit where
  State := Spot
  Action _ := Move
  init := .chance
  active state _ := state = .heads ∨ state = .tails
  available _ _ := Set.univ
  terminal state := state = .tookIt ∨ state = .leftIt
  step state joint :=
    match state with
    | .chance =>
        FinDist.mix (1 / 2) (by norm_num) (by norm_num)
          (FinDist.pure .heads) (FinDist.pure .tails)
    | _ =>
        match joint.1 () with
        | some move => FinDist.pure move.resolve
        | none => FinDist.pure .leftIt
  progress := by
    rintro state hterm
    by_cases hactive : state = Spot.heads ∨ state = Spot.tails
    · exact ⟨fun _ => some .take, fun _ => ⟨hactive, Set.mem_univ _⟩⟩
    · exact ⟨fun _ => none, fun _ => hactive⟩

theorem coinThenMove_heads_not_terminal : ¬ coinThenMove.terminal .heads := by simp

theorem coinThenMove_tails_not_terminal : ¬ coinThenMove.terminal .tails := by simp

/-- The coin state is a chance state: execution continues and nobody moves. -/
theorem coinThenMove_chance_isChance : coinThenMove.IsChance .chance := by
  refine ⟨by simp, fun i hactive => ?_⟩
  rcases hactive with h | h <;> exact absurd h (by simp)

/-! ### Hostile test: the chance law is normalized and nondegenerate

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

/-! ### Hostile test: the run steps through chance rather than halting -/

/-- A policy that always takes. -/
def takePolicy : coinThenMove.Chooser := fun state hterm =>
  if hactive : state = Spot.heads ∨ state = Spot.tails then
    ⟨fun _ => some .take, hterm, fun _ => ⟨hactive, Set.mem_univ _⟩⟩
  else ⟨fun _ => none, hterm, fun _ => hactive⟩

/-- A policy that always leaves. -/
def leavePolicy : coinThenMove.Chooser := fun state hterm =>
  if hactive : state = Spot.heads ∨ state = Spot.tails then
    ⟨fun _ => some .leave, hterm, fun _ => ⟨hactive, Set.mem_univ _⟩⟩
  else ⟨fun _ => none, hterm, fun _ => hactive⟩

/-- One step from the chance node is the coin law, not a halt. -/
theorem runFor_one_from_chance :
    coinThenMove.runFor takePolicy 1 .chance =
      coinThenMove.chanceLaw coinThenMove_chance_isChance := by
  rw [ExecutionProtocol.runFor_succ_of_chance takePolicy 0 coinThenMove_chance_isChance,
    show coinThenMove.runFor takePolicy 0 = FinDist.pure from rfl, FinDist.bind_pure]

/-- Terminal states are absorbing under every policy and every fuel. -/
theorem runFor_tookIt (fuel : ℕ) :
    coinThenMove.runFor takePolicy fuel .tookIt = FinDist.pure .tookIt :=
  ExecutionProtocol.runFor_of_terminal takePolicy fuel (by simp)

/-! ### Hostile test: the chosen action actually drives the run

A runner that consulted the chooser but discarded its answer — or that picked
any legal action itself — would make the two policies agree. They do not. -/

theorem runFor_one_heads_take :
    coinThenMove.runFor takePolicy 1 .heads = FinDist.pure .tookIt := by
  rw [ExecutionProtocol.runFor_succ_of_not_terminal takePolicy 0
    coinThenMove_heads_not_terminal]
  simp [takePolicy, Move.resolve]

theorem runFor_one_tails_take :
    coinThenMove.runFor takePolicy 1 .tails = FinDist.pure .tookIt := by
  rw [ExecutionProtocol.runFor_succ_of_not_terminal takePolicy 0
    coinThenMove_tails_not_terminal]
  simp [takePolicy, Move.resolve]

theorem runFor_one_heads_leave :
    coinThenMove.runFor leavePolicy 1 .heads = FinDist.pure .leftIt := by
  rw [ExecutionProtocol.runFor_succ_of_not_terminal leavePolicy 0
    coinThenMove_heads_not_terminal]
  simp [leavePolicy, Move.resolve]

theorem runFor_one_tails_leave :
    coinThenMove.runFor leavePolicy 1 .tails = FinDist.pure .leftIt := by
  rw [ExecutionProtocol.runFor_succ_of_not_terminal leavePolicy 0
    coinThenMove_tails_not_terminal]
  simp [leavePolicy, Move.resolve]

/-- Taking, through the coin, ends at `tookIt` with certainty. -/
theorem prob_tookIt_take :
    (coinThenMove.runFor takePolicy 2 .chance).prob .tookIt = 1 := by
  rw [ExecutionProtocol.runFor_succ_of_chance takePolicy 1 coinThenMove_chance_isChance,
    FinDist.prob_bind, ExecutionProtocol.chanceLaw]
  show (FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure Spot.heads) (FinDist.pure Spot.tails)).expect
      (fun s => (coinThenMove.runFor takePolicy 1 s).prob .tookIt) = 1
  rw [FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure,
    runFor_one_heads_take, runFor_one_tails_take]
  simp

/-- Leaving, through the same coin, never reaches `tookIt`. -/
theorem prob_tookIt_leave :
    (coinThenMove.runFor leavePolicy 2 .chance).prob .tookIt = 0 := by
  rw [ExecutionProtocol.runFor_succ_of_chance leavePolicy 1 coinThenMove_chance_isChance,
    FinDist.prob_bind, ExecutionProtocol.chanceLaw]
  show (FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure Spot.heads) (FinDist.pure Spot.tails)).expect
      (fun s => (coinThenMove.runFor leavePolicy 1 s).prob .tookIt) = 0
  rw [FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure,
    runFor_one_heads_leave, runFor_one_tails_leave]
  simp [FinDist.prob_pure_eq_ite]

/-- **The probe.** The run law depends on the chooser's answer, so the runner
cannot be discarding it. -/
theorem takePolicy_ne_leavePolicy :
    coinThenMove.runFor takePolicy 2 .chance ≠
      coinThenMove.runFor leavePolicy 2 .chance := by
  intro hequal
  have hcontra : (1 : ℝ) = 0 := by
    rw [← prob_tookIt_take, ← prob_tookIt_leave, hequal]
  exact one_ne_zero hcontra

end GameTheory.Tests
