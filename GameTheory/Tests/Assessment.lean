/-
# Probes for the one-shot-deviation interface

`GameTheory.Protocol.Assessment` reduces the open-game context to two fields and
*derives* local optimality from them. These probes check that the reduction did
not throw away the content.

The failure mode to rule out is a context whose `value` ignores one of its two
fields. Such a `Context` would still satisfy every theorem in the module —
`isLocallyOptimal_iff_no_profitable_deviation` is a tautology about `value`, and
would hold just as well if `value` were constant. So each probe below fixes one
field and varies the other.
-/

import GameTheory.Protocol.Assessment

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Probability
open GameTheory.Protocol.ExecutionProtocol (Context)

/-- Two hidden states and a stopping state. -/
inductive Room | left | right | done
  deriving DecidableEq, Repr

/-- The deviator's two calls. -/
inductive Call | up | down
  deriving DecidableEq, Repr

/-- A protocol just rich enough to carry a context: one mover, two rooms. -/
@[reducible]
def rooms : ExecutionProtocol Unit where
  State := Room
  Action _ := Call
  init := .left
  active state _ := state ≠ .done
  available _ _ := Set.univ
  terminal state := state = .done
  terminal_inactive := by rintro state rfl i h; exact h rfl
  step _ _ := FinDist.pure .done
  progress := by
    rintro state hterm
    exact ⟨fun _ => some .up, fun _ => ⟨hterm, Set.mem_univ _⟩⟩

/-- A context whose choice matters: `up` leads to `left`, `down` to `right`. -/
def splitContext (continuation : Room → ℝ) : rooms.Context () where
  outcome choice :=
    match choice with
    | some .up => FinDist.pure .left
    | some .down => FinDist.pure .right
    | none => FinDist.pure .done
  continuation := continuation

/-- A continuation that prefers `left`. -/
def prefersLeft : Room → ℝ
  | .left => 1
  | .right => 0
  | .done => 0

/-- A continuation that prefers `right`. -/
def prefersRight : Room → ℝ
  | .left => 0
  | .right => 1
  | .done => 0

theorem value_up (continuation : Room → ℝ) :
    (splitContext continuation).value (some .up) = continuation .left :=
  FinDist.expect_pure ..

theorem value_down (continuation : Room → ℝ) :
    (splitContext continuation).value (some .down) = continuation .right :=
  FinDist.expect_pure ..

/-- Both calls are on the table. -/
def bothCalls : Set (Option Call) := {some .up, some .down}

/-! ## Probe 1: the value depends on the continuation

Fixing the outcome map and varying only the continuation flips which call is
optimal. This kills any `value` that ignores the continuation — which is
precisely the field the open-game context contributes and a static equilibrium
lacks. -/

theorem up_optimal_under_prefersLeft :
    (splitContext prefersLeft).IsLocallyOptimal bothCalls (some .up) := by
  rintro alternative (rfl | rfl)
  · rw [value_up]
  · rw [value_down, value_up]
    norm_num [prefersLeft]

theorem up_not_optimal_under_prefersRight :
    ¬ (splitContext prefersRight).IsLocallyOptimal bothCalls (some .up) := by
  intro hopt
  have hdown := hopt (some .down) (by simp [bothCalls])
  rw [value_down, value_up] at hdown
  norm_num [prefersRight] at hdown

/-! ## Probe 2: the value depends on the outcome map

Fixing the continuation and varying only where the calls lead flips the optimum
back. This kills any `value` that ignores the outcome map. -/

/-- The same continuation, but the calls lead the other way. -/
def swappedContext (continuation : Room → ℝ) : rooms.Context () where
  outcome choice :=
    match choice with
    | some .up => FinDist.pure .right
    | some .down => FinDist.pure .left
    | none => FinDist.pure .done
  continuation := continuation

theorem up_optimal_under_swapped :
    (swappedContext prefersRight).IsLocallyOptimal bothCalls (some .up) := by
  rintro alternative (rfl | rfl) <;>
    simp [Context.value, swappedContext, prefersRight, FinDist.expect_pure]

/-- Same continuation as `up_not_optimal_under_prefersRight`, opposite verdict:
only the outcome map changed. -/
theorem outcome_map_matters :
    ¬ (splitContext prefersRight).IsLocallyOptimal bothCalls (some .up) ∧
      (swappedContext prefersRight).IsLocallyOptimal bothCalls (some .up) :=
  ⟨up_not_optimal_under_prefersRight, up_optimal_under_swapped⟩

/-! ## Probe 3: a profitable one-shot deviation is exhibited, not just denied

`isLocallyOptimal_iff_no_profitable_deviation` would be vacuously useful if no
profitable deviation ever existed. Here is one. -/

theorem down_is_profitable_under_prefersRight :
    (splitContext prefersRight).IsProfitableDeviation bothCalls (some .up) (some .down) := by
  refine ⟨by simp [bothCalls], ?_⟩
  rw [value_up, value_down]
  norm_num [prefersRight]

/-- And the interface theorem converts the exhibited deviation into a refutation
of optimality, rather than the refutation being assumed. -/
theorem no_optimality_from_profitable_deviation :
    ¬ (splitContext prefersRight).IsLocallyOptimal bothCalls (some .up) := by
  rw [Context.isLocallyOptimal_iff_no_profitable_deviation]
  intro hnone
  exact hnone ⟨some .down, down_is_profitable_under_prefersRight⟩

/-! ## Probe 4: `ofBelief` really averages over the belief

The belief-built context must depend on the belief, not just on one state. -/

/-- A branch that reports where it was. -/
def roomBranch (state : Room) (_choice : Option Call) : FinDist Room := FinDist.pure state

theorem ofBelief_value_pure (state : Room) (continuation : Room → ℝ)
    (choice : Option Call) :
    (Context.ofBelief (E := rooms) (i := ()) (FinDist.pure state) roomBranch
      continuation).value choice = continuation state := by
  rw [Context.ofBelief_value]
  simp [roomBranch]

/-- Two different point beliefs give two different values, so the belief is not
being discarded. -/
theorem belief_matters :
    (Context.ofBelief (E := rooms) (i := ()) (FinDist.pure .left) roomBranch
        prefersLeft).value (some .up) ≠
      (Context.ofBelief (E := rooms) (i := ()) (FinDist.pure .right) roomBranch
        prefersLeft).value (some .up) := by
  rw [ofBelief_value_pure, ofBelief_value_pure]
  simp [prefersLeft]

end GameTheory.Tests
