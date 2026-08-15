/-
# Hostile arena tests

Cyclic and merging arenas must fail the premises of tree extraction *for the
intended reason*.

This is the test that `Trace` being `Type`-valued exists to make possible. The
obvious alternative — stating history uniqueness as `Subsingleton` of a
`Prop`-valued reachability relation — is vacuously true by proof irrelevance, so
it cannot distinguish a tree from a merging arena at all. Here `Trace` is data,
so `IsTreeShaped` is refutable, and this file refutes it.
-/

import GameTheory.Protocol.Execution

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol (Trace)

/-- The state a history arrived from, if any. Reading this out of a `Trace` is
possible only because traces are data. -/
def tracePrevious {ι : Type} {E : ExecutionProtocol ι} :
    ∀ {state : E.State}, Trace E state → Option E.State
  | _, .start => none
  | _, .extend (source := source) _ _ _ _ => some source

/-! ## A merging arena

Two different first moves lead to the same state, so that state has two
histories. -/

/-- States of the merging arena. -/
inductive Spot | start | lft | rgt | merged
  deriving DecidableEq, Repr

/-- The single player's directions. -/
inductive Dir | goLeft | goRight
  deriving DecidableEq, Repr

/-- One choice, then both branches rejoin. -/
@[reducible]
def mergingArena : ExecutionProtocol Unit where
  State := Spot
  Action _ := Dir
  init := .start
  active state _ := state = .start
  available _ _ := Set.univ
  terminal state := state = .merged
  step state joint :=
    match state with
    | .start =>
        match joint.1 () with
        | some .goLeft => FinDist.pure .lft
        | some .goRight => FinDist.pure .rgt
        | none => FinDist.pure .lft
    | _ => FinDist.pure .merged
  progress := by
    rintro state hterm
    by_cases hactive : state = Spot.start
    · exact ⟨fun _ => some .goLeft, fun _ => ⟨hactive, Set.mem_univ _⟩⟩
    · exact ⟨fun _ => none, fun _ => hactive⟩

theorem legal_goLeft : mergingArena.Legal .start (fun _ => some .goLeft) :=
  ⟨by simp, fun _ => ⟨rfl, Set.mem_univ _⟩⟩

theorem legal_goRight : mergingArena.Legal .start (fun _ => some .goRight) :=
  ⟨by simp, fun _ => ⟨rfl, Set.mem_univ _⟩⟩

theorem legal_lft : mergingArena.Legal .lft mergingArena.noop :=
  mergingArena.noop_isLegal (by simp) (fun _ h => by simp at h)

theorem legal_rgt : mergingArena.Legal .rgt mergingArena.noop :=
  mergingArena.noop_isLegal (by simp) (fun _ h => by simp at h)

theorem realized_lft :
    Spot.lft ∈ (mergingArena.step .start ⟨_, legal_goLeft⟩).support :=
  FinDist.mem_support_pure.2 rfl

theorem realized_rgt :
    Spot.rgt ∈ (mergingArena.step .start ⟨_, legal_goRight⟩).support :=
  FinDist.mem_support_pure.2 rfl

theorem realized_merged_of_lft :
    Spot.merged ∈ (mergingArena.step .lft ⟨_, legal_lft⟩).support :=
  FinDist.mem_support_pure.2 rfl

theorem realized_merged_of_rgt :
    Spot.merged ∈ (mergingArena.step .rgt ⟨_, legal_rgt⟩).support :=
  FinDist.mem_support_pure.2 rfl

/-- Reaching `merged` through the left branch. -/
def traceViaLeft : Trace mergingArena .merged :=
  .extend (.extend .start _ legal_goLeft realized_lft) _ legal_lft realized_merged_of_lft

/-- Reaching `merged` through the right branch. -/
def traceViaRight : Trace mergingArena .merged :=
  .extend (.extend .start _ legal_goRight realized_rgt) _ legal_rgt realized_merged_of_rgt

/-- The two histories are genuinely different data: they arrive from different
states. -/
theorem traceViaLeft_ne_traceViaRight : traceViaLeft ≠ traceViaRight := by
  intro hequal
  have hprev := congrArg tracePrevious hequal
  simp [traceViaLeft, traceViaRight, tracePrevious] at hprev

/-- A merging arena refutes tree-shapedness, and for the
intended reason: one state carries two distinct histories. -/
theorem mergingArena_not_treeShaped : ¬ mergingArena.IsTreeShaped := by
  intro htree
  exact traceViaLeft_ne_traceViaRight ((htree .merged).allEq traceViaLeft traceViaRight)

/-- The contrast that motivates making histories data. Had reachability been
stated as a `Prop`, uniqueness would be vacuous by proof irrelevance and the
merging arena above would have *passed* the tree-extraction premise. This is
reproduced here so the contrast is visible. -/
def ReachableProp {ι : Type} (E : ExecutionProtocol ι) (state : E.State) : Prop :=
  Nonempty (Trace E state)

example (state : mergingArena.State) : Subsingleton (ReachableProp mergingArena state) :=
  ⟨fun _ _ => rfl⟩

/-! ## A cyclic arena

Play never stops, so no horizon bounds it. -/

/-- The only state of the cyclic arena. -/
inductive Cycle | loop
  deriving DecidableEq, Repr

/-- An administrative step that returns to where it started. -/
@[reducible]
def cyclicArena : ExecutionProtocol Unit where
  State := Cycle
  Action _ := Empty
  init := .loop
  active _ _ := False
  available _ _ := Set.univ
  terminal _ := False
  step _ _ := FinDist.pure .loop
  progress := fun _ _ => ⟨fun _ => none, fun _ h => h⟩

theorem legal_loop : cyclicArena.Legal .loop cyclicArena.noop :=
  cyclicArena.noop_isLegal (fun h => h) (fun _ h => h)

theorem realized_loop :
    Cycle.loop ∈ (cyclicArena.step .loop ⟨_, legal_loop⟩).support :=
  FinDist.mem_support_pure.2 rfl

/-- A history that goes round the loop `count` times. -/
def loopTrace : (count : ℕ) → Trace cyclicArena .loop
  | 0 => .start
  | count + 1 => .extend (loopTrace count) _ legal_loop realized_loop

@[simp]
theorem loopTrace_length (count : ℕ) : (loopTrace count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [loopTrace, Trace.length] using ih

/-- No horizon bounds a cyclic arena, and for the intended
reason: histories of every length exist and none of them has stopped. -/
theorem cyclicArena_not_boundedHorizon (horizon : ℕ) :
    ¬ cyclicArena.BoundedHorizon horizon := by
  intro hbound
  exact hbound .loop (loopTrace horizon) (by simp)

end GameTheory.Tests
