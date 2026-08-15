/-
# Hostile extraction tests

The probe for `GameTheory.Protocol.Extraction`. A protocol may have states that
look like decision states — somebody is active, play has not stopped — but that
no history ever reaches. Strategy extraction is only meaningful if such states
are genuinely invisible to the run.

`ghostArena` has exactly one: `ghost`. The two tests are that it is *not*
reachable, and that two choosers differing only there induce the same run.
Without the first test the second would be vacuous.
-/

import GameTheory.Protocol.Extraction

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol (Trace Reachable)

/-- States of the ghost arena. -/
inductive GhostSpot | begin | ghost | leftStop | rightStop
  deriving DecidableEq, Repr

/-- The single player's directions. -/
inductive Way | goLeft | goRight
  deriving DecidableEq, Repr

/-- One real decision, and one decision state nothing reaches. -/
@[reducible]
def ghostArena : ExecutionProtocol Unit where
  State := GhostSpot
  Action _ := Way
  init := .begin
  active state _ := state = .begin ∨ state = .ghost
  available _ _ := Set.univ
  terminal state := state = .leftStop ∨ state = .rightStop
  step state joint :=
    match state with
    | .begin =>
        match joint.1 () with
        | some .goLeft => FinDist.pure .leftStop
        | some .goRight => FinDist.pure .rightStop
        | none => FinDist.pure .leftStop
    | _ => FinDist.pure .leftStop
  progress := by
    rintro state hterm
    by_cases hactive : state = GhostSpot.begin ∨ state = GhostSpot.ghost
    · exact ⟨fun _ => some .goLeft, fun _ => ⟨hactive, Set.mem_univ _⟩⟩
    · exact ⟨fun _ => none, fun _ => hactive⟩

/-- Every realized step lands on a stopping state. -/
theorem ghostArena_step_target (source : GhostSpot) (joint : ∀ _ : Unit, Option Way)
    (isLegal : ghostArena.Legal source joint) (target : GhostSpot)
    (hrealized : target ∈ (ghostArena.step source ⟨joint, isLegal⟩).support) :
    target = .leftStop ∨ target = .rightStop := by
  cases source with
  | begin =>
    cases hjoint : joint () with
    | none => exact Or.inl (by simpa [hjoint] using hrealized)
    | some way =>
      cases way
      · exact Or.inl (by simpa [hjoint] using hrealized)
      · exact Or.inr (by simpa [hjoint] using hrealized)
  | ghost => exact Or.inl (by simpa using hrealized)
  | leftStop => exact absurd (Or.inl rfl) isLegal.1
  | rightStop => exact absurd (Or.inr rfl) isLegal.1

/-- Only `begin` and the two stopping states carry histories.

The index must be typed `ghostArena.State` rather than `GhostSpot`: `cases` on
an indexed inductive fails to build its motive when the index is stated at the
reduced carrier, because carriers are stored as structure fields. -/
theorem ghostArena_trace_state {state : ghostArena.State} (trace : Trace ghostArena state) :
    state = .begin ∨ state = .leftStop ∨ state = .rightStop := by
  cases trace with
  | start => exact Or.inl rfl
  | extend prior joint isLegal realized =>
    exact Or.inr (ghostArena_step_target _ joint isLegal _ realized)

/-- **Probe 1.** The ghost state really is unreachable, so the test below is not
vacuous. -/
theorem ghost_not_reachable : ¬ ghostArena.Reachable .ghost := by
  rintro ⟨trace⟩
  rcases ghostArena_trace_state trace with h | h | h <;> simp at h

/-- A chooser that goes left everywhere. -/
def leftEverywhere : ghostArena.Chooser := fun state hterm =>
  if hactive : state = GhostSpot.begin ∨ state = GhostSpot.ghost then
    ⟨fun _ => some .goLeft, hterm, fun _ => ⟨hactive, Set.mem_univ _⟩⟩
  else ⟨fun _ => none, hterm, fun _ => hactive⟩

/-- The same chooser, except that it goes right at the unreachable state. -/
def leftExceptGhost : ghostArena.Chooser := fun state hterm =>
  if hghost : state = GhostSpot.ghost then
    ⟨fun _ => some .goRight, hterm, fun _ => ⟨Or.inr hghost, Set.mem_univ _⟩⟩
  else if hactive : state = GhostSpot.begin ∨ state = GhostSpot.ghost then
    ⟨fun _ => some .goLeft, hterm, fun _ => ⟨hactive, Set.mem_univ _⟩⟩
  else ⟨fun _ => none, hterm, fun _ => hactive⟩

/-- The two choosers differ, as terms. -/
theorem choosers_differ_at_ghost :
    leftEverywhere .ghost (by simp) ≠ leftExceptGhost .ghost (by simp) := by
  intro hequal
  rw [Subtype.ext_iff] at hequal
  have hjoint := congrFun hequal ()
  simp [leftEverywhere, leftExceptGhost] at hjoint

/-- But they agree on every decision *site*, because the ghost is not one. -/
theorem restrict_eq : leftEverywhere.restrict = leftExceptGhost.restrict := by
  funext site
  obtain ⟨state, hreachable, hterm⟩ := site
  have hnotghost : state ≠ GhostSpot.ghost := by
    rintro rfl
    exact ghost_not_reachable hreachable
  simp [ExecutionProtocol.Chooser.restrict, leftEverywhere, leftExceptGhost, hnotghost]

/-- **Probe 2.** Differing off the reachable decision sites cannot be observed:
the two choosers induce the same run law at every fuel. -/
theorem runFor_eq_of_ghost_only_difference (fuel : ℕ) :
    ghostArena.runFor leftEverywhere fuel .begin =
      ghostArena.runFor leftExceptGhost fuel .begin :=
  ExecutionProtocol.runFor_congr_of_restrict_eq restrict_eq fuel
    ExecutionProtocol.reachable_init

end GameTheory.Tests
