/-
# The simultaneous-action slice

The measurement that runs *against* the finite-first presentation. It needs no
certificates where the general-state protocol needs two plus an extraction
construction, so this is the axis where the comparison reverses.

The general-state protocol has several players active at one state and a `step`
that consumes a joint action, so simultaneity is native. The finite-first
`Tree.node` carries a single `mover`, so the only way to encode the same game is
to sequentialize it — and this file proves that sequentializing is not
faithful: it strictly enlarges the strategy space, because the second mover's
contingent plan gets to depend on the first mover's action.

That is the classical reason a game tree needs information sets before it can
represent a simultaneous move. Here it is a theorem about strategy counts.
-/

import GameTheory.Protocol.Tree
import GameTheory.Protocol.Execution

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Probability

/-- Outcomes of a one-shot matching game. -/
inductive Pair | opening | agreed | split
  deriving DecidableEq, Repr

/-! ## The general-state encoding: simultaneity is native -/

/-- Two players call simultaneously; they agree exactly when the calls match. -/
@[reducible]
def matching : ExecutionProtocol (Fin 2) where
  State := Pair
  Action _ := Bool
  init := .opening
  active state _ := state = .opening
  available _ _ := Set.univ
  terminal state := state = .agreed ∨ state = .split
  terminal_inactive := by rintro state (rfl | rfl) i h <;> simp at h
  step state joint :=
    match state with
    | .opening =>
        match joint.1 0, joint.1 1 with
        | some first, some second =>
            FinDist.pure (if first = second then .agreed else .split)
        | _, _ => FinDist.pure .split
    | _ => FinDist.pure .split
  progress := by
    rintro state hterm
    by_cases hopen : state = Pair.opening
    · exact ⟨fun _ => some true, fun _ => ⟨hopen, Set.mem_univ _⟩⟩
    · exact ⟨fun _ => none, fun _ => hopen⟩

/-- Both players move at the opening state. This is what the tree cannot say. -/
theorem matching_both_active : ∀ i : Fin 2, matching.active .opening i :=
  fun _ => rfl

/-- A legal joint action at the opening state must supply a move for *both*
players; neither may sit out. -/
theorem matching_legal_forces_both {joint : ∀ _ : Fin 2, Option Bool}
    (hlegal : matching.Legal .opening joint) (i : Fin 2) :
    ∃ call : Bool, joint i = some call := by
  have hi := hlegal.2 i
  cases hcase : joint i with
  | none => rw [hcase] at hi; exact absurd rfl hi
  | some call => exact ⟨call, rfl⟩

/-- Both players call `true`. -/
def bothTrue : ∀ _ : Fin 2, Option Bool := fun _ => some true

/-- The first player deviates to `false`. -/
def firstFalse : ∀ _ : Fin 2, Option Bool := fun i => if i = 0 then some false else some true

theorem legal_bothTrue : matching.Legal .opening bothTrue :=
  ⟨by simp, fun _ => ⟨rfl, Set.mem_univ _⟩⟩

theorem legal_firstFalse : matching.Legal .opening firstFalse := by
  refine ⟨by simp, fun i => ?_⟩
  by_cases h : i = 0 <;> simp [firstFalse, h]

/-- **Discriminating probe.** The outcome depends on *both* calls: changing only
the first player's call flips the result. A protocol that read one player's
action and ignored the other would fail this. -/
theorem matching_outcome_depends_on_both :
    matching.step .opening ⟨bothTrue, legal_bothTrue⟩ ≠
      matching.step .opening ⟨firstFalse, legal_firstFalse⟩ := by
  have hboth : matching.step .opening ⟨bothTrue, legal_bothTrue⟩ = FinDist.pure .agreed := rfl
  have hfirst : matching.step .opening ⟨firstFalse, legal_firstFalse⟩ =
      FinDist.pure .split := rfl
  rw [hboth, hfirst]
  intro hequal
  have hmass := congrArg (fun law => FinDist.prob law Pair.agreed) hequal
  simp [FinDist.prob_pure_eq_ite] at hmass

/-! ## The finite-first encoding: only by sequentializing

`Tree.node` carries one `mover`, so the same game must be written as a first
move followed by a second. -/

/-- The sequentialized matching game. -/
def sequentialTree : Tree (Fin 2) (fun _ => Bool) Pair :=
  .node 0 fun first => .node 1 fun second =>
    .leaf (if first = second then .agreed else .split)

/-- A simultaneous strategy profile is one call per player. -/
abbrev SimultaneousProfile : Type := ∀ _ : Fin 2, Bool

theorem card_simultaneousProfile : Fintype.card SimultaneousProfile = 4 := by rfl

/-- The sequentialized tree has eight contingent plans, because the second
mover's plan is a *function* of the first mover's call. -/
theorem card_sequentialPlans : Fintype.card (Tree.PureStrategy sequentialTree) = 8 := by
  rfl

/-- **The measurement.** Sequentializing a simultaneous move is not faithful: it
strictly enlarges the strategy space. The finite-first candidate therefore
cannot encode this slice without gaining an information layer — the very
machinery whose absence made it cheaper on the certificate axis. -/
theorem sequentialization_enlarges_strategy_space :
    Fintype.card (Tree.PureStrategy sequentialTree) ≠ Fintype.card SimultaneousProfile := by
  rw [card_sequentialPlans, card_simultaneousProfile]
  decide

/-- And the extra plans are real: the second mover can condition on the first
mover's call, which no simultaneous strategy can do. -/
def respondingPlan : Tree.PureStrategy sequentialTree :=
  (true, fun first => (first, fun _ => PUnit.unit))

/-- The responding plan matches whatever the first mover called, so it always
reaches `agreed` — an outcome no simultaneous profile can guarantee against
both calls. -/
theorem respondingPlan_always_agrees :
    Tree.eval sequentialTree respondingPlan = FinDist.pure .agreed := rfl

end GameTheory.Tests
