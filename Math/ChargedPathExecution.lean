/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Math.ChargedPathSelection

/-!
# Chronological execution in a charged relation

This file supplies the choice principle needed to execute a multivalued local
rule. It deliberately uses `ChargedRelation.Path` and `InfinitePathFrom`
rather than introducing a second finite- or infinite-path language.

An edge stream is recorded only as the existential data needed to expose each
chronological edge. The constructor `infinitePathFromOfEdgeStream` packages
the same data into the charged-path API, so its prefix charges and budget
theorems are immediately available.
-/

open scoped BigOperators

namespace Math.ChargedPathBudget.ChargedRelation

universe u v

variable {State : Type u} {Edge : Type v}

namespace Path

@[simp]
theorem length_castTgt {R : ChargedRelation State Edge} {s t w : State}
    (h : t = w) (path : R.Path s t) :
    (path.castTgt h).length = path.length := by
  subst h
  rfl

@[simp]
theorem length_castSrc {R : ChargedRelation State Edge} {s t w : State}
    (h : s = t) (path : R.Path s w) :
    (path.castSrc h).length = path.length := by
  subst h
  rfl

@[simp]
theorem length_edge {R : ChargedRelation State Edge} (edge : Edge)
    {s t : State} (hsrc : R.src edge = s) (htgt : R.tgt edge = t) :
    (Path.edge edge hsrc htgt).length = 1 := by
  simp [Path.edge, Path.single]

end Path

/-- A target is reachable when there is a finite charged path to it. -/
def Reaches (R : ChargedRelation State Edge) (start target : State) : Prop :=
  Nonempty (R.Path start target)

/-- A chronological edge stream exposes one actual relation edge at every date. -/
def HasEdgeStreamFrom (R : ChargedRelation State Edge) (start : State) : Prop :=
  ∃ state : ℕ → State, ∃ edge : ℕ → Edge,
    state 0 = start ∧
      ∀ n, R.src (edge n) = state n ∧ R.tgt (edge n) = state (n + 1)

/-- A chronological execution either reaches a terminal state in finite time
or supplies an actual edge at every date forever. -/
def HasChronologicalExecution (R : ChargedRelation State Edge)
    (Terminal : State → Prop) (start : State) : Prop :=
  (∃ terminal, R.Reaches start terminal ∧ Terminal terminal) ∨
    R.HasEdgeStreamFrom start

/-- Package chronological single-edge data into the established infinite-path
API. Each block of the resulting path is exactly one edge. -/
noncomputable def infinitePathFromOfEdgeStream
    (R : ChargedRelation State Edge) (start : State)
    (state : ℕ → State) (edge : ℕ → Edge)
    (hzero : state 0 = start)
    (hstep : ∀ n, R.src (edge n) = state n ∧ R.tgt (edge n) = state (n + 1)) :
    R.InfinitePathFrom start where
  state := state
  state_zero := hzero
  segment n := Path.edge (edge n) (hstep n).1 (hstep n).2
  segment_length_pos n := by
    simp

/-- The charged-path block extracted from a chronological edge stream has the
charge of that edge. -/
@[simp]
theorem infinitePathFromOfEdgeStream_segment_chargeSum
    (R : ChargedRelation State Edge) (start : State)
    (state : ℕ → State) (edge : ℕ → Edge)
    (hzero : state 0 = start)
    (hstep : ∀ n, R.src (edge n) = state n ∧ R.tgt (edge n) = state (n + 1))
    (n : ℕ) :
    ((infinitePathFromOfEdgeStream R start state edge hzero hstep).segment n).chargeSum =
      R.charge (edge n) := by
  simp [infinitePathFromOfEdgeStream]

/-- Prefix charge in the charged-path package is the chronological sum of the
edge charges. -/
theorem infinitePathFromOfEdgeStream_partialCharge
    (R : ChargedRelation State Edge) (start : State)
    (state : ℕ → State) (edge : ℕ → Edge)
    (hzero : state 0 = start)
    (hstep : ∀ n, R.src (edge n) = state n ∧ R.tgt (edge n) = state (n + 1))
    (n : ℕ) :
    (infinitePathFromOfEdgeStream R start state edge hzero hstep).partialCharge n =
      ∑ k ∈ Finset.range n, R.charge (edge k) := by
  simp [InfinitePathFrom.partialCharge]

/-- Reachability is preserved by appending one relation edge. -/
theorem reaches_tgt_of_reaches_src (R : ChargedRelation State Edge)
    {start current : State} (hcurrent : R.Reaches start current)
    (edge : Edge) (hsrc : R.src edge = current) :
    R.Reaches start (R.tgt edge) := by
  rcases hcurrent with ⟨path⟩
  exact ⟨path.append (Path.edge edge hsrc rfl)⟩

/-- Dependent choice turns local progress at every reachable state into either
a finite terminal execution or an infinite chronological edge stream. -/
theorem hasChronologicalExecution_of_reachable_progress
    (R : ChargedRelation State Edge) (Terminal : State → Prop) (start : State)
    (progress : ∀ current, R.Reaches start current →
      Terminal current ∨ ∃ edge, R.src edge = current) :
    R.HasChronologicalExecution Terminal start := by
  classical
  by_cases hterminal : ∃ terminal, R.Reaches start terminal ∧ Terminal terminal
  · exact Or.inl hterminal
  · right
    let Reachable := {current : State // R.Reaches start current}
    have hnext : ∀ current : Reachable, ∃ edge, R.src edge = current.1 := by
      intro current
      rcases progress current.1 current.2 with hterm | hstep
      · exact False.elim (hterminal ⟨current.1, current.2, hterm⟩)
      · exact hstep
    let chosenEdge : Reachable → Edge := fun current => Classical.choose (hnext current)
    have chosenEdge_src (current : Reachable) :
        R.src (chosenEdge current) = current.1 :=
      Classical.choose_spec (hnext current)
    let advance : Reachable → Reachable := fun current =>
      ⟨R.tgt (chosenEdge current),
        reaches_tgt_of_reaches_src R current.2 (chosenEdge current) (chosenEdge_src current)⟩
    let initial : Reachable := ⟨start, ⟨Path.nil start⟩⟩
    let orbit : ℕ → Reachable :=
      fun n => Nat.rec initial (fun _ current => advance current) n
    refine ⟨fun n => (orbit n).1, fun n => chosenEdge (orbit n), ?_, ?_⟩
    · rfl
    · intro n
      refine ⟨chosenEdge_src (orbit n), ?_⟩
      change R.tgt (chosenEdge (orbit n)) = (orbit (n + 1)).1
      simp only [orbit]
      rfl

end Math.ChargedPathBudget.ChargedRelation
