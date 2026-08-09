/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# Chronological execution for a multivalued finite relation

A local successor relation may have several outgoing edges. Finite
reachability below records only witnessed edges. The first theorem yields one
of three chronological objects: a finite terminal path, one coherent infinite
path, or a finite path to a typed no-successor obstruction.

The second theorem is the positive counterpart. If every reached state is
terminal or has a witnessed successor, it produces a finite terminal execution
or one coherent infinite execution, with no obstruction branch.

Occupation measures and balance equations do not occur in either theorem and
cannot be used as path edges.
-/

noncomputable section

namespace GameTheory

universe u

/-- A finite path in a supplied successor relation. -/
inductive FiniteSuccessorPath {state : Type u}
    (edge : state → state → Prop) : state → state → Prop
  | refl (current : state) : FiniteSuccessorPath edge current current
  | tail {start current next : state} :
      FiniteSuccessorPath edge start current →
      edge current next →
      FiniteSuccessorPath edge start next

/-- A finite path all of whose vertices remain in a displayed carrier. -/
inductive FiniteSuccessorPathWithin {state : Type u} [DecidableEq state]
    (carrier : Finset state) (edge : state → state → Prop) :
    state → state → Prop
  | refl {current : state} :
      current ∈ carrier →
      FiniteSuccessorPathWithin carrier edge current current
  | tail {start current next : state} :
      FiniteSuccessorPathWithin carrier edge start current →
      next ∈ carrier →
      edge current next →
      FiniteSuccessorPathWithin carrier edge start next

/-- Finite reachability generated only by witnessed charged steps. -/
inductive ChargedExecutableReach {state : Type u}
    (Step : state → ℝ → state → Prop) (start : state) : state → Prop
  | refl : ChargedExecutableReach Step start start
  | tail {current next : state} :
      ChargedExecutableReach Step start current →
      (∃ charge, Step current charge next) →
      ChargedExecutableReach Step start next

/-- One coherent infinite chronological execution. -/
structure ChronologicalInfinitePath {state : Type u}
    (Step : state → ℝ → state → Prop) (start : state) where
  vertex : ℕ → state
  charge : ℕ → ℝ
  initial : vertex 0 = start
  step : ∀ time, Step (vertex time) (charge time) (vertex (time + 1))

/-- Terminal exit, recurrent execution, or a reached typed obstruction.

This is a proposition rather than a data-valued sum. That permits the proof
to inspect existential reachability witnesses while retaining the exact path
objects inside the positive branches. -/
inductive ChronologicalExecutionOutcome {state : Type u}
    (Terminal : state → Prop)
    (Step : state → ℝ → state → Prop)
    (Obstruction : state → Prop)
    (start : state) : Prop where
  | absorbing (endpoint : state) :
      ChargedExecutableReach Step start endpoint →
      Terminal endpoint →
      ChronologicalExecutionOutcome Terminal Step Obstruction start
  | recurrent :
      ChronologicalInfinitePath Step start →
      ChronologicalExecutionOutcome Terminal Step Obstruction start
  | obstructed (endpoint : state) :
      ChargedExecutableReach Step start endpoint →
      Obstruction endpoint →
      ChronologicalExecutionOutcome Terminal Step Obstruction start

/-- Terminal execution or one coherent infinite execution, with no failure
constructor. -/
inductive ChronologicalExecution {state : Type u}
    (Terminal : state → Prop)
    (Step : state → ℝ → state → Prop)
    (start : state) : Prop where
  | absorbing (endpoint : state) :
      ChargedExecutableReach Step start endpoint →
      Terminal endpoint →
      ChronologicalExecution Terminal Step start
  | recurrent :
      ChronologicalInfinitePath Step start →
      ChronologicalExecution Terminal Step start

/-- **Chronological execution trichotomy for a multivalued relation.**

If a reachable terminal exists, retain a finite witnessed path to it. If every
reachable state has a witnessed successor, recursively choose one coherent
infinite path. Otherwise retain a reached no-successor state and classify it
as a typed obstruction. -/
theorem chronologicalExecutionOutcome_of_classifier
    {state : Type u}
    (Terminal : state → Prop)
    (Step : state → ℝ → state → Prop)
    (Obstruction : state → Prop)
    (start : state)
    (classify : ∀ current,
      (¬ ∃ charge next, Step current charge next) → Obstruction current) :
    ChronologicalExecutionOutcome Terminal Step Obstruction start := by
  classical
  by_cases hterminal :
      ∃ endpoint,
        ChargedExecutableReach Step start endpoint ∧ Terminal endpoint
  · obtain ⟨endpoint, hreach, hend⟩ := hterminal
    exact .absorbing endpoint hreach hend
  by_cases hclosed : ∀ current,
      ChargedExecutableReach Step start current →
        ∃ charge next, Step current charge next
  · let Reachable :=
      {current : state // ChargedExecutableReach Step start current}
    have hpair : ∀ current : Reachable,
        ∃ data : ℝ × state,
          Step current.1 data.1 data.2 := by
      intro current
      obtain ⟨charge, next, hstep⟩ := hclosed current.1 current.2
      exact ⟨(charge, next), hstep⟩
    let chosen : Reachable → ℝ × state :=
      fun current => Classical.choose (hpair current)
    have chosen_spec (current : Reachable) :
        Step current.1 (chosen current).1 (chosen current).2 :=
      Classical.choose_spec (hpair current)
    let advance : Reachable → Reachable := fun current =>
      ⟨(chosen current).2,
        ChargedExecutableReach.tail current.2
          ⟨(chosen current).1, chosen_spec current⟩⟩
    let orbit : ℕ → Reachable := fun time =>
      Nat.rec
        (motive := fun _ => Reachable)
        ⟨start, ChargedExecutableReach.refl⟩
        (fun _ current => advance current)
        time
    refine .recurrent {
      vertex := fun time => (orbit time).1
      charge := fun time => (chosen (orbit time)).1
      initial := rfl
      step := ?_ }
    intro time
    have horbit : orbit (time + 1) = advance (orbit time) := rfl
    rw [horbit]
    exact chosen_spec (orbit time)
  · push Not at hclosed
    obtain ⟨endpoint, hreach, hfailure⟩ := hclosed
    have hnone : ¬ ∃ charge next, Step endpoint charge next := by
      intro hstep
      obtain ⟨charge, next, hstep⟩ := hstep
      exact hfailure charge next hstep
    exact .obstructed endpoint hreach (classify endpoint hnone)

/-- **Positive chronological execution from reached progress.**

If every state reached by witnessed steps is either terminal or has another
witnessed step, then one reached terminal exists or dependent choice produces
one coherent infinite execution. This theorem does not infer the progress
hypothesis from graph connectivity or an occupation measure. -/
theorem chronologicalExecution_of_reachable_progress
    {state : Type u}
    (Terminal : state → Prop)
    (Step : state → ℝ → state → Prop)
    (start : state)
    (progress : ∀ current,
      ChargedExecutableReach Step start current →
        Terminal current ∨ ∃ charge next, Step current charge next) :
    ChronologicalExecution Terminal Step start := by
  classical
  by_cases hterminal :
      ∃ endpoint,
        ChargedExecutableReach Step start endpoint ∧ Terminal endpoint
  · obtain ⟨endpoint, hreach, hend⟩ := hterminal
    exact .absorbing endpoint hreach hend
  · have hclosed : ∀ current,
        ChargedExecutableReach Step start current →
          ∃ charge next, Step current charge next := by
      intro current hreach
      rcases progress current hreach with hterminalCurrent | hstep
      · exact False.elim (hterminal ⟨current, hreach, hterminalCurrent⟩)
      · exact hstep
    let Reachable :=
      {current : state // ChargedExecutableReach Step start current}
    have hpair : ∀ current : Reachable,
        ∃ data : ℝ × state,
          Step current.1 data.1 data.2 := by
      intro current
      obtain ⟨charge, next, hstep⟩ := hclosed current.1 current.2
      exact ⟨(charge, next), hstep⟩
    let chosen : Reachable → ℝ × state :=
      fun current => Classical.choose (hpair current)
    have chosen_spec (current : Reachable) :
        Step current.1 (chosen current).1 (chosen current).2 :=
      Classical.choose_spec (hpair current)
    let advance : Reachable → Reachable := fun current =>
      ⟨(chosen current).2,
        ChargedExecutableReach.tail current.2
          ⟨(chosen current).1, chosen_spec current⟩⟩
    let orbit : ℕ → Reachable := fun time =>
      Nat.rec
        (motive := fun _ => Reachable)
        ⟨start, ChargedExecutableReach.refl⟩
        (fun _ current => advance current)
        time
    refine .recurrent {
      vertex := fun time => (orbit time).1
      charge := fun time => (chosen (orbit time)).1
      initial := rfl
      step := ?_ }
    intro time
    have horbit : orbit (time + 1) = advance (orbit time) := rfl
    rw [horbit]
    exact chosen_spec (orbit time)

end GameTheory
