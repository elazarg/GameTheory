/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Set.Basic

/-!
# Knowledge induced by views

This module defines the generic epistemic construction induced by a view
function `view : X → V`.

Two states are indistinguishable exactly when the view function returns the same
value on them. This gives an equivalence relation and the standard S5 knowledge
modality independently of what the view represents.

The module also records the basic coarsening principle: if a coarser view is a
projection of a finer view, then anything known from the coarser view is also
known from the finer view.
-/

set_option autoImplicit false

namespace Math
namespace ViewKnowledge

universe u v w

variable {X : Type u} {V : Type v} {W : Type w}

/-- Indistinguishability induced by `view`. -/
def Same (view : X → V) (left right : X) : Prop :=
  view left = view right

theorem Same.refl (view : X → V) (state : X) :
    Same view state state := rfl

theorem Same.symm {view : X → V} {left right : X}
    (h : Same view left right) :
    Same view right left :=
  Eq.symm h

theorem Same.trans {view : X → V} {a b c : X}
    (hab : Same view a b) (hbc : Same view b c) :
    Same view a c :=
  Eq.trans hab hbc

/-- Coarsening indistinguishability: equal finer views remain equal after any
projection. -/
theorem Same.coarsen {view : X → V} (project : V → W)
    {left right : X} (h : Same view left right) :
    Same (fun state => project (view state)) left right :=
  congrArg project h

/-- Coarsening indistinguishability when the coarse view is propositionally
equal to a projection of the fine view. -/
theorem Same.coarsen_of_eq {fineView : X → V} {coarseView : X → W}
    (project : V → W)
    (hcoarse : ∀ state, coarseView state = project (fineView state))
    {left right : X} (h : Same fineView left right) :
    Same coarseView left right := by
  unfold Same
  rw [hcoarse left, hcoarse right, h]

/-- The knowledge cell induced by `view` at `state`. -/
def Cell (view : X → V) (state : X) : Set X :=
  { other | Same view state other }

@[simp] theorem mem_Cell_iff
    (view : X → V) (state other : X) :
    other ∈ Cell view state ↔ Same view state other := by
  rfl

/-- The current state belongs to its own knowledge cell. -/
theorem Cell.self (view : X → V) (state : X) :
    state ∈ Cell view state :=
  Same.refl view state

/-- States with the same view have the same knowledge cell. -/
theorem Cell.eq_of_same {view : X → V} {left right : X}
    (h : Same view left right) :
    Cell view left = Cell view right := by
  ext other
  constructor
  · intro hleft
    exact Same.trans (Same.symm h) hleft
  · intro hright
    exact Same.trans h hright

/-- A finer view's knowledge cell is included in the knowledge cell of any
coarsening. -/
theorem Cell.subset_coarsen (view : X → V) (project : V → W)
    (state : X) :
    Cell view state ⊆ Cell (fun other => project (view other)) state := by
  intro other hcell
  exact Same.coarsen project hcell

/-- A finer view's knowledge cell is included in a propositionally specified
coarsening. -/
theorem Cell.subset_coarsen_of_eq
    (fineView : X → V) (coarseView : X → W) (project : V → W)
    (hcoarse : ∀ state, coarseView state = project (fineView state))
    (state : X) :
    Cell fineView state ⊆ Cell coarseView state := by
  intro other hcell
  exact Same.coarsen_of_eq project hcoarse hcell

/-- `Knows view state event` means `event` holds throughout the knowledge cell
induced by `view` at `state`. -/
def Knows (view : X → V) (state : X) (event : Set X) : Prop :=
  ∀ {other}, other ∈ Cell view state → event other

/-- Veridicality: known events are true at the current state. -/
theorem Knows.truth {view : X → V} {state : X} {event : Set X}
    (h : Knows view state event) :
    event state :=
  h (Cell.self view state)

/-- Knowledge is monotone in the event. -/
theorem Knows.mono {view : X → V} {state : X}
    {event stronger : Set X}
    (h : Knows view state event)
    (hsub : ∀ {other}, event other → stronger other) :
    Knows view state stronger := by
  intro other hcell
  exact hsub (h hcell)

/-- Known events are closed under conjunction. -/
theorem Knows.and {view : X → V} {state : X}
    {left right : Set X}
    (hleft : Knows view state left)
    (hright : Knows view state right) :
    Knows view state { other | left other ∧ right other } := by
  intro other hcell
  exact ⟨hleft hcell, hright hcell⟩

/-- K-style distribution: if an implication is known and its premise is known,
then its conclusion is known. -/
theorem Knows.mp {view : X → V} {state : X}
    {premise conclusion : Set X}
    (himp : Knows view state { other | premise other → conclusion other })
    (hpremise : Knows view state premise) :
    Knows view state conclusion := by
  intro other hcell
  exact himp hcell (hpremise hcell)

/-- If an event is known at one state, it is known at every indistinguishable
state. -/
theorem Knows.of_same {view : X → V} {state other : X}
    {event : Set X}
    (hknow : Knows view state event)
    (hsame : Same view state other) :
    Knows view other event := by
  intro third hthird
  exact hknow (Same.trans hsame hthird)

/-- Anything known from a coarser view is also known from the finer view that
projects to it. -/
theorem Knows.of_coarser {view : X → V} (project : V → W)
    {state : X} {event : Set X}
    (hknow : Knows (fun other => project (view other)) state event) :
    Knows view state event := by
  intro other hcell
  exact hknow (Same.coarsen project hcell)

/-- Anything known from a propositionally specified coarser view is also known
from the finer view that projects to it. -/
theorem Knows.of_coarser_eq
    (fineView : X → V) (coarseView : X → W) (project : V → W)
    (hcoarse : ∀ state, coarseView state = project (fineView state))
    {state : X} {event : Set X}
    (hknow : Knows coarseView state event) :
    Knows fineView state event := by
  intro other hcell
  exact hknow (Same.coarsen_of_eq project hcoarse hcell)

/-- Positive introspection for view-induced knowledge. -/
theorem Knows.positive_introspection {view : X → V} {state : X}
    {event : Set X}
    (hknow : Knows view state event) :
    Knows view state { other | Knows view other event } := by
  intro other hcell
  exact Knows.of_same hknow hcell

/-- Negative introspection for view-induced knowledge. -/
theorem Knows.negative_introspection {view : X → V} {state : X}
    {event : Set X}
    (hnot : ¬ Knows view state event) :
    Knows view state { other | ¬ Knows view other event } := by
  intro other hcell hother
  apply hnot
  intro third hthird
  exact hother (Same.trans (Same.symm hcell) hthird)

end ViewKnowledge
end Math
