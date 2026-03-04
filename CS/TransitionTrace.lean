import Mathlib.Logic.Relation

set_option autoImplicit false

namespace CS
namespace Transition

/-- A labeled finite trace witness for a transition system.

`ReachBy step tr s t` means that starting at `s`, following labels in `tr`
produces a valid step sequence ending at `t`. -/
inductive ReachBy {σ α : Type*} (step : α → σ → σ → Prop) :
    List α → σ → σ → Prop
  | nil (s : σ) : ReachBy step [] s s
  | cons {a : α} {rest : List α} {s u t : σ} :
      step a s u → ReachBy step rest u t → ReachBy step (a :: rest) s t

variable {σ α β : Type*}
variable {step : α → σ → σ → Prop}

@[simp] theorem reachBy_nil (s : σ) : ReachBy step [] s s := ReachBy.nil _

@[simp] theorem reachBy_singleton {a : α} {s t : σ}
    (h : step a s t) : ReachBy step [a] s t := by
  exact ReachBy.cons h (ReachBy.nil _)

/-- Concatenate trace witnesses. -/
theorem reachBy_append {w1 w2 : List α} {s u t : σ}
    (h1 : ReachBy step w1 s u) (h2 : ReachBy step w2 u t) :
    ReachBy step (w1 ++ w2) s t := by
  induction h1 with
  | nil _ => simpa using h2
  | @cons a rest s m u hsm hmu ih =>
      exact ReachBy.cons hsm (by simpa using ih h2)

/-- Split a trace witness over list concatenation. -/
theorem reachBy_split {w1 w2 : List α} {s t : σ}
    (h : ReachBy step (w1 ++ w2) s t) :
    ∃ u, ReachBy step w1 s u ∧ ReachBy step w2 u t := by
  induction w1 generalizing s with
  | nil =>
      refine ⟨s, ReachBy.nil s, ?_⟩
      simpa using h
  | cons a rest ih =>
      cases h with
      | cons hstep hrest =>
          rcases ih hrest with ⟨u, hleft, hright⟩
          exact ⟨u, ReachBy.cons hstep hleft, hright⟩

/-- Append one step at the tail of a trace witness. -/
theorem reachBy_append_singleton {w : List α} {a : α} {s t u : σ}
    (h : ReachBy step w s t) (ht : step a t u) :
    ReachBy step (w ++ [a]) s u := by
  exact reachBy_append h (reachBy_singleton ht)

/-- Unlabeled one-step relation induced by existence of a label. -/
def StepExists (step : α → σ → σ → Prop) : σ → σ → Prop :=
  fun s t => ∃ a, step a s t

/-- Any labeled trace induces unlabeled reachability. -/
theorem reaches_of_reachBy {w : List α} {s t : σ}
    (h : ReachBy step w s t) :
    Relation.ReflTransGen (StepExists step) s t := by
  induction h with
  | nil _ => exact .refl
  | @cons a rest s u t hs hrest ih =>
      exact Relation.ReflTransGen.head ⟨a, hs⟩ ih

/-- Any unlabeled reachability proof can be reified into a finite label trace. -/
theorem exists_reachBy_of_reaches {s t : σ}
    (h : Relation.ReflTransGen (StepExists step) s t) :
    ∃ w : List α, ReachBy step w s t := by
  induction h with
  | refl => exact ⟨[], ReachBy.nil _⟩
  | tail hab hbc ih =>
      rcases ih with ⟨w, hw⟩
      rcases hbc with ⟨a, ha⟩
      exact ⟨w ++ [a], reachBy_append_singleton hw ha⟩

/-- Reachability equivalence between explicit traces and reflexive-transitive closure. -/
theorem exists_reachBy_iff_reaches {s t : σ} :
    (∃ w : List α, ReachBy step w s t) ↔
      Relation.ReflTransGen (StepExists step) s t := by
  constructor
  · rintro ⟨w, hw⟩
    exact reaches_of_reachBy hw
  · intro h
    exact exists_reachBy_of_reaches h

/-- Relabel a trace witness through a step-preserving map. -/
theorem reachBy_map_labels
    {step' : β → σ → σ → Prop} (f : α → β)
    (hmap : ∀ a s t, step a s t → step' (f a) s t)
    {w : List α} {s t : σ}
    (h : ReachBy step w s t) :
    ReachBy step' (w.map f) s t := by
  induction h with
  | nil s => simp [ReachBy.nil]
  | @cons a rest s u t hs hrest ih =>
      exact ReachBy.cons (hmap a s u hs) ih

/-- Map states along a simulation-compatible function while preserving labels. -/
theorem reachBy_map_states
    {τ : Type*} {step' : α → τ → τ → Prop}
    (stateMap : σ → τ)
    (hmap : ∀ a s t, step a s t → step' a (stateMap s) (stateMap t))
    {w : List α} {s t : σ}
    (h : ReachBy step w s t) :
    ReachBy step' w (stateMap s) (stateMap t) := by
  induction h with
  | nil s =>
      exact ReachBy.nil (step := step') (stateMap s)
  | @cons a rest s u t hs hrest ih =>
      exact ReachBy.cons (hmap a s u hs) ih

/-- A step-invariant observable is constant along any labeled reachability witness. -/
theorem obs_eq_of_reachBy
    {Ω : Type*} (obs : σ → Ω)
    (hstep : ∀ a s t, step a s t → obs s = obs t)
    {w : List α} {s t : σ}
    (h : ReachBy step w s t) :
    obs s = obs t := by
  induction h with
  | nil s =>
      rfl
  | @cons a rest s u t hs hrest ih =>
      exact (hstep a s u hs).trans ih

/-- State-map transport for unlabeled reflexive-transitive reachability. -/
theorem reaches_map_states
    {τ : Type*} {step' : τ → τ → Prop}
    (stateMap : σ → τ)
    (hmap : ∀ s t, StepExists step s t → step' (stateMap s) (stateMap t))
    {s t : σ}
    (h : Relation.ReflTransGen (StepExists step) s t) :
    Relation.ReflTransGen step' (stateMap s) (stateMap t) := by
  induction h with
  | refl =>
      exact .refl
  | tail hab hbc ih =>
      exact Relation.ReflTransGen.tail ih (hmap _ _ hbc)

/-- A one-step invariant observable is also invariant on reflexive-transitive reachability. -/
theorem obs_eq_of_reaches
    {Ω : Type*} (obs : σ → Ω)
    (hstep : ∀ s t, StepExists step s t → obs s = obs t)
    {s t : σ}
    (h : Relation.ReflTransGen (StepExists step) s t) :
    obs s = obs t := by
  induction h with
  | refl =>
      rfl
  | tail hab hbc ih =>
      exact ih.trans (hstep _ _ hbc)

end Transition
end CS
