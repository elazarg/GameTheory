import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Basic
import Semantics.TransitionTrace

set_option autoImplicit false

namespace Semantics
namespace Trace

open Semantics.Transition

variable {α σ : Type*}

/-- A trace language is prefix-closed when every prefix of an admitted trace
is also admitted. -/
def PrefixClosed (L : Set (List α)) : Prop :=
  ∀ ⦃u v : List α⦄, u <+: v → v ∈ L → u ∈ L

/-- Rootedness of a trace language (`[]` is admitted). -/
def Rooted (L : Set (List α)) : Prop :=
  [] ∈ L

/-- A tree represented as a language of finite traces. -/
def IsTraceTree (L : Set (List α)) : Prop :=
  PrefixClosed L ∧ Rooted L

theorem PrefixClosed.mem_of_prefix {L : Set (List α)}
    (hL : PrefixClosed L) {u v : List α}
    (huv : u <+: v) (hv : v ∈ L) : u ∈ L :=
  hL huv hv

theorem PrefixClosed.mem_take {L : Set (List α)}
    (hL : PrefixClosed L) {v : List α}
    (hv : v ∈ L) (n : Nat) :
    v.take n ∈ L := by
  exact hL (List.take_prefix n v) hv

theorem PrefixClosed.mem_left_of_append {L : Set (List α)}
    (hL : PrefixClosed L) (u v : List α)
    (huv : u ++ v ∈ L) :
    u ∈ L := by
  exact hL ⟨v, rfl⟩ huv

theorem PrefixClosed.empty : PrefixClosed (∅ : Set (List α)) := by
  intro _ _ _ hv
  exact False.elim hv

theorem PrefixClosed.univ : PrefixClosed (Set.univ : Set (List α)) := by
  intro _ _ _ _
  simp

theorem PrefixClosed.inter {L K : Set (List α)}
    (hL : PrefixClosed L) (hK : PrefixClosed K) :
    PrefixClosed (L ∩ K) := by
  intro u v huv hv
  exact ⟨hL huv hv.1, hK huv hv.2⟩

theorem PrefixClosed.union {L K : Set (List α)}
    (hL : PrefixClosed L) (hK : PrefixClosed K) :
    PrefixClosed (L ∪ K) := by
  intro u v huv hv
  rcases hv with hv | hv
  · exact Or.inl (hL huv hv)
  · exact Or.inr (hK huv hv)

/-- Prefix-closed languages with at least one trace are rooted. -/
theorem Rooted.of_nonempty_prefixClosed {L : Set (List α)}
    (hL : PrefixClosed L) (hne : Set.Nonempty L) :
    Rooted L := by
  rcases hne with ⟨w, hw⟩
  have hnil : ([] : List α) <+: w := ⟨w, rfl⟩
  exact hL hnil hw

/-- Language of traces realizable from a start state. -/
def TracesFrom (step : α → σ → σ → Prop) (s : σ) : Set (List α) :=
  { w | ∃ t, ReachBy step w s t }

theorem mem_tracesFrom_iff (step : α → σ → σ → Prop) (s : σ) (w : List α) :
    w ∈ TracesFrom step s ↔ ∃ t, ReachBy step w s t := Iff.rfl

theorem rooted_tracesFrom (step : α → σ → σ → Prop) (s : σ) :
    Rooted (TracesFrom step s) := by
  exact ⟨s, reachBy_nil (step := step) s⟩

theorem prefixClosed_tracesFrom (step : α → σ → σ → Prop) (s : σ) :
    PrefixClosed (TracesFrom step s) := by
  intro u v huv hv
  rcases hv with ⟨t, hvt⟩
  have hvEq : v = u ++ v.drop u.length := List.prefix_append_drop huv
  have hv' : ReachBy step (u ++ v.drop u.length) s t := by
    exact hvEq ▸ hvt
  rcases reachBy_split (step := step) (w1 := u) (w2 := v.drop u.length) hv' with
    ⟨m, hum, _⟩
  exact ⟨m, hum⟩

theorem isTraceTree_tracesFrom (step : α → σ → σ → Prop) (s : σ) :
    IsTraceTree (TracesFrom step s) :=
  ⟨prefixClosed_tracesFrom step s, rooted_tracesFrom step s⟩

theorem append_mem_tracesFrom_iff
    (step : α → σ → σ → Prop) (s : σ) (u v : List α) :
    (u ++ v) ∈ TracesFrom step s
      ↔ ∃ m, ReachBy step u s m ∧ v ∈ TracesFrom step m := by
  constructor
  · intro huv
    rcases huv with ⟨t, hst⟩
    rcases reachBy_split (step := step) (w1 := u) (w2 := v) hst with ⟨m, hus, hvt⟩
    exact ⟨m, hus, ⟨t, hvt⟩⟩
  · rintro ⟨m, hus, ⟨t, hvt⟩⟩
    exact ⟨t, reachBy_append hus hvt⟩

end Trace
end Semantics
