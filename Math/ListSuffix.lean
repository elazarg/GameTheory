import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace Math
namespace List
namespace Suffix

variable {α : Type*}

def SuffixClosed (P : List α → Prop) : Prop :=
  ∀ {l₁ l₂ : List α}, List.IsSuffix l₂ l₁ → P l₁ → P l₂

theorem suffixClosed_of_forall_cons
    {P : List α → Prop}
    (hcons : ∀ a l, P (a :: l) → P l) :
    SuffixClosed P := by
  intro l₁ l₂ hs hP
  rcases hs with ⟨t, rfl⟩
  induction t with
  | nil =>
      simpa using hP
  | cons a t ih =>
      have hP' : P (a :: (t ++ l₂)) := by
        simpa using hP
      exact ih (hcons a (t ++ l₂) hP')

theorem suffixClosed_tail
    {P : List α → Prop}
    (hP : SuffixClosed P) (a : α) (l : List α) :
    P (a :: l) → P l := by
  intro h
  exact hP ⟨[a], by simp⟩ h

theorem suffixClosed_trans
    {P : List α → Prop}
    (hP : SuffixClosed P)
    {l₁ l₂ l₃ : List α}
    (h12 : List.IsSuffix l₂ l₁)
    (h23 : List.IsSuffix l₃ l₂)
    (hl₁ : P l₁) :
    P l₃ := by
  exact hP h23 (hP h12 hl₁)

theorem suffixClosed_map
    {β : Type*} {P : List β → Prop} (hP : SuffixClosed P)
    (f : α → β) :
    SuffixClosed (fun l : List α => P (l.map f)) := by
  intro l₁ l₂ hs h
  have hs' : List.IsSuffix (l₂.map f) (l₁.map f) := by
    rcases hs with ⟨t, ht⟩
    refine ⟨t.map f, ?_⟩
    have hmap : List.map f (t ++ l₂) = List.map f l₁ := congrArg (List.map f) ht
    simpa [List.map_append] using hmap
  exact hP hs' h

theorem suffixClosed_append_right
    {P : List α → Prop} (hP : SuffixClosed P) (u : List α) :
    SuffixClosed (fun l : List α => P (l ++ u)) := by
  intro l₁ l₂ hs h
  rcases hs with ⟨t, ht⟩
  have hs' : List.IsSuffix (l₂ ++ u) (l₁ ++ u) := by
    refine ⟨t, ?_⟩
    simpa [List.append_assoc] using congrArg (fun l => l ++ u) ht
  exact hP hs' h

end Suffix
end List
end Math
