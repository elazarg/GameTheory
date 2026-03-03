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

end Suffix
end List
end Math
