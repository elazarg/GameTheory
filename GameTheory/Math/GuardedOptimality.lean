module

/-
# Guarded comparison optimality

A choice is optimal when it and every allowed alternative lie in the domain
of evaluation, and its comparison with every allowed alternative holds.
The domain and comparison are independent arguments; no order laws are needed.
The chosen element must be admissible even when there are no alternatives.
-/

public import Mathlib.Data.Set.Defs

@[expose] public section

namespace GameTheory.Math

universe uα us ut

/-- The chosen element and every allowed alternative are admissible, and the
chosen element is weakly preferred to each allowed alternative. -/
def IsOptimalOn {α : Type uα} (admissible : α → Prop) (prefers : α → α → Prop)
    (allowed : Set α) (chosen : α) : Prop :=
  admissible chosen ∧ (∀ alternative ∈ allowed, admissible alternative) ∧
    ∀ alternative ∈ allowed, prefers chosen alternative

/-- Optimality transfers when admissibility of the chosen element transfers
and every target alternative is covered in both domain and comparison. -/
theorem IsOptimalOn.of_coverage
    {Source : Type us} {Target : Type ut}
    {sourceAdmissible : Source → Prop} {targetAdmissible : Target → Prop}
    {sourcePrefers : Source → Source → Prop} {targetPrefers : Target → Target → Prop}
    {sourceAllowed : Set Source} {targetAllowed : Set Target}
    {chosen : Source} {compiled : Target}
    (optimal : IsOptimalOn sourceAdmissible sourcePrefers sourceAllowed chosen)
    (base : sourceAdmissible chosen → targetAdmissible compiled)
    (coverage : ∀ alternative ∈ targetAllowed, ∃ original ∈ sourceAllowed,
      (sourceAdmissible original → targetAdmissible alternative) ∧
        (sourcePrefers chosen original → targetPrefers compiled alternative)) :
    IsOptimalOn targetAdmissible targetPrefers targetAllowed compiled :=
  ⟨base optimal.1,
    fun alternative allowed => (coverage alternative allowed).elim fun original covered =>
      covered.2.1 (optimal.2.1 original covered.1),
    fun alternative allowed => (coverage alternative allowed).elim fun original covered =>
      covered.2.2 (optimal.2.2 original covered.1)⟩

end GameTheory.Math
