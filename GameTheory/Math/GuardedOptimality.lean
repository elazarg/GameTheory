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

section Accessors

variable {α : Type uα} {admissible : α → Prop} {prefers : α → α → Prop}
  {allowed : Set α} {chosen alternative : α}

/-- The chosen element lies in the domain of evaluation. -/
theorem IsOptimalOn.chosen_admissible
    (optimal : IsOptimalOn admissible prefers allowed chosen) : admissible chosen :=
  optimal.1

/-- Every allowed alternative lies in the domain of evaluation. -/
theorem IsOptimalOn.alternative_admissible
    (optimal : IsOptimalOn admissible prefers allowed chosen)
    (offered : alternative ∈ allowed) : admissible alternative :=
  optimal.2.1 alternative offered

/-- The chosen element is weakly preferred to every allowed alternative. -/
theorem IsOptimalOn.chosen_prefers
    (optimal : IsOptimalOn admissible prefers allowed chosen)
    (offered : alternative ∈ allowed) : prefers chosen alternative :=
  optimal.2.2 alternative offered

end Accessors

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
  ⟨base optimal.chosen_admissible,
    fun alternative allowed => (coverage alternative allowed).elim fun _ covered =>
      covered.2.1 (optimal.alternative_admissible covered.1),
    fun alternative allowed => (coverage alternative allowed).elim fun _ covered =>
      covered.2.2 (optimal.chosen_prefers covered.1)⟩

end GameTheory.Math
