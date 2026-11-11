module

/-
# Choice across strategic and allocation menus

One correspondence describes non-expected-utility best responses and tied
welfare-maximizing allocations. Budget feasibility selects the menu; it does
not alter the preference or turn distinct optimal allocations into their union.
-/

public import GameTheory.Tests.Potential
public import GameTheory.Mechanism.Knapsack.Basic
public import GameTheory.Math.FiniteChoice

@[expose] public section

noncomputable section

namespace GameTheory.Tests.ChoiceConsumers

open GameTheory.Math

def responseRank (chosen alternative : Bool) : Prop :=
  Potential.supportPreference ()
    (Potential.form.play (Profile.update Potential.falseProfile () chosen))
    (Potential.form.play (Profile.update Potential.falseProfile () alternative))

theorem responseRank_iff (chosen alternative : Bool) :
    responseRank chosen alternative ↔ chosen = true ∨ alternative = false := by
  cases chosen <;> cases alternative <;>
    simp [responseRank, Potential.supportPreference, Potential.form, Profile.update_same]

def responseChoice : Finset Bool → Set Bool := FiniteChoice.best responseRank

theorem responseChoice_consistent :
    FiniteChoice.Feasible responseChoice ∧ FiniteChoice.Nonempty responseChoice ∧
      FiniteChoice.WeakAxiom responseChoice := by
  apply (FiniteChoice.rationalizable_iff responseChoice).1
  refine ⟨responseRank, ?_, ?_, fun _ => rfl⟩
  · intro a b
    cases a <;> cases b <;> simp [responseRank_iff]
  · intro a b c hab hbc
    simp only [responseRank_iff] at hab hbc ⊢
    rcases hab with ha | hb
    · exact Or.inl ha
    · rcases hbc with hb' | hc
      · cases hb.symm.trans hb'
      · exact Or.inr hc

/-- The observed full-menu choice is exactly the existing best-response
predicate, with the previously proved non-EU preference. -/
theorem selected_iff_bestResponse (candidate : Bool) :
    candidate ∈ responseChoice Finset.univ ↔
      IsBestResponse Potential.form Potential.supportPreference ()
        Potential.falseProfile candidate :=
  (isBestResponse_iff_mem_best Potential.form Potential.supportPreference ()
    Potential.falseProfile candidate).symm

theorem revealed_response_recovers_comparisons (chosen alternative : Bool) :
    FiniteChoice.revealed responseChoice chosen alternative ↔ responseRank chosen alternative :=
  FiniteChoice.revealed_best (fun a => by cases a <;> simp [responseRank_iff]) chosen alternative

/-- The global lottery preference has no EU representation. The two pure
actions alone do not identify that global preference from observed choice. -/
theorem response_preference_not_expectedUtility :
    ¬ ∃ utility : Bool → Unit → ℝ,
      Potential.supportPreference = euPreference utility :=
  Potential.supportPreference_not_expectedUtility

namespace Allocation

open GameTheory.Mechanism.Knapsack

def budget : Data Bool := ⟨fun _ => 1, 1⟩

def value (_ : Bool) : ℝ := 1

def rank (chosen alternative : Finset Bool) : Prop :=
  welfare value alternative ≤ welfare value chosen

def choices : Finset (Finset Bool) → Set (Finset Bool) := FiniteChoice.best rank

/-- The complete choice family is consistent. A budget supplies one of its
menus, rather than an assumption that every finite menu is a budget menu. -/
theorem choices_consistent :
    FiniteChoice.Feasible choices ∧ FiniteChoice.Nonempty choices ∧
      FiniteChoice.WeakAxiom choices :=
  (FiniteChoice.rationalizable_iff choices).1
    ⟨rank, fun _ _ => le_total _ _, fun _ _ _ hab hbc => hbc.trans hab, fun _ => rfl⟩

theorem canonical_selection_is_chosen :
    welfareMaximizer budget value Finset.univ (by norm_num [budget]) ∈
      choices (feasibleAllocations budget Finset.univ) :=
  welfareMaximizer_mem_best budget value Finset.univ (by norm_num [budget])

theorem singleton_chosen (agent : Bool) :
    {agent} ∈ choices (feasibleAllocations budget Finset.univ) := by
  classical
  refine ⟨?_, fun alternative offered => ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (by simp), ?_⟩
    simp [Feasible, budget, load, aggregate]
  · have feasible := feasible_of_mem_feasibleAllocations budget Finset.univ offered
    simpa [rank, value, welfare, Feasible, budget, load, aggregate] using feasible

/-- Both tied optimal allocations are retained, but their joint allocation
exceeds capacity. -/
theorem tied_choices_have_infeasible_union :
    {false} ∈ choices (feasibleAllocations budget Finset.univ) ∧
    {true} ∈ choices (feasibleAllocations budget Finset.univ) ∧
    ¬ Feasible budget ({false} ∪ {true}) := by
  refine ⟨singleton_chosen false, singleton_chosen true, ?_⟩
  norm_num [Feasible, budget, load, aggregate]

end Allocation

/-- Choice on natural-number menus needs no finite ambient alternative type. -/
theorem natural_number_choices_consistent :
    FiniteChoice.Feasible (FiniteChoice.best (fun chosen alternative : ℕ => alternative ≤ chosen)) ∧
    FiniteChoice.Nonempty (FiniteChoice.best (fun chosen alternative : ℕ => alternative ≤ chosen)) ∧
    FiniteChoice.WeakAxiom
      (FiniteChoice.best (fun chosen alternative : ℕ => alternative ≤ chosen)) :=
  (FiniteChoice.rationalizable_iff _).1
    ⟨fun chosen alternative => alternative ≤ chosen, fun _ _ => le_total _ _,
      fun _ _ _ hab hbc => hbc.trans hab, fun _ => rfl⟩

end GameTheory.Tests.ChoiceConsumers
