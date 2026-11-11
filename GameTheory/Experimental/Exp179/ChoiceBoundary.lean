module

/-
Finite-menu representation controls for EXP-179: greatest versus maximal,
observational incomparability, evaluation guards, tied bundle witnesses and
the necessity of revealed-preference consistency.
-/

public import GameTheory.Math.FiniteChoice
public import GameTheory.Math.GuardedOptimality
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace GameTheory.Experimental.ChoiceBoundary

open GameTheory.Math

/-- Two offered alternatives are incomparable under equality. -/
def pair : Finset Bool := {false, true}

/-- Equality makes every available alternative maximal under Mathlib's
standard predicate. No global order on alternatives is installed. -/
theorem equality_maximal_iff (menu : Finset Bool) (chosen : Bool) :
    let : LE Bool := ⟨Eq⟩
    Maximal (fun item => item ∈ menu) chosen ↔ chosen ∈ menu := by
  let : LE Bool := ⟨Eq⟩
  constructor
  · exact fun maximal => maximal.1
  · intro member
    refine ⟨member, ?_⟩
    intro other _ equal
    exact equal.symm

theorem both_equality_maximal :
    let : LE Bool := ⟨Eq⟩
    Maximal (fun item => item ∈ pair) false ∧ Maximal (fun item => item ∈ pair) true := by
  constructor
  · exact (equality_maximal_iff pair false).2 (by simp [pair])
  · exact (equality_maximal_iff pair true).2 (by simp [pair])

/-- Neither equality-maximal alternative is greatest in this menu. -/
theorem equality_pair_has_no_greatest : FiniteChoice.best (fun x y : Bool => x = y) pair = ∅ := by
  ext chosen
  cases chosen <;> simp [FiniteChoice.best, pair]

/-- Observational choice selects every offered alternative. -/
def chooseAll (menu : Finset Bool) : Set Bool := menu

theorem chooseAll_eq_equality_maximals (menu : Finset Bool) :
    chooseAll menu = {chosen | letI : LE Bool := ⟨Eq⟩
      Maximal (fun item => item ∈ menu) chosen} := by
  ext chosen
  exact (equality_maximal_iff menu chosen).symm

/-- Complete indifference has exactly the same observable choice as maximal
selection from the incomplete equality preference. -/
theorem chooseAll_eq_best_indifference (menu : Finset Bool) :
    chooseAll menu = FiniteChoice.best (fun _ _ : Bool => True) menu := by
  ext chosen
  simp [chooseAll, FiniteChoice.best]

theorem chooseAll_rationalizable :
    ∃ prefers : Bool → Bool → Prop,
      (∀ a b, prefers a b ∨ prefers b a) ∧
      (∀ a b c, prefers a b → prefers b c → prefers a c) ∧
      ∀ menu, chooseAll menu = FiniteChoice.best prefers menu :=
  ⟨fun _ _ => True, fun _ _ => Or.inl trivial,
    fun _ _ _ _ _ => trivial, chooseAll_eq_best_indifference⟩

/-- Binary revealed preference cannot recover the latent incomparability. -/
theorem revealed_erases_incomparability :
    FiniteChoice.revealed chooseAll false true ∧ ¬ (false = true) := by
  simp [FiniteChoice.revealed, chooseAll]

/-- Evaluation-domain guards allow an incumbent outside an empty alternative
set. Feasible choice still selects no alternative from that empty menu. -/
theorem empty_guarded_optimality :
    IsOptimalOn (fun _ : Bool => True) (fun x y => x = y) ∅ true :=
  ⟨trivial, by simp, by simp⟩

theorem empty_best_choice : FiniteChoice.best (fun x y : Bool => x = y) ∅ = ∅ := by
  ext chosen
  simp [FiniteChoice.best]

/-- Represented bundles are singletons only. -/
def singletonBundle (index : Bool) : Set Bool := {index}

def tiedBestIndices : Set Bool := FiniteChoice.best (fun _ _ : Bool => True) pair

/-- Flattening a correspondence of tied bundle indices into a union changes
its meaning from choosing one alternative bundle to accepting all its items. -/
def chosenUnion : Set Bool :=
  {item | ∃ index ∈ tiedBestIndices, item ∈ singletonBundle index}

theorem tied_indices_both_best : false ∈ tiedBestIndices ∧ true ∈ tiedBestIndices := by
  simp [tiedBestIndices, FiniteChoice.best, pair]

theorem chosenUnion_eq_univ : chosenUnion = Set.univ := by
  ext item
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨item, ?_, ?_⟩
    · cases item <;> simp [tiedBestIndices, FiniteChoice.best, pair]
    · simp [singletonBundle]

/-- The union of all tied best bundles is not itself a represented bundle. -/
theorem chosenUnion_not_represented : ¬ ∃ index, chosenUnion = singletonBundle index := by
  rintro ⟨index, equal⟩
  have opposite : (!index) ∈ chosenUnion := by
    rw [chosenUnion_eq_univ]
    trivial
  rw [equal] at opposite
  cases index <;> simp [singletonBundle] at opposite

/-- A feasible nonempty selector can still have cyclic binary preferences. -/
noncomputable def cyclicChoice (menu : Finset ℕ) : Set ℕ :=
  if 0 ∈ menu ∧ 1 ∈ menu ∧ 2 ∉ menu then {0} else
  if 1 ∈ menu ∧ 2 ∈ menu ∧ 0 ∉ menu then {1} else
  if 0 ∈ menu ∧ 2 ∈ menu ∧ 1 ∉ menu then {2} else menu

theorem cyclicChoice_feasible : FiniteChoice.Feasible cyclicChoice := by
  intro menu chosen selected
  unfold cyclicChoice at selected
  split_ifs at selected with h01 h12 h02
  · have equal : chosen = 0 := selected
    subst chosen
    exact h01.1
  · have equal : chosen = 1 := selected
    subst chosen
    exact h12.1
  · have equal : chosen = 2 := selected
    subst chosen
    exact h02.2.1
  · exact selected

theorem cyclicChoice_nonempty : FiniteChoice.Nonempty cyclicChoice := by
  intro menu nonempty
  unfold cyclicChoice
  split_ifs
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact nonempty

theorem cyclic_revealed_not_transitive :
    FiniteChoice.revealed cyclicChoice 0 1 ∧
    FiniteChoice.revealed cyclicChoice 1 2 ∧
    ¬ FiniteChoice.revealed cyclicChoice 0 2 := by
  classical
  simp [FiniteChoice.revealed, cyclicChoice]

theorem cyclicChoice_not_weakAxiom : ¬ FiniteChoice.WeakAxiom cyclicChoice := by
  intro consistent
  have transitive := FiniteChoice.revealed_transitive cyclicChoice_feasible cyclicChoice_nonempty consistent
  exact cyclic_revealed_not_transitive.2.2
    (transitive 0 1 2 cyclic_revealed_not_transitive.1 cyclic_revealed_not_transitive.2.1)

end GameTheory.Experimental.ChoiceBoundary
