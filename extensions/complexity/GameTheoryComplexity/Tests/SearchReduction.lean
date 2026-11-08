module

public import Complexity.Computability.Complexity.Classes.TFNP
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

@[expose] public section

/-! Controls distinguishing search reductions from decision reductions, totality
from efficient verification, and correctly wired solution composition. -/

namespace GameTheory.Complexity.Tests.SearchReduction

open Cslib.Complexity Turing.MultiTapeTM

def oneSolution (_ y : List Bool) : Prop := y = [false]

def twoSolutions (_ y : List Bool) : Prop := y = [false] ∨ y = [true]

/-- Matching existence predicates does not make an identity decoder sound. -/
theorem existence_matches_but_identity_decoder_fails :
    (∀ x, (∃ y, oneSolution x y) ↔ ∃ y, twoSolutions x y) ∧
      ¬ (∀ x y, twoSolutions x y → oneSolution x y) := by
  constructor
  · intro x
    exact ⟨fun _ => ⟨[false], Or.inl rfl⟩, fun _ => ⟨[false], rfl⟩⟩
  · intro h
    have hf := h [] [true] (Or.inr rfl)
    cases hf

def unboundedSource (_ _ : List Bool) : Prop := True

def emptySolution (_ y : List Bool) : Prop := y = []

/-- Native verification receives a typed instance and candidate pair. -/
theorem emptySolution_mem_TFNP : emptySolution ∈ TFNP encBits := by
  refine ⟨⟨⟨0, ?_⟩, (fun p : List Bool × List Bool => decide (p.2 = [])),
    ComputableInPolyTime.decide_eq' (.snd encBits encBits) (.const []), ?_⟩,
    fun _ => ⟨[], rfl⟩⟩
  · intro x y hy
    simp only [emptySolution] at hy
    simp [hy]
  · intro x y
    simp [emptySolution]

/-- A valid search reduction does not bound the source's other accepted witnesses. -/
theorem unboundedReduction : SearchReducible encBits encBits unboundedSource emptySolution :=
  .of_isTotalSearch (fun _ => ⟨[], rfl⟩) (.const []) (.const []) (fun _ _ _ => trivial)

theorem unboundedSource_not_polyBalanced :
    ¬ ∃ p : Polynomial ℕ, ∀ x y, unboundedSource x y → y.length ≤ p.eval x.length := by
  rintro ⟨p, hp⟩
  have h := hp [] (List.replicate (p.eval 0 + 1) false) trivial
  simp only [List.length_nil, List.length_replicate] at h
  omega

theorem unboundedSource_not_TFNP : unboundedSource ∉ TFNP encBits := by
  intro h
  exact unboundedSource_not_polyBalanced h.1.1

/-- A decoder's vacuous implication cannot erase the source's nonempty domain. -/
theorem no_reduction_to_empty_domain :
    ¬ SearchReducible encBits encBits emptySolution (fun _ _ => False) := by
  rintro ⟨f, g, hf, hg, hdomain, hsound⟩
  obtain ⟨w, hw⟩ := hdomain [] ⟨[], rfl⟩
  exact hw

def sourceRelation (x y : List Bool) : Prop := y = x ++ (false :: x)

def middleRelation (x y : List Bool) : Prop := y = x

def sourceInstance (x : List Bool) : List Bool := false :: x

def sourceDecoder (p : List Bool × List Bool) : List Bool := p.1 ++ p.2

def middleDecoder (p : List Bool × List Bool) : List Bool := p.1

theorem sourceToMiddle : SearchReducible encBits encBits sourceRelation middleRelation := by
  have htotal : IsTotalSearch middleRelation := fun x => ⟨x, rfl⟩
  refine SearchReducible.of_isTotalSearch htotal
    (f := sourceInstance) (g := sourceDecoder) ?_ ?_ ?_
  · exact .bitsCons (.const false) .id'
  · exact .bitsAppend (.fst encBits encBits) (.snd encBits encBits)
  · intro x y hy
    exact congrArg (fun z => x ++ z) hy

theorem middleToEmpty : SearchReducible encBits encBits middleRelation emptySolution :=
  .of_isTotalSearch (fun _ => ⟨[], rfl⟩) (.const []) (.fst encBits encBits)
    (fun _ _ _ => rfl)

/-- Composition is a native reduction; explicit maps make its wiring reviewable. -/
theorem sourceToEmpty : SearchReducible encBits encBits sourceRelation emptySolution :=
  sourceToMiddle.trans middleToEmpty

def composedDecoder (p : List Bool × List Bool) : List Bool :=
  sourceDecoder (p.1, middleDecoder (sourceInstance p.1, p.2))

/-- The inner decoder sees the mapped instance while the outer retains the original. -/
theorem composed_decoder_retains_both_instances (x z : List Bool) :
    composedDecoder (x, z) = x ++ (false :: x) := rfl

theorem wrong_outer_instance_changes_solution :
    sourceDecoder (false :: [true], false :: [true]) ≠
      composedDecoder ([true], []) := by decide +kernel

theorem wrong_inner_instance_changes_solution :
    sourceDecoder ([true], middleDecoder ([true], [])) ≠
      composedDecoder ([true], []) := by decide +kernel

end GameTheory.Complexity.Tests.SearchReduction
