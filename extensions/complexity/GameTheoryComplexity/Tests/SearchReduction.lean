import GameTheoryComplexity.Backend.SearchReduction
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.P.DecisionFn

/-! Controls distinguishing search reductions from decision reductions, totality
from efficient verification, and correctly wired solution composition. -/

namespace GameTheory.Complexity.Tests.SearchReduction

open _root_.Complexity
open _root_.Complexity.Cobham
open GameTheory.Complexity.Backend

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

/-- The target really is TFNP, including rejection of malformed pair codes. -/
theorem emptySolution_mem_TFNP : emptySolution ∈ TFNP := by
  refine ⟨⟨⟨0, ?_⟩, ?_⟩, fun x => ⟨[], rfl⟩⟩
  · intro x y hy
    simp [emptySolution] at hy
    simp [hy]
  · apply mem_P_of_decisionFn
      (eqFlagFn_mem_FP id_mem_FP (pairFn_mem_FP pairFst_mem_FP const_nil_mem_FP))
    intro z
    have heq : z ∈ pairLang emptySolution ↔ z = pair (pairFst z) [] := by
      constructor
      · rintro ⟨x, y, hz, hy⟩
        subst y
        simp [hz]
      · intro hz
        exact ⟨pairFst z, [], hz, rfl⟩
    rw [heq, ← eqFlag_eq_true_iff]
    rcases eqFlag_flag z (pair (pairFst z) []) with h | h <;> simp [h]

def unboundedReduction : SearchReduction unboundedSource emptySolution where
  instanceMap := fun _ => []
  instanceMap_mem_FP := constFn_mem_FP []
  decode := fun _ => []
  decode_mem_FPn := cobham_iff_FPn.mp (Cobham.const [])
  sound := fun _ _ _ => trivial

/-- A valid search reduction does not bound all source witnesses. -/
theorem unboundedSource_not_polyBalanced : ¬ PolyBalanced unboundedSource := by
  rintro ⟨p, hp⟩
  have h := hp [] (List.replicate (p.eval 0 + 1) false) trivial
  simp only [List.length_nil, List.length_replicate] at h
  omega

theorem unboundedSource_not_TFNP : unboundedSource ∉ TFNP := by
  intro h
  exact unboundedSource_not_polyBalanced h.1.1

def sourceRelation (x y : List Bool) : Prop := y = x ++ (false :: x)

def middleRelation (x y : List Bool) : Prop := y = x

def sourceToMiddle : SearchReduction sourceRelation middleRelation where
  instanceMap := fun x => false :: x
  instanceMap_mem_FP := CobhamFP_subset_FP (.bit false)
  decode := fun v => v 0 ++ v 1
  decode_mem_FPn := cobham_iff_FPn.mp Cobham.append
  sound := by
    intro x y hy
    exact congrArg (fun z => x ++ z) hy

def middleToEmpty : SearchReduction middleRelation emptySolution where
  instanceMap := fun _ => []
  instanceMap_mem_FP := constFn_mem_FP []
  decode := fun v => v 0
  decode_mem_FPn := cobham_iff_FPn.mp (.proj 0)
  sound := fun _ _ _ => rfl

/-- The inner decoder sees the mapped instance while the outer one retains the
original source instance. -/
theorem composed_decoder_retains_both_instances (x z : List Bool) :
    (sourceToMiddle.trans middleToEmpty).decode ![x, z] = x ++ (false :: x) := rfl

theorem wrong_outer_instance_changes_solution :
    sourceToMiddle.decode ![false :: [true], false :: [true]] ≠
      (sourceToMiddle.trans middleToEmpty).decode ![[true], []] := by decide

theorem wrong_inner_instance_changes_solution :
    sourceToMiddle.decode ![[true], middleToEmpty.decode ![[true], []]] ≠
      (sourceToMiddle.trans middleToEmpty).decode ![[true], []] := by decide

end GameTheory.Complexity.Tests.SearchReduction
