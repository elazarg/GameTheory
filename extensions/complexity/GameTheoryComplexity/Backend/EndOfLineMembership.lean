module

public import GameTheoryComplexity.Backend.EndOfLineVerifier
public import GameTheoryComplexity.Backend.NativeEndOfLineSemantics

@[expose] public section

/-! Native search-class membership for the concrete endpoint relation.
The circuit evaluator supplies uniformly efficient pointers on the fixed-width
cube. Invalid source promises are decoded to the designated empty witness.
-/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM
open ComputableInPolyTime

/-- The concrete endpoint relation belongs to the native directed parity class. -/
theorem endOfLineRelation_mem_PPAD :
    endOfLineRelation ∈ Cslib.Complexity.PPAD encBits := by
  let P : List Bool × List Bool → List Bool := fun p => endOfLinePredecessor p.1 p.2
  let S : List Bool × List Bool → List Bool := fun p => endOfLineSuccessor p.1 p.2
  have hn := EndOfLineMachineOps.width_polyTime (id' (encIn := encBits))
  have hP : ComputableInPolyTime P (encPair encBits encBits) encBits :=
    EndOfLineMachineOps.predecessor_polyTime (fst encBits encBits) (snd encBits encBits)
  have hS : ComputableInPolyTime S (encPair encBits encBits) encBits :=
    EndOfLineMachineOps.successor_polyTime (fst encBits encBits) (snd encBits encBits)
  have hP_length : ∀ input u, u.length = endOfLineWidth input →
      (P (input, u)).length = endOfLineWidth input :=
    fun _ u hu => (evaluateCircuitVector_length _ u).trans hu
  have hS_length : ∀ input u, u.length = endOfLineWidth input →
      (S (input, u)).length = endOfLineWidth input :=
    fun _ u hu => (evaluateCircuitVector_length _ u).trans hu
  have hnative := Cslib.Complexity.endOfLineRel_mem_PPAD hn hP hS hP_length hS_length
  have hred : Cslib.Complexity.SearchReducible encBits encBits endOfLineRelation
      (Cslib.Complexity.endOfLineRel endOfLineWidth P S) := by
    apply Cslib.Complexity.SearchReducible.of_isTotalSearch
      (f := id) (g := fun p : List Bool × List Bool =>
        if endOfLineSourceFlag p.1 then p.2 else [])
      (Cslib.Complexity.isTotalSearch_endOfLineRel hS_length) id'
      ((endOfLineSourceFlag_polyTime (fst encBits encBits)).ite
        (snd encBits encBits) (const []))
    intro input witness hw
    by_cases hsource : endOfLineSourceFlag input = true
    · have hs := (endOfLineSourceFlag_accept input).mp hsource
      have he := (NativeEndOfLine.endOfLineRel_iff endOfLineWidth P S input
        hs.1 hs.2.1 hs.2.2 witness).mp hw
      rw [ite_eq_left hsource]
      exact Or.inl ⟨hs, he⟩
    · have hs : ¬endOfLineSourceValid input :=
        fun h => hsource ((endOfLineSourceFlag_accept input).mpr h)
      rw [ite_eq_right hsource]
      exact Or.inr ⟨hs, rfl⟩
  exact hred.mem_PPAD endOfLineRelation_mem_FNP hnative

end GameTheory.Complexity.Backend
