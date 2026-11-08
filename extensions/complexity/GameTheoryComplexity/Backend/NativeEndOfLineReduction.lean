module

public import GameTheoryComplexity.Backend.EndOfLineCircuitGeneration
public import GameTheoryComplexity.Backend.EndOfLineVerifier
public import GameTheoryComplexity.Backend.RawEndOfLine

@[expose] public section

/-! Native End-of-Line families reduce to concrete endpoint and raw-witness instances.
The answer decoder returns target endpoints when the source flag holds, and the
native zero vertex otherwise. Every accepted target answer is preserved.
-/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM

private theorem generatedSource_iff {α : Type} (n : α → ℕ)
    (P S : α × List Bool → List Bool) (a : α)
    (hS_length : ∀ u : List Bool, u.length = n a → (S (a, u)).length = n a)
    (inst : List Bool) (hwidth : endOfLineWidth inst = n a)
    (hpointers : ∀ u : List Bool, u.length = n a →
      endOfLinePredecessor inst u = NativeEndOfLine.activePredecessor n P S (a, u) ∧
      endOfLineSuccessor inst u = Cslib.Complexity.ppadToPppMap n P S (a, u)) :
    endOfLineSourceValid inst ↔
      Cslib.Complexity.hasOut n P S a (Cslib.Complexity.zeroVertex (n a)) = true := by
  let zero := Cslib.Complexity.zeroVertex (n a)
  have hzero : zero.length = n a := by
    simp only [zero, Cslib.Complexity.zeroVertex, List.length_replicate]
  have horigin : endOfLineOrigin inst = zero := by
    rw [endOfLineOrigin, hwidth]
    rfl
  have hread := hpointers zero hzero
  have hsuccessor_length : (Cslib.Complexity.ppadToPppMap n P S (a, zero)).length = n a :=
    Cslib.Complexity.length_ppadToPppMap hS_length hzero
  have hread_next := (hpointers _ hsuccessor_length).1
  rw [endOfLineSourceValid, horigin, hread.1, hread.2, hread_next]
  exact NativeEndOfLine.active_source_iff n P S a

private theorem generatedEndpoint_iff {α : Type} (n : α → ℕ)
    (P S : α × List Bool → List Bool) (a : α)
    (hP_length : ∀ u : List Bool, u.length = n a → (P (a, u)).length = n a)
    (hS_length : ∀ u : List Bool, u.length = n a → (S (a, u)).length = n a)
    (inst : List Bool)
    (hpointers : ∀ u : List Bool, u.length = n a →
      endOfLinePredecessor inst u = NativeEndOfLine.activePredecessor n P S (a, u) ∧
      endOfLineSuccessor inst u = Cslib.Complexity.ppadToPppMap n P S (a, u))
    (u : List Bool) (hu : u.length = n a) :
    GameTheory.Math.EndOfLine.IsEndpoint
        (endOfLinePredecessor inst) (endOfLineSuccessor inst) u ↔
      (Cslib.Complexity.hasIn n P S a u != Cslib.Complexity.hasOut n P S a u) = true := by
  have hread := hpointers u hu
  have hpred_length := NativeEndOfLine.activePredecessor_length n P S a hP_length u hu
  have hsucc_length : (Cslib.Complexity.ppadToPppMap n P S (a, u)).length = n a :=
    Cslib.Complexity.length_ppadToPppMap hS_length hu
  have hread_pred := (hpointers _ hpred_length).2
  have hread_succ := (hpointers _ hsucc_length).1
  rw [← NativeEndOfLine.isEndpoint_active_iff n P S a u]
  simp only [GameTheory.Math.EndOfLine.IsEndpoint, GameTheory.Math.EndOfLine.HasSuccessor,
    GameTheory.Math.EndOfLine.HasPredecessor, hread.1, hread.2, hread_pred, hread_succ]

/-- Every native End-of-Line family search-reduces to the concrete endpoint
relation. The decoder handles every accepted target answer, including the empty
fallback when the generated source flag fails. -/
theorem nativeEndOfLine_searchReducible {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {P S : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hP_length : ∀ a (u : List Bool), u.length = n a → (P (a, u)).length = n a)
    (hS_length : ∀ a (u : List Bool), u.length = n a → (S (a, u)).length = n a) :
    Cslib.Complexity.SearchReducible enc encBits
      (Cslib.Complexity.endOfLineRel n P S) endOfLineRelation := by
  obtain ⟨inst, hinst, hwidth, hpointers⟩ :=
    exists_activeEndOfLineInstance hn hP hS hP_length hS_length
  let decode (p : α × List Bool) : List Bool :=
    if endOfLineSourceFlag (inst p.1) then p.2
    else Cslib.Complexity.zeroVertex (n p.1)
  have hinput := hinst.comp (ComputableInPolyTime.fst enc encBits)
  have hzero := (ComputableInPolyTime.bitsReplicate false).comp
    (hn.comp (ComputableInPolyTime.fst enc encBits))
  have hdecode : ComputableInPolyTime decode (encPair enc encBits) encBits :=
    (endOfLineSourceFlag_polyTime hinput).ite (ComputableInPolyTime.snd enc encBits) hzero
  refine Cslib.Complexity.SearchReducible.of_isTotalSearch
    endOfLineRelation_total hinst hdecode ?_
  intro a w hw
  by_cases hvalid : endOfLineSourceValid (inst a)
  · have hflag := (endOfLineSourceFlag_accept (inst a)).mpr hvalid
    have hnative : Cslib.Complexity.endOfLineRel n P S a w := by
      rcases hw with ⟨_, hwlength, hwne, hendpoint⟩ | ⟨hinvalid, _⟩
      · have hu : w.length = n a := hwlength.trans (hwidth a)
        have horigin : endOfLineOrigin (inst a) = Cslib.Complexity.zeroVertex (n a) := by
          rw [endOfLineOrigin, hwidth a]
          rfl
        have hne : w ≠ Cslib.Complexity.zeroVertex (n a) := by
          simpa only [horigin] using hwne
        have hparity := (generatedEndpoint_iff n P S a (hP_length a) (hS_length a)
          (inst a) (hpointers a) w hu).mp hendpoint
        refine ⟨hu, ?_⟩
        simpa [hne] using hparity
      · exact (hinvalid hvalid).elim
    simpa [decode, hflag] using hnative
  · have hflag : endOfLineSourceFlag (inst a) = false := by
      apply Bool.eq_false_iff.mpr
      exact fun ht => hvalid ((endOfLineSourceFlag_accept (inst a)).mp ht)
    have hout : Cslib.Complexity.hasOut n P S a
        (Cslib.Complexity.zeroVertex (n a)) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hvalid ((generatedSource_iff n P S a (hS_length a)
        (inst a) (hwidth a) (hpointers a)).mpr ht)
    simpa [decode, hflag] using
      Cslib.Complexity.endOfLineRel_zeroVertex_of_hasOut_eq_false hout

/-- Every native End-of-Line family also reduces to the concrete asymmetric raw
relation. Active pointers rule out a broken first link, so every accepted raw
witness away from the fallback is a genuine non-source endpoint. -/
theorem nativeEndOfLine_raw_searchReducible {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {P S : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hP_length : ∀ a (u : List Bool), u.length = n a → (P (a, u)).length = n a)
    (hS_length : ∀ a (u : List Bool), u.length = n a → (S (a, u)).length = n a) :
    Cslib.Complexity.SearchReducible enc encBits
      (Cslib.Complexity.endOfLineRel n P S) rawEndOfLineRelation := by
  obtain ⟨inst, hinst, hwidth, hpointers⟩ :=
    exists_activeEndOfLineInstance hn hP hS hP_length hS_length
  let decode (p : α × List Bool) : List Bool :=
    if endOfLineSourceFlag (inst p.1) then p.2
    else Cslib.Complexity.zeroVertex (n p.1)
  have hinput := hinst.comp (ComputableInPolyTime.fst enc encBits)
  have hzero := (ComputableInPolyTime.bitsReplicate false).comp
    (hn.comp (ComputableInPolyTime.fst enc encBits))
  have hdecode : ComputableInPolyTime decode (encPair enc encBits) encBits :=
    (endOfLineSourceFlag_polyTime hinput).ite (ComputableInPolyTime.snd enc encBits) hzero
  refine Cslib.Complexity.SearchReducible.of_isTotalSearch
    rawEndOfLineRelation_total hinst hdecode ?_
  intro a w hw
  by_cases hvalid : endOfLineSourceValid (inst a)
  · have hflag := (endOfLineSourceFlag_accept (inst a)).mpr hvalid
    have hout := (generatedSource_iff n P S a (hS_length a)
      (inst a) (hwidth a) (hpointers a)).mp hvalid
    have hnative : Cslib.Complexity.endOfLineRel n P S a w := by
      rcases hw with ⟨_, hwlength, hraw⟩ | ⟨hinvalid, _⟩
      · have hu : w.length = n a := hwlength.trans (hwidth a)
        have horigin : endOfLineOrigin (inst a) = Cslib.Complexity.zeroVertex (n a) := by
          rw [endOfLineOrigin, hwidth a]
          rfl
        have hraw_active : GameTheory.Math.EndOfLine.RawWitness
            (fun v => NativeEndOfLine.activePredecessor n P S (a, v))
            (fun v => Cslib.Complexity.ppadToPppMap n P S (a, v))
            (Cslib.Complexity.zeroVertex (n a)) w := by
          rw [horigin] at hraw
          exact (GameTheory.Math.EndOfLine.rawWitness_congrOn
            (endOfLinePredecessor (inst a)) (endOfLineSuccessor (inst a))
            (fun v => NativeEndOfLine.activePredecessor n P S (a, v))
            (fun v => Cslib.Complexity.ppadToPppMap n P S (a, v))
            (fun v : List Bool => v.length = n a)
            (fun v hv => (hpointers a v hv).1) (fun v hv => (hpointers a v hv).2)
            (fun v hv => NativeEndOfLine.activePredecessor_length n P S a (hP_length a) v hv)
            (fun v hv => Cslib.Complexity.length_ppadToPppMap (P := P) (hS_length a) hv)
            (Cslib.Complexity.zeroVertex (n a)) w hu).mp hraw
        have hparts := (NativeEndOfLine.rawWitness_active_iff n P S a hout w).mp hraw_active
        have hparity := (NativeEndOfLine.isEndpoint_active_iff n P S a w).mp hparts.2
        refine ⟨hu, ?_⟩
        simpa [hparts.1] using hparity
      · exact (hinvalid ⟨hvalid.1, hvalid.2.1⟩).elim
    simpa [decode, hflag] using hnative
  · have hflag : endOfLineSourceFlag (inst a) = false := by
      apply Bool.eq_false_iff.mpr
      exact fun ht => hvalid ((endOfLineSourceFlag_accept (inst a)).mp ht)
    have hout : Cslib.Complexity.hasOut n P S a
        (Cslib.Complexity.zeroVertex (n a)) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hvalid ((generatedSource_iff n P S a (hS_length a)
        (inst a) (hwidth a) (hpointers a)).mpr ht)
    simpa [decode, hflag] using
      Cslib.Complexity.endOfLineRel_zeroVertex_of_hasOut_eq_false hout

end GameTheory.Complexity.Backend
