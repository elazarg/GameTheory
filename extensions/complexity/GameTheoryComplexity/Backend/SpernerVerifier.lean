import GameTheoryComplexity.Backend.SpernerProblem
import Complexitylib.Classes.P.NormalForm

/-! A polynomial-time Sperner verifier checks one triangle code and its three
corner colors. The canonical paired verifier rejects malformed outer encodings;
its machine certificate measures the complete serialized input. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.Sperner

private theorem headFlag_flag (word : List Bool) :
    bitAt [] word = [true] ∨ bitAt [] word = [false] := by
  cases word with
  | nil => exact Or.inr rfl
  | cons first rest => cases first <;> simp [bitAt_nil_left]

private theorem source_head (b : ℕ) : bitAt [] (encodeGridNode b none) = [false] := by
  change bitAt [] (List.replicate (2 * b + 2) false) = _
  rw [Nat.add_comm (2 * b) 2, List.replicate_add]
  rfl

private def triangleFlag (input word : List Bool) : List Bool :=
  andBit (gridNodeAcceptFlag (pairFst input) word) (bitAt [] word)

private theorem triangleFlag_accept (input word : List Bool) :
    triangleFlag input word = [true] ↔
      ∃ t, decodeGridNode (pairFst input).length word = some (some t) := by
  have hn : gridNodeAcceptFlag (pairFst input) word = [true] ∨
      gridNodeAcceptFlag (pairFst input) word = [false] := andBit_flag _ _
  rw [triangleFlag, andBit_eq_true_iff hn (headFlag_flag _)]
  constructor
  · rintro ⟨ha, hh⟩
    obtain ⟨node, hd⟩ := (gridNodeAcceptFlag_accept _ _).mp ha
    cases node with
    | none =>
      rw [← encodeGridNode_decode hd, source_head] at hh
      contradiction
    | some t => exact ⟨t, hd⟩
  · rintro ⟨t, hd⟩
    refine ⟨(gridNodeAcceptFlag_accept _ _).mpr ⟨some t, hd⟩, ?_⟩
    rw [← encodeGridNode_decode hd]
    rfl

private theorem encodedColors_eq_iff (a b : Fin 3) :
    encodeGridColor a = encodeGridColor b ↔ a = b := by
  constructor
  · intro h
    simpa only [decodeGridColor_encode] using congrArg decodeGridColor h
  · rintro rfl
    rfl

private def colorFlag (input word : List Bool) : List Bool :=
  let a := gridCornerColor (pairFst input) (evaluateCircuitVector (pairSnd input)) word 0
  let b := gridCornerColor (pairFst input) (evaluateCircuitVector (pairSnd input)) word 1
  let c := gridCornerColor (pairFst input) (evaluateCircuitVector (pairSnd input)) word 2
  andBit (notBit (eqFlag a b))
    (andBit (notBit (eqFlag b c)) (notBit (eqFlag c a)))

private theorem colorFlag_accept {input word : List Bool} {t : GridTriangle}
    (hd : decodeGridNode (pairFst input).length word = some (some t)) :
    colorFlag input word = [true] ↔
      Trichromatic
        (spernerColor input (corner t 0).1 (corner t 0).2)
        (spernerColor input (corner t 1).1 (corner t 1).2)
        (spernerColor input (corner t 2).1 (corner t 2).2) := by
  have hv := decodeGridNode_valid hd t rfl
  rw [colorFlag, ← encodeGridNode_decode hd,
    gridCornerColor_encode _ _ t 0 hv, gridCornerColor_encode _ _ t 1 hv,
    gridCornerColor_encode _ _ t 2 hv]
  rw [andBit_eq_true_iff (negFlag_flag (eqFlag_flag _ _)) (andBit_flag _ _),
    andBit_eq_true_iff (negFlag_flag (eqFlag_flag _ _)) (negFlag_flag (eqFlag_flag _ _)),
    negFlag_accept (eqFlag_flag _ _), negFlag_accept (eqFlag_flag _ _),
    negFlag_accept (eqFlag_flag _ _)]
  simp only [eqFlag_eq_true_iff, encodedColors_eq_iff, Trichromatic, spernerColor]

/-- Check exact triangle encoding and the three distinct corner colors. -/
def spernerVerdict (input word : List Bool) : List Bool :=
  andBit (triangleFlag input word) (colorFlag input word)

theorem spernerVerdict_flag (input word : List Bool) :
    spernerVerdict input word = [true] ∨ spernerVerdict input word = [false] :=
  andBit_flag _ _

theorem spernerVerdict_accept (input word : List Bool) :
    spernerVerdict input word = [true] ↔ spernerRelation input word := by
  have ht : triangleFlag input word = [true] ∨ triangleFlag input word = [false] :=
    andBit_flag _ _
  have hc : colorFlag input word = [true] ∨ colorFlag input word = [false] :=
    andBit_flag _ _
  rw [spernerVerdict, andBit_eq_true_iff ht hc, triangleFlag_accept]
  constructor
  · rintro ⟨⟨t, hd⟩, hc⟩
    exact ⟨t, hd, (colorFlag_accept hd).mp hc⟩
  · rintro ⟨t, hd, hc⟩
    exact ⟨⟨t, hd⟩, (colorFlag_accept hd).mpr hc⟩

private theorem verdict_pair_mem_FP :
    (fun z => spernerVerdict (pairFst z) (pairSnd z)) ∈ FP := by
  have hr := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hs := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hw := pairSnd_mem_FP
  have hhead : (fun z => bitAt [] (pairSnd z)) ∈ FP :=
    CobhamFP_subset_FP (headFlagFn (FP_subset_CobhamFP hw))
  have htriangle := andBitFn_mem_FP (gridNodeAcceptFlagFn_mem_FP hr hw) hhead
  have h₀ := gridCornerColorUniformFn_mem_FP 0 hr hs hw _ evaluateCircuitVector_pair_mem_FP
  have h₁ := gridCornerColorUniformFn_mem_FP 1 hr hs hw _ evaluateCircuitVector_pair_mem_FP
  have h₂ := gridCornerColorUniformFn_mem_FP 2 hr hs hw _ evaluateCircuitVector_pair_mem_FP
  exact andBitFn_mem_FP htriangle
    (andBitFn_mem_FP (notBitFn_mem_FP (eqFlagFn_mem_FP h₀ h₁))
      (andBitFn_mem_FP (notBitFn_mem_FP (eqFlagFn_mem_FP h₁ h₂))
        (notBitFn_mem_FP (eqFlagFn_mem_FP h₂ h₀))))

/-- Reject noncanonical outer pairs before verifying a Sperner triangle. -/
def spernerPairedVerdict (z : List Bool) : List Bool :=
  andBit (eqFlag z (pair (pairFst z) (pairSnd z)))
    (spernerVerdict (pairFst z) (pairSnd z))

/-- One polynomial-time string computation performs the complete verification. -/
theorem spernerPairedVerdict_mem_FP : spernerPairedVerdict ∈ FP :=
  andBitFn_mem_FP
    (eqFlagFn_mem_FP id_mem_FP (pairFn_mem_FP pairFst_mem_FP pairSnd_mem_FP))
    verdict_pair_mem_FP

/-- The complete verifier has an actual deterministic machine with polynomial runtime. -/
theorem exists_spernerPairedVerdict_machine :
    ∃ (k : ℕ) (machine : TM k) (bound : Polynomial ℕ),
      machine.ComputesInTime spernerPairedVerdict bound.eval :=
  mem_FP_iff_computesInTime_polynomial.mp spernerPairedVerdict_mem_FP

theorem spernerPairedVerdict_accept (z : List Bool) :
    spernerPairedVerdict z = [true] ↔ z ∈ pairLang spernerRelation := by
  rw [spernerPairedVerdict,
    andBit_eq_true_iff (eqFlag_flag _ _) (spernerVerdict_flag _ _),
    eqFlag_eq_true_iff, spernerVerdict_accept]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨pairFst z, pairSnd z, hz, h⟩
  · rintro ⟨input, word, rfl, h⟩
    simp only [pairFst_pair, pairSnd_pair]
    exact ⟨trivial, h⟩

/-- Linear witness balance and the polynomial-time paired verifier give FNP membership. -/
theorem spernerRelation_mem_FNP : spernerRelation ∈ FNP := by
  refine ⟨spernerRelation_polyBalanced, mem_P_of_decisionFn spernerPairedVerdict_mem_FP ?_⟩
  intro z
  rw [← spernerPairedVerdict_accept]
  rcases andBit_flag (eqFlag z (pair (pairFst z) (pairSnd z)))
    (spernerVerdict (pairFst z) (pairSnd z)) with h | h <;>
    simp [spernerPairedVerdict, h]

end GameTheory.Complexity.Backend
