import GameTheoryComplexity.BimatrixNash

/-! Kernel-checked arithmetic, malformed-input and canonical-pair controls. -/
namespace GameTheory.Complexity.Tests.GeneralBimatrix
open _root_.Complexity _root_.Complexity.Cobham Backend

-- A binary product, rather than an iteration over the represented magnitude.
example : Nat.fromBitsLE (binaryWordMul [true, true, true] [true, true, true]) = 49 :=
  by decide

-- Unequal lengths and leading zero padding preserve numerical multiplication.
example : Nat.fromBitsLE (binaryWordMul [true, false, false] [false, true]) = 2 :=
  by decide

example : Nat.fromBitsLE (binaryWordMul [] [true, true]) = 0 := by decide

-- Empty and unterminated headers are malformed, with exactly one fallback answer.
example : generalBimatrixRelation [] [] := Or.inr ⟨by decide, rfl⟩

example : ¬generalBimatrixRelation [] [false] := by
  rw [generalBimatrixRelation_invalid_iff _ _ (by decide)]
  decide

example : generalBimatrixRelation [true] [] := Or.inr ⟨by decide, rfl⟩

-- Exercise the actual verifier's malformed-input fallback.
example : generalBimatrixVerdict ![[], []] = [true] := by decide

example : generalBimatrixVerdict ![[], [false]] = [false] := by decide

-- The outer serialization must be canonical even if decoded components accept.
example : generalBimatrixPairedVerdict (pair [] []) = [true] := by
  rw [generalBimatrixPairedVerdict, canonicalPairedVerifier_eq_true_iff
    _ generalBimatrixVerdict_flag]
  simp only [pairFst_pair, pairSnd_pair]
  exact ⟨trivial, by decide⟩

example : generalBimatrixPairedVerdict [true] = [false] := by decide

-- The exported result certifies this exact serialized relation.
example : generalBimatrixRelation ∈ FNP := bimatrixNashRelation_mem_FNP

end GameTheory.Complexity.Tests.GeneralBimatrix
