module

public import GameTheoryComplexity.Backend.GeneralBimatrixFNP

@[expose] public section

/-! Kernel-checked arithmetic, malformed-input and native verifier controls. -/
namespace GameTheory.Complexity.Tests.GeneralBimatrix
open Turing.MultiTapeTM Cslib.Complexity Backend

-- A binary product, rather than an iteration over the represented magnitude.
example : ofBits (binaryWordMul [true, true, true] [true, true, true]) = 49 :=
  by decide

-- Unequal lengths and leading zero padding preserve numerical multiplication.
example : ofBits (binaryWordMul [true, false, false] [false, true]) = 2 :=
  by decide

example : ofBits (binaryWordMul [] [true, true]) = 0 := by decide

-- Empty and unterminated headers are malformed, with exactly one fallback answer.
example : generalBimatrixRelation [] [] := Or.inr ⟨by decide, rfl⟩

example : ¬generalBimatrixRelation [] [false] := by
  rw [generalBimatrixRelation_invalid_iff _ _ (by decide)]
  decide

example : generalBimatrixRelation [true] [] := Or.inr ⟨by decide, rfl⟩

-- Exercise the actual verifier's malformed-input fallback.
example : generalBimatrixVerdict ![[], []] = [true] := by decide

example : generalBimatrixVerdict ![[], [false]] = [false] := by decide

-- Boolean native verification retains precisely the same malformed-game fallback.
example : generalBimatrixAccepts [] [] = true := by decide
example : generalBimatrixAccepts [] [false] = false := by decide

example : ComputableInPolyTime
    (fun p : List Bool × List Bool => generalBimatrixAccepts p.1 p.2)
    (encPair encBits encBits) encBool :=
  generalBimatrixAccepts_polyTime (ComputableInPolyTime.fst encBits encBits)
    (ComputableInPolyTime.snd encBits encBits)

-- The exported result certifies this exact serialized relation.
example : generalBimatrixRelation ∈ FNP encBits := generalBimatrixRelation_mem_FNP

end GameTheory.Complexity.Tests.GeneralBimatrix
