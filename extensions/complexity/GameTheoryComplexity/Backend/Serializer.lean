module

public import GameTheoryComplexity.Backend.Complexitylib
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

@[expose] public section

/-! Canonical Boolean serialization has a native deterministic polynomial-time
certificate on framed pairs. The certificate includes pair decoding and writing
the unary parameter, delimiter and sample payload.
-/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM

/-- Normalize the first word to unary, delimit it, and retain the sample payload. -/
def serializeBoolean (input : List Bool × List Bool) : List Bool :=
  List.replicate input.1.length true ++ [false] ++ input.2

/-- One actual deterministic polynomial-time machine implements the serializer. -/
theorem serializeBoolean_polyTime :
    ComputableInPolyTime serializeBoolean (encPair encBits encBits) encBits := by
  have hfirst := ComputableInPolyTime.fst encBits encBits
  have hsecond := ComputableInPolyTime.snd encBits encBits
  have hprefix := (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.length_bits.comp hfirst)
  exact (hprefix.bitsAppend (ComputableInPolyTime.const [false])).bitsAppend hsecond

/-- The serializer receives the unary parameter and samples in their original order. -/
def booleanTuple (sampleDegree κ : ℕ) (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    List Bool × List Bool :=
  (List.replicate κ true, List.ofFn draws)

/-- The certified machine writes exactly the input consumed by the sample test. -/
theorem serializeBoolean_booleanTuple (sampleDegree κ : ℕ)
    (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    serializeBoolean (booleanTuple sampleDegree κ draws) = booleanInput sampleDegree κ draws := by
  simp [serializeBoolean, booleanTuple, booleanInput]

/-- The native framed pair has an exact linear size formula. -/
theorem booleanTuple_encode_length (sampleDegree κ : ℕ)
    (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    (encPair encBits encBits (booleanTuple sampleDegree κ draws)).length =
      2 * κ + 1 + (κ + 1) ^ sampleDegree := by
  simp [booleanTuple]

/-- Every sample tuple of the prescribed size has a parameter-polynomial encoding. -/
theorem booleanTuple_encode_length_bound (sampleDegree κ : ℕ)
    (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    (encPair encBits encBits (booleanTuple sampleDegree κ draws)).length ≤
      4 * (κ + 1) ^ (sampleDegree + 1) := by
  have hlength := booleanInput_length_bound sampleDegree κ draws
  rw [booleanInput_length] at hlength
  rw [booleanTuple_encode_length]
  omega

end GameTheory.Complexity.Backend
