module

public import GameTheoryComplexity.Backend.SpernerGridWords
public import GameTheoryComplexity.Backend.SpernerGridCodecMachine
public import GameTheoryComplexity.Backend.SpernerBinarySteps

@[expose] public section

/-! Binary grid controls cover the smallest width, canonical source rejection,
coordinate order, arithmetic carries, a source path, and a disconnected cycle. -/

namespace GameTheory.Complexity.Tests.SpernerGridWords

open GameTheory.Complexity.Backend GameTheory.Math.Sperner GameTheory.Math.EndOfLine
open Turing.MultiTapeTM

example : gridNodeWidth 0 = 2 ∧ encodeGridNode 0 none = [false, false] ∧
    encodeGridNode 0 (some ⟨0, 0, false⟩) = [true, false] ∧
    encodeGridNode 0 (some ⟨0, 0, true⟩) = [true, true] := by decide

example : decodeGridNode 0 [false, false] = some none ∧
    decodeGridNode 0 [true, false] = some (some ⟨0, 0, false⟩) ∧
    decodeGridNode 0 [true, true] = some (some ⟨0, 0, true⟩) ∧
    decodeGridNode 0 [false, true] = none := by decide

example : decodeGridNode 0 [] = none ∧ decodeGridNode 0 [true] = none ∧
    decodeGridNode 0 [true, false, false] = none ∧
    decodeGridNode 1 [false, false, true, false] = none := by decide

example : encodeGridNode 1 (some ⟨1, 0, true⟩) = [true, true, true, false] ∧
    decodeGridNode 1 [true, false, false, true] = some (some ⟨0, 1, false⟩) := by decide

example : wordGridPointer 0 (fun _ _ => 0) true [false, false] = [false, false] ∧
    wordGridPointer 0 (fun _ _ => 0) false [false, false] = [true, false] ∧
    wordGridPointer 0 (fun _ _ => 0) true [true, false] = [false, false] ∧
    IsEndpoint (wordGridPointer 0 (fun _ _ => 0) true)
      (wordGridPointer 0 (fun _ _ => 0) false) [true, false] := by decide

example : wordGridPointer 0 (fun _ _ => 0) true [false, true] = [false, true] ∧
    wordGridPointer 0 (fun _ _ => 0) false [false, true] = [false, true] ∧
    ¬IsEndpoint (wordGridPointer 0 (fun _ _ => 0) true)
      (wordGridPointer 0 (fun _ _ => 0) false) [false, true] := by decide

example : wordGridPointer 1 (fun _ _ => 0) false [true, false, false, false] =
    [true, true, true, false] ∧
    IsEndpoint (wordGridPointer 1 (fun _ _ => 0) true)
      (wordGridPointer 1 (fun _ _ => 0) false) [true, true, true, false] := by decide

private def cycleInterior (i j : ℕ) : Fin 3 := if i = 2 ∧ j = 2 then 1 else 0

example :
    wordGridPointer 2 cycleInterior false (encodeGridNode 2 (some ⟨1, 1, false⟩)) =
      encodeGridNode 2 (some ⟨1, 1, true⟩) ∧
    wordGridPointer 2 cycleInterior false (encodeGridNode 2 (some ⟨1, 1, true⟩)) =
      encodeGridNode 2 (some ⟨1, 2, false⟩) ∧
    wordGridPointer 2 cycleInterior false (encodeGridNode 2 (some ⟨1, 2, false⟩)) =
      encodeGridNode 2 (some ⟨2, 2, true⟩) ∧
    wordGridPointer 2 cycleInterior false (encodeGridNode 2 (some ⟨2, 2, true⟩)) =
      encodeGridNode 2 (some ⟨2, 2, false⟩) ∧
    wordGridPointer 2 cycleInterior false (encodeGridNode 2 (some ⟨2, 2, false⟩)) =
      encodeGridNode 2 (some ⟨2, 1, true⟩) ∧
    wordGridPointer 2 cycleInterior false (encodeGridNode 2 (some ⟨2, 1, true⟩)) =
      encodeGridNode 2 (some ⟨1, 1, false⟩) := by decide

example : ¬IsEndpoint (wordGridPointer 2 cycleInterior true)
    (wordGridPointer 2 cycleInterior false) (encodeGridNode 2 (some ⟨1, 1, false⟩)) := by
  decide

example : gridSuccBits [true, true, false] = [false, false, true] ∧
    gridPredBits [false, false, true] = [true, true, false] ∧
    gridSuccBits [true, true] = [false, false] ∧
    gridPredBits [false, false] = [true, true] := by decide

example : gridNodeAcceptFlag [] [false, false] = [true] ∧
    gridNodeAcceptFlag [] [true, false] = [true] ∧
    gridNodeAcceptFlag [] [false, true] = [false] ∧
    gridNodeAcceptFlag [] [] = [false] := by decide

example : ComputableInPolyTime
    (fun p : List Bool × List Bool => gridWidthWord p.1) (encPair encBits encBits) encBits :=
  gridWidthWord_polyTime (ComputableInPolyTime.fst encBits encBits)

example : ComputableInPolyTime
    (fun p : List Bool × List Bool => gridNodeAcceptFlag p.1 p.2)
    (encPair encBits encBits) encBits :=
  gridNodeAcceptFlag_polyTime (ComputableInPolyTime.fst encBits encBits)
    (ComputableInPolyTime.snd encBits encBits)

example : ComputableInPolyTime gridSuccBits encBits encBits ∧
    ComputableInPolyTime gridPredBits encBits encBits :=
  ⟨gridSuccBits_polyTime, gridPredBits_polyTime⟩

end GameTheory.Complexity.Tests.SpernerGridWords
