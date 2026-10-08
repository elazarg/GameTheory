import GameTheoryComplexity.Backend.GridRoutingWords
import GameTheoryComplexity.Backend.GridRoutingEndpointMachine

/-! Binary routing controls exercise full-capacity point words, malformed lengths,
padded arithmetic, endpoint label extraction, and actual switched wire execution. -/

namespace GameTheory.Complexity.Tests.GridRouting

open GameTheory.Complexity.Backend GameTheory.Math.GridWire GameTheory.Math.EndOfLine
open _root_.Complexity _root_.Complexity.Cobham

example : routingCoordinateWidth 0 = 3 ∧ routingPointWidth 0 = 6 ∧
    encodeRoutingPoint 0 (0, 0) = List.replicate 6 false ∧
    decodeRoutingPoint 0 (List.replicate 6 true) = some (7, 7) := by decide

example : decodeRoutingPoint 0 (encodeRoutingPoint 0 (7, 0)) = some (7, 0) ∧
    decodeRoutingPoint 0 (encodeRoutingPoint 0 (0, 7)) = some (0, 7) ∧
    decodeRoutingPoint 0 (encodeRoutingPoint 0 (8, 0)) = some (0, 0) := by decide

example : decodeRoutingPoint 0 [] = none ∧
    decodeRoutingPoint 0 (List.replicate 5 false) = none ∧
    decodeRoutingPoint 0 (List.replicate 7 false) = none ∧
    routingPointAcceptFlag [] (List.replicate 6 true) = [true] ∧
    routingPointAcceptFlag [] (List.replicate 5 true) = [false] := by decide

example : routingPointXBits [] (encodeRoutingPoint 0 (5, 2)) = [true, false, true] ∧
    routingPointYBits [] (encodeRoutingPoint 0 (5, 2)) = [false, true, false] := by decide

example : routingDivThreeBits [] = [] ∧ routingDivSixBits [] = [] ∧
    routingModThreeBits [] = [false, false] := by decide

example : routingDivThreeBits (Nat.toBitsLE 8 17) = Nat.toBitsLE 8 5 ∧
    routingDivSixBits (Nat.toBitsLE 8 17) = Nat.toBitsLE 7 2 ∧
    routingModThreeBits (Nat.toBitsLE 8 17) = [false, true] ∧
    routingDivSixBits (Nat.toBitsLE 8 36) = Nat.toBitsLE 7 6 := by decide

example : routingEndpointLabelBits [] (encodeRoutingPoint 0 (vertexPoint 0)) = [] ∧
    routingEndpointLabelBits [false, false, false]
      (encodeRoutingPoint 3 (vertexPoint 7)) = [true, true, true] ∧
    routingEndpointLabelBits [false, false, false]
      (encodeRoutingPoint 3 (vertexPoint 8)) = [false, false, false] := by decide

example : (fun z => routingEndpointLabelBits (pairFst z) (pairSnd z)) ∈ FP :=
  routingEndpointLabelBitsFn_mem_FP pairFst_mem_FP pairSnd_mem_FP

example : (fun z => routingPointAcceptFlag (pairFst z) (pairSnd z)) ∈ FP :=
  routingPointAcceptFlagFn_mem_FP pairFst_mem_FP pairSnd_mem_FP

example : routingDivThreeBits ∈ FP ∧ routingDivSixBits ∈ FP ∧ routingModThreeBits ∈ FP :=
  ⟨routingDivThreeBits_mem_FP, routingDivSixBits_mem_FP, routingModThreeBits_mem_FP⟩

private def fixtureS : ℕ → ℕ
  | 0 => 4
  | 1 => 3
  | 2 => 0
  | i => i

private def fixtureP : ℕ → ℕ
  | 0 => 2
  | 3 => 1
  | 4 => 0
  | i => i

example :
    wordRoutingPointer 3 fixtureP fixtureS false (encodeRoutingPoint 3 (13, 3)) =
      encodeRoutingPoint 3 (13, 4) ∧
    wordRoutingPointer 3 fixtureP fixtureS false (encodeRoutingPoint 3 (13, 4)) =
      encodeRoutingPoint 3 (12, 4) ∧
    wordRoutingPointer 3 fixtureP fixtureS false (encodeRoutingPoint 3 (12, 4)) =
      encodeRoutingPoint 3 (12, 5) ∧
    wordRoutingPointer 3 fixtureP fixtureS false (encodeRoutingPoint 3 (12, 5)) =
      encodeRoutingPoint 3 (13, 5) ∧
    wordRoutingPointer 3 fixtureP fixtureS false (encodeRoutingPoint 3 (13, 5)) =
      encodeRoutingPoint 3 (13, 6) := by decide

example : wordRoutingPointer 3 fixtureP fixtureS true (encodeRoutingPoint 3 (12, 5)) =
      encodeRoutingPoint 3 (12, 4) ∧
    wordRoutingPointer 3 fixtureP fixtureS true (encodeRoutingPoint 3 (12, 4)) =
      encodeRoutingPoint 3 (13, 4) := by decide

example : wordRoutingPointer 3 fixtureP fixtureS true (encodeRoutingPoint 3 (12, 3)) =
      encodeRoutingPoint 3 (12, 3) ∧
    wordRoutingPointer 3 fixtureP fixtureS false (encodeRoutingPoint 3 (12, 3)) =
      encodeRoutingPoint 3 (12, 3) ∧
    ¬IsEndpoint (wordRoutingPointer 3 fixtureP fixtureS true)
      (wordRoutingPointer 3 fixtureP fixtureS false) (encodeRoutingPoint 3 (12, 3)) := by decide

example : wordRoutingPointer 3 fixtureP fixtureS true [] = [] ∧
    wordRoutingPointer 3 fixtureP fixtureS false [true] = [true] ∧
    wordRoutingPointer 3 fixtureP fixtureS true (encodeRoutingPoint 3 (511, 511)) =
      encodeRoutingPoint 3 (511, 511) ∧
    wordRoutingPointer 3 fixtureP fixtureS false (encodeRoutingPoint 3 (511, 511)) =
      encodeRoutingPoint 3 (511, 511) := by decide

private def sourceP (i : ℕ) : ℕ := if i = 1 then 0 else i

private def sourceS (i : ℕ) : ℕ := if i = 0 then 1 else i

example : wordRoutingPointer 1 sourceP sourceS true (encodeRoutingPoint 1 (0, 0)) =
      encodeRoutingPoint 1 (0, 0) ∧
    wordRoutingPointer 1 sourceP sourceS false (encodeRoutingPoint 1 (0, 0)) ≠
      encodeRoutingPoint 1 (0, 0) ∧
    wordRoutingPointer 1 sourceP sourceS true
        (wordRoutingPointer 1 sourceP sourceS false (encodeRoutingPoint 1 (0, 0))) =
      encodeRoutingPoint 1 (0, 0) :=
  wordRouting_source (by decide) (by decide) (by decide) (by decide)

example : routingEndpointLabelBits [false, false, false]
    (encodeRoutingPoint 3 (vertexPoint 2)) = Nat.toBitsLE 3 2 := by decide

example {b : ℕ} {P S : ℕ → ℕ} {word : List Bool}
    (hP : ∀ i, i < 2 ^ b → P i < 2 ^ b) (hS : ∀ i, i < 2 ^ b → S i < 2 ^ b)
    (he : IsEndpoint (wordRoutingPointer b P S true) (wordRoutingPointer b P S false) word) :
    ∃ i, i < 2 ^ b ∧ IsEndpoint P S i ∧
      routingEndpointLabelBits (List.replicate b false) word = Nat.toBitsLE b i := by
  obtain ⟨i, hi, hd, hend⟩ := wordRouting_endpoint_decodes hP hS he
  refine ⟨i, hi, hend, ?_⟩
  have h := routingEndpointLabelBits_eq_bits (ruler := List.replicate b false)
    (by simpa only [List.length_replicate] using hd)
    (by simpa only [List.length_replicate] using hi)
  simpa only [List.length_replicate] using h

end GameTheory.Complexity.Tests.GridRouting
