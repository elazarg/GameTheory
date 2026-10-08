import GameTheoryComplexity.Backend.GridRoutingNodeCodec
import GameTheoryComplexity.Backend.GridRoutingLiveMachine
import GameTheoryComplexity.Backend.GridRoutingImageMachine
import GameTheoryComplexity.Backend.GridRoutingNodeMachine
import GameTheoryComplexity.Backend.GridRoutingDecoderMachine
import GameTheoryComplexity.Backend.GridRoutingNodeStepMachine
import GameTheoryComplexity.Backend.GridRoutingPointerMachine

/-! Internal routing controls retain arbitrary raw fields, distinguish total
interpretation from liveness, and exercise displaced crossing occurrences. -/

namespace GameTheory.Complexity.Tests.GridRoutingNodes

open GameTheory.Complexity.Backend GameTheory.Math.GridWire
open GameTheory.Math.EndOfLine
open _root_.Complexity _root_.Complexity.Cobham

private def ruler : List Bool := [false, false, false]

private def field (value : ℕ) : List Bool := Nat.toBitsLE 8 value

private def originalS (i : ℕ) : ℕ :=
  if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 0 else i

private def originalP (i : ℕ) : ℕ :=
  if i = 0 then 2 else if i = 3 then 1 else if i = 4 then 0 else i

private def Squery (bits : List Bool) : List Bool :=
  Nat.toBitsLE 3 (originalS (Nat.fromBitsLE bits))

private def Pquery (bits : List Bool) : List Bool :=
  Nat.toBitsLE 3 (originalP (Nat.fromBitsLE bits))

example (owner x y : List Bool) :
    routingDecodeNodeBits (routingInteriorNodeBits owner x y) =
      .inr (Nat.fromBitsLE owner, (Nat.fromBitsLE x, Nat.fromBitsLE y)) :=
  routingDecodeNodeBits_interior owner x y

example : routingDecodeNodeBits (routingVertexNodeBits [true, false, false, true]) =
      .inl 9 ∧
    routingDecodeNodeBits
        (routingInteriorNodeBits [true, false, false, true] [true] [false, false, true, true]) =
      .inr (9, (1, 12)) ∧
    routingNodeOwnerBits (routingInteriorNodeBits (field 9) [] [true]) = field 9 := by decide

example : routingDecodeNodeBits [] = .inl 0 ∧
    routingDecodeNodeBits [false] = .inl 0 ∧
    routingDecodeNodeBits [true] = .inr (0, (0, 0)) ∧
    routingNodeXBits (routingVertexNodeBits (field 9)) = [] ∧
    Nat.fromBitsLE (routingNodeYBits (routingVertexNodeBits (field 9))) = 54 := by decide

example : routingLiveVertexFlag ruler (field 7) = [true] ∧
    routingLiveVertexFlag ruler (field 9) = [false] ∧
    routingLiveVertexFlag [] [] = [true] ∧
    routingLiveVertexFlag [] [true] = [false] := by decide

example : routingLiveInteriorFlag ruler Pquery Squery [true] [] (field 6) = [false] ∧
    routingLiveInteriorFlag ruler Pquery Squery [true] [] (field 18) = [false] ∧
    routingLiveInteriorFlag ruler Pquery Squery [true] [true] (field 6) = [true] ∧
    routingLiveInteriorFlag ruler Pquery Squery [true] [true] (field 12) = [false] ∧
    routingLiveInteriorFlag ruler Pquery Squery (field 9) [true] (field 6) = [false] ∧
    routingLiveInteriorFlag ruler Pquery Squery [true, true] [true] (field 18) = [false] := by
  decide

example : (fun z => routingInteriorNodeBits (pairFst z) (pairSnd z) (pairFst z)) ∈ FP :=
  routingInteriorNodeBitsFn_mem_FP pairFst_mem_FP pairSnd_mem_FP pairFst_mem_FP

example : (fun z => routingVertexNodeBits (pairSnd z)) ∈ FP :=
  routingVertexNodeBitsFn_mem_FP pairSnd_mem_FP

example : (fun z => routingNodeOwnerBits (pairSnd z)) ∈ FP :=
  routingNodeOwnerBitsFn_mem_FP pairSnd_mem_FP

example : (fun z => routingLiveVertexFlag (pairFst z) (pairSnd z)) ∈ FP :=
  routingLiveVertexFlagFn_mem_FP pairFst_mem_FP pairSnd_mem_FP

example : (fun z => routingLiveInteriorFlag (pairFst z)
    (fun vertex => pairSnd z ++ vertex) (fun vertex => vertex ++ pairSnd z)
    (pairFst z) (pairSnd z) (pairFst z)) ∈ FP :=
  routingLiveInteriorFlagUniformFn_mem_FP (fun seed vertex => seed ++ vertex)
    (fun seed vertex => vertex ++ seed) pairFst_mem_FP pairSnd_mem_FP pairFst_mem_FP
    pairSnd_mem_FP pairFst_mem_FP (appendFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
    (appendFn_mem_FP pairSnd_mem_FP pairFst_mem_FP)

private def imagePoint (P S : List Bool → List Bool) (owner : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (Nat.fromBitsLE (routingImageXBits ruler P S (field owner) (field p.1) (field p.2)),
    Nat.fromBitsLE (routingImageYBits ruler P S (field owner) (field p.1) (field p.2)))

example : imagePoint Pquery Squery 1 (12, 6) = (11, 7) ∧
    imagePoint Pquery Squery 0 (12, 6) = (13, 5) ∧
    Nat.fromBitsLE (routingSwitchOwnerBits ruler Pquery Squery (field 1) (field 12) (field 6)) =
      0 ∧
    Nat.fromBitsLE (routingSwitchOwnerBits ruler Pquery Squery [] (field 12) (field 6)) =
      1 := by decide

example : imagePoint Pquery Squery 2 (12, 3) = (13, 4) ∧
    imagePoint Pquery Squery 0 (12, 3) = (11, 2) ∧
    Nat.fromBitsLE (routingSwitchOwnerBits ruler Pquery Squery (field 2) (field 12) (field 3)) =
      0 ∧
    Nat.fromBitsLE (routingSwitchOwnerBits ruler Pquery Squery [] (field 12) (field 3)) =
      2 := by decide

private def downSquery (bits : List Bool) : List Bool :=
  let i := Nat.fromBitsLE bits
  Nat.toBitsLE 3 (if i = 3 then 0 else if i = 4 then 2 else i)

private def downPquery (bits : List Bool) : List Bool :=
  let i := Nat.fromBitsLE bits
  Nat.toBitsLE 3 (if i = 0 then 3 else if i = 2 then 4 else i)

example : imagePoint downPquery downSquery 4 (72, 15) = (73, 14) ∧
    imagePoint downPquery downSquery 3 (72, 15) = (71, 16) ∧
    Nat.fromBitsLE (routingSwitchOwnerBits ruler downPquery downSquery
      (field 4) (field 72) (field 15)) = 3 ∧
    Nat.fromBitsLE (routingSwitchOwnerBits ruler downPquery downSquery
      (field 3) (field 72) (field 15)) = 4 := by decide

private def phantomSquery (bits : List Bool) : List Bool :=
  let i := Nat.fromBitsLE bits
  Nat.toBitsLE 3 (if i = 1 then 4 else if i = 3 then 0 else i)

private def phantomPquery (bits : List Bool) : List Bool :=
  let i := Nat.fromBitsLE bits
  Nat.toBitsLE 3 (if i = 0 then 3 else if i = 4 then 1 else i)

-- The rightward strand stops at column 36 before reaching the downward strand's column 72.
example : routingCrossingFlag ruler phantomPquery phantomSquery (field 72) (field 6) =
      [false] ∧
    imagePoint phantomPquery phantomSquery 1 (72, 6) = (72, 6) := by decide

example : routingImageXBits ruler Pquery Squery (field 1) [true] (field 6) = [true] ∧
    routingImageYBits ruler Pquery Squery (field 1) [true] (field 6) = field 6 ∧
    routingSwitchOwnerBits ruler Pquery Squery (field 1) [true] (field 6) = field 1 ∧
    routingImageXBits ruler Pquery Squery (field 9) (field 12) (field 6) = field 12 ∧
    routingImageYBits ruler Pquery Squery (field 9) (field 12) (field 6) = field 6 ∧
    routingSwitchOwnerBits ruler Pquery Squery (field 9) (field 12) (field 6) = field 9 := by
  decide

example : (fun z => routingImageXBits (pairFst z)
    (fun vertex => pairSnd z ++ vertex) (fun vertex => vertex ++ pairSnd z)
    (pairFst z) (pairSnd z) (pairFst z)) ∈ FP :=
  routingImageXBitsUniformFn_mem_FP (fun seed vertex => seed ++ vertex)
    (fun seed vertex => vertex ++ seed) pairFst_mem_FP pairSnd_mem_FP pairFst_mem_FP
    pairSnd_mem_FP pairFst_mem_FP (appendFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
    (appendFn_mem_FP pairSnd_mem_FP pairFst_mem_FP)

example : (fun z => routingSwitchOwnerBits (pairFst z)
    (fun vertex => pairSnd z ++ vertex) (fun vertex => vertex ++ pairSnd z)
    (pairFst z) (pairSnd z) (pairFst z)) ∈ FP :=
  routingSwitchOwnerBitsUniformFn_mem_FP (fun seed vertex => seed ++ vertex)
    (fun seed vertex => vertex ++ seed) pairFst_mem_FP pairSnd_mem_FP pairFst_mem_FP
    pairSnd_mem_FP pairFst_mem_FP (appendFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
    (appendFn_mem_FP pairSnd_mem_FP pairFst_mem_FP)

example : routingLiveNodeFlag ruler Pquery Squery [] = [true] ∧
    routingLiveNodeFlag ruler Pquery Squery [true] = [false] ∧
    routingLiveNodeFlag ruler Pquery Squery (routingVertexNodeBits (field 9)) = [false] ∧
    routingLiveNodeFlag ruler Pquery Squery
      (routingInteriorNodeBits [true] [true] (field 6)) = [true] := by decide

example : routingNodeSwitchBits ruler Pquery Squery (routingVertexNodeBits (field 9)) =
      routingVertexNodeBits (field 9) ∧
    routingDecodeNodeBits (routingNodeSwitchBits ruler Pquery Squery
      (routingInteriorNodeBits (field 1) (field 12) (field 6))) = .inr (0, (12, 6)) ∧
    routingDecodeNodeBits (routingNodeSwitchBits ruler Pquery Squery [true]) =
      .inr (0, (0, 0)) := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [routingNodeSwitchBits_decode, routingDecodeNodeBits_interior]
    decide
  · rw [routingNodeSwitchBits_decode]
    decide

example (node : List Bool) : routingDecodeNodeBits
    (routingNodeSwitchBits ruler Pquery Squery (routingNodeSwitchBits ruler Pquery Squery node)) =
      routingDecodeNodeBits node := by
  rw [routingNodeSwitchBits_decode, routingNodeSwitchBits_decode]
  exact GameTheory.Math.GridWire.routedSwitch_involutive _ _ _ _

example : Nat.fromBitsLE (routingNodeImageXBits ruler Pquery Squery
      (routingInteriorNodeBits (field 1) (field 12) (field 6))) = 11 ∧
    Nat.fromBitsLE (routingNodeImageYBits ruler Pquery Squery
      (routingInteriorNodeBits (field 1) (field 12) (field 6))) = 7 ∧
    Nat.fromBitsLE (routingNodeImageYBits ruler Pquery Squery
      (routingVertexNodeBits (field 9))) = 54 := by decide

example : (fun z => routingLiveNodeFlag (pairFst z)
    (fun vertex => pairSnd z ++ vertex) (fun vertex => vertex ++ pairSnd z) (pairSnd z)) ∈ FP :=
  routingLiveNodeFlagUniformFn_mem_FP (fun seed vertex => seed ++ vertex)
    (fun seed vertex => vertex ++ seed) pairFst_mem_FP pairSnd_mem_FP pairSnd_mem_FP
    (appendFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
    (appendFn_mem_FP pairSnd_mem_FP pairFst_mem_FP)

example : (fun z => routingNodeSwitchBits (pairFst z)
    (fun vertex => pairSnd z ++ vertex) (fun vertex => vertex ++ pairSnd z) (pairSnd z)) ∈ FP :=
  routingNodeSwitchBitsUniformFn_mem_FP (fun seed vertex => seed ++ vertex)
    (fun seed vertex => vertex ++ seed) pairFst_mem_FP pairSnd_mem_FP pairSnd_mem_FP
    (appendFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
    (appendFn_mem_FP pairSnd_mem_FP pairFst_mem_FP)

example : routingDecodeResultBits (pair [true] []) = some (.inl 0) ∧
    routingDecodeResultBits (pair [false] []) = none ∧
    routingDecodeResultBits [] = none := by decide

example : routingChooseNodeBits ruler Pquery Squery [] [] [] = pair [false] [] ∧
    routingChooseNodeBits ruler Pquery Squery [] [] [[]] = pair [true] [] := by decide

example : (routingCandidateNodes ruler Pquery (field 13) (field 3)).length = 6 := rfl

example : routingDecodeResultBits (routingDecoderBits ruler Pquery Squery [] []) =
    some (.inl 0) := by
  rw [routingDecoderBits_decode]
  decide

example : routingDecodeResultBits
      (routingDecoderBits ruler Pquery Squery (field 13) (field 4)) =
      some (.inr (2, (12, 3))) ∧
    routingDecodeResultBits (routingDecoderBits ruler Pquery Squery (field 11) (field 2)) =
      some (.inr (0, (12, 3))) ∧
    routingDecodeResultBits (routingDecoderBits ruler Pquery Squery (field 13) (field 3)) =
      some (.inr (2, (13, 3))) := by
  simp only [routingDecoderBits_decode]
  decide

example : routingDecodeResultBits
      (routingDecoderBits ruler Pquery Squery (field 12) (field 3)) = none ∧
    routingDecodeResultBits (routingDecoderBits ruler Pquery Squery (field 11) (field 4)) =
      none ∧
    routingDecodeResultBits (routingDecoderBits ruler Pquery Squery (field 100) (field 100)) =
      none := by
  simp only [routingDecoderBits_decode]
  decide

example : (fun z => routingDecoderBits (pairFst z)
    (fun vertex => pairSnd z ++ vertex) (fun vertex => vertex ++ pairSnd z)
    (pairFst z) (pairSnd z)) ∈ FP :=
  routingDecoderBitsUniformFn_mem_FP (fun seed vertex => seed ++ vertex)
    (fun seed vertex => vertex ++ seed) pairFst_mem_FP pairSnd_mem_FP pairFst_mem_FP
    pairSnd_mem_FP (appendFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
    (appendFn_mem_FP pairSnd_mem_FP pairFst_mem_FP)

example : routingDecodeNodeBits (routingNodeStepBits ruler Pquery Squery
      (routingInteriorNodeBits [true] [true] (field 6)) true) = .inl 1 ∧
    routingDecodeNodeBits (routingNodeStepBits ruler Pquery Squery
      (routingInteriorNodeBits [true] [] (field 19)) false) = .inl 3 ∧
    routingDecodeNodeBits (routingNodeStepBits ruler Pquery Squery
      (routingVertexNodeBits (field 2)) false) = .inr (2, (1, 12)) ∧
    routingDecodeNodeBits (routingNodeStepBits ruler Pquery Squery
      (routingVertexNodeBits (field 4)) true) = .inr (0, (0, 25)) := by
  simp only [routingNodeStepBits_decode, routingDecodeNodeBits_interior,
    routingDecodeNodeBits_vertex]
  decide

example : routingNodeStepBits ruler Pquery Squery [true] true = [true] ∧
    routingNodeStepBits ruler Pquery Squery [true] false = [true] ∧
    routingNodeStepBits ruler Pquery Squery (routingVertexNodeBits (field 9)) false =
      routingVertexNodeBits (field 9) ∧
    routingNodeStepBits ruler Pquery Squery
        (routingInteriorNodeBits (field 9) [true] (field 6)) true =
      routingInteriorNodeBits (field 9) [true] (field 6) := by decide

example : routingDecodeNodeBits (routingNodeStepBits ruler Pquery Squery [] false) =
      .inr (0, (1, 0)) ∧
    routingNodeStepBits ruler Pquery Squery (routingVertexNodeBits (field 2)) true =
      routingVertexNodeBits (field 2) ∧
    routingNodeStepBits ruler Pquery Squery (routingVertexNodeBits (field 4)) false =
      routingVertexNodeBits (field 4) := by
  refine ⟨?_, by decide, by decide⟩
  rw [routingNodeStepBits_decode]
  decide

example : routingDecodeNodeBits (routingNodeStepBits ruler downPquery downSquery
      (routingInteriorNodeBits (field 3) (field 72) (field 15)) false) =
      .inr (3, (72, 14)) ∧
    routingDecodeNodeBits (routingNodeStepBits ruler downPquery downSquery
      (routingInteriorNodeBits (field 3) (field 72) (field 15)) true) =
      .inr (3, (72, 16)) := by
  simp only [routingNodeStepBits_decode, routingDecodeNodeBits_interior]
  decide

example (incoming : Bool) : (fun z => routingNodeStepBits (pairFst z)
    (fun vertex => pairSnd z ++ vertex) (fun vertex => vertex ++ pairSnd z)
    (pairSnd z) incoming) ∈ FP :=
  routingNodeStepBitsUniformFn_mem_FP incoming (fun seed vertex => seed ++ vertex)
    (fun seed vertex => vertex ++ seed) pairFst_mem_FP pairSnd_mem_FP pairSnd_mem_FP
    (appendFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
    (appendFn_mem_FP pairSnd_mem_FP pairFst_mem_FP)

private theorem pointer_step (p q : ℕ × ℕ) (incoming : Bool)
    (hp : p.1 < 2 ^ routingCoordinateWidth 3 ∧ p.2 < 2 ^ routingCoordinateWidth 3)
    (hstep : (if incoming then gridRoutedPredecessor 8 (routingOriginalPointer ruler Pquery)
      (routingOriginalPointer ruler Squery) p else gridRoutedSuccessor 8
      (routingOriginalPointer ruler Pquery) (routingOriginalPointer ruler Squery) p) = q) :
    routingPointerMachine ruler Pquery Squery incoming (encodeRoutingPoint 3 p) =
      encodeRoutingPoint 3 q := by
  rw [routingPointerMachine_eq_words]
  rw [show ruler.length = 3 from rfl, wordRoutingPointer_encode hp]
  exact congrArg (encodeRoutingPoint 3) hstep

example : routingPointerMachine ruler Pquery Squery false (encodeRoutingPoint 3 (13, 3)) =
      encodeRoutingPoint 3 (13, 4) ∧
    routingPointerMachine ruler Pquery Squery false (encodeRoutingPoint 3 (13, 4)) =
      encodeRoutingPoint 3 (12, 4) ∧
    routingPointerMachine ruler Pquery Squery false (encodeRoutingPoint 3 (12, 4)) =
      encodeRoutingPoint 3 (12, 5) ∧
    routingPointerMachine ruler Pquery Squery false (encodeRoutingPoint 3 (12, 5)) =
      encodeRoutingPoint 3 (13, 5) ∧
    routingPointerMachine ruler Pquery Squery false (encodeRoutingPoint 3 (13, 5)) =
      encodeRoutingPoint 3 (13, 6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact pointer_step _ _ false (by decide) (by decide)

example : routingPointerMachine ruler Pquery Squery true (encodeRoutingPoint 3 (13, 4)) =
      encodeRoutingPoint 3 (13, 3) ∧
    routingPointerMachine ruler Pquery Squery true (encodeRoutingPoint 3 (12, 4)) =
      encodeRoutingPoint 3 (13, 4) ∧
    routingPointerMachine ruler Pquery Squery true (encodeRoutingPoint 3 (12, 5)) =
      encodeRoutingPoint 3 (12, 4) ∧
    routingPointerMachine ruler Pquery Squery true (encodeRoutingPoint 3 (13, 5)) =
      encodeRoutingPoint 3 (12, 5) ∧
    routingPointerMachine ruler Pquery Squery true (encodeRoutingPoint 3 (13, 6)) =
      encodeRoutingPoint 3 (13, 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact pointer_step _ _ true (by decide) (by decide)

example : routingDecodeNodeBits (routingSwitchedNodeStepBits ruler Pquery Squery false
      (routingInteriorNodeBits (field 2) (field 12) (field 3))) = .inr (0, (12, 4)) ∧
    routingDecodeNodeBits (routingSwitchedNodeStepBits ruler Pquery Squery true
      (routingInteriorNodeBits (field 0) (field 12) (field 4))) = .inr (2, (12, 3)) := by
  simp only [routingSwitchedNodeStepBits_decode, routingDecodeNodeBits_interior]
  decide

example (incoming : Bool) : routingPointerMachine ruler Pquery Squery incoming [] = [] ∧
    routingPointerMachine ruler Pquery Squery incoming [true] = [true] ∧
    routingPointerMachine ruler Pquery Squery incoming (encodeRoutingPoint 3 (12, 3)) =
      encodeRoutingPoint 3 (12, 3) ∧
    routingPointerMachine ruler Pquery Squery incoming (encodeRoutingPoint 3 (100, 100)) =
      encodeRoutingPoint 3 (100, 100) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [routingPointerMachine_eq_words]
    rfl
  · rw [routingPointerMachine_eq_words]
    rfl
  · cases incoming <;> exact pointer_step _ _ _ (by decide) (by decide)
  · cases incoming <;> exact pointer_step _ _ _ (by decide) (by decide)

private def originPquery (bits : List Bool) : List Bool :=
  let i := Nat.fromBitsLE bits
  Nat.toBitsLE 3 (if i = 1 then 0 else i)

private def originSquery (bits : List Bool) : List Bool :=
  let i := Nat.fromBitsLE bits
  Nat.toBitsLE 3 (if i = 0 then 1 else i)

example : routingPointerMachine ruler originPquery originSquery true (encodeRoutingPoint 3 (0, 0)) =
      encodeRoutingPoint 3 (0, 0) ∧
    routingPointerMachine ruler originPquery originSquery false (encodeRoutingPoint 3 (0, 0)) ≠
      encodeRoutingPoint 3 (0, 0) ∧
    routingPointerMachine ruler originPquery originSquery true
        (routingPointerMachine ruler originPquery originSquery false
          (encodeRoutingPoint 3 (0, 0))) =
      encodeRoutingPoint 3 (0, 0) := by
  simp only [routingPointerMachine_eq_words]
  exact wordRouting_source (by decide) (by decide) (by decide) (by decide)

-- Vertex one belongs to the separate one-to-three path, rather than the two-to-zero-to-four path.
example : IsEndpoint (routingPointerMachine ruler Pquery Squery true)
    (routingPointerMachine ruler Pquery Squery false) (encodeRoutingPoint 3 (vertexPoint 1)) := by
  have hP := fun i (hi : i < 2 ^ ruler.length) => routingOriginalPointer_lt ruler Pquery hi
  have hS := fun i (hi : i < 2 ^ ruler.length) => routingOriginalPointer_lt ruler Squery hi
  have he : IsEndpoint (gridRoutedPredecessor 8 (routingOriginalPointer ruler Pquery)
      (routingOriginalPointer ruler Squery)) (gridRoutedSuccessor 8
      (routingOriginalPointer ruler Pquery) (routingOriginalPointer ruler Squery))
      (vertexPoint 1) := (gridRouted_vertex_endpoint_iff (by decide) hP hS).mpr (by decide)
  have hd := decodeRoutingPoint_encode 3 (vertexPoint 1) (by decide) (by decide)
  have hw := (wordRouting_endpoint_iff hd).mpr he
  simpa only [IsEndpoint, HasPredecessor, HasSuccessor, routingPointerMachine_eq_words,
    show ruler.length = 3 from rfl] using hw

example (incoming : Bool) : (fun z => routingPointerMachine (pairFst z)
    (fun vertex => pairSnd z ++ vertex) (fun vertex => vertex ++ pairSnd z)
    incoming (pairSnd z)) ∈ FP :=
  routingPointerMachineUniformFn_mem_FP incoming (fun seed vertex => seed ++ vertex)
    (fun seed vertex => vertex ++ seed) pairFst_mem_FP pairSnd_mem_FP pairSnd_mem_FP
    (appendFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
    (appendFn_mem_FP pairSnd_mem_FP pairFst_mem_FP)

end GameTheory.Complexity.Tests.GridRoutingNodes
