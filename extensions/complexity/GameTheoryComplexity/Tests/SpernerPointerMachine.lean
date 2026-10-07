import GameTheoryComplexity.Backend.SpernerPointerMachine
import GameTheoryComplexity.Backend.CircuitVectorMachine

/-! Machine-level controls exercise source paths, boundary carries, rejected
encodings and a disconnected cycle. The uniform certificate permits both the
coordinate ruler and the serialized circuit seed to vary with the input. -/

namespace GameTheory.Complexity.Tests.SpernerPointerMachine

open GameTheory.Complexity.Backend GameTheory.Math.Sperner GameTheory.Math.EndOfLine
open _root_.Complexity _root_.Complexity.Cobham

/-- At zero coordinate width, the lower triangle is a sink and the upper is isolated. -/
theorem smallest_grid_all_words :
    gridPointerMachine [] (fun _ => []) true [false, false] = [false, false] ∧
      gridPointerMachine [] (fun _ => []) false [false, false] = [true, false] ∧
      gridPointerMachine [] (fun _ => []) true [true, false] = [false, false] ∧
      gridPointerMachine [] (fun _ => []) false [true, false] = [true, false] ∧
      gridPointerMachine [] (fun _ => []) true [true, true] = [true, true] ∧
      gridPointerMachine [] (fun _ => []) false [true, true] = [true, true] ∧
      gridPointerMachine [] (fun _ => []) true [false, true] = [false, true] ∧
      gridPointerMachine [] (fun _ => []) false [false, true] = [false, true] := by decide

/-- Constant interior color zero gives a source path ending at an upper triangle. -/
theorem one_bit_source_path :
    gridPointerMachine [false] (fun _ => []) false [false, false, false, false] =
        [true, false, false, false] ∧
      gridPointerMachine [false] (fun _ => []) true [true, false, false, false] =
        [false, false, false, false] ∧
      gridPointerMachine [false] (fun _ => []) false [true, false, false, false] =
        [true, true, true, false] ∧
      gridPointerMachine [false] (fun _ => []) true [true, true, true, false] =
        [true, false, false, false] ∧
      gridPointerMachine [false] (fun _ => []) false [true, true, true, false] =
        [true, true, true, false] := by decide

theorem one_bit_upper_endpoint :
    IsEndpoint (gridPointerMachine [true] (fun _ => []) true)
      (gridPointerMachine [true] (fun _ => []) false) [true, true, true, false] := by decide

/-- A carry to coordinate two is a boundary, even if a wrapped query would return zero. -/
theorem boundary_carries_override_query :
    gridCornerColor [false] (fun _ => []) [true, false, true, true] 1 = [false, true] ∧
      gridCornerColor [false] (fun _ => []) [true, false, true, true] 2 = [false, true] ∧
      gridCornerColor [false] (fun _ => []) [true, true, true, true] 1 = [false, true] ∧
      gridCornerColor [false] (fun _ => []) [true, true, true, true] 2 = [false, true] := by
  decide

/-- Coordinate queries use distinct little-endian blocks with one extra bit each. -/
theorem query_coordinate_order_and_width :
    gridCornerColor [false, false]
      (fun word => if word = [true, false, false, false, true, false]
        then [true, false] else [])
      (encodeGridNode 2 (some ⟨1, 2, false⟩)) 0 = [true, false] := by decide

theorem query_color_priority :
    gridCornerColor [false, false] (fun _ => [true, true, true])
      (encodeGridNode 2 (some ⟨1, 2, false⟩)) 0 = [true, false] := by decide

/-- Incorrect lengths and unused source-tag words retain themselves in both directions. -/
theorem rejected_words_are_isolated (incoming : Bool) :
    gridPointerMachine [false] (fun _ => []) incoming [] = [] ∧
      gridPointerMachine [false] (fun _ => []) incoming [true] = [true] ∧
      gridPointerMachine [false] (fun _ => []) incoming [true, false, false] =
        [true, false, false] ∧
      gridPointerMachine [false] (fun _ => []) incoming [true, false, false, false, false] =
        [true, false, false, false, false] ∧
      gridPointerMachine [false] (fun _ => []) incoming [false, true, false, false] =
        [false, true, false, false] ∧
      gridPointerMachine [false] (fun _ => []) incoming [false, false, true, false] =
        [false, false, true, false] := by cases incoming <;> decide

private def cycleQuery (word : List Bool) : List Bool :=
  [decide (Nat.fromBitsLE (word.take 3) = 2 ∧ Nat.fromBitsLE (word.drop 3) = 2), false]

/-- The source component is not the whole graph: a six-triangle cycle remains present. -/
theorem disconnected_cycle :
    gridPointerMachine [false, false] cycleQuery false
        (encodeGridNode 2 (some ⟨1, 1, false⟩)) =
      encodeGridNode 2 (some ⟨1, 1, true⟩) ∧
      gridPointerMachine [false, false] cycleQuery false
          (encodeGridNode 2 (some ⟨1, 1, true⟩)) =
        encodeGridNode 2 (some ⟨1, 2, false⟩) ∧
      gridPointerMachine [false, false] cycleQuery false
          (encodeGridNode 2 (some ⟨1, 2, false⟩)) =
        encodeGridNode 2 (some ⟨2, 2, true⟩) ∧
      gridPointerMachine [false, false] cycleQuery false
          (encodeGridNode 2 (some ⟨2, 2, true⟩)) =
        encodeGridNode 2 (some ⟨2, 2, false⟩) ∧
      gridPointerMachine [false, false] cycleQuery false
          (encodeGridNode 2 (some ⟨2, 2, false⟩)) =
        encodeGridNode 2 (some ⟨2, 1, true⟩) ∧
      gridPointerMachine [false, false] cycleQuery false
          (encodeGridNode 2 (some ⟨2, 1, true⟩)) =
        encodeGridNode 2 (some ⟨1, 1, false⟩) := by decide

theorem cycle_vertex_is_not_endpoint :
    ¬IsEndpoint (gridPointerMachine [false, false] cycleQuery true)
      (gridPointerMachine [false, false] cycleQuery false)
      (encodeGridNode 2 (some ⟨1, 1, false⟩)) := by decide

/-- Certified circuit queries remain polynomial when the ruler, seed and vertex all vary. -/
theorem uniform_circuit_pointer_mem_FP (incoming : Bool) :
    (fun z => gridPointerMachine (pairFst z)
      (evaluateCircuitVector (pairFst (pairSnd z))) incoming (pairSnd (pairSnd z))) ∈ FP :=
  gridPointerMachineUniformFn_mem_FP incoming pairFst_mem_FP
    (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) evaluateCircuitVector_pair_mem_FP

end GameTheory.Complexity.Tests.SpernerPointerMachine
