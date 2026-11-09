module

public import GameTheoryComplexity.Backend.SpernerPointerMachine
public import GameTheoryComplexity.Backend.CircuitVectorMachine

@[expose] public section

/-! Machine-level controls exercise source paths, boundary carries, rejected
encodings and a disconnected cycle. The uniform certificate permits both the
coordinate ruler and the serialized circuit seed to vary with the input. -/

namespace GameTheory.Complexity.Tests.SpernerPointerMachine

open GameTheory.Complexity.Backend GameTheory.Math.Sperner GameTheory.Math.EndOfLine
open Turing.MultiTapeTM Cslib.BitString

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
  [decide (lsbValue (word.take 3) = 2 ∧ lsbValue (word.drop 3) = 2), false]

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

/-- Certified queries charge the varying ruler, circuit seed and vertex together. -/
theorem uniform_circuit_pointer_polyTime (incoming : Bool) :
    ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) =>
      gridPointerMachine p.1 (evaluateCircuitVector p.2.1) incoming p.2.2)
      (encPair encBits (encPair encBits encBits)) encBits := by
  have hrest := ComputableInPolyTime.snd encBits (encPair encBits encBits)
  have hr := ComputableInPolyTime.fst encBits (encPair encBits encBits)
  have hv := (ComputableInPolyTime.snd encBits encBits).comp hrest
  have hseed := (ComputableInPolyTime.fst encBits encBits).comp hrest
  have hquery := evaluateCircuitVector_polyTime
    (hseed.comp (ComputableInPolyTime.fst (encPair encBits (encPair encBits encBits)) encBits))
    (ComputableInPolyTime.snd (encPair encBits (encPair encBits encBits)) encBits)
  exact gridPointerMachine_polyTime incoming hr hv
    (fun p => evaluateCircuitVector p.2.1) hquery

end GameTheory.Complexity.Tests.SpernerPointerMachine
