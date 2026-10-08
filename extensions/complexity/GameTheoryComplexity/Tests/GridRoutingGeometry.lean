import GameTheoryComplexity.Backend.GridRoutingArithmetic
import GameTheoryComplexity.Backend.GridRoutingBitFields
import GameTheoryComplexity.Backend.GridRoutingGeometryMachine
import GameTheoryComplexity.Backend.GridRoutingGuards
import GameTheoryComplexity.Backend.GridRoutingQueries
import GameTheoryComplexity.Backend.GridRoutingCrossingMachine
import GameTheoryComplexity.Backend.GridRoutingWireMachine

/-! Routing arithmetic controls distinguish numeric equality from word equality,
exercise retained carries and truncation, and test exact lane membership. -/

namespace GameTheory.Complexity.Tests.GridRoutingGeometry

open GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

example : routingEQFlag [] [false, false] = [true] ∧
    routingEQFlag [true] [true, false, false] = [true] ∧
    routingEQFlag [true] [false, true] = [false] ∧
    routingLTFlag [true, false, false] [true] = [false] ∧
    routingLTFlag [true] [false, true, false] = [true] := by decide

example : routingAddBits [true, true, true] [true] = [false, false, false, true] ∧
    routingTripleBits [true, true, true] = Nat.toBitsLE 5 21 ∧
    routingSixBits [true, true, true] = Nat.toBitsLE 6 42 ∧
    routingAddBits [] [] = [false] := by decide

example : routingPadBits [false, false, false] [true, true, true, true, true] =
      [true, true, true] ∧
    routingPadBits [false, false, false, false, false] [true] =
      [true, false, false, false, false] ∧
    routingPadBits [] [true, true] = [] ∧
    routingShiftBits [] [true, false] = [true, false] := by decide

example : routingShiftBits [false, false, false] [true, false] =
      [false, false, false, true, false] ∧
    (routingShiftBits [false, false, false] [true, false]).drop 3 = [true, false] ∧
    (routingShiftBits [false, false, false] [true, false]).take 3 = [false, false, false] := by
  decide

example : Nat.fromBitsLE ([true, false] ++ [false, true]) = 9 ∧
    Nat.fromBitsLE ([true, false, true, true].drop 2) = 3 ∧
    Nat.fromBitsLE ([true, false, true, true].take 2) = 1 := by decide

example : (fun z => routingPadBits (pairFst z) (pairSnd z)) ∈ FP :=
  routingPadBitsFn_mem_FP pairFst_mem_FP pairSnd_mem_FP

example : (fun z => routingShiftBits (pairFst z) (pairSnd z)) ∈ FP :=
  routingShiftBitsFn_mem_FP pairFst_mem_FP pairSnd_mem_FP

example : (fun z => routingAddBits (pairFst z) (pairSnd z)) ∈ FP :=
  routingAddBitsFn_mem_FP pairFst_mem_FP pairSnd_mem_FP

example : (fun z => routingEQFlag (pairFst z) (pairSnd z)) ∈ FP :=
  routingEQFlagFn_mem_FP pairFst_mem_FP pairSnd_mem_FP

private def ruler : List Bool := [false, false, false]

private def field (value : ℕ) : List Bool := Nat.toBitsLE 8 value

example : Nat.fromBitsLE (routingColumnBits ruler [true] (field 3)) = 33 ∧
    Nat.fromBitsLE (routingTargetRowBits [true, true]) = 21 ∧
    Nat.fromBitsLE (routingVerticalOwnerBits ruler (field 219)) = 9 ∧
    routingVerticalOwnerBits ruler (field 219) ≠ Nat.toBitsLE 3 9 := by decide

example : routingCenterBits [true, true, true] = Nat.toBitsLE 6 6 ∧
    routingCenterBits [true, true, true, true] = Nat.toBitsLE 7 15 ∧
    Nat.fromBitsLE (routingCenterBits []) = 0 := by decide

example : routingOnWireFlag ruler [true] [true, true] (field 12) (field 6) = [true] ∧
    routingOnWireFlag ruler [true] [true, true] (field 33) (field 12) = [true] ∧
    routingOnWireFlag ruler [true] [true, true] (field 12) (field 21) = [true] ∧
    routingOnWireFlag ruler [true] [true, true] [] (field 20) = [true] ∧
    routingOnWireFlag ruler [true] [true, true] (field 12) (field 12) = [false] := by decide

example :
    routingHorizontalInteriorFlag ruler [true] [true, true] (field 12) (field 6) = [true] ∧
    routingHorizontalInteriorFlag ruler [true] [true, true] [] (field 6) = [false] ∧
    routingHorizontalInteriorFlag ruler [true] [true, true] (field 33) (field 6) = [false] ∧
    routingVerticalInteriorFlag ruler [true] [true, true] (field 33) (field 12) = [true] ∧
    routingVerticalInteriorFlag ruler [true] [true, true] (field 33) (field 6) = [false] ∧
    routingVerticalInteriorFlag ruler [true] [true, true] (field 33) (field 21) = [false] := by
  decide

example : routingVerticalInteriorFlag ruler [true, true] [true] (field 75) (field 12) =
      [true] ∧
    routingVerticalInteriorFlag ruler [true, true] [true] (field 75) (field 9) = [false] ∧
    routingVerticalInteriorFlag ruler [true, true] [true] (field 75) (field 18) = [false] ∧
    routingBetweenFlag (field 21) (field 12) (field 6) = [true] ∧
    routingStrictBetweenFlag (field 21) (field 21) (field 6) = [false] ∧
    routingStrictBetweenFlag (field 12) (field 12) (field 12) = [false] := by decide

example : (fun z => routingColumnBits (pairFst z) (pairSnd z) (pairFst z)) ∈ FP :=
  routingColumnBitsFn_mem_FP pairFst_mem_FP pairSnd_mem_FP pairFst_mem_FP

example : (fun z => routingOnWireFlag (pairFst z) (pairSnd z) (pairFst z)
    (pairSnd z) (pairFst z)) ∈ FP :=
  routingOnWireFlagFn_mem_FP pairFst_mem_FP pairSnd_mem_FP pairFst_mem_FP
    pairSnd_mem_FP pairFst_mem_FP

example : (fun z => routingCenterBits (pairSnd z)) ∈ FP :=
  routingCenterBitsFn_mem_FP pairSnd_mem_FP

example : (fun z => routingVerticalOwnerBits (pairFst z) (pairSnd z)) ∈ FP :=
  routingVerticalOwnerBitsFn_mem_FP pairFst_mem_FP pairSnd_mem_FP

example : (fun z => routingTargetRowBits (pairSnd z)) ∈ FP :=
  routingTargetRowBitsFn_mem_FP pairSnd_mem_FP

example : (fun z => routingHorizontalInteriorFlag (pairFst z) (pairSnd z) (pairFst z)
    (pairSnd z) (pairFst z)) ∈ FP :=
  routingHorizontalInteriorFlagFn_mem_FP pairFst_mem_FP pairSnd_mem_FP pairFst_mem_FP
    pairSnd_mem_FP pairFst_mem_FP

example : (fun z => routingVerticalInteriorFlag (pairFst z) (pairSnd z) (pairFst z)
    (pairSnd z) (pairFst z)) ∈ FP :=
  routingVerticalInteriorFlagFn_mem_FP pairFst_mem_FP pairSnd_mem_FP pairFst_mem_FP
    pairSnd_mem_FP pairFst_mem_FP

example : routingRectangleFlag ruler (field 191) (field 47) = [true] ∧
    routingRectangleFlag ruler (field 192) (field 47) = [false] ∧
    routingRectangleFlag ruler (field 191) (field 48) = [false] ∧
    routingRectangleFlag ruler (field 219) (field 12) = [false] ∧
    routingRectangleFlag [] [] [] = [true] ∧
    routingRectangleFlag [] [false, true] [true, false, true] = [true] ∧
    routingRectangleFlag [] [true, true] [] = [false] ∧
    routingRectangleFlag [] [] [false, true, true] = [false] ∧
    routingRectangleFlag [] (routingCenterBits [false, true]) [] = [false] ∧
    routingRectangleFlag [] [] (routingCenterBits [true, false, true]) = [false] := by decide

example : (fun z => routingRectangleFlag (pairFst z) (pairSnd z) (pairFst z)) ∈ FP :=
  routingRectangleFlagFn_mem_FP pairFst_mem_FP pairSnd_mem_FP pairFst_mem_FP

example : routingQueryBits ruler (fun _ => [true, true, true, true, true]) [] =
      [true, true, true] ∧
    routingQueryBits ruler (fun _ => []) (field 9) = field 9 ∧
    routingQueryBits [] (fun _ => [true]) [false, false] = [] ∧
    routingQueryBits [] (fun _ => []) [true] = [true] ∧
    routingOriginalPointer [] (fun _ => [true]) 0 = 0 ∧
    routingOriginalPointer [] (fun _ => []) 1 = 1 := by decide

example : routingQueryBits ruler
    (fun bits => if bits = [true, false, false] then [false, true, true, true] else [])
    [true, false, false, false, false] = [false, true, true] := by decide

private def originalS (i : ℕ) : ℕ :=
  if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 0 else i

private def originalP (i : ℕ) : ℕ :=
  if i = 0 then 2 else if i = 3 then 1 else if i = 4 then 0 else i

private def Squery (bits : List Bool) : List Bool :=
  Nat.toBitsLE 3 (originalS (Nat.fromBitsLE bits))

private def Pquery (bits : List Bool) : List Bool :=
  Nat.toBitsLE 3 (originalP (Nat.fromBitsLE bits))

example : routingActiveEdgeFlag ruler Pquery Squery (field 1) = [true] ∧
    routingActiveEdgeFlag ruler (fun bits => bits) Squery (field 1) = [false] ∧
    routingActiveEdgeFlag ruler Pquery Squery (field 3) = [false] ∧
    routingActiveEdgeFlag ruler Pquery Squery (field 9) = [false] := by decide

example : (fun z => routingQueryBits (pairFst z)
    (fun vertex => pairSnd z ++ vertex) (pairSnd z)) ∈ FP :=
  routingQueryBitsUniformFn_mem_FP (fun seed vertex => seed ++ vertex)
    pairFst_mem_FP pairSnd_mem_FP pairSnd_mem_FP
    (appendFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)

example : (fun z => routingActiveEdgeFlag (pairFst z)
    (fun vertex => pairSnd z ++ vertex) (fun vertex => vertex ++ pairSnd z)
    (pairSnd z)) ∈ FP :=
  routingActiveEdgeFlagUniformFn_mem_FP (fun seed vertex => seed ++ vertex)
    (fun seed vertex => vertex ++ seed) pairFst_mem_FP pairSnd_mem_FP pairSnd_mem_FP
    (appendFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
    (appendFn_mem_FP pairSnd_mem_FP pairFst_mem_FP)

example : Nat.fromBitsLE (routingHorizontalOwnerBits ruler Pquery (field 6)) = 1 ∧
    Nat.fromBitsLE (routingHorizontalOwnerBits ruler Pquery (field 3)) = 2 ∧
    Nat.fromBitsLE (routingHorizontalOwnerBits ruler Pquery (field 21)) = 1 ∧
    Nat.fromBitsLE (routingHorizontalOwnerBits ruler Pquery (field 57)) = 9 := by decide

example : routingCrossingFlag ruler Pquery Squery (field 12) (field 3) = [true] ∧
    routingCrossingFlag ruler Pquery Squery (field 12) (field 6) = [true] ∧
    routingCrossingFlag ruler Pquery Squery (field 12) [] = [false] ∧
    routingCrossingFlag ruler Pquery Squery (field 12) (field 27) = [false] ∧
    routingCrossingFlag ruler Pquery Squery (field 12) (field 9) = [false] ∧
    routingCrossingFlag ruler Pquery Squery (field 219) (field 6) = [false] := by decide

example : routingCrossingFlag ruler
    (fun bits => if Nat.fromBitsLE bits = 4 then bits else Pquery bits)
    Squery (field 12) (field 3) = [false] := by decide

example : (fun z => routingHorizontalOwnerBits (pairFst z)
    (fun vertex => pairSnd z ++ vertex) (pairSnd z)) ∈ FP :=
  routingHorizontalOwnerBitsUniformFn_mem_FP (fun seed vertex => seed ++ vertex)
    pairFst_mem_FP pairSnd_mem_FP pairSnd_mem_FP
    (appendFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)

example : (fun z => routingCrossingFlag (pairFst z)
    (fun vertex => pairSnd z ++ vertex) (fun vertex => vertex ++ pairSnd z)
    (pairFst z) (pairSnd z)) ∈ FP :=
  routingCrossingFlagUniformFn_mem_FP (fun seed vertex => seed ++ vertex)
    (fun seed vertex => vertex ++ seed) pairFst_mem_FP pairSnd_mem_FP pairFst_mem_FP
    pairSnd_mem_FP (appendFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
    (appendFn_mem_FP pairSnd_mem_FP pairFst_mem_FP)

example : routingWireStepBits ruler [true] [true, true] (field 12) (field 6) false =
      encodeRoutingPoint 3 (13, 6) ∧
    routingWireStepBits ruler [true] [true, true] (field 12) (field 6) true =
      encodeRoutingPoint 3 (11, 6) ∧
    routingWireStepBits ruler [true] [true, true] (field 33) (field 12) false =
      encodeRoutingPoint 3 (33, 13) ∧
    routingWireStepBits ruler [true] [true, true] (field 33) (field 12) true =
      encodeRoutingPoint 3 (33, 11) := by decide

example : routingWireStepBits ruler [true] [true, true] (field 12) (field 21) false =
      encodeRoutingPoint 3 (11, 21) ∧
    routingWireStepBits ruler [true] [true, true] (field 12) (field 21) true =
      encodeRoutingPoint 3 (13, 21) ∧
    routingWireStepBits ruler [true] [true, true] [] (field 20) false =
      encodeRoutingPoint 3 (0, 19) ∧
    routingWireStepBits ruler [true] [true, true] [] (field 20) true =
      encodeRoutingPoint 3 (0, 21) := by decide

example : routingWireStepBits ruler [true, true] [true] (field 75) (field 12) false =
      encodeRoutingPoint 3 (75, 11) ∧
    routingWireStepBits ruler [true, true] [true] (field 75) (field 12) true =
      encodeRoutingPoint 3 (75, 13) ∧
    routingWireStepBits ruler [true] [true, true] [] (field 6) true =
      encodeRoutingPoint 3 (0, 6) ∧
    routingWireStepBits ruler [true] [true, true] [] (field 18) false =
      encodeRoutingPoint 3 (0, 18) ∧
    routingWireStepBits ruler [true] [true, true] (field 12) (field 12) false =
      encodeRoutingPoint 3 (12, 12) := by decide

example : routingSaturatingPredBits [] = [] ∧
    routingSaturatingPredBits [false, false, false] = [false, false, false] ∧
    routingSaturatingPredBits [true, false, false] = [false, false, false] := by decide

example : routingWireStepBits [] [] [true, true] [true, true, true] [] false =
      encodeRoutingPoint 0 (8, 0) ∧
    routingWireStepBits [] [] [true, true] [true, true, true] [] false =
      List.replicate 6 false ∧
    decodeRoutingPoint 0 (routingWireStepBits [] [] [true, true] [true, true, true] [] false) =
      some (0, 0) := by decide

example {ruler i j x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hi : i ∈ FP) (hj : j ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP)
    (incoming : Bool) :
    (fun z => routingWireStepBits (ruler z) (i z) (j z) (x z) (y z) incoming) ∈ FP :=
  routingWireStepBitsFn_mem_FP incoming hr hi hj hx hy

end GameTheory.Complexity.Tests.GridRoutingGeometry
