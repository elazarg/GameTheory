module

public import GameTheoryComplexity.Backend.GridRoutingArithmetic
public import GameTheoryComplexity.Backend.GridRoutingBitFields
public import GameTheoryComplexity.Backend.GridRoutingGeometryMachine
public import GameTheoryComplexity.Backend.GridRoutingGuards
public import GameTheoryComplexity.Backend.GridRoutingQueries
public import GameTheoryComplexity.Backend.GridRoutingCrossingMachine
public import GameTheoryComplexity.Backend.GridRoutingWireMachine

@[expose] public section

/-! Routing arithmetic controls distinguish numeric equality from word equality,
exercise retained carries and truncation, and test exact lane membership. -/

namespace GameTheory.Complexity.Tests.GridRoutingGeometry

open GameTheory.Complexity.Backend
open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString

example : routingEQFlag [] [false, false] = [true] ∧
    routingEQFlag [true] [true, false, false] = [true] ∧
    routingEQFlag [true] [false, true] = [false] ∧
    routingLTFlag [true, false, false] [true] = [false] ∧
    routingLTFlag [true] [false, true, false] = [true] := by decide

example : routingAddBits [true, true, true] [true] = [false, false, false, true] ∧
    routingTripleBits [true, true, true] = lowBits 5 21 ∧
    routingSixBits [true, true, true] = lowBits 6 42 ∧
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

example : lsbValue ([true, false] ++ [false, true]) = 9 ∧
    lsbValue ([true, false, true, true].drop 2) = 3 ∧
    lsbValue ([true, false, true, true].take 2) = 1 := by decide

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingPadBits (Prod.fst z) (Prod.snd z)) (encPair encBits encBits) encBits :=
  routingPadBits_polyTime (fst encBits encBits) (snd encBits encBits)

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingShiftBits (Prod.fst z) (Prod.snd z)) (encPair encBits encBits) encBits :=
  routingShiftBits_polyTime (fst encBits encBits) (snd encBits encBits)

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingAddBits (Prod.fst z) (Prod.snd z)) (encPair encBits encBits) encBits :=
  routingAddBits_polyTime (fst encBits encBits) (snd encBits encBits)

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingEQFlag (Prod.fst z) (Prod.snd z)) (encPair encBits encBits) encBits :=
  routingEQFlag_polyTime (fst encBits encBits) (snd encBits encBits)

private def ruler : List Bool := [false, false, false]

private def field (value : ℕ) : List Bool := lowBits 8 value

example : lsbValue (routingColumnBits ruler [true] (field 3)) = 33 ∧
    lsbValue (routingTargetRowBits [true, true]) = 21 ∧
    lsbValue (routingVerticalOwnerBits ruler (field 219)) = 9 ∧
    routingVerticalOwnerBits ruler (field 219) ≠ lowBits 3 9 := by decide

example : routingCenterBits [true, true, true] = lowBits 6 6 ∧
    routingCenterBits [true, true, true, true] = lowBits 7 15 ∧
    lsbValue (routingCenterBits []) = 0 := by decide

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

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingColumnBits (Prod.fst z) (Prod.snd z) (Prod.fst z)) (encPair encBits encBits) encBits :=
  routingColumnBits_polyTime (fst encBits encBits) (snd encBits encBits) (fst encBits encBits)

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingOnWireFlag (Prod.fst z) (Prod.snd z) (Prod.fst z)
    (Prod.snd z) (Prod.fst z)) (encPair encBits encBits) encBits :=
  routingOnWireFlag_polyTime (fst encBits encBits) (snd encBits encBits) (fst encBits encBits)
    (snd encBits encBits) (fst encBits encBits)

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingCenterBits (Prod.snd z)) (encPair encBits encBits) encBits :=
  routingCenterBits_polyTime (snd encBits encBits)

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingVerticalOwnerBits (Prod.fst z) (Prod.snd z)) (encPair encBits encBits) encBits :=
  routingVerticalOwnerBits_polyTime (fst encBits encBits) (snd encBits encBits)

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingTargetRowBits (Prod.snd z)) (encPair encBits encBits) encBits :=
  routingTargetRowBits_polyTime (snd encBits encBits)

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingHorizontalInteriorFlag (Prod.fst z) (Prod.snd z) (Prod.fst z)
    (Prod.snd z) (Prod.fst z)) (encPair encBits encBits) encBits :=
  routingHorizontalInteriorFlag_polyTime (fst encBits encBits) (snd encBits encBits) (fst encBits encBits)
    (snd encBits encBits) (fst encBits encBits)

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingVerticalInteriorFlag (Prod.fst z) (Prod.snd z) (Prod.fst z)
    (Prod.snd z) (Prod.fst z)) (encPair encBits encBits) encBits :=
  routingVerticalInteriorFlag_polyTime (fst encBits encBits) (snd encBits encBits) (fst encBits encBits)
    (snd encBits encBits) (fst encBits encBits)

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

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingRectangleFlag (Prod.fst z) (Prod.snd z) (Prod.fst z)) (encPair encBits encBits) encBits :=
  routingRectangleFlag_polyTime (fst encBits encBits) (snd encBits encBits) (fst encBits encBits)

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
  lowBits 3 (originalS (lsbValue bits))

private def Pquery (bits : List Bool) : List Bool :=
  lowBits 3 (originalP (lsbValue bits))

example : routingActiveEdgeFlag ruler Pquery Squery (field 1) = [true] ∧
    routingActiveEdgeFlag ruler (fun bits => bits) Squery (field 1) = [false] ∧
    routingActiveEdgeFlag ruler Pquery Squery (field 3) = [false] ∧
    routingActiveEdgeFlag ruler Pquery Squery (field 9) = [false] := by decide

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingQueryBits (Prod.fst z)
    (fun vertex => Prod.snd z ++ vertex) (Prod.snd z)) (encPair encBits encBits) encBits :=
  routingQueryBitsUniform_polyTime (fun seed vertex => seed ++ vertex)
    (fst encBits encBits) (snd encBits encBits) (snd encBits encBits)
    (bitsAppend (fst encBits encBits) (snd encBits encBits))

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingActiveEdgeFlag (Prod.fst z)
    (fun vertex => Prod.snd z ++ vertex) (fun vertex => vertex ++ Prod.snd z)
    (Prod.snd z)) (encPair encBits encBits) encBits :=
  routingActiveEdgeFlagUniform_polyTime (fun seed vertex => seed ++ vertex)
    (fun seed vertex => vertex ++ seed) (fst encBits encBits) (snd encBits encBits) (snd encBits encBits)
    (bitsAppend (fst encBits encBits) (snd encBits encBits))
    (bitsAppend (snd encBits encBits) (fst encBits encBits))

example : lsbValue (routingHorizontalOwnerBits ruler Pquery (field 6)) = 1 ∧
    lsbValue (routingHorizontalOwnerBits ruler Pquery (field 3)) = 2 ∧
    lsbValue (routingHorizontalOwnerBits ruler Pquery (field 21)) = 1 ∧
    lsbValue (routingHorizontalOwnerBits ruler Pquery (field 57)) = 9 := by decide

example : routingCrossingFlag ruler Pquery Squery (field 12) (field 3) = [true] ∧
    routingCrossingFlag ruler Pquery Squery (field 12) (field 6) = [true] ∧
    routingCrossingFlag ruler Pquery Squery (field 12) [] = [false] ∧
    routingCrossingFlag ruler Pquery Squery (field 12) (field 27) = [false] ∧
    routingCrossingFlag ruler Pquery Squery (field 12) (field 9) = [false] ∧
    routingCrossingFlag ruler Pquery Squery (field 219) (field 6) = [false] := by decide

example : routingCrossingFlag ruler
    (fun bits => if lsbValue bits = 4 then bits else Pquery bits)
    Squery (field 12) (field 3) = [false] := by decide

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingHorizontalOwnerBits (Prod.fst z)
    (fun vertex => Prod.snd z ++ vertex) (Prod.snd z)) (encPair encBits encBits) encBits :=
  routingHorizontalOwnerBitsUniform_polyTime (fun seed vertex => seed ++ vertex)
    (fst encBits encBits) (snd encBits encBits) (snd encBits encBits)
    (bitsAppend (fst encBits encBits) (snd encBits encBits))

example : ComputableInPolyTime (fun z : List Bool × List Bool => routingCrossingFlag (Prod.fst z)
    (fun vertex => Prod.snd z ++ vertex) (fun vertex => vertex ++ Prod.snd z)
    (Prod.fst z) (Prod.snd z)) (encPair encBits encBits) encBits :=
  routingCrossingFlagUniform_polyTime (fun seed vertex => seed ++ vertex)
    (fun seed vertex => vertex ++ seed) (fst encBits encBits) (snd encBits encBits) (fst encBits encBits)
    (snd encBits encBits) (bitsAppend (fst encBits encBits) (snd encBits encBits))
    (bitsAppend (snd encBits encBits) (fst encBits encBits))

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
    (hr : ComputableInPolyTime ruler encBits encBits) (hi : ComputableInPolyTime i encBits encBits) (hj : ComputableInPolyTime j encBits encBits) (hx : ComputableInPolyTime x encBits encBits) (hy : ComputableInPolyTime y encBits encBits)
    (incoming : Bool) :
    ComputableInPolyTime (fun z => routingWireStepBits (ruler z) (i z) (j z) (x z) (y z) incoming) encBits encBits :=
  routingWireStepBits_polyTime incoming hr hi hj hx hy

end GameTheory.Complexity.Tests.GridRoutingGeometry
