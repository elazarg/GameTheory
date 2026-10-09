import GameTheoryComplexity.Backend.BinarySignedRowSelection

namespace GameTheory.Complexity.Tests.BinarySignedRowSelection
open GameTheory.Complexity.Backend

private def width : List Bool := [false, false, false]
private def one : List Bool := [false, true, false]
private def two : List Bool := [false, false, true]
private def negativeOne : List Bool := [true, true, false]
private def zero : List Bool := [false, false, false]

-- A later strict improvement wins; the next equal ratio retains its earlier index.
example : binarySignedRowSelectedIndex (binarySignedRowSelect
    ![[true, false, true], [false], width, two ++ one ++ one, one ++ one ++ one]) = some 1 := by
  decide +kernel

-- A negative direction is ineligible even when its coefficient is smaller.
example : binarySignedRowSelectedIndex (binarySignedRowSelect
    ![[false, true], [true], width, zero ++ two, negativeOne ++ one]) = some 1 := by
  decide +kernel

-- Zero and negative directions produce the explicit absent state.
example : binarySignedRowSelect
    ![[false, false], [true], width, one ++ two, zero ++ negativeOne] = [false] := by
  decide +kernel

example : binarySignedRowSelect ![[], [true], width, one, one] = [false] := by decide +kernel

-- With no coefficients all eligible ratios tie, so the earliest eligible row wins.
example : binarySignedRowSelectedIndex (binarySignedRowSelect
    ![[true, true], [], width, [], one ++ one]) = some 0 := by
  decide +kernel

-- Missing coefficient fields decode as zero and can improve the current ratio.
example : binarySignedRowSelectedIndex (binarySignedRowSelect
    ![[false, false], [false], width, one, one ++ one]) = some 1 := by
  decide +kernel

example : _root_.Complexity.Cobham binarySignedRowSelect := binarySignedRowSelect_cobham
example : _root_.Complexity.Cobham.FPn binarySignedRowSelect := binarySignedRowSelect_mem_FPn

end GameTheory.Complexity.Tests.BinarySignedRowSelection
