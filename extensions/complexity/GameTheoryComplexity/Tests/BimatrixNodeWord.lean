import GameTheoryComplexity.Backend.BimatrixNodeWord

namespace GameTheory.Complexity.Tests.BimatrixNodeWord
open GameTheory.Complexity.Backend

-- The masked source is all false; its unmasked basis consists of the slack variables.
example : bimatrixNodeBasicWord ![[false, false], List.replicate 8 false] =
    [true, false, true, false] := by decide +kernel
example : bimatrixNodeEnteringWord ![[false, false], List.replicate 8 false] =
    [false, true, false, false] := by decide +kernel
example : bimatrixNodeSyntaxFlag ![[false, false], List.replicate 8 false] = [true] := by
  decide +kernel
example : bimatrixNodeSyntaxFlag ![[true], List.replicate 4 false] = [true] := by decide +kernel

-- A duplicated nonbasic label supplies a valid internal port.
example : bimatrixNodeSyntaxFlag ![[true, false],
    [false, true, true, false, false, true, true, false]] = [true] := by decide +kernel

-- Cardinality and port tests are independent: a basic entering variable is rejected.
example : bimatrixNodeSyntaxFlag ![[true, true],
    [false, false, false, false, true, true, false, false]] = [false] := by decide +kernel

-- A nonbasic entering variable away from zero must belong to a duplicated label.
example : bimatrixNodeSyntaxFlag ![[true, true],
    [false, false, false, false, false, true, false, true]] = [false] := by decide +kernel

-- Covering every label except zero is checked separately from basis cardinality.
example : bimatrixNodeSyntaxFlag ![[true, true],
    [true, false, false, true, false, false, false, false]] = [false] := by decide +kernel

-- Missing and multiply selected entering variables fail the one-hot check.
example : bimatrixNodeSyntaxFlag ![[true, true],
    [false, false, false, false, false, true, false, false]] = [false] := by decide +kernel
example : bimatrixNodeSyntaxFlag ![[true, true],
    [false, false, false, false, false, false, true, false]] = [false] := by decide +kernel

-- Truncated words remain total, but their exact-width validation fails.
example : bimatrixNodeBasicWord ![[true], []] = [true, false] := by decide +kernel
example : bimatrixNodeSyntaxFlag ![[true], []] = [false] := by decide +kernel
example : bimatrixNodeSyntaxFlag ![[], []] = [false] := by decide +kernel

example : _root_.Complexity.Cobham bimatrixNodeSyntaxFlag := bimatrixNodeSyntaxFlag_cobham
example : _root_.Complexity.Cobham.FPn bimatrixNodeSyntaxFlag := bimatrixNodeSyntaxFlag_mem_FPn

end GameTheory.Complexity.Tests.BimatrixNodeWord
