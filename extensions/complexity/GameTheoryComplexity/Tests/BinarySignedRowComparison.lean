import GameTheoryComplexity.Backend.BinarySignedRowComparison

/-! Kernel controls for packed symbolic ratio rows and length-based scan clocks. -/
namespace GameTheory.Complexity.Tests.BinarySignedRowComparison
open Backend

-- Width-three signed fields; equal leading coefficients force a late comparison.
example : binarySignedRowLT
    ![[true, true], [true, true, true],
      [false, true, false, false, false, false],
      [false, true, false, false, true, false], [false, true], [false, true]] = [true] := by
  decide +kernel

-- The first difference wins even when the final difference has the opposite sign.
example : binarySignedRowLT
    ![[true, true], [true, true, true],
      [false, false, false, false, false, true],
      [false, true, false, false, false, false], [false, true], [false, true]] = [true] := by
  decide +kernel
example : binarySignedRowLT
    ![[true, true], [true, true, true],
      [false, true, false, false, false, false],
      [false, false, false, false, false, true], [false, true], [false, true]] = [false] := by
  decide +kernel

-- Equal ratios have distinct scales and signed perturbation coefficients.
example : binarySignedRowLT
    ![[true, true], [true, true, true],
      [false, false, true, true, false, true],
      [false, true, false, true, true, false], [false, false, true], [false, true]] = [false] := by
  decide +kernel

-- The clock and width use lengths, including false bits.
example : binarySignedRowLT
    ![[false, false], [false, false, false],
      [false, true, false, false, false, false],
      [false, true, false, false, true, false], [false, true], [false, true]] = [true] := by
  decide +kernel

-- No coordinates and zero-width fields give equal rows.
example : binarySignedRowLT ![[], [true], [true], [], [false, true], [false, true]] = [false] := by
  decide +kernel
example : binarySignedRowLT ![[true], [], [true], [], [false, true], [false, true]] = [false] := by
  decide +kernel

-- Missing fields, sign-only fields and negative zero are decoded totally.
example : binarySignedRowLT
    ![[true, true], [true, true, true], [true, false, false], [], [false, true], [false, true]] =
      [false] := by decide +kernel
example : binarySignedRowLT
    ![[true], [true, true, true], [true], [false, true], [false, true], [false, true]] = [true] := by
  decide +kernel

end GameTheory.Complexity.Tests.BinarySignedRowComparison
