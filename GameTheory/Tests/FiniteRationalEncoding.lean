import GameTheory.Math.FiniteRationalEncoding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Common-denominator encodings handle empty vectors, reduced fractions, and zeros. -/

namespace GameTheory.Tests.FiniteRationalEncoding

open GameTheory.Math.FiniteRationalEncoding

private def fractions : Fin 3 → ℚ := ![1 / 2, 2 / 3, 0]

example : denominator fractions = 6 := by decide +kernel

example : numerator fractions = (![3, 4, 0] : Fin 3 → ℕ) := by
  funext i
  fin_cases i <;> decide +kernel

example (i : Fin 3) : (numerator fractions i : ℚ) / (denominator fractions : ℚ) =
    fractions i := by
  apply decode
  intro j
  fin_cases j <;> decide +kernel

example : denominator (fun i : Fin 0 => Fin.elim0 i : Fin 0 → ℚ) = 1 := by
  simp [denominator]

example : denominator fractions ≤ 3 ^ Fintype.card (Fin 3) := by
  apply denominator_le
  intro i
  fin_cases i <;> decide +kernel

example (i : Fin 3) : numerator fractions i ≤ 2 * 3 ^ Fintype.card (Fin 3) := by
  apply numerator_le
  · intro j
    fin_cases j <;> decide +kernel
  · intro j
    fin_cases j <;> decide +kernel

-- Negative inputs have a natural numerator of zero; exact decoding requires nonnegativity.
example : numerator (fun _ : Fin 1 => (-1 / 2 : ℚ)) 0 = 0 := by decide +kernel

example : (numerator (fun _ : Fin 1 => (-1 / 2 : ℚ)) 0 : ℚ) /
    (denominator (fun _ : Fin 1 => (-1 / 2 : ℚ)) : ℚ) ≠ -1 / 2 := by decide +kernel

end GameTheory.Tests.FiniteRationalEncoding
