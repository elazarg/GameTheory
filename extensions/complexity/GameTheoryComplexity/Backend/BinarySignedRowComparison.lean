module

public import GameTheoryComplexity.Backend.BinarySignedCrossComparison
public import GameTheoryComplexity.Backend.BinaryIndexedLexicographic
public import GameTheoryComplexity.Backend.WordOperations
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import GameTheory.Math.IntegerRatioSelection

@[expose] public section

/-! Exact lexicographic comparison of packed signed binary rows.
Field widths and coefficient counts are supplied as length rulers. Truncated fields,
empty fields, and magnitude padding retain the total signed-word semantics.
-/

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

/-- Extract one fixed-width signed field using an index ruler and width ruler. -/
def binarySignedRowField (v : Fin 3 → List Bool) : List Bool :=
  ((v 2).drop ((v 0).length * (v 1).length)).take (v 1).length

theorem binarySignedRowField_length (v : Fin 3 → List Bool) :
    (binarySignedRowField v).length ≤ (v 1).length := List.length_take_le _ _

@[fun_prop] theorem binarySignedRowField_polyTime :
    ComputableInPolyTime binarySignedRowField (encPi encBits) encBits := by
  have hindex : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hwidth : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hrow : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 2)
      (encPi encBits) encBits := .pi_apply encBits 2
  have hindexLength := ComputableInPolyTime.length_bits_comp hindex
  have hwidthLength := ComputableInPolyTime.length_bits_comp hwidth
  have hoffset := ComputableInPolyTime.unary_mul' hindexLength hwidthLength
  exact (hrow.bitsDropWithInput hoffset).bitsTakeWithInput hwidthLength

/-- Total signed values in a packed row, indexed by field positions. -/
def binarySignedRowValue (width row : List Bool) (i : ℕ) : ℤ :=
  binarySignedValue ((row.drop (i * width.length)).take width.length)

private def rowColumnLT (v : Fin 6 → List Bool) : List Bool :=
  binarySignedCrossLT ![binarySignedRowField ![v 0, v 1, v 2],
    binarySignedRowField ![v 0, v 1, v 3], v 4, v 5]

private def rowColumnGT (v : Fin 6 → List Bool) : List Bool :=
  binarySignedCrossLT ![binarySignedRowField ![v 0, v 1, v 3],
    binarySignedRowField ![v 0, v 1, v 2], v 5, v 4]

private def rowColumnEQ (v : Fin 6 → List Bool) : List Bool :=
  notFlag (orFlag (rowColumnLT v) (rowColumnGT v))

private theorem rowColumnLT_value (v : Fin 6 → List Bool) :
    rowColumnLT v = [decide (binarySignedRowValue (v 1) (v 2) (v 0).length * binarySignedValue (v 5) <
      binarySignedRowValue (v 1) (v 3) (v 0).length * binarySignedValue (v 4))] := by
  exact binarySignedCrossLT_value _ _ _ _

private theorem rowColumnGT_value (v : Fin 6 → List Bool) :
    rowColumnGT v = [decide (binarySignedRowValue (v 1) (v 3) (v 0).length * binarySignedValue (v 4) <
      binarySignedRowValue (v 1) (v 2) (v 0).length * binarySignedValue (v 5))] := by
  exact binarySignedCrossLT_value _ _ _ _

private theorem rowColumnEQ_value (v : Fin 6 → List Bool) :
    rowColumnEQ v = [decide (binarySignedRowValue (v 1) (v 2) (v 0).length * binarySignedValue (v 5) =
      binarySignedRowValue (v 1) (v 3) (v 0).length * binarySignedValue (v 4))] := by
  rw [rowColumnEQ, rowColumnLT_value, rowColumnGT_value]
  generalize binarySignedRowValue (v 1) (v 2) (v 0).length * binarySignedValue (v 5) = a
  generalize binarySignedRowValue (v 1) (v 3) (v 0).length * binarySignedValue (v 4) = b
  rcases lt_trichotomy a b with hab | rfl | hba
  · simp [hab, not_lt_of_ge hab.le, hab.ne, orFlag, notFlag]
  · simp [orFlag, notFlag]
  · simp [hba, not_lt_of_ge hba.le, hba.ne', orFlag, notFlag]

private theorem rowColumnLT_polyTime :
    ComputableInPolyTime rowColumnLT (encPi encBits) encBits := by
  let hfield : ComputableInPolyTime (fun v : Fin 6 → List Bool =>
      binarySignedRowField ![v 0, v 1, v 2]) (encPi encBits) encBits := by
    have hargs : ComputableInPolyTime (fun v : Fin 6 → List Bool =>
        ![v 0, v 1, v 2]) (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact .pi_apply encBits 0
      · exact .pi_apply encBits 1
      · exact .pi_apply encBits 2
    exact binarySignedRowField_polyTime.comp hargs
  let hfield' : ComputableInPolyTime (fun v : Fin 6 → List Bool =>
      binarySignedRowField ![v 0, v 1, v 3]) (encPi encBits) encBits := by
    have hargs : ComputableInPolyTime (fun v : Fin 6 → List Bool =>
        ![v 0, v 1, v 3]) (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact .pi_apply encBits 0
      · exact .pi_apply encBits 1
      · exact .pi_apply encBits 3
    exact binarySignedRowField_polyTime.comp hargs
  have hargs : ComputableInPolyTime (fun v : Fin 6 → List Bool =>
      ![binarySignedRowField ![v 0, v 1, v 2],
        binarySignedRowField ![v 0, v 1, v 3], v 4, v 5])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hfield
    · exact hfield'
    · exact .pi_apply encBits 4
    · exact .pi_apply encBits 5
  exact binarySignedCrossLT_polyTime.comp hargs

private theorem rowColumnGT_polyTime :
    ComputableInPolyTime rowColumnGT (encPi encBits) encBits := by
  let hfield : ComputableInPolyTime (fun v : Fin 6 → List Bool =>
      binarySignedRowField ![v 0, v 1, v 3]) (encPi encBits) encBits := by
    have hargs : ComputableInPolyTime (fun v : Fin 6 → List Bool =>
        ![v 0, v 1, v 3]) (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact .pi_apply encBits 0
      · exact .pi_apply encBits 1
      · exact .pi_apply encBits 3
    exact binarySignedRowField_polyTime.comp hargs
  let hfield' : ComputableInPolyTime (fun v : Fin 6 → List Bool =>
      binarySignedRowField ![v 0, v 1, v 2]) (encPi encBits) encBits := by
    have hargs : ComputableInPolyTime (fun v : Fin 6 → List Bool =>
        ![v 0, v 1, v 2]) (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact .pi_apply encBits 0
      · exact .pi_apply encBits 1
      · exact .pi_apply encBits 2
    exact binarySignedRowField_polyTime.comp hargs
  have hargs : ComputableInPolyTime (fun v : Fin 6 → List Bool =>
      ![binarySignedRowField ![v 0, v 1, v 3],
        binarySignedRowField ![v 0, v 1, v 2], v 5, v 4])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hfield
    · exact hfield'
    · exact .pi_apply encBits 5
    · exact .pi_apply encBits 4
  exact binarySignedCrossLT_polyTime.comp hargs

private theorem rowColumnEQ_polyTime :
    ComputableInPolyTime rowColumnEQ (encPi encBits) encBits := by
  exact notFlag_polyTime.comp (orFlag_polyTime.comp
    (rowColumnLT_polyTime.prod rowColumnGT_polyTime))

/-- Compare two packed signed rows lexicographically after denominator cross-products.
Arguments are coefficient-count ruler, field-width ruler, the two rows, and their denominators. -/
def binarySignedRowLT (v : Fin 6 → List Bool) : List Bool :=
  binaryIndexedLexLT
    (fun w => binarySignedCrossLT ![
      binarySignedRowField ![w 0, w 1, w 2],
      binarySignedRowField ![w 0, w 1, w 3], w 4, w 5])
    (fun w => notFlag (orFlag
      (binarySignedCrossLT ![
        binarySignedRowField ![w 0, w 1, w 2],
        binarySignedRowField ![w 0, w 1, w 3], w 4, w 5])
      (binarySignedCrossLT ![
        binarySignedRowField ![w 0, w 1, w 3],
        binarySignedRowField ![w 0, w 1, w 2], w 5, w 4])))
    (v 0) (Fin.tail v)

@[simp] theorem binarySignedRowLT_length (v : Fin 6 → List Bool) :
    (binarySignedRowLT v).length = 1 := binaryIndexedLexLT_length _ _ _ _

@[fun_prop] theorem binarySignedRowLT_polyTime :
    ComputableInPolyTime binarySignedRowLT (encPi encBits) encBits :=
  by
    change ComputableInPolyTime
      (fun v : Fin 6 → List Bool =>
        binaryIndexedLexLT rowColumnLT rowColumnEQ (v 0) (Fin.tail v))
      (encPi encBits) encBits
    have hclock : ComputableInPolyTime (fun v : Fin 6 → List Bool => v 0)
        (encPi encBits) encBits := .pi_apply encBits 0
    have hparams : ComputableInPolyTime (fun v : Fin 6 → List Bool => Fin.tail v)
        (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      exact .pi_apply encBits (Fin.succ i)
    exact binaryIndexedLexLT_polyTime rowColumnLT_polyTime rowColumnEQ_polyTime
      hclock hparams

/-- The first unequal cross-product determines the output, independently of ruler bits. -/
theorem binarySignedRowLT_value (v : Fin 6 → List Bool) :
    binarySignedRowLT v = [decide (∃ i < (v 0).length,
      binarySignedRowValue (v 1) (v 2) i * binarySignedValue (v 5) <
        binarySignedRowValue (v 1) (v 3) i * binarySignedValue (v 4) ∧
      ∀ j < i, binarySignedRowValue (v 1) (v 2) j * binarySignedValue (v 5) =
        binarySignedRowValue (v 1) (v 3) j * binarySignedValue (v 4))] := by
  apply binaryIndexedLexLT_value
  · intro r
    exact rowColumnEQ_value (Fin.cons r (Fin.tail v))
  · intro r
    exact rowColumnLT_value (Fin.cons r (Fin.tail v))

/-- Packed comparison agrees with the canonical integer ratio comparator. -/
theorem binarySignedRowLT_compare (v : Fin 6 → List Bool) :
    binarySignedRowLT v = [GameTheory.Math.IntegerRatioSelection.compare
      ![(fun i : Fin (v 0).length => binarySignedRowValue (v 1) (v 2) i.val),
        (fun i : Fin (v 0).length => binarySignedRowValue (v 1) (v 3) i.val)]
      ![binarySignedValue (v 4), binarySignedValue (v 5)] 0 1] := by
  rw [binarySignedRowLT_value]
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, GameTheory.Math.IntegerRatioSelection.compare,
    GameTheory.Math.FiniteLexicographicCompare.lexLT_eq_true]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨i, hi, hl, he⟩
    exact ⟨⟨i, hi⟩, fun j hj => he j.val hj, hl⟩
  · rintro ⟨i, he, hl⟩
    exact ⟨i.val, i.isLt, hl, fun j hj => he ⟨j, hj.trans i.isLt⟩ hj⟩

/-- Positive denominators identify the output with strict rational lexicographic order. -/
theorem binarySignedRowLT_ratio_lt_iff (v : Fin 6 → List Bool)
    (hdx : 0 < binarySignedValue (v 4)) (hdy : 0 < binarySignedValue (v 5)) :
    binarySignedRowLT v = [true] ↔
      toLex (fun i : Fin (v 0).length =>
        (binarySignedRowValue (v 1) (v 2) i.val : ℚ) / (binarySignedValue (v 4) : ℚ)) <
      toLex (fun i : Fin (v 0).length =>
        (binarySignedRowValue (v 1) (v 3) i.val : ℚ) / (binarySignedValue (v 5) : ℚ)) := by
  rw [binarySignedRowLT_compare]
  simp only [List.cons.injEq, and_true]
  exact GameTheory.Math.IntegerRatioSelection.compare_eq_true _ _ 0 1 hdx hdy

end GameTheory.Complexity.Backend
