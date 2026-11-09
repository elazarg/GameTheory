module

public import GameTheoryComplexity.Backend.GeneralBimatrixSignedInput
public import GameTheory.Finite.BimatrixBasisBounds

@[expose] public section

/-! Certified ambient system columns for the positively shifted bimatrix game.
Row and label indices are length rulers. Payoff columns use the two off-diagonal
blocks; slack columns use the identity. No rational arithmetic is executed.
-/
namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM

/-- One integer column entry, with arguments row, label, kind flag and instance. -/
def generalBimatrixColumnWord (v : Fin 4 → List Bool) : List Bool :=
  let rows := generalRowRuler (v 3)
  if (v 2).headD false then
    if rows.length ≤ (v 0).length then
      if rows.length ≤ (v 1).length then [false]
      else generalShiftedPayoffWord true ![v 1, (v 0).drop rows.length, v 3]
    else if rows.length ≤ (v 1).length then
      generalShiftedPayoffWord false ![v 0, (v 1).drop rows.length, v 3]
    else [false]
  else if (v 0).length = (v 1).length then [false, true] else [false]

/-- The word represents the two off-diagonal payoff blocks or an identity column. -/
theorem generalBimatrixColumnWord_value (v : Fin 4 → List Bool) :
    binarySignedValue (generalBimatrixColumnWord v) =
      if (v 2).headD false then
        if generalRowCount (v 3) ≤ (v 0).length then
          if generalRowCount (v 3) ≤ (v 1).length then 0 else
            decodeGeneralPayoff true (v 3) (v 1).length ((v 0).length - generalRowCount (v 3)) +
              ((2 : ℤ) ^ generalCoefficientBits (v 3) + 1)
        else if generalRowCount (v 3) ≤ (v 1).length then
          decodeGeneralPayoff false (v 3) (v 0).length ((v 1).length - generalRowCount (v 3)) +
            ((2 : ℤ) ^ generalCoefficientBits (v 3) + 1)
        else 0
      else if (v 0).length = (v 1).length then 1 else 0 := by
  unfold generalBimatrixColumnWord
  simp only [generalRowCount]
  split
  · split <;> split <;>
      simp_all only [↓reduceIte, generalShiftedPayoffWord_value, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, List.length_drop] <;> rfl
  · split <;> rfl

/-- Canonical finite indices recover precisely the existing integer system columns. -/
theorem generalBimatrixColumnWord_integer (input : List Bool)
    (i label : Fin (generalRowCount input + generalColCount input)) (kind : Bool) :
    binarySignedValue (generalBimatrixColumnWord
      ![List.replicate i.val true, List.replicate label.val true, [kind], input]) =
      GameTheory.Finite.bimatrixIntegerColumns
        (fun r c => decodeGeneralPayoff false input r.val c.val +
          ((2 : ℤ) ^ generalCoefficientBits input + 1))
        (fun r c => decodeGeneralPayoff true input r.val c.val +
          ((2 : ℤ) ^ generalCoefficientBits input + 1)) i (toLex (label, kind)) := by
  have numShift (z : ℤ) (h : ℕ) :
      ((z : ℚ) + (2 ^ h + 1)).num = z + (2 ^ h + 1) := by
    rw [show (2 ^ h + 1 : ℚ) = ((2 ^ h + 1 : ℤ) : ℚ) by norm_cast,
      ← Int.cast_add, Rat.num_intCast]
  rw [generalBimatrixColumnWord_value]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, List.length_replicate]
  cases kind
  · simp [GameTheory.Finite.bimatrixIntegerColumns, GameTheory.Finite.bimatrixBasisColumns,
      Pi.single_apply, Fin.ext_iff]
    split <;> simp
  · have hi : i = finSumFinEquiv (finSumFinEquiv.symm i) := (Equiv.apply_symm_apply _ _).symm
    have hl : label = finSumFinEquiv (finSumFinEquiv.symm label) := (Equiv.apply_symm_apply _ _).symm
    cases hr : finSumFinEquiv.symm i <;> cases hc : finSumFinEquiv.symm label <;>
      rw [hr] at hi <;> rw [hc] at hl <;>
      rw [hi, hl] <;>
      simp [GameTheory.Finite.bimatrixIntegerColumns, GameTheory.Finite.bimatrixBasisColumns,
        GameTheory.Finite.bimatrixEnteringColumn, GameTheory.Finite.bimatrixComplementaryMatrix,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Nat.not_le.mpr (Fin.isLt _), numShift]

@[fun_prop] theorem generalBimatrixColumnWord_polyTime :
    ComputableInPolyTime generalBimatrixColumnWord (encPi encBits) encBits := by
  have hinput : ComputableInPolyTime (fun v : Fin 4 → List Bool => ![v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact .pi_apply encBits (3 : Fin 4)
  have hrows0 := generalRowRuler_polyTime.comp hinput
  have hrows : ComputableInPolyTime (fun v : Fin 4 → List Bool => generalRowRuler (v 3))
      (encPi encBits) encBits := by
    apply ComputableInPolyTime.of_tidy
    apply hrows0.tidy.of_enc_eq
    intro v
    rfl
  have hrow : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hcolumn : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hkind : ComputableInPolyTime (fun v : Fin 4 → List Bool => (v 2).headD false)
      (encPi encBits) encBool := (ComputableInPolyTime.headD false).comp (.pi_apply encBits 2)
  have hrowsLength := ComputableInPolyTime.length_bits_comp hrows
  have hrowLength := ComputableInPolyTime.length_bits_comp hrow
  have hcolumnLength := ComputableInPolyTime.length_bits_comp hcolumn
  have hrowOutside := ComputableTidilyInPolyTime.unary_le' hrowsLength.tidy hrowLength.tidy
  have hcolumnOutside := ComputableTidilyInPolyTime.unary_le' hrowsLength.tidy hcolumnLength.tidy
  have hequal := ComputableTidilyInPolyTime.decide_eq' hrowLength.tidy hcolumnLength.tidy
  have hrowDrop := hrow.bitsDropWithInput hrowsLength
  have hcolumnDrop := hcolumn.bitsDropWithInput hrowsLength
  have hbargs : ComputableInPolyTime
      (fun v : Fin 4 → List Bool => ![v 1, (v 0).drop (generalRowRuler (v 3)).length, v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hcolumn
    · exact hrowDrop
    · exact .pi_apply encBits 3
  have haargs : ComputableInPolyTime
      (fun v : Fin 4 → List Bool => ![v 0, (v 1).drop (generalRowRuler (v 3)).length, v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hrow
    · exact hcolumnDrop
    · exact .pi_apply encBits 3
  have hb := (generalShiftedPayoffWord_polyTime true).comp hbargs
  have ha := (generalShiftedPayoffWord_polyTime false).comp haargs
  have hpayoff := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.ite_decide hrowOutside
      (.ite_decide hcolumnOutside (.const [false]) hb.tidy)
      (.ite_decide hcolumnOutside ha.tidy (.const [false])))
  have hidentity : ComputableInPolyTime
      (fun v : Fin 4 → List Bool =>
        if (v 0).length = (v 1).length then [false, true] else [false])
      (encPi encBits) encBits := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.ite_decide hequal (.const [false, true]) (.const [false]))
  have h := hkind.ite hpayoff hidentity
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq (g := generalBimatrixColumnWord)
  intro v
  rfl

end GameTheory.Complexity.Backend
