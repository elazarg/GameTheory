import GameTheoryComplexity.Backend.GeneralBimatrixSignedInput
import GameTheory.Finite.BimatrixBasisBounds

/-! Certified ambient system columns for the positively shifted bimatrix game.
Row and label indices are length rulers. Payoff columns use the two off-diagonal
blocks; slack columns use the identity. No rational arithmetic is executed.
-/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- One integer column entry, with arguments row, label, kind flag and instance. -/
def generalBimatrixColumnWord (v : Fin 4 → List Bool) : List Bool :=
  let rows := generalRowRuler (v 3)
  caseBit₀ (v 2)
    (caseBit₀ (lenLeFlag (v 0) rows)
      (caseBit₀ (lenLeFlag (v 1) rows) [false]
        (generalShiftedPayoffWord true ![v 1, (v 0).drop rows.length, v 3]))
      (caseBit₀ (lenLeFlag (v 1) rows)
        (generalShiftedPayoffWord false ![v 0, (v 1).drop rows.length, v 3]) [false]))
    (caseBit₀ (lenEqFlag (v 0) (v 1)) [false, true] [false])

private theorem case_head (x a b : List Bool) :
    caseBit₀ x a b = if x.headD false then a else b := by
  cases x with
  | nil => rfl
  | cons c x => cases c <;> rfl

private theorem lenLe_value (a b : List Bool) : lenLeFlag a b = [decide (b.length ≤ a.length)] := by
  rcases lenLeFlag_flag a b with h | h
  · have hv := (lenLeFlag_eq_true_iff a b).mp h
    simp [h, hv]
  · have hv : ¬b.length ≤ a.length := by
      intro hn
      have ht := (lenLeFlag_eq_true_iff a b).mpr hn
      simp [h] at ht
    simp [h, hv]

private theorem lenEq_value (a b : List Bool) : lenEqFlag a b = [decide (a.length = b.length)] := by
  rcases lenEqFlag_flag a b with h | h
  · have hv := (lenEqFlag_eq_true_iff a b).mp h
    simp [h, hv]
  · have hv : a.length ≠ b.length := by
      intro hn
      have ht := (lenEqFlag_eq_true_iff a b).mpr hn
      simp [h] at ht
    simp [h, hv]

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
  rw [generalBimatrixColumnWord, case_head, lenLe_value, lenLe_value, lenEq_value]
  simp only [case_head, List.headD_cons, decide_eq_true_eq, generalRowCount]
  split
  · split <;> split <;>
      simp_all only [↓reduceIte, generalShiftedPayoffWord_value, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, List.length_drop] <;> rfl
  · split <;> rfl

theorem generalBimatrixColumnWord_cobham : Cobham generalBimatrixColumnWord := by
  have hm : Cobham fun v : Fin 4 → List Bool => generalRowRuler (v 3) :=
    (Cobham.comp generalRowRuler_cobham fun _ => Cobham.proj 3).of_eq fun _ => rfl
  have hx : Cobham fun v : Fin 4 → List Bool => (v 0).drop (generalRowRuler (v 3)).length :=
    Cobham.dropFn hm (.proj 0)
  have hy : Cobham fun v : Fin 4 → List Bool => (v 1).drop (generalRowRuler (v 3)).length :=
    Cobham.dropFn hm (.proj 1)
  have hb : Cobham fun v : Fin 4 → List Bool =>
      generalShiftedPayoffWord true ![v 1, (v 0).drop (generalRowRuler (v 3)).length, v 3] :=
    Cobham.comp₃ (generalShiftedPayoffWord_cobham true) (.proj 1) hx (.proj 3)
  have ha : Cobham fun v : Fin 4 → List Bool =>
      generalShiftedPayoffWord false ![v 0, (v 1).drop (generalRowRuler (v 3)).length, v 3] :=
    Cobham.comp₃ (generalShiftedPayoffWord_cobham false) (.proj 0) hy (.proj 3)
  exact (Cobham.iteFn (.proj 2)
    (Cobham.iteFn (lenLeFlag_mem (.proj 0) hm)
      (Cobham.iteFn (lenLeFlag_mem (.proj 1) hm) (Cobham.const [false]) hb)
      (Cobham.iteFn (lenLeFlag_mem (.proj 1) hm) ha (Cobham.const [false])))
    (Cobham.iteFn (lenEqFlag_mem (.proj 0) (.proj 1))
      (Cobham.const [false, true]) (Cobham.const [false]))).of_eq fun _ => rfl

theorem generalBimatrixColumnWord_mem_FPn : FPn generalBimatrixColumnWord :=
  cobham_iff_FPn.mp generalBimatrixColumnWord_cobham

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

end GameTheory.Complexity.Backend
