import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
import GameTheoryComplexity.Backend.BrouwerNashHeaders
import GameTheoryComplexity.Backend.BinarySignedIndicator
import GameTheoryComplexity.Backend.BinarySignedFiniteSum
import GameTheoryComplexity.Backend.BinaryUnaryEncoding
import GameTheoryComplexity.Backend.BrouwerNashProgram

namespace GameTheory.Complexity.Backend.BrouwerNashJitterQuery
open _root_.Complexity _root_.Complexity.Cobham
open scoped BigOperators

private def term (axis : Bool) (v : Fin 6 → List Bool) : List Bool :=
  let source := ![v 3, v 4, v 5]
  let dim := BrouwerNashHeaders.dimensionRuler source
  let capacity := [false, false] ++ binaryLengthWord dim
  let shift := binarySignedSub (false :: binaryLengthWord (v 0))
    [false, false, false, true, false, true]
  let output := BrouwerNashHeaders.globalRuler source ++
    smash (v 0) (BrouwerNashHeaders.sampleRuler source) ++ (if axis then [false] else [])
  let input := BrouwerNashHeaders.precisionRuler source ++ List.replicate 3 false
  let value := binarySignedAdd
    (binarySignedIndicator ![v 2, if axis then [false] else [], capacity])
    (binarySignedIndicator ![v 2, input, binarySignedMul capacity shift])
  caseBit₀ (lenEqFlag (v 1) output) value []

private theorem term_cobham (axis : Bool) : Cobham (term axis) := by
  have hd : Cobham fun v : Fin 6 → List Bool =>
      BrouwerNashHeaders.dimensionRuler ![v 3, v 4, v 5] :=
    Cobham.comp₃ BrouwerNashHeaders.dimensionRuler_cobham (.proj 3) (.proj 4) (.proj 5)
  have hp : Cobham fun v : Fin 6 → List Bool =>
      BrouwerNashHeaders.precisionRuler ![v 3, v 4, v 5] :=
    Cobham.comp₃ BrouwerNashHeaders.precisionRuler_cobham (.proj 3) (.proj 4) (.proj 5)
  have hg : Cobham fun v : Fin 6 → List Bool =>
      BrouwerNashHeaders.globalRuler ![v 3, v 4, v 5] :=
    Cobham.comp₃ BrouwerNashHeaders.globalRuler_cobham (.proj 3) (.proj 4) (.proj 5)
  have hs : Cobham fun v : Fin 6 → List Bool =>
      BrouwerNashHeaders.sampleRuler ![v 3, v 4, v 5] :=
    Cobham.comp₃ BrouwerNashHeaders.sampleRuler_cobham (.proj 3) (.proj 4) (.proj 5)
  have hc := appendFn (Cobham.const [false, false])
    (Cobham.comp binaryLengthWord_cobham fun _ : Fin 1 => hd)
  have hshift := Cobham.comp₂ binarySignedSub_cobham
    (appendFn (Cobham.const [false])
      (Cobham.comp binaryLengthWord_cobham fun _ : Fin 1 => Cobham.proj (0 : Fin 6)))
    (Cobham.const [false, false, false, true, false, true])
  exact Cobham.iteFn
    (lenEqFlag_mem (.proj 1) (appendFn
      (appendFn hg (Cobham.comp₂ Cobham.smash (.proj 0) hs))
      (Cobham.const (if axis then [false] else []))))
    (Cobham.comp₂ binarySignedAdd_cobham
      (Cobham.comp₃ binarySignedIndicator_cobham (.proj 2)
        (Cobham.const (if axis then [false] else [])) hc)
      (Cobham.comp₃ binarySignedIndicator_cobham (.proj 2)
        (appendFn hp (Cobham.const (List.replicate 3 false)))
        (Cobham.comp₂ binarySignedMul_cobham hc hshift))) Cobham.empty

/-- Jitter coefficients retain signed offsets for all forty-one sample positions. -/
def coefficientWord (v : Fin 5 → List Bool) : List Bool :=
  binarySignedAdd (binarySignedFiniteSum (term false) 41 v)
    (binarySignedFiniteSum (term true) 41 v)

set_option maxRecDepth 4096 in
theorem coefficientWord_cobham : Cobham coefficientWord :=
  Cobham.comp₂ binarySignedAdd_cobham
    (binarySignedFiniteSum_cobham (term_cobham false) 41)
    (binarySignedFiniteSum_cobham (term_cobham true) 41)

theorem coefficientWord_mem_FPn : FPn coefficientWord :=
  cobham_iff_FPn.mp coefficientWord_cobham

private theorem capacity_value (r : List Bool) :
    binarySignedValue ([false, false] ++ binaryLengthWord r) = 2 * (r.length : ℤ) := by
  simp only [List.cons_append, List.nil_append, binarySignedValue, List.headD_cons,
    Bool.false_eq_true, ite_false, List.tail_cons, Nat.fromBitsLE_cons, zero_add,
    binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]

private theorem shift_value (r : List Bool) :
    binarySignedValue (binarySignedSub (false :: binaryLengthWord r)
      [false, false, false, true, false, true]) = (r.length : ℤ) - 20 := by
  rw [binarySignedSub_value]
  have htwenty : binarySignedValue [false, false, false, true, false, true] = 20 := by decide
  rw [htwenty]
  simp only [binarySignedValue, List.headD_cons, Bool.false_eq_true, ite_false,
    List.tail_cons, binaryLengthWord_value]

private theorem term_value (axis : Bool) (out action source code₀ code₁ : List Bool)
    (t : Fin 41) :
    binarySignedValue (term axis
      ![List.replicate t.val false, out, action, source, code₀, code₁]) =
      if out.length = BrouwerNashLayout.sampleBase (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
          (if axis then 1 else 0) then
        (if action.length / 2 = (if axis then 1 else 0) ∧ action.length % 2 = 1
          then 2 * (BrouwerNashLayout.dimension (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0) +
        (if action.length / 2 = BrouwerNashLayout.precision (pairFst source).length + 3 ∧
            action.length % 2 = 1 then
          2 * (BrouwerNashLayout.dimension (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) *
            ((t.val : ℤ) - 20) else 0)
      else 0 := by
  change binarySignedValue (caseBit₀ (lenEqFlag out
    (BrouwerNashHeaders.globalRuler ![source, code₀, code₁] ++
      smash (List.replicate t.val false)
        (BrouwerNashHeaders.sampleRuler ![source, code₀, code₁]) ++
      (if axis then [false] else [])))
    (binarySignedAdd
      (binarySignedIndicator ![action, if axis then [false] else [],
        [false, false] ++ binaryLengthWord
          (BrouwerNashHeaders.dimensionRuler ![source, code₀, code₁])])
      (binarySignedIndicator ![action,
        BrouwerNashHeaders.precisionRuler ![source, code₀, code₁] ++ List.replicate 3 false,
        binarySignedMul ([false, false] ++ binaryLengthWord
          (BrouwerNashHeaders.dimensionRuler ![source, code₀, code₁]))
          (binarySignedSub (false :: binaryLengthWord (List.replicate t.val false))
            [false, false, false, true, false, true])])) []) = _
  rw [BrouwerNashCoefficientQuery.select_value, binarySignedAdd_value, binarySignedIndicator_value,
    binarySignedIndicator_value, binarySignedMul_value, capacity_value, shift_value]
  simp only [List.length_append, List.length_replicate, smash_length,
    BrouwerNashHeaders.dimensionRuler_length, BrouwerNashHeaders.precisionRuler_length,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length]
  cases axis <;> rfl
private theorem term_coefficients (axis : Bool) (out action source code₀ code₁ : List Bool)
    (t : Fin 41)
    (r : Fin (BrouwerNashLayout.dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (term axis
      ![List.replicate t.val false, out, action, source, code₀, code₁]) =
      if out.length = BrouwerNashLayout.sampleBase (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
          (if axis then 1 else 0) then
        (BrouwerNashProgram.affine₂
          (BrouwerNashProgram.slot (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
            (if axis then 1 else 0))
          (BrouwerNashProgram.slot (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
            (BrouwerNashLayout.alpha (BrouwerNashLayout.precision (pairFst source).length)))
          (2 * (BrouwerNashLayout.dimension (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ))
          (2 * (BrouwerNashLayout.dimension (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) *
            ((t.val : ℤ) - 20)) 0).coefficients r else 0 := by
  have hg : BrouwerNashLayout.globalCount (pairFst source).length <
      BrouwerNashLayout.dimension (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length :=
    (Nat.le_add_right _ _).trans_lt (BrouwerNashLayout.allocated_lt_dimension _ _ _)
  have hp : 0 < BrouwerNashLayout.precision (pairFst source).length := by
    simp only [BrouwerNashLayout.precision]
    omega
  have ha : (if axis then 1 else 0) <
      BrouwerNashLayout.dimension (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    have hglobal : 1 < BrouwerNashLayout.globalCount (pairFst source).length := by
      simp only [BrouwerNashLayout.globalCount]
      omega
    cases axis <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      omega
  have hz : BrouwerNashLayout.alpha (BrouwerNashLayout.precision (pairFst source).length) =
      BrouwerNashLayout.precision (pairFst source).length + 3 := by
    simp only [BrouwerNashLayout.alpha, ite_eq_right hp.ne']
    omega
  have haz : BrouwerNashLayout.alpha (BrouwerNashLayout.precision (pairFst source).length) <
      BrouwerNashLayout.dimension (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    rw [hz]
    have hglobal : BrouwerNashLayout.precision (pairFst source).length + 3 <
        BrouwerNashLayout.globalCount (pairFst source).length := by
      simp only [BrouwerNashLayout.globalCount]
      omega
    omega
  rw [term_value, hr, BrouwerNashCoefficientQuery.affine₂_coefficients]
  have hx := BrouwerNashCoefficientQuery.pairedAction_iff r
    (BrouwerNashProgram.slot (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
      (if axis then 1 else 0))
  rw [BrouwerNashProgram.slot_val _ _ _ _ ha] at hx
  have hy := BrouwerNashCoefficientQuery.pairedAction_iff r
    (BrouwerNashProgram.slot (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
      (BrouwerNashLayout.alpha (BrouwerNashLayout.precision (pairFst source).length)))
  rw [BrouwerNashProgram.slot_val _ _ _ _ haz, hz] at hy
  simp only [hz, hx, hy]
/-- Each jitter output selects its canonical signed affine coefficients. -/
theorem coefficientWord_value (out action source code₀ code₁ : List Bool)
    (r : Fin (BrouwerNashLayout.dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      ∑ axis : Fin 2, ∑ t : Fin 41,
        if out.length = BrouwerNashLayout.sampleBase (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t + axis.val then
          (BrouwerNashProgram.affine₂
            (BrouwerNashProgram.slot (pairFst source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length axis.val)
            (BrouwerNashProgram.slot (pairFst source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
              (BrouwerNashLayout.alpha (BrouwerNashLayout.precision (pairFst source).length)))
            (2 * (BrouwerNashLayout.dimension (pairFst source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ))
            (2 * (BrouwerNashLayout.dimension (pairFst source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) *
              ((t.val : ℤ) - 20)) 0).coefficients r else 0 := by
  rw [coefficientWord, binarySignedAdd_value, Fin.sum_univ_two]
  apply congrArg₂ (· + ·)
  · rw [binarySignedFiniteSum_value, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t _
    exact term_coefficients false out action source code₀ code₁ t r hr
  · rw [binarySignedFiniteSum_value, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t _
    exact term_coefficients true out action source code₀ code₁ t r hr
private theorem jitter_injective (b ell₀ ell₁ : ℕ) (t t' : Fin 41) (a a' : Fin 2)
    (he : BrouwerNashLayout.sampleBase b ell₀ ell₁ t + a.val =
      BrouwerNashLayout.sampleBase b ell₀ ell₁ t' + a'.val) : t = t' ∧ a = a' := by
  let w := BrouwerNashLayout.sampleWidth b ell₀ ell₁
  have hw : 2 ≤ w := by dsimp [w, BrouwerNashLayout.sampleWidth]; omega
  have ha := a.isLt
  have ha' := a'.isLt
  have ht : t = t' := by
    apply Fin.ext
    dsimp only [BrouwerNashLayout.sampleBase] at he
    change _ + t.val * w + _ = _ + t'.val * w + _ at he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm := Nat.mul_le_mul_right w (show t.val + 1 ≤ t'.val by omega)
      rw [Nat.add_mul, one_mul] at hm
      omega
    · have hm := Nat.mul_le_mul_right w (show t'.val + 1 ≤ t.val by omega)
      rw [Nat.add_mul, one_mul] at hm
      omega
  subst t'
  exact ⟨rfl, Fin.ext (by omega)⟩

/-- A jitter output receives precisely its signed affine coefficients. -/
theorem coefficientWord_at (out action source code₀ code₁ : List Bool)
    (t : Fin 41) (axis : Fin 2)
    (r : Fin (BrouwerNashLayout.dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val)
    (ho : out.length = BrouwerNashLayout.sampleBase (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t + axis.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      (BrouwerNashProgram.affine₂
        (BrouwerNashProgram.slot (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length axis.val)
        (BrouwerNashProgram.slot (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
          (BrouwerNashLayout.alpha (BrouwerNashLayout.precision (pairFst source).length)))
        (2 * (BrouwerNashLayout.dimension (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ))
        (2 * (BrouwerNashLayout.dimension (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) *
          ((t.val : ℤ) - 20)) 0).coefficients r := by
  rw [coefficientWord_value out action source code₀ code₁ r hr, Finset.sum_eq_single axis]
  · rw [Finset.sum_eq_single t]
    · exact ite_eq_left ho
    · intro t' _ hne
      apply ite_eq_right
      intro he
      exact hne (jitter_injective _ _ _ t t' axis axis (ho.symm.trans he)).1.symm
    · simp
  · intro a' _ hne
    apply Finset.sum_eq_zero
    intro t' _
    apply ite_eq_right
    intro he
    exact hne (jitter_injective _ _ _ t t' axis a' (ho.symm.trans he)).2.symm
  · simp

/-- Jitter emits zero outside the first two slots of every sample. -/
theorem coefficientWord_eq_zero_of_outside (out action source code₀ code₁ : List Bool)
    (r : Fin (BrouwerNashLayout.dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val)
    (hno : ∀ t : Fin 41,
      ¬ (BrouwerNashLayout.sampleBase (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t ≤ out.length ∧
        out.length < BrouwerNashLayout.sampleBase (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t + 2)) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) = 0 := by
  rw [coefficientWord_value out action source code₀ code₁ r hr]
  apply Finset.sum_eq_zero
  intro axis _
  apply Finset.sum_eq_zero
  intro t _
  apply ite_eq_right
  intro he
  apply hno t
  have ha := axis.isLt
  omega
end GameTheory.Complexity.Backend.BrouwerNashJitterQuery
