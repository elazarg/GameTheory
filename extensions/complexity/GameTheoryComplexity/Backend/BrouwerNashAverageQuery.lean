import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
import GameTheoryComplexity.Backend.BrouwerNashProgram
import GameTheoryComplexity.Backend.BrouwerNashHeaders
import GameTheoryComplexity.Backend.BinarySignedIndicator
import GameTheoryComplexity.Backend.BinaryUnaryEncoding
import GameTheoryComplexity.Backend.BinarySignedFiniteSum

namespace GameTheory.Complexity.Backend.BrouwerNashAverageQuery
open _root_.Complexity _root_.Complexity.Cobham
open scoped BigOperators

private def flagTerm (axis : Bool) (v : Fin 7 → List Bool) : List Bool :=
  let source := ![v 4, v 5, v 6]
  let sample := BrouwerNashHeaders.sampleRuler source
  let input := BrouwerNashHeaders.globalRuler source ++ smash (v 2) sample ++ sample.drop 16 ++
    smash (v 1) [false, false, false, false] ++ smash (v 0) [false, false] ++ [false]
  let units := binaryLengthWord (BrouwerNashHeaders.unitsRuler source)
  let flag := binaryLengthParity (v 0)
  let scalar := caseBit₀ (if axis then flag else notBit flag)
    ([false, false, false] ++ units) ([false, false] ++ units)
  binarySignedIndicator ![v 3, input, scalar]

private theorem flagTerm_cobham (axis : Bool) : Cobham (flagTerm axis) := by
  have hS : Cobham fun v : Fin 7 → List Bool =>
      BrouwerNashHeaders.sampleRuler ![v 4, v 5, v 6] :=
    Cobham.comp₃ BrouwerNashHeaders.sampleRuler_cobham (.proj 4) (.proj 5) (.proj 6)
  have hG : Cobham fun v : Fin 7 → List Bool =>
      BrouwerNashHeaders.globalRuler ![v 4, v 5, v 6] :=
    Cobham.comp₃ BrouwerNashHeaders.globalRuler_cobham (.proj 4) (.proj 5) (.proj 6)
  have hU : Cobham fun v : Fin 7 → List Bool =>
      binaryLengthWord (BrouwerNashHeaders.unitsRuler ![v 4, v 5, v 6]) :=
    Cobham.comp binaryLengthWord_cobham fun _ : Fin 1 =>
      Cobham.comp₃ BrouwerNashHeaders.unitsRuler_cobham (.proj 4) (.proj 5) (.proj 6)
  have hF : Cobham fun v : Fin 7 → List Bool =>
      if axis then binaryLengthParity (v 0) else notBit (binaryLengthParity (v 0)) := by
    cases axis
    · exact Cobham.notFn (Cobham.comp binaryLengthParity_cobham fun _ : Fin 1 => .proj 0)
    · exact Cobham.comp binaryLengthParity_cobham fun _ : Fin 1 => .proj 0
  exact Cobham.comp₃ binarySignedIndicator_cobham (.proj 3)
    (appendFn (appendFn (appendFn (appendFn (appendFn hG
      (Cobham.comp₂ Cobham.smash (.proj 2) hS))
      (dropFn (Cobham.const (List.replicate 16 false)) hS))
      (Cobham.comp₂ Cobham.smash (.proj 1) (Cobham.const [false, false, false, false])))
      (Cobham.comp₂ Cobham.smash (.proj 0) (Cobham.const [false, false])))
      (Cobham.const [false]))
    (Cobham.iteFn hF (appendFn (Cobham.const [false, false, false]) hU)
      (appendFn (Cobham.const [false, false]) hU))

private def flags (axis : Bool) (v : Fin 6 → List Bool) : List Bool :=
  binarySignedFiniteSum (flagTerm axis) 2 v

private theorem flags_cobham (axis : Bool) : Cobham (flags axis) :=
  binarySignedFiniteSum_cobham (flagTerm_cobham axis) 2

private def corners (axis : Bool) (v : Fin 5 → List Bool) : List Bool :=
  binarySignedFiniteSum (flags axis) 4 v

private theorem corners_cobham (axis : Bool) : Cobham (corners axis) :=
  binarySignedFiniteSum_cobham (flags_cobham axis) 4

private def samples (axis : Bool) (v : Fin 4 → List Bool) : List Bool :=
  binarySignedFiniteSum (corners axis) 41 v

private theorem samples_cobham (axis : Bool) : Cobham (samples axis) :=
  binarySignedFiniteSum_cobham (corners_cobham axis) 41
/-- Query the two shared means from output, action, source and scalar circuit codes. -/
def coefficientWord (v : Fin 5 → List Bool) : List Bool :=
  let source := ![v 2, v 3, v 4]
  let precision := BrouwerNashHeaders.precisionRuler source
  binarySignedAdd
    (caseBit₀ (lenEqFlag (v 0) (precision ++ List.replicate 5 false))
      (samples false ![v 1, v 2, v 3, v 4]) [])
    (caseBit₀ (lenEqFlag (v 0) (precision ++ List.replicate 6 false))
      (samples true ![v 1, v 2, v 3, v 4]) [])

/-- Every average coefficient is computed by bounded scans. -/
theorem coefficientWord_cobham : Cobham coefficientWord := by
  have hp : Cobham fun v : Fin 5 → List Bool =>
      BrouwerNashHeaders.precisionRuler ![v 2, v 3, v 4] :=
    Cobham.comp₃ BrouwerNashHeaders.precisionRuler_cobham (.proj 2) (.proj 3) (.proj 4)
  have hs (axis : Bool) : Cobham fun v : Fin 5 → List Bool =>
      samples axis ![v 1, v 2, v 3, v 4] :=
    (Cobham.comp (samples_cobham axis) fun i : Fin 4 => .proj i.succ).of_eq fun v => by
      congr 1
      ext i
      fin_cases i <;> rfl
  exact Cobham.comp₂ binarySignedAdd_cobham
    (Cobham.iteFn (lenEqFlag_mem (.proj 0)
      (appendFn hp (Cobham.const (List.replicate 5 false)))) (hs false) Cobham.empty)
    (Cobham.iteFn (lenEqFlag_mem (.proj 0)
      (appendFn hp (Cobham.const (List.replicate 6 false)))) (hs true) Cobham.empty)

theorem coefficientWord_mem_FPn : FPn coefficientWord :=
  cobham_iff_FPn.mp coefficientWord_cobham

private theorem scalar_two (r : List Bool) :
    binarySignedValue (false :: false :: binaryLengthWord r) = 2 * (r.length : ℤ) := by
  simp only [binarySignedValue, List.headD_cons,
    Bool.false_eq_true, ite_false, List.tail_cons, Nat.fromBitsLE_cons, zero_add,
    binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]

private theorem scalar_four (r : List Bool) :
    binarySignedValue (false :: false :: false :: binaryLengthWord r) =
      4 * (r.length : ℤ) := by
  simp only [binarySignedValue, List.headD_cons,
    Bool.false_eq_true, ite_false, List.tail_cons, Nat.fromBitsLE_cons, zero_add,
    binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem flagTerm_value (axis : Bool) (action source code₀ code₁ : List Bool)
    (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
    binarySignedValue (flagTerm axis ![List.replicate flag.val false,
      List.replicate corner.val false, List.replicate t.val false, action, source, code₀, code₁]) =
      if action.length / 2 = BrouwerNashLayout.sampleBase (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
          BrouwerNashLayout.minimum (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length corner flag ∧
          action.length % 2 = 1
      then 2 * (BrouwerNashLayout.units (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) *
        BrouwerNashProgram.componentWeight (if axis then 1 else 0) flag else 0 := by
  change binarySignedValue (binarySignedIndicator ![action,
    BrouwerNashHeaders.globalRuler ![source, code₀, code₁] ++
      smash (List.replicate t.val false)
        (BrouwerNashHeaders.sampleRuler ![source, code₀, code₁]) ++
      (BrouwerNashHeaders.sampleRuler ![source, code₀, code₁]).drop 16 ++
      smash (List.replicate corner.val false) [false, false, false, false] ++
      smash (List.replicate flag.val false) [false, false] ++ [false],
    caseBit₀ (if axis then binaryLengthParity (List.replicate flag.val false)
      else notBit (binaryLengthParity (List.replicate flag.val false)))
      ([false, false, false] ++
        binaryLengthWord (BrouwerNashHeaders.unitsRuler ![source, code₀, code₁]))
      ([false, false] ++
        binaryLengthWord (BrouwerNashHeaders.unitsRuler ![source, code₀, code₁]))]) = _
  rw [binarySignedIndicator_value]
  simp only [List.length_append, List.length_replicate, smash_length, List.length_drop,
    List.length_cons, List.length_nil, BrouwerNashHeaders.globalRuler_length,
    BrouwerNashHeaders.sampleRuler_length]
  change (if action.length / 2 =
      BrouwerNashLayout.globalCount (pairFst source).length +
      t.val * BrouwerNashLayout.sampleWidth (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
      (BrouwerNashLayout.sampleWidth (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length - 16) +
      corner.val * 4 + flag.val * 2 + 1 ∧ action.length % 2 = 1 then _ else 0) = _
  have hlen : BrouwerNashLayout.sampleWidth (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length - 16 =
      BrouwerNashLayout.minimumBase (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    simp only [BrouwerNashLayout.sampleWidth, BrouwerNashLayout.minimumBase,
      BrouwerNashLayout.colorBase, BrouwerNashLayout.weightBase]
    omega
  rw [hlen]
  have hindex : BrouwerNashLayout.globalCount (pairFst source).length +
      t.val * BrouwerNashLayout.sampleWidth (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
      BrouwerNashLayout.minimumBase (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
      corner.val * 4 + flag.val * 2 + 1 =
      BrouwerNashLayout.sampleBase (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
      BrouwerNashLayout.minimum (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length corner flag := by
    simp only [BrouwerNashLayout.sampleBase, BrouwerNashLayout.minimum,
      BrouwerNashLayout.minimumTemporary]
    omega
  rw [hindex]
  cases axis <;> fin_cases flag <;>
    simp only [binaryLengthParity_value, List.length_replicate, notBit, caseBit₀,
      BrouwerNashProgram.componentWeight] <;> norm_num <;>
    simp only [scalar_two, scalar_four, BrouwerNashHeaders.unitsRuler_length] <;>
    congr 1 <;> ring_nf <;> rfl

private theorem samples_value (axis : Bool) (action source code₀ code₁ : List Bool) :
    binarySignedValue (samples axis ![action, source, code₀, code₁]) =
      ∑ t : Fin 41, ∑ corner : Fin 4, ∑ flag : Fin 2,
        if action.length / 2 = BrouwerNashLayout.sampleBase (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
            BrouwerNashLayout.minimum (pairFst source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length corner flag ∧
            action.length % 2 = 1
        then 2 * (BrouwerNashLayout.units (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) *
          BrouwerNashProgram.componentWeight (if axis then 1 else 0) flag else 0 := by
  simp only [samples, binarySignedFiniteSum_value, corners, flags]
  simp only [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro corner _
  apply Finset.sum_congr rfl
  intro flag _
  exact flagTerm_value axis action source code₀ code₁ t corner flag
private theorem samples_coefficients (axis : Bool) (action source code₀ code₁ : List Bool)
    (r : Fin (BrouwerNashLayout.dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (samples axis ![action, source, code₀, code₁]) =
      (BrouwerNashProgram.averageGate (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
        (if axis then 1 else 0)).coefficients r := by
  rw [samples_value, hr]
  rcases finProdFinEquiv.surjective r with ⟨⟨a, bit⟩, rfl⟩
  by_cases hb : bit = 0
  · subst bit
    have hzero : (finProdFinEquiv (a, (0 : Fin 2))).val % 2 = 0 := by
      change (0 + 2 * a.val) % 2 = 0
      omega
    simp only [hzero, Nat.zero_ne_one, and_false, ite_false, Finset.sum_const_zero]
    dsimp only [BrouwerNashProgram.averageGate, GameTheory.Finite.BimatrixArithmeticGate.gate]
    exact (GameTheory.Finite.BimatrixArithmeticGate.coefficients_zero _ 0 a).symm
  · have hb : bit = 1 := by
      apply Fin.ext
      have hlt := bit.isLt
      have hne : bit.val ≠ 0 := fun h => hb (Fin.ext h)
      omega
    subst bit
    have hmod : (finProdFinEquiv (a, (1 : Fin 2))).val % 2 = 1 := by
      change (1 + 2 * a.val) % 2 = 1
      omega
    have hdiv : (finProdFinEquiv (a, (1 : Fin 2))).val / 2 = a.val := by
      change (1 + 2 * a.val) / 2 = a.val
      omega
    dsimp only [BrouwerNashProgram.averageGate, GameTheory.Finite.BimatrixArithmeticGate.gate]
    rw [GameTheory.Finite.BimatrixArithmeticGate.coefficients_one, add_zero]
    simp only [hmod, hdiv, and_true]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro corner _
    apply Finset.sum_congr rfl
    intro flag _
    have hb := BrouwerNashLayout.sample_lt_dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
      (BrouwerNashLayout.minimum (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length corner flag)
      (BrouwerNashProgram.minimum_lt_sampleWidth _ _ _ corner flag false)
    have he : a.val =
        BrouwerNashLayout.sampleBase (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
        BrouwerNashLayout.minimum (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length corner flag ↔
        a = BrouwerNashProgram.slot (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
        (BrouwerNashLayout.sampleBase (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
        BrouwerNashLayout.minimum (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length corner flag) := by
      rw [Fin.ext_iff, BrouwerNashProgram.slot_val _ _ _ _ hb]
    simp only [he]
/-- The two mean slots agree with the canonical gate coefficients; other outputs give zero. -/
theorem coefficientWord_value (out action source code₀ code₁ : List Bool)
    (r : Fin (BrouwerNashLayout.dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      (if out.length = BrouwerNashLayout.average (pairFst source).length 0 then
        (BrouwerNashProgram.averageGate (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length 0).coefficients r
      else 0) +
      (if out.length = BrouwerNashLayout.average (pairFst source).length 1 then
        (BrouwerNashProgram.averageGate (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length 1).coefficients r
      else 0) := by
  change binarySignedValue (binarySignedAdd
    (caseBit₀ (lenEqFlag out
      (BrouwerNashHeaders.precisionRuler ![source, code₀, code₁] ++ List.replicate 5 false))
      (samples false ![action, source, code₀, code₁]) [])
    (caseBit₀ (lenEqFlag out
      (BrouwerNashHeaders.precisionRuler ![source, code₀, code₁] ++ List.replicate 6 false))
      (samples true ![action, source, code₀, code₁]) [])) = _
  rw [binarySignedAdd_value, BrouwerNashCoefficientQuery.select_value,
    BrouwerNashCoefficientQuery.select_value,
    samples_coefficients false _ _ _ _ r hr, samples_coefficients true _ _ _ _ r hr]
  simp only [List.length_append, List.length_replicate, BrouwerNashHeaders.precisionRuler_length]
  rfl
end GameTheory.Complexity.Backend.BrouwerNashAverageQuery
