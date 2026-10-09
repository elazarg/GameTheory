import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
import GameTheoryComplexity.Backend.BrouwerNashHeaders
import GameTheoryComplexity.Backend.BinaryIndexedLookup
import GameTheoryComplexity.Backend.BinarySignedIndicator
import GameTheoryComplexity.Backend.BinarySignedFiniteSum
import GameTheoryComplexity.Backend.BinaryUnaryEncoding

namespace GameTheory.Complexity.Backend.BrouwerNashExtractionQuery
open _root_.Complexity _root_.Complexity.Cobham
open scoped BigOperators

private def base (v : Fin 7 → List Bool) : List Bool :=
  BrouwerNashHeaders.globalRuler ![v 4, v 5, v 6] ++
    smash (v 1) (BrouwerNashHeaders.sampleRuler ![v 4, v 5, v 6])

private theorem base_cobham : Cobham base :=
  appendFn
    (Cobham.comp₃ BrouwerNashHeaders.globalRuler_cobham (.proj 4) (.proj 5) (.proj 6))
    (Cobham.comp₂ Cobham.smash (.proj 1)
      (Cobham.comp₃ BrouwerNashHeaders.sampleRuler_cobham (.proj 4) (.proj 5) (.proj 6)))

private def axisOffset (axis : Bool) (v : Fin 7 → List Bool) : List Bool :=
  if axis then smash (BrouwerNashHeaders.sourceDepthRuler ![v 4, v 5, v 6]) [false, false]
  else []

private theorem axisOffset_cobham (axis : Bool) : Cobham (axisOffset axis) := by
  cases axis
  · exact Cobham.empty
  · exact Cobham.comp₂ Cobham.smash
      (Cobham.comp₃ BrouwerNashHeaders.sourceDepthRuler_cobham (.proj 4) (.proj 5) (.proj 6))
      (Cobham.const [false, false])

private def digitRuler (axis : Bool) (v : Fin 7 → List Bool) : List Bool :=
  base v ++ [false, false] ++ axisOffset axis v ++ smash (v 0) [false, false]

private theorem digitRuler_cobham (axis : Bool) : Cobham (digitRuler axis) :=
  appendFn (appendFn (appendFn base_cobham (Cobham.const [false, false]))
    (axisOffset_cobham axis))
    (Cobham.comp₂ Cobham.smash (.proj 0) (Cobham.const [false, false]))

private def remainderRuler (axis : Bool) (v : Fin 7 → List Bool) : List Bool :=
  caseBit₀ (lenEqFlag (v 0) [])
    (base v ++ (if axis then [false] else []))
    (base v ++ [false, false, false] ++ axisOffset axis v ++
      smash (v 0).tail [false, false])

private theorem remainderRuler_cobham (axis : Bool) : Cobham (remainderRuler axis) :=
  Cobham.iteFn (lenEqFlag_mem (.proj 0) Cobham.empty)
    (appendFn base_cobham (Cobham.const (if axis then [false] else [])))
    (appendFn (appendFn (appendFn base_cobham (Cobham.const [false, false, false]))
      (axisOffset_cobham axis))
      (Cobham.comp₂ Cobham.smash (Cobham.tailFn (.proj 0)) (Cobham.const [false, false])))

private def test (axis next : Bool) (v : Fin 7 → List Bool) : List Bool :=
  andBit
    (lenEqFlag (v 2) (digitRuler axis v ++ (if next then [false] else [])))
    (notBit (lenLeFlag (v 0) (BrouwerNashHeaders.sourceDepthRuler ![v 4, v 5, v 6])))

private theorem test_cobham (axis next : Bool) : Cobham (test axis next) :=
  Cobham.andFn
    (lenEqFlag_mem (.proj 2)
      (appendFn (digitRuler_cobham axis) (Cobham.const (if next then [false] else []))))
    (Cobham.notFn (lenLeFlag_mem (.proj 0)
      (Cobham.comp₃ BrouwerNashHeaders.sourceDepthRuler_cobham (.proj 4) (.proj 5) (.proj 6))))

/-- Arguments are digit ordinal, sample ordinal, output, action, source and two color codes. -/
def indexedCoefficientWord (axis next : Bool) (v : Fin 7 → List Bool) : List Bool :=
  let bits := binaryLengthWord (BrouwerNashHeaders.dimensionRuler ![v 4, v 5, v 6])
  if next then binarySignedSub
    (binarySignedIndicator ![v 3, remainderRuler axis v, [false, false, false] ++ bits])
    (binarySignedIndicator ![v 3, digitRuler axis v, [false, false] ++ bits])
  else binarySignedSub
    (binarySignedIndicator ![v 3, remainderRuler axis v, [false, false] ++ bits]) [false, true]

private theorem indexedCoefficientWord_cobham (axis next : Bool) :
    Cobham (indexedCoefficientWord axis next) := by
  have hb := Cobham.comp binaryLengthWord_cobham fun _ : Fin 1 =>
    Cobham.comp₃ BrouwerNashHeaders.dimensionRuler_cobham
      (Cobham.proj (4 : Fin 7)) (.proj 5) (.proj 6)
  have hc := appendFn (Cobham.const [false, false]) hb
  have hd := appendFn (Cobham.const [false, false, false]) hb
  cases next
  · exact (Cobham.comp₂ binarySignedSub_cobham
      (Cobham.comp₃ binarySignedIndicator_cobham (.proj 3)
        (remainderRuler_cobham axis) hc) (Cobham.const [false, true])).of_eq fun v => rfl
  · exact (Cobham.comp₂ binarySignedSub_cobham
      (Cobham.comp₃ binarySignedIndicator_cobham (.proj 3)
        (remainderRuler_cobham axis) hd)
      (Cobham.comp₃ binarySignedIndicator_cobham (.proj 3)
        (digitRuler_cobham axis) hc)).of_eq fun v => rfl

/-- Select one alternating extraction coefficient within one sample and coordinate. -/
def sampleCoefficientWord (axis next : Bool) (v : Fin 6 → List Bool) : List Bool :=
  binaryIndexedLookup (test axis next) (indexedCoefficientWord axis next)
    (BrouwerNashHeaders.sourceDepthRuler ![v 3, v 4, v 5])
    (BrouwerNashHeaders.widthRuler ![v 3, v 4, v 5]) v

private theorem sampleCoefficientWord_cobham (axis next : Bool) :
    Cobham (sampleCoefficientWord axis next) := by
  have hg := binaryIndexedLookup_cobham (test_cobham axis next)
    (indexedCoefficientWord_cobham axis next)
  have hc : Cobham fun v : Fin 6 → List Bool =>
      BrouwerNashHeaders.sourceDepthRuler ![v 3, v 4, v 5] :=
    Cobham.comp₃ BrouwerNashHeaders.sourceDepthRuler_cobham (.proj 3) (.proj 4) (.proj 5)
  have hw : Cobham fun v : Fin 6 → List Bool =>
      BrouwerNashHeaders.widthRuler ![v 3, v 4, v 5] :=
    Cobham.comp₃ BrouwerNashHeaders.widthRuler_cobham (.proj 3) (.proj 4) (.proj 5)
  have hv : ∀ i : Fin 8, Cobham fun v : Fin 6 → List Bool =>
      (Fin.cons (BrouwerNashHeaders.sourceDepthRuler ![v 3, v 4, v 5])
        (Fin.cons (BrouwerNashHeaders.widthRuler ![v 3, v 4, v 5]) v) : Fin 8 → List Bool) i := by
    intro i
    exact Fin.cases hc (fun j => Fin.cases hw (fun a => .proj a) j) i
  exact (Cobham.comp hg hv).of_eq fun v => rfl

private def sample (v : Fin 6 → List Bool) : List Bool :=
  binarySignedAdd
    (binarySignedAdd (sampleCoefficientWord false false v) (sampleCoefficientWord false true v))
    (binarySignedAdd (sampleCoefficientWord true false v) (sampleCoefficientWord true true v))

private theorem sample_cobham : Cobham sample :=
  Cobham.comp₂ binarySignedAdd_cobham
    (Cobham.comp₂ binarySignedAdd_cobham (sampleCoefficientWord_cobham false false)
      (sampleCoefficientWord_cobham false true))
    (Cobham.comp₂ binarySignedAdd_cobham (sampleCoefficientWord_cobham true false)
      (sampleCoefficientWord_cobham true true))

/-- Query alternating digit and remainder coefficients using bounded source-depth scans. -/
def coefficientWord : (Fin 5 → List Bool) → List Bool := binarySignedFiniteSum sample 41

theorem coefficientWord_cobham : Cobham coefficientWord :=
  binarySignedFiniteSum_cobham sample_cobham 41

theorem coefficientWord_mem_FPn : FPn coefficientWord :=
  cobham_iff_FPn.mp coefficientWord_cobham

private theorem lenEq_value (a b : List Bool) :
    lenEqFlag a b = [decide (a.length = b.length)] := by
  rcases lenEqFlag_flag a b with h | h
  · rw [h]; simp [(lenEqFlag_eq_true_iff a b).mp h]
  · rw [h]
    have hn : a.length ≠ b.length := by
      intro he
      have ht := (lenEqFlag_eq_true_iff a b).mpr he
      rw [h] at ht
      contradiction
    simp [hn]

private theorem lenLe_value (a b : List Bool) :
    lenLeFlag a b = [decide (b.length ≤ a.length)] := by
  rcases lenLeFlag_flag a b with h | h
  · rw [h]; simp [(lenLeFlag_eq_true_iff a b).mp h]
  · rw [h]
    have hn : ¬ b.length ≤ a.length := by
      intro he
      have ht := (lenLeFlag_eq_true_iff a b).mpr he
      rw [h] at ht
      contradiction
    simp [hn]

private theorem and_decide (P Q : Prop) [Decidable P] [Decidable Q] :
    andBit [decide P] [decide Q] = [decide (P ∧ Q)] := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq, andBit, caseBit₀]

private theorem not_decide (P : Prop) [Decidable P] :
    notBit [decide P] = [decide (¬ P)] := by
  by_cases hp : P <;> simp [hp, notBit, caseBit₀]

private theorem test_value (axis next : Bool)
    (ordinal sample out action source code₀ code₁ : List Bool) :
    test axis next ![ordinal, sample, out, action, source, code₀, code₁] =
      [decide (out.length = BrouwerNashLayout.globalCount (pairFst source).length +
          sample.length * BrouwerNashLayout.sampleWidth (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
          2 + (if axis then 2 * (pairFst source).length else 0) + 2 * ordinal.length +
          (if next then 1 else 0) ∧ ordinal.length < (pairFst source).length)] := by
  dsimp only [test]
  rw [lenEq_value, lenLe_value, not_decide, and_decide]
  simp only [digitRuler, base, axisOffset, List.length_append, smash_length,
    List.length_cons, List.length_nil, BrouwerNashHeaders.sourceDepthRuler_length,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length]
  congr 2
  apply propext
  dsimp
  cases axis <;> cases next <;> simp [smash_length] <;> omega
private theorem remainderRuler_length (axis : Bool)
    (ordinal sample out action source code₀ code₁ : List Bool) :
    (remainderRuler axis ![ordinal, sample, out, action, source, code₀, code₁]).length =
      BrouwerNashLayout.globalCount (pairFst source).length +
        sample.length * BrouwerNashLayout.sampleWidth (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        (if ordinal.length = 0 then (if axis then 1 else 0)
          else 3 + (if axis then 2 * (pairFst source).length else 0) +
            2 * (ordinal.length - 1)) := by
  dsimp only [remainderRuler]
  rw [lenEq_value]
  change (caseBit₀ [decide (ordinal.length = 0)] _ _).length = _
  by_cases ho : ordinal.length = 0
  · simp only [ho, decide_true, caseBit₀, Bool.cond_true, List.length_append,
      ite_true]
    simp only [base, smash_length, List.length_append, BrouwerNashHeaders.globalRuler_length,
      BrouwerNashHeaders.sampleRuler_length]
    dsimp
    cases axis <;> simp only [ite_true, Bool.false_eq_true, ite_false,
      List.length_cons, List.length_nil]
  · simp only [ho, decide_false, caseBit₀, Bool.cond_false, List.length_append,
      List.length_cons, List.length_nil, ite_false]
    simp only [base, axisOffset, smash_length, List.length_append,
      BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length]
    dsimp
    cases axis <;> simp [smash_length] <;> omega
private theorem digitRuler_length (axis : Bool)
    (ordinal sample out action source code₀ code₁ : List Bool) :
    (digitRuler axis ![ordinal, sample, out, action, source, code₀, code₁]).length =
      BrouwerNashLayout.globalCount (pairFst source).length +
        sample.length * BrouwerNashLayout.sampleWidth (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        2 + (if axis then 2 * (pairFst source).length else 0) + 2 * ordinal.length := by
  simp only [digitRuler, base, axisOffset, List.length_append, smash_length,
    List.length_cons, List.length_nil, BrouwerNashHeaders.globalRuler_length,
    BrouwerNashHeaders.sampleRuler_length]
  dsimp
  cases axis <;> simp [smash_length] <;> omega

private theorem capacity_value (r : List Bool) :
    binarySignedValue ([false, false] ++ binaryLengthWord r) = 2 * (r.length : ℤ) := by
  simp only [List.cons_append, List.nil_append, binarySignedValue, List.headD_cons,
    Bool.false_eq_true, ite_false, List.tail_cons, Nat.fromBitsLE_cons, zero_add,
    binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]

private theorem doubleCapacity_value (r : List Bool) :
    binarySignedValue ([false, false, false] ++ binaryLengthWord r) =
      4 * (r.length : ℤ) := by
  simp only [List.cons_append, List.nil_append, binarySignedValue, List.headD_cons,
    Bool.false_eq_true, ite_false, List.tail_cons, Nat.fromBitsLE_cons, zero_add,
    binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Digit and residual coefficients have their exact signed scalar interpretations. -/
theorem indexedCoefficientWord_value (axis next : Bool)
    (ordinal sample out action source code₀ code₁ : List Bool) :
    let k := BrouwerNashLayout.dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
    let base := BrouwerNashLayout.globalCount (pairFst source).length +
      sample.length * BrouwerNashLayout.sampleWidth (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
    let rem := base + (if ordinal.length = 0 then (if axis then 1 else 0)
      else 3 + (if axis then 2 * (pairFst source).length else 0) + 2 * (ordinal.length - 1))
    let digit := base + 2 + (if axis then 2 * (pairFst source).length else 0) +
      2 * ordinal.length
    binarySignedValue (indexedCoefficientWord axis next
      ![ordinal, sample, out, action, source, code₀, code₁]) =
      if next then
        (if action.length / 2 = rem ∧ action.length % 2 = 1 then 4 * (k : ℤ) else 0) -
        (if action.length / 2 = digit ∧ action.length % 2 = 1 then 2 * (k : ℤ) else 0)
      else (if action.length / 2 = rem ∧ action.length % 2 = 1 then 2 * (k : ℤ) else 0) - 1 := by
  dsimp only
  cases next
  · simp only [indexedCoefficientWord, Bool.false_eq_true, ite_false]
    rw [binarySignedSub_value, binarySignedIndicator_value, capacity_value,
      remainderRuler_length, BrouwerNashHeaders.dimensionRuler_length]
    change (if action.length / 2 = _ ∧ action.length % 2 = 1 then _ else 0) -
      binarySignedValue [false, true] = _
    rfl
  · simp only [indexedCoefficientWord, ite_true]
    rw [binarySignedSub_value, binarySignedIndicator_value, binarySignedIndicator_value,
      doubleCapacity_value, capacity_value, remainderRuler_length, digitRuler_length,
      BrouwerNashHeaders.dimensionRuler_length]
    rfl
private theorem guarded_natAbs (P : Prop) [Decidable P] (z : ℤ) :
    (if P then z else 0).natAbs ≤ z.natAbs := by
  by_cases hp : P <;> simp [hp]

private theorem indexedCoefficientWord_bound (axis next : Bool)
    (ordinal sample out action source code₀ code₁ : List Bool) :
    (binarySignedValue (indexedCoefficientWord axis next
      ![ordinal, sample, out, action, source, code₀, code₁])).natAbs ≤
      100 * BrouwerNashLayout.dimension (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
  have hk := BrouwerNashLayout.dimension_pos (pairFst source).length
    (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
  rw [indexedCoefficientWord_value]
  cases next
  · simp only [Bool.false_eq_true, ite_false]
    refine (Int.natAbs_sub_le _ _).trans ?_
    have hi := guarded_natAbs
      (action.length / 2 = BrouwerNashLayout.globalCount (pairFst source).length +
        sample.length * BrouwerNashLayout.sampleWidth (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        (if ordinal.length = 0 then (if axis then 1 else 0)
          else 3 + (if axis then 2 * (pairFst source).length else 0) +
            2 * (ordinal.length - 1)) ∧ action.length % 2 = 1)
      (2 * (BrouwerNashLayout.dimension (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ))
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at hi ⊢
    omega
  · simp only [ite_true]
    refine (Int.natAbs_sub_le _ _).trans ?_
    have hi := guarded_natAbs
      (action.length / 2 = BrouwerNashLayout.globalCount (pairFst source).length +
        sample.length * BrouwerNashLayout.sampleWidth (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        (if ordinal.length = 0 then (if axis then 1 else 0)
          else 3 + (if axis then 2 * (pairFst source).length else 0) +
            2 * (ordinal.length - 1)) ∧ action.length % 2 = 1)
      (4 * (BrouwerNashLayout.dimension (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ))
    have hj := guarded_natAbs
      (action.length / 2 = BrouwerNashLayout.globalCount (pairFst source).length +
        sample.length * BrouwerNashLayout.sampleWidth (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        2 + (if axis then 2 * (pairFst source).length else 0) + 2 * ordinal.length ∧
        action.length % 2 = 1)
      (2 * (BrouwerNashLayout.dimension (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ))
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at hi hj ⊢
    omega
/-- A unique digit or residual output contributes its guarded indexed coefficient. -/
theorem sampleCoefficientWord_value (axis next : Bool)
    (sample out action source code₀ code₁ : List Bool) :
    binarySignedValue (sampleCoefficientWord axis next
      ![sample, out, action, source, code₀, code₁]) =
      ∑ i ∈ Finset.range (pairFst source).length,
        if out.length = BrouwerNashLayout.globalCount (pairFst source).length +
            sample.length * BrouwerNashLayout.sampleWidth (pairFst source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
            2 + (if axis then 2 * (pairFst source).length else 0) + 2 * i +
            (if next then 1 else 0) then
          binarySignedValue (indexedCoefficientWord axis next
            ![List.replicate i false, sample, out, action, source, code₀, code₁]) else 0 := by
  let hit := fun i => decide (out.length =
    BrouwerNashLayout.globalCount (pairFst source).length +
      sample.length * BrouwerNashLayout.sampleWidth (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
      2 + (if axis then 2 * (pairFst source).length else 0) + 2 * i +
      (if next then 1 else 0) ∧ i < (pairFst source).length)
  let value := fun i => binarySignedValue (indexedCoefficientWord axis next
    ![List.replicate i false, sample, out, action, source, code₀, code₁])
  have hw : 0 < (BrouwerNashHeaders.widthRuler ![source, code₀, code₁]).length := by
    rw [BrouwerNashHeaders.widthRuler_length]
    omega
  have hx := binaryIndexedLookup_sum_value (test axis next) (indexedCoefficientWord axis next)
    (BrouwerNashHeaders.widthRuler ![source, code₀, code₁])
    ![sample, out, action, source, code₀, code₁] hit value
    (fun ordinal => test_value axis next ordinal sample out action source code₀ code₁)
    (by
      intro ordinal _
      change binarySignedValue (indexedCoefficientWord axis next
        ![ordinal, sample, out, action, source, code₀, code₁]) = _
      dsimp only [value]
      rw [indexedCoefficientWord_value, indexedCoefficientWord_value]
      simp only [List.length_replicate]) hw
    (BrouwerNashHeaders.sourceDepthRuler ![source, code₀, code₁])
    (by
      intro i _ _
      apply BrouwerNashHeaders.widthRuler_fits
      rw [BrouwerNashHeaders.dimensionRuler_length]
      exact indexedCoefficientWord_bound axis next (List.replicate i false)
        sample out action source code₀ code₁)
    (by
      intro i _ j _ hi hj
      have hi' := of_decide_eq_true hi
      have hj' := of_decide_eq_true hj
      omega)
  change binarySignedValue (binaryIndexedLookup (test axis next) (indexedCoefficientWord axis next)
    (BrouwerNashHeaders.sourceDepthRuler ![source, code₀, code₁])
    (BrouwerNashHeaders.widthRuler ![source, code₀, code₁])
    ![sample, out, action, source, code₀, code₁]) = _
  rw [hx]
  change (∑ i ∈ Finset.range (pairFst source).length, if hit i then value i else 0) = _
  apply Finset.sum_congr rfl
  intro i hi
  have hir := Finset.mem_range.mp hi
  dsimp only [hit, value]
  simp only [hir, and_true, decide_eq_true_eq]
/-- The emitted extraction coefficients equal the guarded sum over the canonical allocation. -/
theorem coefficientWord_value (out action source code₀ code₁ : List Bool) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      ∑ t : Fin 41, ∑ axis : Fin 2, ∑ next : Fin 2,
        ∑ i ∈ Finset.range (pairFst source).length,
          if out.length = BrouwerNashLayout.sampleBase (pairFst source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
              2 + 2 * (pairFst source).length * axis.val + 2 * i + next.val then
            binarySignedValue (indexedCoefficientWord (decide (axis = 1)) (decide (next = 1))
              ![List.replicate i false, List.replicate t.val false, out, action,
                source, code₀, code₁]) else 0 := by
  rw [coefficientWord, binarySignedFiniteSum_value, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  change binarySignedValue (sample ![List.replicate t.val false, out, action,
    source, code₀, code₁]) = _
  rw [sample, binarySignedAdd_value, binarySignedAdd_value, binarySignedAdd_value,
    sampleCoefficientWord_value, sampleCoefficientWord_value,
    sampleCoefficientWord_value, sampleCoefficientWord_value]
  simp only [Fin.sum_univ_two, List.length_replicate]
  norm_num [BrouwerNashLayout.sampleBase]
private theorem remainder_coefficients {k : ℕ} (a z : Fin k) (r : Fin (k * 2)) :
    (GameTheory.Finite.BimatrixBinaryExtraction.remainderGate a z).coefficients r =
      (if r = finProdFinEquiv (a, 1) then 4 * (k : ℤ) else 0) -
      (if r = finProdFinEquiv (z, 1) then 2 * (k : ℤ) else 0) := by
  rcases finProdFinEquiv.surjective r with ⟨⟨j, bit⟩, rfl⟩
  by_cases hb : bit = 0
  · subst bit
    simp [GameTheory.Finite.BimatrixBinaryExtraction.remainderGate,
      GameTheory.Finite.BimatrixArithmeticGate.gate,
      GameTheory.Finite.BimatrixArithmeticGate.coefficients]
  · have hb : bit = 1 := by
      apply Fin.ext
      have hlt := bit.isLt
      have hne : bit.val ≠ 0 := fun h => hb (Fin.ext h)
      omega
    subst bit
    simp [GameTheory.Finite.BimatrixBinaryExtraction.remainderGate,
      GameTheory.Finite.BimatrixArithmeticGate.gate,
      GameTheory.Finite.BimatrixArithmeticGate.coefficients]
    rfl

/-- An indexed query at a valid extraction stage agrees with the canonical game gate. -/
theorem indexedCoefficientWord_gate (axis next : Bool)
    (ordinal sample out action source code₀ code₁ : List Bool) (t : Fin 41) (j : ℕ)
    (hj : j < (pairFst source).length) (ho : ordinal.length = j) (ht : sample.length = t.val)
    (r : Fin (BrouwerNashLayout.dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (indexedCoefficientWord axis next
      ![ordinal, sample, out, action, source, code₀, code₁]) =
      if next then
        (GameTheory.Finite.BimatrixBinaryExtraction.remainderGate
          (BrouwerNashProgram.sampleRef (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
            (BrouwerNashLayout.remainder (pairFst source).length (if axis then 1 else 0) j))
          (BrouwerNashProgram.sampleRef (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
            (BrouwerNashLayout.digit (pairFst source).length
              (if axis then 1 else 0) j))).coefficients r
      else (GameTheory.Finite.BimatrixBinaryExtraction.digitGate
          (BrouwerNashProgram.sampleRef (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
            (BrouwerNashLayout.remainder (pairFst source).length
              (if axis then 1 else 0) j))).coefficients r := by
  have hrem : BrouwerNashLayout.remainder (pairFst source).length (if axis then 1 else 0) j <
      BrouwerNashLayout.sampleWidth (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    simp only [BrouwerNashLayout.remainder, BrouwerNashLayout.jitter,
      BrouwerNashLayout.sampleWidth]
    cases axis <;> norm_num <;> split_ifs <;> omega
  have hdig : BrouwerNashLayout.digit (pairFst source).length (if axis then 1 else 0) j <
      BrouwerNashLayout.sampleWidth (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    simp only [BrouwerNashLayout.digit, BrouwerNashLayout.sampleWidth]
    cases axis <;> norm_num <;> omega
  have hrv := BrouwerNashProgram.slot_val (pairFst source).length
    (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length _
    (BrouwerNashLayout.sample_lt_dimension _ _ _ t _ hrem)
  have hdv := BrouwerNashProgram.slot_val (pairFst source).length
    (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length _
    (BrouwerNashLayout.sample_lt_dimension _ _ _ t _ hdig)
  have heRem := BrouwerNashCoefficientQuery.pairedAction_iff r
    (BrouwerNashProgram.sampleRef (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
      (BrouwerNashLayout.remainder (pairFst source).length (if axis then 1 else 0) j))
  have heDig := BrouwerNashCoefficientQuery.pairedAction_iff r
    (BrouwerNashProgram.sampleRef (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
      (BrouwerNashLayout.digit (pairFst source).length (if axis then 1 else 0) j))
  dsimp only [BrouwerNashProgram.sampleRef] at heRem heDig
  rw [hrv] at heRem
  rw [hdv] at heDig
  rw [indexedCoefficientWord_value, ho, ht, hr]
  have heRem' :
      (r.val / 2 = BrouwerNashLayout.globalCount (pairFst source).length +
        t.val * BrouwerNashLayout.sampleWidth (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        (if j = 0 then (if axis then 1 else 0)
          else 3 + (if axis then 2 * (pairFst source).length else 0) + 2 * (j - 1)) ∧
          r.val % 2 = 1) ↔
        r = finProdFinEquiv
          (BrouwerNashProgram.sampleRef (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
            (BrouwerNashLayout.remainder (pairFst source).length
              (if axis then 1 else 0) j), 1) := by
    convert heRem using 1
    · cases axis <;> by_cases hj0 : j = 0 <;>
        simp [hj0, BrouwerNashLayout.sampleBase, BrouwerNashLayout.remainder,
          BrouwerNashLayout.jitter]
    · rfl
  have heDig' :
      (r.val / 2 = BrouwerNashLayout.globalCount (pairFst source).length +
        t.val * BrouwerNashLayout.sampleWidth (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        2 + (if axis then 2 * (pairFst source).length else 0) + 2 * j ∧ r.val % 2 = 1) ↔
        r = finProdFinEquiv
          (BrouwerNashProgram.sampleRef (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
            (BrouwerNashLayout.digit (pairFst source).length (if axis then 1 else 0) j), 1) := by
    convert heDig using 1
    · cases axis <;> simp [BrouwerNashLayout.sampleBase, BrouwerNashLayout.digit] <;> omega
    · rfl
  cases next
  · simp only [Bool.false_eq_true, ite_false,
      GameTheory.Finite.BimatrixBinaryExtraction.digitGate, mul_ite, mul_one, mul_zero,
      heRem']
  · simp only [ite_true, remainder_coefficients, heRem', heDig']
/-- A sample scan preserves the exact coefficient at its allocated extraction output. -/
theorem sampleCoefficientWord_at (axis next : Bool)
    (sample out action source code₀ code₁ : List Bool) (t : Fin 41) (j : ℕ)
    (hj : j < (pairFst source).length) (ht : sample.length = t.val)
    (ho : out.length = BrouwerNashLayout.sampleBase (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
      BrouwerNashLayout.digit (pairFst source).length (if axis then 1 else 0) j +
        (if next then 1 else 0)) :
    binarySignedValue (sampleCoefficientWord axis next
      ![sample, out, action, source, code₀, code₁]) =
      binarySignedValue (indexedCoefficientWord axis next
        ![List.replicate j false, sample, out, action, source, code₀, code₁]) := by
  rw [sampleCoefficientWord_value, Finset.sum_eq_single j]
  · have he : out.length = BrouwerNashLayout.globalCount (pairFst source).length +
        sample.length * BrouwerNashLayout.sampleWidth (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        2 + (if axis then 2 * (pairFst source).length else 0) + 2 * j +
          (if next then 1 else 0) := by
      rw [ht]
      simp only [BrouwerNashLayout.sampleBase, BrouwerNashLayout.digit] at ho
      cases axis <;> norm_num at ho ⊢ <;> omega
    exact ite_eq_left he
  · intro i _ hne
    apply ite_eq_right
    intro he
    rw [ht] at he
    simp only [BrouwerNashLayout.sampleBase, BrouwerNashLayout.digit] at ho
    cases axis <;> norm_num at ho he <;> omega
  · intro hno
    exact False.elim (hno (Finset.mem_range.mpr hj))

/-- With no allocated digit or remainder output, every extraction coefficient is zero. -/
theorem coefficientWord_eq_zero (out action source code₀ code₁ : List Bool)
    (hno : ∀ (t : Fin 41) (axis next : Fin 2) (j : ℕ), j < (pairFst source).length →
      out.length ≠ BrouwerNashLayout.sampleBase (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
        BrouwerNashLayout.digit (pairFst source).length axis j + next.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) = 0 := by
  rw [coefficientWord_value]
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro axis _
  apply Finset.sum_eq_zero
  intro next _
  apply Finset.sum_eq_zero
  intro j hj
  apply ite_eq_right
  intro he
  apply hno t axis next j (Finset.mem_range.mp hj)
  dsimp only [BrouwerNashLayout.digit]
  omega
private theorem extraction_injective (b ell₀ ell₁ : ℕ)
    (t t' : Fin 41) (a a' s s' : Fin 2) (j j' : ℕ) (hj : j < b) (hj' : j' < b)
    (he : BrouwerNashLayout.sampleBase b ell₀ ell₁ t + BrouwerNashLayout.digit b a j + s.val =
      BrouwerNashLayout.sampleBase b ell₀ ell₁ t' +
        BrouwerNashLayout.digit b a' j' + s'.val) :
    t = t' ∧ a = a' ∧ s = s' ∧ j = j' := by
  let w := BrouwerNashLayout.sampleWidth b ell₀ ell₁
  have hw : 2 + 4 * b ≤ w := by
    dsimp [w, BrouwerNashLayout.sampleWidth]
    omega
  have ha := a.isLt
  have ha' := a'.isLt
  have hs := s.isLt
  have hs' := s'.isLt
  have ho : BrouwerNashLayout.digit b a j + s.val < w := by
    dsimp [BrouwerNashLayout.digit]
    have hmul := Nat.mul_le_mul_left (2 * b) (show a.val ≤ 1 by omega)
    omega
  have ho' : BrouwerNashLayout.digit b a' j' + s'.val < w := by
    dsimp [BrouwerNashLayout.digit]
    have hmul := Nat.mul_le_mul_left (2 * b) (show a'.val ≤ 1 by omega)
    omega
  have ht : t = t' := by
    apply Fin.ext
    dsimp [BrouwerNashLayout.sampleBase] at he
    change _ + t.val * w + _ + _ = _ + t'.val * w + _ + _ at he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm := Nat.mul_le_mul_right w (show t.val + 1 ≤ t'.val by omega)
      rw [Nat.add_mul, one_mul] at hm
      omega
    · have hm := Nat.mul_le_mul_right w (show t'.val + 1 ≤ t.val by omega)
      rw [Nat.add_mul, one_mul] at hm
      omega
  subst t'
  have he' : BrouwerNashLayout.digit b a j + s.val =
      BrouwerNashLayout.digit b a' j' + s'.val := by omega
  refine ⟨rfl, ?_⟩
  dsimp [BrouwerNashLayout.digit] at he'
  fin_cases a <;> fin_cases a' <;> fin_cases s <;> fin_cases s' <;>
    simp_all <;> omega

/-- An allocated extraction output receives exactly its canonical coefficient query. -/
theorem coefficientWord_at (out action source code₀ code₁ : List Bool)
    (t : Fin 41) (axis next : Fin 2) (j : ℕ) (hj : j < (pairFst source).length)
    (ho : out.length = BrouwerNashLayout.sampleBase (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
      BrouwerNashLayout.digit (pairFst source).length axis j + next.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      binarySignedValue (indexedCoefficientWord (decide (axis = 1)) (decide (next = 1))
        ![List.replicate j false, List.replicate t.val false, out, action,
          source, code₀, code₁]) := by
  rw [coefficientWord_value]
  have hhit (t' : Fin 41) (a' s' : Fin 2) (j' : ℕ) (hj' : j' < (pairFst source).length)
      (he : out.length = BrouwerNashLayout.sampleBase (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t' +
        2 + 2 * (pairFst source).length * a'.val + 2 * j' + s'.val) :
      t = t' ∧ axis = a' ∧ next = s' ∧ j = j' := by
    apply extraction_injective (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
      t t' axis a' next s' j j' hj hj'
    simpa only [BrouwerNashLayout.digit, Nat.add_assoc] using ho.symm.trans he
  rw [Finset.sum_eq_single t]
  · rw [Finset.sum_eq_single axis]
    · rw [Finset.sum_eq_single next]
      · rw [Finset.sum_eq_single j]
        · apply ite_eq_left
          simpa only [BrouwerNashLayout.digit, Nat.add_assoc] using ho
        · intro j' hj' hne
          apply ite_eq_right
          intro he
          exact hne (hhit t axis next j' (Finset.mem_range.mp hj') he).2.2.2.symm
        · intro hno
          exact False.elim (hno (Finset.mem_range.mpr hj))
      · intro s' _ hne
        apply Finset.sum_eq_zero
        intro j' hj'
        apply ite_eq_right
        intro he
        exact hne (hhit t axis s' j' (Finset.mem_range.mp hj') he).2.2.1.symm
      · simp
    · intro a' _ hne
      apply Finset.sum_eq_zero
      intro s' _
      apply Finset.sum_eq_zero
      intro j' hj'
      apply ite_eq_right
      intro he
      exact hne (hhit t a' s' j' (Finset.mem_range.mp hj') he).2.1.symm
    · simp
  · intro t' _ hne
    apply Finset.sum_eq_zero
    intro a' _
    apply Finset.sum_eq_zero
    intro s' _
    apply Finset.sum_eq_zero
    intro j' hj'
    apply ite_eq_right
    intro he
    exact hne (hhit t' a' s' j' (Finset.mem_range.mp hj') he).1.symm
  · simp
/-- Extraction emits zero outside every sample's contiguous extraction interval. -/
theorem coefficientWord_eq_zero_of_outside (out action source code₀ code₁ : List Bool)
    (hno : ∀ t : Fin 41,
      ¬ (BrouwerNashLayout.sampleBase (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t + 2 ≤
          out.length ∧
        out.length < BrouwerNashLayout.sampleBase (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
            2 + 4 * (pairFst source).length)) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) = 0 := by
  apply coefficientWord_eq_zero
  intro t axis next j hj he
  apply hno t
  have ha := axis.isLt
  have hn := next.isLt
  have hm := Nat.mul_le_mul_left (2 * (pairFst source).length)
    (show axis.val ≤ 1 by omega)
  dsimp only [BrouwerNashLayout.digit] at he
  omega
/-- The contiguous extraction interval consists exactly of two-bit digit stages on two axes. -/
theorem exists_extractionSlot (b i : ℕ) (hlo : 2 ≤ i) (hhi : i < 2 + 4 * b) :
    ∃ (axis stage : Fin 2) (j : ℕ), j < b ∧
      i = BrouwerNashLayout.digit b axis j + stage.val := by
  by_cases hfirst : i < 2 + 2 * b
  · refine ⟨0, ⟨(i - 2) % 2, Nat.mod_lt _ (by omega)⟩, (i - 2) / 2, ?_, ?_⟩
    · omega
    · simp only [BrouwerNashLayout.digit, Fin.val_zero, mul_zero, add_zero]
      omega
  · refine ⟨1, ⟨(i - 2 - 2 * b) % 2, Nat.mod_lt _ (by omega)⟩,
      (i - 2 - 2 * b) / 2, ?_, ?_⟩
    · omega
    · simp only [BrouwerNashLayout.digit, Fin.val_one, mul_one]
      omega

/-- Every extraction slot selects its canonical digit or remainder gate. -/
theorem sampleGate_extraction_of_interval (b i : ℕ)
    (raw₀ raw₁ : _root_.Complexity.CircuitCode.RawCircuit) (t : Fin 41)
    (hlo : 2 ≤ i) (hhi : i < 2 + 4 * b) :
    ∃ (axis stage : Fin 2) (j : ℕ), j < b ∧
      i = BrouwerNashLayout.digit b axis j + stage.val ∧
      BrouwerNashProgram.sampleGate b raw₀ raw₁ t i =
        if stage.val = 0 then GameTheory.Finite.BimatrixBinaryExtraction.digitGate
          (BrouwerNashProgram.sampleRef b raw₀.length raw₁.length t
            (BrouwerNashLayout.remainder b axis j))
        else GameTheory.Finite.BimatrixBinaryExtraction.remainderGate
          (BrouwerNashProgram.sampleRef b raw₀.length raw₁.length t
            (BrouwerNashLayout.remainder b axis j))
          (BrouwerNashProgram.sampleRef b raw₀.length raw₁.length t
            (BrouwerNashLayout.digit b axis j)) := by
  obtain ⟨axis, stage, j, hj, hi⟩ := exists_extractionSlot b i hlo hhi
  refine ⟨axis, stage, j, hj, hi, ?_⟩
  rw [hi]
  exact BrouwerNashProgram.sampleGate_extraction b raw₀ raw₁ t axis j hj stage
end GameTheory.Complexity.Backend.BrouwerNashExtractionQuery
