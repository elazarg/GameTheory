import GameTheoryComplexity.Backend.BrouwerNashGlobalQuery
import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery



/-! Exact coefficient and affine-kind agreement for every shared feedback-program output. -/
namespace GameTheory.Complexity.Backend.BrouwerNashGlobalQuery
open _root_.Complexity
open GameTheory.Finite BrouwerNashLayout BrouwerNashProgram BrouwerNashCoefficientQuery

private theorem shared_lt_dimension (b ell₀ ell₁ i : ℕ) (hi : i < globalCount b) :
    i < dimension b ell₀ ell₁ := by
  have h := allocated_lt_dimension b ell₀ ell₁
  omega

private theorem affine₁_numeric {k : ℕ} (a : Fin k) (ca : ℤ) (r : Fin (k * 2)) :
    (BimatrixArithmeticGate.gate (fun j => if j = a then ca else 0) 0).coefficients r =
      if r.val / 2 = a.val ∧ r.val % 2 = 1 then ca else 0 := by
  simp only [affine₁_coefficients, ← pairedAction_iff]

/-- The complete shared query agrees at each alpha-chain output. -/
theorem coefficientWord_alpha (out action source code₀ code₁ : List Bool)
    (j : ℕ) (hj : j < precision (pairFst source).length)
    (ho : out.length = 4 + j)
    (r : Fin (dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      (BimatrixDyadicGate.halvingGate (slot (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
        (alpha j))).coefficients r := by
  have hT : 50 ≤ precision (pairFst source).length := by unfold precision; omega
  rw [coefficientWord_expansion, alphaWord_value, oneWord_value, positiveWord_value,
    doubleWord_value, doubleWord_value, negativeWord_value, negativeWord_value,
    halfWord_value, halfWord_value, subtractWord_value, subtractWord_value,
    BrouwerNashAverageQuery.coefficientWord_value _ _ _ _ _ r hr]
  simp (disch := omega) only [ho, BrouwerNashLayout.positive,
    BrouwerNashLayout.feedbackSub, BrouwerNashLayout.feedbackHalf, BrouwerNashLayout.average,
    Fin.val_zero, Fin.val_one, zero_mul, one_mul,
    ite_eq_left, ite_eq_right, add_zero]
  change _ = (BimatrixArithmeticGate.gate (fun z => if z = slot _ _ _ (alpha j)
    then (dimension _ _ _ : ℤ) else 0) 0).coefficients r
  rw [affine₁_numeric, slot_val]
  · simp only [hr, Nat.add_sub_cancel_left]
  · apply shared_lt_dimension
    unfold alpha one globalCount
    split_ifs <;> omega

/-- The positive shared block emits its exact integer scaling coefficient. -/
theorem coefficientWord_positive (out action source code₀ code₁ : List Bool)
    (ho : out.length = positive (pairFst source).length)
    (r : Fin (dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      (positiveGate (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length).coefficients r := by
  have hT : 50 ≤ precision (pairFst source).length := by unfold precision; omega
  rw [coefficientWord_expansion, alphaWord_value, oneWord_value, positiveWord_value,
    doubleWord_value, doubleWord_value, negativeWord_value, negativeWord_value,
    halfWord_value, halfWord_value, subtractWord_value, subtractWord_value,
    BrouwerNashAverageQuery.coefficientWord_value _ _ _ _ _ r hr]
  simp (disch := omega) only [ho, BrouwerNashLayout.positive,
    BrouwerNashLayout.feedbackSub, BrouwerNashLayout.feedbackHalf, BrouwerNashLayout.average,
    Fin.val_zero, Fin.val_one, zero_mul, one_mul,
    ite_eq_left, ite_eq_right, ite_true, zero_add, add_zero]
  unfold positiveGate
  rw [affine₁_numeric, slot_val]
  · rw [hr]
  · apply shared_lt_dimension
    unfold alpha one globalCount
    split_ifs <;> omega

/-- The constant-one output retains the normalized affine offset. -/
theorem coefficientWord_one (out action source code₀ code₁ : List Bool)
    (ho : out.length = one)
    (r : Fin (dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) = 2 := by
  have hT : 50 ≤ precision (pairFst source).length := by unfold precision; omega
  rw [coefficientWord_expansion, alphaWord_value, oneWord_value, positiveWord_value,
    doubleWord_value, doubleWord_value, negativeWord_value, negativeWord_value,
    halfWord_value, halfWord_value, subtractWord_value, subtractWord_value,
    BrouwerNashAverageQuery.coefficientWord_value _ _ _ _ _ r hr]
  simp (disch := omega) only [ho, BrouwerNashLayout.one, BrouwerNashLayout.positive,
    BrouwerNashLayout.feedbackSub, BrouwerNashLayout.feedbackHalf, BrouwerNashLayout.average,
    Fin.val_zero, Fin.val_one, zero_mul, one_mul,
    ite_eq_left, ite_eq_right, ite_true, zero_add, add_zero]

/-- The shared zero block and unallocated padding emit zero coefficients. -/
theorem coefficientWord_zero (out action source code₀ code₁ : List Bool)
    (ho : out.length = zero ∨ globalCount (pairFst source).length ≤ out.length)
    (r : Fin (dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) = 0 := by
  have hT : 50 ≤ precision (pairFst source).length := by unfold precision; omega
  have hcases : out.length = 3 ∨ 3 * precision (pairFst source).length + 11 ≤ out.length := by
    simpa only [zero, globalCount] using ho
  rw [coefficientWord_expansion, alphaWord_value, oneWord_value, positiveWord_value,
    doubleWord_value, doubleWord_value, negativeWord_value, negativeWord_value,
    halfWord_value, halfWord_value, subtractWord_value, subtractWord_value,
    BrouwerNashAverageQuery.coefficientWord_value _ _ _ _ _ r hr]
  rcases hcases with hzero | hlarge
  · simp (disch := omega) [hzero, BrouwerNashLayout.positive,
      BrouwerNashLayout.feedbackSub, BrouwerNashLayout.feedbackHalf, BrouwerNashLayout.average]
  · have hnonempty : out ≠ [] := by
      intro h
      subst out
      simp only [List.length_nil] at hlarge
      omega
    simp (disch := omega) [BrouwerNashLayout.positive,
      BrouwerNashLayout.feedbackSub, BrouwerNashLayout.feedbackHalf, BrouwerNashLayout.average,
      hnonempty]
    split_ifs <;> omega

/-- Both coordinate outputs use their own final feedback doubling block. -/
theorem coefficientWord_coordinate (out action source code₀ code₁ : List Bool)
    (axis : Fin 2) (ho : out.length = coordinate axis)
    (r : Fin (dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      (BimatrixFeedbackGate.doubleGate (slot (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
        (feedbackSub (pairFst source).length axis))).coefficients r := by
  have hT : 50 ≤ precision (pairFst source).length := by unfold precision; omega
  rw [coefficientWord_expansion, alphaWord_value, oneWord_value, positiveWord_value,
    doubleWord_value, doubleWord_value, negativeWord_value, negativeWord_value,
    halfWord_value, halfWord_value, subtractWord_value, subtractWord_value,
    BrouwerNashAverageQuery.coefficientWord_value _ _ _ _ _ r hr]
  change _ = (BimatrixArithmeticGate.gate (fun z => if z = slot _ _ _
    (feedbackSub (pairFst source).length axis) then 4 * (dimension _ _ _ : ℤ) else 0)
    0).coefficients r
  rw [affine₁_numeric, slot_val]
  · fin_cases axis <;>
      simp (disch := omega) only [ho, BrouwerNashLayout.coordinate, hr,
        BrouwerNashLayout.positive, BrouwerNashLayout.feedbackSub,
        BrouwerNashLayout.feedbackHalf, BrouwerNashLayout.average,
        Fin.val_zero, Fin.val_one, zero_mul, one_mul, mul_zero, mul_one,
        ite_eq_left, ite_eq_right, ite_true, zero_add, add_zero]
  · apply shared_lt_dimension
    have ha := axis.isLt
    unfold feedbackSub feedbackHalf globalCount
    omega

/-- The mean output selects exactly its canonical finite color-mean coefficient. -/
theorem coefficientWord_average (out action source code₀ code₁ : List Bool)
    (axis : Fin 2) (ho : out.length = average (pairFst source).length axis)
    (r : Fin (dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      (averageGate (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
        axis).coefficients r := by
  have hT : 50 ≤ precision (pairFst source).length := by unfold precision; omega
  rw [coefficientWord_expansion, alphaWord_value, oneWord_value, positiveWord_value,
    doubleWord_value, doubleWord_value, negativeWord_value, negativeWord_value,
    halfWord_value, halfWord_value, subtractWord_value, subtractWord_value,
    BrouwerNashAverageQuery.coefficientWord_value _ _ _ _ _ r hr]
  fin_cases axis <;>
    simp (disch := omega) only [ho, BrouwerNashLayout.positive,
      BrouwerNashLayout.feedbackSub, BrouwerNashLayout.feedbackHalf, BrouwerNashLayout.average,
      Fin.val_zero, Fin.val_one, zero_mul, one_mul, mul_zero, mul_one,
      ite_eq_left, ite_eq_right, ite_true, zero_add, add_zero]
  all_goals rfl

/-- Every negative-mean halving output selects the exact predecessor in its coordinate chain. -/
theorem coefficientWord_negative (out action source code₀ code₁ : List Bool)
    (axis : Fin 2) (j : ℕ) (hj : j < precision (pairFst source).length)
    (ho : out.length = negative (pairFst source).length axis (j + 1))
    (r : Fin (dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      (BimatrixDyadicGate.halvingGate (slot (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
        (negative (pairFst source).length axis j))).coefficients r := by
  have hT : 50 ≤ precision (pairFst source).length := by unfold precision; omega
  have ho' : out.length = precision (pairFst source).length + 7 +
      axis.val * precision (pairFst source).length + j := by
    simpa only [negative, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel] using ho
  rw [coefficientWord_expansion, alphaWord_value, oneWord_value, positiveWord_value,
    doubleWord_value, doubleWord_value, negativeWord_value, negativeWord_value,
    halfWord_value, halfWord_value, subtractWord_value, subtractWord_value,
    BrouwerNashAverageQuery.coefficientWord_value _ _ _ _ _ r hr]
  change _ = (BimatrixArithmeticGate.gate (fun z => if z = slot _ _ _
    (negative (pairFst source).length axis j) then (dimension _ _ _ : ℤ) else 0)
    0).coefficients r
  rw [affine₁_numeric, slot_val]
  · fin_cases axis <;>
      simp (disch := omega) only [ho', hr, BrouwerNashLayout.positive,
        BrouwerNashLayout.feedbackSub, BrouwerNashLayout.feedbackHalf, BrouwerNashLayout.average,
        Fin.val_zero, Fin.val_one, zero_mul, one_mul, mul_zero, mul_one,
        Nat.add_sub_cancel_left,
        ite_eq_left, ite_eq_right, zero_add, add_zero]
    all_goals rfl
  · apply shared_lt_dimension
    fin_cases axis <;> simp only [negative, average, globalCount, zero_mul, one_mul] <;>
      split_ifs <;> omega

private theorem halfAdd_numeric {k : ℕ} (a z : Fin k) (r : Fin (k * 2)) :
    (BimatrixFeedbackGate.halfAddGate a z).coefficients r =
      (if r.val / 2 = a.val ∧ r.val % 2 = 1 then (k : ℤ) else 0) +
      (if r.val / 2 = z.val ∧ r.val % 2 = 1 then (k : ℤ) else 0) := by
  change (affine₂ a z (k : ℤ) k 0).coefficients r = _
  simp only [affine₂_coefficients, ← pairedAction_iff]

private theorem subtractHalf_numeric {k : ℕ} (a z : Fin k) (r : Fin (k * 2)) :
    (BimatrixFeedbackGate.subtractHalfGate a z).coefficients r =
      (if r.val / 2 = a.val ∧ r.val % 2 = 1 then 2 * (k : ℤ) else 0) +
      (if r.val / 2 = z.val ∧ r.val % 2 = 1 then -(k : ℤ) else 0) := by
  have hgate : BimatrixFeedbackGate.subtractHalfGate a z =
      affine₂ a z (2 * (k : ℤ)) (-k) 0 := by
    unfold BimatrixFeedbackGate.subtractHalfGate affine₂
    congr 1
    funext j
    simp only [BimatrixFeedbackGate.subtractHalfCoefficients, sub_eq_add_neg]
    split_ifs <;> simp
  rw [hgate]
  simp only [affine₂_coefficients, ← pairedAction_iff]

/-- Both auxiliary feedback stages reproduce their canonical affine factories. -/
theorem coefficientWord_feedback (out action source code₀ code₁ : List Bool)
    (axis stage : Fin 2)
    (ho : out.length = feedbackHalf (pairFst source).length axis + stage.val)
    (r : Fin (dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      (globalGate (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
        (feedbackHalf (pairFst source).length axis + stage.val)).coefficients r := by
  have hT : 50 ≤ precision (pairFst source).length := by unfold precision; omega
  have hq : coordinate axis < dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    apply shared_lt_dimension
    have ha := axis.isLt
    unfold coordinate globalCount
    omega
  have hp : positive (pairFst source).length < dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    apply shared_lt_dimension
    unfold positive globalCount
    omega
  have hh : feedbackHalf (pairFst source).length axis < dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    apply shared_lt_dimension
    have ha := axis.isLt
    unfold feedbackHalf globalCount
    omega
  have hn : negative (pairFst source).length axis (precision (pairFst source).length) <
      dimension (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    apply shared_lt_dimension
    fin_cases axis <;> simp only [negative, average, globalCount, zero_mul, one_mul] <;>
      split_ifs <;> omega
  rw [coefficientWord_expansion, alphaWord_value, oneWord_value, positiveWord_value,
    doubleWord_value, doubleWord_value, negativeWord_value, negativeWord_value,
    halfWord_value, halfWord_value, subtractWord_value, subtractWord_value,
    BrouwerNashAverageQuery.coefficientWord_value _ _ _ _ _ r hr, globalGate_feedback]
  fin_cases stage
  · simp only [Fin.val_zero, ite_true]
    rw [halfAdd_numeric, slot_val _ _ _ _ hq, slot_val _ _ _ _ hp]
    fin_cases axis <;>
      simp (disch := omega) only [ho, hr, BrouwerNashLayout.coordinate,
        BrouwerNashLayout.positive, BrouwerNashLayout.feedbackSub,
        BrouwerNashLayout.feedbackHalf, BrouwerNashLayout.average,
        Fin.val_zero, Fin.val_one, zero_mul, one_mul, mul_zero, mul_one,
        ite_eq_left, ite_eq_right, ite_true, zero_add, add_zero]
    all_goals rfl
  · simp only [Fin.val_one, Nat.one_ne_zero, ite_false]
    rw [subtractHalf_numeric, slot_val _ _ _ _ hh, slot_val _ _ _ _ hn]
    fin_cases axis <;>
      simp (disch := omega) only [ho, hr, BrouwerNashLayout.positive,
        BrouwerNashLayout.feedbackSub, BrouwerNashLayout.feedbackHalf, BrouwerNashLayout.average,
        Fin.val_zero, Fin.val_one, zero_mul, one_mul, mul_zero, mul_one,
        ite_eq_left, ite_eq_right, ite_true, zero_add, add_zero]
    all_goals rfl

/-- The actual polynomial-time shared selector agrees with every allocated global gate. -/
theorem coefficientWord_value (out action source code₀ code₁ : List Bool)
    (r : Fin (dimension (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      if out.length < globalCount (pairFst source).length then
        (globalGate (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
          out.length).coefficients r else 0 := by
  let b := (pairFst source).length
  let ell₀ := (circuitUnaryPrefix code₀).length
  let ell₁ := (circuitUnaryPrefix code₁).length
  change _ = if out.length < globalCount b then
    (globalGate b ell₀ ell₁ out.length).coefficients r else 0
  have hT : 50 ≤ precision b := by unfold precision; omega
  by_cases hg : out.length < globalCount b
  · rw [ite_eq_left hg]
    by_cases hq : out.length < 2
    · let axis : Fin 2 := ⟨out.length, hq⟩
      have ho : out.length = coordinate axis := rfl
      rw [ho, globalGate_coordinate]
      exact coefficientWord_coordinate _ _ _ _ _ axis ho r hr
    by_cases h1 : out.length = one
    · rw [h1, globalGate_one, coefficientWord_one _ _ _ _ _ h1 r hr]
      simp [BimatrixArithmeticGate.gate, BimatrixArithmeticGate.coefficients]
    by_cases h0 : out.length = zero
    · rw [h0, globalGate_zero, coefficientWord_zero _ _ _ _ _ (Or.inl h0) r hr]
      simp [BimatrixArithmeticGate.gate, BimatrixArithmeticGate.coefficients]
    have h4 : 4 ≤ out.length := by simp only [one] at h1; simp only [zero] at h0; omega
    by_cases ha : out.length < positive b
    · let j := out.length - 4
      have hj : j < precision b := by unfold j; simp only [positive] at ha; omega
      have ho : out.length = 4 + j := by unfold j; omega
      have he : out.length = alpha (j + 1) := by
        rw [ho]
        simp [alpha]
        omega
      rw [he, globalGate_alpha _ _ _ _ hj]
      exact coefficientWord_alpha _ _ _ _ _ j hj ho r hr
    by_cases hp : out.length = positive b
    · rw [hp, globalGate_positive]
      exact coefficientWord_positive _ _ _ _ _ hp r hr
    by_cases hm : out.length < precision b + 7
    · have hlo : precision b + 5 ≤ out.length := by simp only [positive] at ha hp; omega
      let axis : Fin 2 := ⟨out.length - (precision b + 5), by omega⟩
      have ho : out.length = average b axis := by unfold average axis; simp only; omega
      rw [ho, globalGate_average]
      exact coefficientWord_average _ _ _ _ _ axis ho r hr
    by_cases hn : out.length < 3 * precision b + 7
    · by_cases hx : out.length < 2 * precision b + 7
      · let j := out.length - (precision b + 7)
        have hj : j < precision b := by unfold j; omega
        have ho : out.length = negative b 0 (j + 1) := by
          simp only [negative, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
            Fin.val_zero, zero_mul, add_zero, Nat.add_sub_cancel]
          unfold j
          omega
        rw [ho, globalGate_negative _ _ _ _ _ hj]
        exact coefficientWord_negative _ _ _ _ _ 0 j hj ho r hr
      · let j := out.length - (precision b + 7 + precision b)
        have hj : j < precision b := by unfold j; omega
        have ho : out.length = negative b 1 (j + 1) := by
          simp only [negative, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
            Fin.val_one, one_mul, Nat.add_sub_cancel]
          unfold j
          omega
        rw [ho, globalGate_negative _ _ _ _ _ hj]
        exact coefficientWord_negative _ _ _ _ _ 1 j hj ho r hr
    have hcases : out.length = 3 * precision b + 7 ∨
        out.length = 3 * precision b + 8 ∨ out.length = 3 * precision b + 9 ∨
        out.length = 3 * precision b + 10 := by
      simp only [globalCount] at hg
      omega
    rcases hcases with ho | ho | ho | ho
    · have he : out.length = feedbackHalf b 0 + (0 : Fin 2).val := by
        simp only [feedbackHalf, Fin.val_zero]
        omega
      rw [he]
      exact coefficientWord_feedback out action source code₀ code₁ 0 0 he r hr
    · have he : out.length = feedbackHalf b 0 + (1 : Fin 2).val := by
        simp only [feedbackHalf, Fin.val_zero, Fin.val_one]
        omega
      rw [he]
      exact coefficientWord_feedback out action source code₀ code₁ 0 1 he r hr
    · have he : out.length = feedbackHalf b 1 + (0 : Fin 2).val := by
        simp only [feedbackHalf, Fin.val_zero, Fin.val_one]
        omega
      rw [he]
      exact coefficientWord_feedback out action source code₀ code₁ 1 0 he r hr
    · have he : out.length = feedbackHalf b 1 + (1 : Fin 2).val := by
        simp only [feedbackHalf, Fin.val_one]
        omega
      rw [he]
      exact coefficientWord_feedback out action source code₀ code₁ 1 1 he r hr
  · rw [ite_eq_right hg]
    exact coefficientWord_zero _ _ _ _ _ (Or.inr (by change globalCount b ≤ out.length; omega)) r hr

/-- All global blocks use the canonical affine kind, including both feedback cycles. -/
theorem globalGate_kind (b ell₀ ell₁ i : ℕ) :
    (globalGate b ell₀ ell₁ i).kind = BimatrixGateProgram.GateKind.affine := by
  unfold globalGate
  split_ifs <;> rfl

end GameTheory.Complexity.Backend.BrouwerNashGlobalQuery
