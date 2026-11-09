module

public import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
public import GameTheoryComplexity.Backend.BrouwerNashHeaders
public import GameTheoryComplexity.Backend.BinarySignedIndicator
public import GameTheoryComplexity.Backend.BinarySignedFiniteSum
public import GameTheoryComplexity.Backend.BinaryUnaryEncoding
public import GameTheoryComplexity.Backend.BrouwerNashProgram

@[expose] public section

/-! Jitter coefficients preserve signed sample offsets and both affine input
contributions. Ordinal callbacks use canonical false rulers; all other query words
retain their exact contents through the native captured context. -/
namespace GameTheory.Complexity.Backend.BrouwerNashJitterQuery
open Turing.MultiTapeTM
open scoped BigOperators

private def term (axis : Bool) (ordinal out action source code₀ code₁ : List Bool) : List Bool :=
  let dim := BrouwerNashHeaders.dimensionRuler source code₀ code₁
  let capacity := [false, false] ++ binaryLengthWord dim
  let shift := binarySignedSub (false :: binaryLengthWord ordinal)
    [false, false, false, true, false, true]
  let output := BrouwerNashHeaders.globalRuler source ++
    List.replicate (ordinal.length * (BrouwerNashHeaders.sampleRuler source code₀ code₁).length) true ++
      (if axis then [false] else [])
  let input := BrouwerNashHeaders.precisionRuler source ++ List.replicate 3 false
  let value := binarySignedAdd
    (binarySignedIndicator ![action, if axis then [false] else [], capacity])
    (binarySignedIndicator ![action, input, binarySignedMul capacity shift])
  if out.length = output.length then value else []

/-- Both axes retain all forty-one signed jitter contributions in their original order. -/
def coefficientWord (source code₀ code₁ out action : List Bool) : List Bool :=
  let query (axis : Bool) (ordinal : List Bool)
      (context : (List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) : List Bool :=
    let source := context.1.1
    let code₀ := context.1.2.1
    let code₁ := context.1.2.2
    let out := context.2.1
    let action := context.2.2
    let dim := BrouwerNashHeaders.dimensionRuler source code₀ code₁
    let capacity := [false, false] ++ binaryLengthWord dim
    let shift := binarySignedSub (false :: binaryLengthWord ordinal)
      [false, false, false, true, false, true]
    let output := BrouwerNashHeaders.globalRuler source ++
      List.replicate (ordinal.length * (BrouwerNashHeaders.sampleRuler source code₀ code₁).length) true ++
        (if axis then [false] else [])
    let input := BrouwerNashHeaders.precisionRuler source ++ List.replicate 3 false
    let value := binarySignedAdd
      (binarySignedIndicator ![action, if axis then [false] else [], capacity])
      (binarySignedIndicator ![action, input, binarySignedMul capacity shift])
    if out.length = output.length then value else []
  let context := ((source, (code₀, code₁)), (out, action))
  binarySignedAdd (binarySignedFiniteSum (query false) 41 context)
    (binarySignedFiniteSum (query true) 41 context)

private theorem term_polyTime (axis : Bool) {Input : Type} {inputEncoding : Input ↪ List Bool}
    {ordinal out action source code₀ code₁ : Input → List Bool}
    (hi : ComputableInPolyTime ordinal inputEncoding encBits)
    (ho : ComputableInPolyTime out inputEncoding encBits)
    (ha : ComputableInPolyTime action inputEncoding encBits)
    (hs : ComputableInPolyTime source inputEncoding encBits)
    (hc₀ : ComputableInPolyTime code₀ inputEncoding encBits)
    (hc₁ : ComputableInPolyTime code₁ inputEncoding encBits) :
    ComputableInPolyTime
      (fun a => term axis (ordinal a) (out a) (action a) (source a) (code₀ a) (code₁ a))
      inputEncoding encBits := by
  have hd := BrouwerNashHeaders.dimensionRuler_polyTime hs hc₀ hc₁
  have hcapacity := ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [false, false])
    (binaryLengthWord_polyTime.comp hd)
  have hshift := binarySignedSub_polyTime
    (ComputableInPolyTime.bitsCons (ComputableInPolyTime.const false)
      (binaryLengthWord_polyTime.comp hi))
    (ComputableInPolyTime.const [false, false, false, true, false, true])
  have houtput := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend (BrouwerNashHeaders.globalRuler_polyTime hs)
      ((ComputableInPolyTime.bitsReplicate true).comp
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp hi)
          (ComputableInPolyTime.length_bits_comp
            (BrouwerNashHeaders.sampleRuler_polyTime hs hc₀ hc₁)))))
    (ComputableInPolyTime.const (if axis then [false] else []))
  have hinput := ComputableInPolyTime.bitsAppend (BrouwerNashHeaders.precisionRuler_polyTime hs)
    (ComputableInPolyTime.const (List.replicate 3 false))
  have hfirstArgs : ComputableInPolyTime (fun a : Input =>
      ![action a, if axis then [false] else [],
        [false, false] ++ binaryLengthWord (BrouwerNashHeaders.dimensionRuler
          (source a) (code₀ a) (code₁ a))]) inputEncoding (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact ha
    · exact ComputableInPolyTime.const (if axis then [false] else [])
    · simpa only [Matrix.cons_val_succ', Matrix.cons_val_zero', Function.comp_apply] using hcapacity
  have hfirst := binarySignedIndicator_polyTime.comp hfirstArgs
  have hproduct := binarySignedMul_polyTime hcapacity hshift
  have hsecondArgs : ComputableInPolyTime (fun a : Input =>
      ![action a, BrouwerNashHeaders.precisionRuler (source a) ++ List.replicate 3 false,
        binarySignedMul ([false, false] ++ binaryLengthWord
          (BrouwerNashHeaders.dimensionRuler (source a) (code₀ a) (code₁ a)))
          (binarySignedSub (false :: binaryLengthWord (ordinal a))
            [false, false, false, true, false, true])]) inputEncoding (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact ha
    · exact hinput
    · simpa only [Matrix.cons_val_succ', Matrix.cons_val_zero', Function.comp_apply] using hproduct
  have hsecond := binarySignedIndicator_polyTime.comp hsecondArgs
  have hvalue := binarySignedAdd_polyTime hfirst hsecond
  have heq := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.decide_eq encUnary).comp
      ((ComputableInPolyTime.length_bits_comp ho).tidy.prod
        (ComputableInPolyTime.length_bits_comp houtput).tidy))
  exact (heq.ite hvalue (ComputableInPolyTime.const [])).of_enc_eq (fun a => by
    simp only [term, Function.comp_apply, decide_eq_true_eq])

private theorem callback_polyTime (axis : Bool) :
    ComputableInPolyTime
      (fun p : ((List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) × List Bool =>
        term axis p.2 p.1.2.1 p.1.2.2 p.1.1.1 p.1.1.2.1 p.1.1.2.2)
      (encPair (encPair (encPair encBits (encPair encBits encBits))
        (encPair encBits encBits)) encBits) encBits := by
  have hcontext := ComputableInPolyTime.fst
    (encPair (encPair encBits (encPair encBits encBits)) (encPair encBits encBits)) encBits
  have hi := ComputableInPolyTime.snd
    (encPair (encPair encBits (encPair encBits encBits)) (encPair encBits encBits)) encBits
  exact term_polyTime axis hi hcontext.snd'.fst' hcontext.snd'.snd'
    hcontext.fst'.fst' hcontext.fst'.snd'.fst' hcontext.fst'.snd'.snd'

/-- Joint query certificates charge source, circuit words and both original query rulers. -/
@[fun_prop] theorem coefficientWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => coefficientWord (source a) (code₀ a) (code₁ a)
      (out a) (action a)) input encBits := by
  have hcontext := (hs.prod (hc₀.prod hc₁)).prod (ho.prod ha)
  exact binarySignedAdd_polyTime
    (binarySignedFiniteSum_polyTime (callback_polyTime false) 41 hcontext)
    (binarySignedFiniteSum_polyTime (callback_polyTime true) 41 hcontext)

private theorem capacity_value (r : List Bool) :
    binarySignedValue ([false, false] ++ binaryLengthWord r) = 2 * (r.length : ℤ) := by
  change ((2 * ofBits (binaryLengthWord r) : ℕ) : ℤ) = _
  rw [binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]

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
    binarySignedValue (term axis (List.replicate t.val false) out action source code₀ code₁) =
      if out.length = BrouwerNashLayout.sampleBase (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
          (if axis then 1 else 0) then
        (if action.length / 2 = (if axis then 1 else 0) ∧ action.length % 2 = 1
          then 2 * (BrouwerNashLayout.dimension (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0) +
        (if action.length / 2 = BrouwerNashLayout.precision (CircuitWords.first source).length + 3 ∧
            action.length % 2 = 1 then
          2 * (BrouwerNashLayout.dimension (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) *
            ((t.val : ℤ) - 20) else 0)
      else 0 := by
  change binarySignedValue (if out.length =
    (BrouwerNashHeaders.globalRuler source ++
      List.replicate ((List.replicate t.val false).length *
        (BrouwerNashHeaders.sampleRuler source code₀ code₁).length) true ++
      (if axis then [false] else [])).length then
    binarySignedAdd
      (binarySignedIndicator ![action, if axis then [false] else [],
        [false, false] ++ binaryLengthWord
          (BrouwerNashHeaders.dimensionRuler source code₀ code₁)])
      (binarySignedIndicator ![action,
        BrouwerNashHeaders.precisionRuler source ++ List.replicate 3 false,
        binarySignedMul ([false, false] ++ binaryLengthWord
          (BrouwerNashHeaders.dimensionRuler source code₀ code₁))
          (binarySignedSub (false :: binaryLengthWord (List.replicate t.val false))
            [false, false, false, true, false, true])]) else []) = _
  rw [BrouwerNashCoefficientQuery.select_value, binarySignedAdd_value,
    binarySignedIndicator_value, binarySignedIndicator_value, binarySignedMul_value,
    capacity_value, shift_value]
  simp only [List.length_append, List.length_replicate,
    BrouwerNashHeaders.dimensionRuler_length, BrouwerNashHeaders.precisionRuler_length,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length]
  cases axis <;> rfl

private theorem term_coefficients (axis : Bool) (out action source code₀ code₁ : List Bool)
    (t : Fin 41)
    (r : Fin (BrouwerNashLayout.dimension (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (term axis (List.replicate t.val false) out action source code₀ code₁) =
      if out.length = BrouwerNashLayout.sampleBase (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
          (if axis then 1 else 0) then
        (BrouwerNashProgram.affine₂
          (BrouwerNashProgram.slot (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
            (if axis then 1 else 0))
          (BrouwerNashProgram.slot (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
            (BrouwerNashLayout.alpha (BrouwerNashLayout.precision (CircuitWords.first source).length)))
          (2 * (BrouwerNashLayout.dimension (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ))
          (2 * (BrouwerNashLayout.dimension (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) *
            ((t.val : ℤ) - 20)) 0).coefficients r else 0 := by
  have hg : BrouwerNashLayout.globalCount (CircuitWords.first source).length <
      BrouwerNashLayout.dimension (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length :=
    (Nat.le_add_right _ _).trans_lt (BrouwerNashLayout.allocated_lt_dimension _ _ _)
  have hp : 0 < BrouwerNashLayout.precision (CircuitWords.first source).length := by
    simp only [BrouwerNashLayout.precision]
    omega
  have ha : (if axis then 1 else 0) <
      BrouwerNashLayout.dimension (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    have hglobal : 1 < BrouwerNashLayout.globalCount (CircuitWords.first source).length := by
      simp only [BrouwerNashLayout.globalCount]
      omega
    cases axis <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      omega
  have hz : BrouwerNashLayout.alpha (BrouwerNashLayout.precision (CircuitWords.first source).length) =
      BrouwerNashLayout.precision (CircuitWords.first source).length + 3 := by
    simp only [BrouwerNashLayout.alpha, ite_eq_right hp.ne']
    omega
  have haz : BrouwerNashLayout.alpha (BrouwerNashLayout.precision (CircuitWords.first source).length) <
      BrouwerNashLayout.dimension (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    rw [hz]
    have hglobal : BrouwerNashLayout.precision (CircuitWords.first source).length + 3 <
        BrouwerNashLayout.globalCount (CircuitWords.first source).length := by
      simp only [BrouwerNashLayout.globalCount]
      omega
    omega
  rw [term_value, hr, BrouwerNashCoefficientQuery.affine₂_coefficients]
  have hx := BrouwerNashCoefficientQuery.pairedAction_iff r
    (BrouwerNashProgram.slot (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
      (if axis then 1 else 0))
  rw [BrouwerNashProgram.slot_val _ _ _ _ ha] at hx
  have hy := BrouwerNashCoefficientQuery.pairedAction_iff r
    (BrouwerNashProgram.slot (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
      (BrouwerNashLayout.alpha (BrouwerNashLayout.precision (CircuitWords.first source).length)))
  rw [BrouwerNashProgram.slot_val _ _ _ _ haz, hz] at hy
  simp only [hz, hx, hy]

/-- Each jitter output selects its canonical signed affine coefficients. -/
theorem coefficientWord_value (out action source code₀ code₁ : List Bool)
    (r : Fin (BrouwerNashLayout.dimension (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord source code₀ code₁ out action) =
      ∑ axis : Fin 2, ∑ t : Fin 41,
        if out.length = BrouwerNashLayout.sampleBase (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t + axis.val then
          (BrouwerNashProgram.affine₂
            (BrouwerNashProgram.slot (CircuitWords.first source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length axis.val)
            (BrouwerNashProgram.slot (CircuitWords.first source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
              (BrouwerNashLayout.alpha (BrouwerNashLayout.precision (CircuitWords.first source).length)))
            (2 * (BrouwerNashLayout.dimension (CircuitWords.first source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ))
            (2 * (BrouwerNashLayout.dimension (CircuitWords.first source).length
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
    (r : Fin (BrouwerNashLayout.dimension (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val)
    (ho : out.length = BrouwerNashLayout.sampleBase (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t + axis.val) :
    binarySignedValue (coefficientWord source code₀ code₁ out action) =
      (BrouwerNashProgram.affine₂
        (BrouwerNashProgram.slot (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length axis.val)
        (BrouwerNashProgram.slot (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
          (BrouwerNashLayout.alpha (BrouwerNashLayout.precision (CircuitWords.first source).length)))
        (2 * (BrouwerNashLayout.dimension (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ))
        (2 * (BrouwerNashLayout.dimension (CircuitWords.first source).length
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
    (r : Fin (BrouwerNashLayout.dimension (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val)
    (hno : ∀ t : Fin 41,
      ¬ (BrouwerNashLayout.sampleBase (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t ≤ out.length ∧
        out.length < BrouwerNashLayout.sampleBase (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t + 2)) :
    binarySignedValue (coefficientWord source code₀ code₁ out action) = 0 := by
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
