import GameTheoryComplexity.Backend.BrouwerNashSelector
import GameTheoryComplexity.Backend.BrouwerNashQueryRegions

/-! Exact scalar correctness of the polynomial Brouwer Nash coefficient selector. Disjoint
numeric regions select the canonical gate factories; every other family contributes zero.
The theorem includes global wires, all sample regions, and unused padding blocks. -/
namespace GameTheory.Complexity.Backend.BrouwerNashSelectorCorrectness
open _root_.Complexity _root_.Complexity.CircuitCode
open GameTheory.Finite
open BrouwerNashLayout BrouwerNashProgram
open scoped BigOperators

private theorem interval_excluded (b e₀ e₁ out offset lo hi : ℕ) (t : Fin 41)
    (hlocal : offset < sampleWidth b e₀ e₁)
    (hout : out = sampleBase b e₀ e₁ t + offset) (hhi : hi ≤ sampleWidth b e₀ e₁)
    (haway : offset < lo ∨ hi ≤ offset) :
    ∀ s : Fin 41, ¬ (sampleBase b e₀ e₁ s + lo ≤ out ∧
      out < sampleBase b e₀ e₁ s + hi) := by
  intro s hs
  have he := BrouwerNashQueryRegions.sampleOutput_interval_unique b e₀ e₁ out offset t s
    hlocal hout (by omega)
  subst s
  omega

section Lengths
variable (out action source code₀ code₁ : List Bool) (e₀ e₁ : ℕ)
variable (hp₀ : (circuitUnaryPrefix code₀).length = e₀)
variable (hp₁ : (circuitUnaryPrefix code₁).length = e₁)
local notation "b" => List.length (pairFst source)
local notation "k" => dimension b e₀ e₁
include hp₀ hp₁

private theorem global_value (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (BrouwerNashGlobalQuery.coefficientWord
      ![out, action, source, code₀, code₁]) =
      if out.length < globalCount b then (globalGate b e₀ e₁ out.length).coefficients r
      else 0 := by
  subst e₀ e₁
  exact BrouwerNashGlobalQuery.coefficientWord_value out action source code₀ code₁ r hr

private theorem jitter_at (t : Fin 41) (axis : Fin 2) (r : Fin (k * 2))
    (hr : action.length = r.val) (hout : out.length = sampleBase b e₀ e₁ t + axis.val) :
    binarySignedValue (BrouwerNashJitterQuery.coefficientWord
      ![out, action, source, code₀, code₁]) =
      (affine₂ (slot b e₀ e₁ axis.val) (slot b e₀ e₁ (alpha (precision b)))
        (2 * (k : ℤ)) (2 * (k : ℤ) * ((t.val : ℤ) - 20)) 0).coefficients r := by
  subst e₀ e₁
  exact BrouwerNashJitterQuery.coefficientWord_at out action source code₀ code₁ t axis r hr hout

private theorem increment_at (t : Fin 41) (axis : Fin 2) (stage : Fin 4) (j : ℕ)
    (hj : j < b) (r : Fin (k * 2)) (hr : action.length = r.val)
    (hout : out.length = sampleBase b e₀ e₁ t + increment b axis j stage) :
    binarySignedValue (BrouwerNashIncrementQuery.allCoefficientWord
      ![out, action, source, code₀, code₁]) =
      (incrementGate b e₀ e₁ t axis j stage).coefficients r := by
  subst e₀ e₁
  exact BrouwerNashIncrementQuery.allCoefficientWord_at source code₀ code₁ out action
    axis stage t j hj hout r hr

private theorem interpolation_at (t : Fin 41) (stage : Fin 8) (r : Fin (k * 2))
    (hr : action.length = r.val)
    (hout : out.length = sampleBase b e₀ e₁ t + (weightBase b + stage.val)) :
    binarySignedValue (BrouwerNashInterpolationQuery.coefficientWord
      ![out, action, source, code₀, code₁]) =
      (interpolationGate b e₀ e₁ t stage.val).coefficients r := by
  subst e₀ e₁
  exact BrouwerNashInterpolationQuery.coefficientWord_interpolation_at source code₀ code₁
    out action stage t r hr hout

private theorem minimum_at (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    (r : Fin (k * 2)) (hr : action.length = r.val)
    (hout : out.length = sampleBase b e₀ e₁ t +
      (minimumTemporary b e₀ e₁ corner flag + (if temporary then 0 else 1))) :
    binarySignedValue (BrouwerNashInterpolationQuery.coefficientWord
      ![out, action, source, code₀, code₁]) =
      (minimumGate b e₀ e₁ t corner flag temporary).coefficients r := by
  subst e₀ e₁
  exact BrouwerNashInterpolationQuery.coefficientWord_minimum_at source code₀ code₁
    out action corner flag temporary t r hr hout

private theorem jitter_zero (r : Fin (k * 2)) (hr : action.length = r.val)
    (hno : ∀ t : Fin 41, ¬ (sampleBase b e₀ e₁ t ≤ out.length ∧
      out.length < sampleBase b e₀ e₁ t + 2)) :
    binarySignedValue (BrouwerNashJitterQuery.coefficientWord
      ![out, action, source, code₀, code₁]) = 0 := by
  subst e₀ e₁
  exact BrouwerNashJitterQuery.coefficientWord_eq_zero_of_outside
    out action source code₀ code₁ r hr hno

private theorem extraction_zero
    (hno : ∀ t : Fin 41, ¬ (sampleBase b e₀ e₁ t + 2 ≤ out.length ∧
      out.length < sampleBase b e₀ e₁ t + 2 + 4 * b)) :
    binarySignedValue (BrouwerNashExtractionQuery.coefficientWord
      ![out, action, source, code₀, code₁]) = 0 := by
  subst e₀ e₁
  exact BrouwerNashExtractionQuery.coefficientWord_eq_zero_of_outside
    out action source code₀ code₁ hno

private theorem increment_zero (r : Fin (k * 2)) (hr : action.length = r.val)
    (hno : ∀ t : Fin 41, ¬ (sampleBase b e₀ e₁ t + 2 + 4 * b ≤ out.length ∧
      out.length < sampleBase b e₀ e₁ t + 2 + 12 * b)) :
    binarySignedValue (BrouwerNashIncrementQuery.allCoefficientWord
      ![out, action, source, code₀, code₁]) = 0 := by
  subst e₀ e₁
  exact BrouwerNashIncrementQuery.allCoefficientWord_zero_of_outside
    source code₀ code₁ out action hno r hr

private theorem fixed_zero (r : Fin (k * 2)) (hr : action.length = r.val)
    (hno : ∀ t : Fin 41,
      ¬ (sampleBase b e₀ e₁ t + weightBase b ≤ out.length ∧
        out.length < sampleBase b e₀ e₁ t + colorBase b) ∧
      ¬ (sampleBase b e₀ e₁ t + minimumBase b e₀ e₁ ≤ out.length ∧
        out.length < sampleBase b e₀ e₁ t + sampleWidth b e₀ e₁)) :
    binarySignedValue (BrouwerNashInterpolationQuery.coefficientWord
      ![out, action, source, code₀, code₁]) = 0 := by
  subst e₀ e₁
  exact BrouwerNashInterpolationQuery.coefficientWord_eq_zero_of_outside
    source code₀ code₁ out action r hr hno

private theorem extraction_at (t : Fin 41) (axis stage : Fin 2) (j : ℕ) (hj : j < b)
    (r : Fin (k * 2)) (hr : action.length = r.val)
    (hout : out.length = sampleBase b e₀ e₁ t + digit b axis j + stage.val) :
    binarySignedValue (BrouwerNashExtractionQuery.coefficientWord
      ![out, action, source, code₀, code₁]) =
      (if stage.val = 0 then BimatrixBinaryExtraction.digitGate
        (sampleRef b e₀ e₁ t (remainder b axis j))
      else BimatrixBinaryExtraction.remainderGate
        (sampleRef b e₀ e₁ t (remainder b axis j))
        (sampleRef b e₀ e₁ t (digit b axis j))).coefficients r := by
  subst e₀ e₁
  rw [BrouwerNashExtractionQuery.coefficientWord_at
    out action source code₀ code₁ t axis stage j hj hout]
  have he := BrouwerNashExtractionQuery.indexedCoefficientWord_gate
    (decide (axis = 1)) (decide (stage = 1)) (List.replicate j false)
    (List.replicate t.val false) out action source code₀ code₁ t j hj
    (List.length_replicate ..) (List.length_replicate ..) r hr
  fin_cases axis <;> fin_cases stage <;> norm_num at he ⊢ <;> exact he
end Lengths
private theorem color_zero (out action source : List Bool) (raw₀ raw₁ : RawCircuit)
    (hw₀ : raw₀.WellFormed (arity (pairFst source).length))
    (hw₁ : raw₁.WellFormed (arity (pairFst source).length))
    (r : Fin (dimension (pairFst source).length raw₀.length raw₁.length * 2))
    (hr : action.length = r.val)
    (hno : ∀ t : Fin 41,
      ¬ (sampleBase (pairFst source).length raw₀.length raw₁.length t +
          colorBase (pairFst source).length ≤ out.length ∧
        out.length < sampleBase (pairFst source).length raw₀.length raw₁.length t +
          minimumBase (pairFst source).length raw₀.length raw₁.length)) :
    binarySignedValue (BrouwerNashColorQuery.coefficientWord
      ![out, action, source, raw₀.encode, raw₁.encode]) = 0 := by
  have hp (raw : RawCircuit) : (circuitUnaryPrefix raw.encode).length = raw.length := by
    simp only [RawCircuit.encode, circuitUnaryPrefix_encode, List.length_replicate]
  let r' : Fin (dimension (pairFst source).length
      (circuitUnaryPrefix raw₀.encode).length (circuitUnaryPrefix raw₁.encode).length * 2) :=
    ⟨r.val, by simpa only [hp] using r.isLt⟩
  apply BrouwerNashColorQuery.coefficientWord_zero_outside
    ![out, action, source, raw₀.encode, raw₁.encode] raw₀ raw₁ rfl rfl hw₀ hw₁ r' hr
  intro t corner offset hoff he
  have hv₂ : (![out, action, source, raw₀.encode, raw₁.encode] : Fin 5 → List Bool) 2 =
      source := rfl
  have hv₃ : (![out, action, source, raw₀.encode, raw₁.encode] : Fin 5 → List Bool) 3 =
      raw₀.encode := rfl
  have hv₄ : (![out, action, source, raw₀.encode, raw₁.encode] : Fin 5 → List Bool) 4 =
      raw₁.encode := rfl
  simp only [hv₂, hv₃, hv₄, hp, Matrix.cons_val_zero] at hoff he
  apply hno t
  have hc := corner.isLt
  have hm := Nat.mul_le_mul_right (cornerWidth (pairFst source).length raw₀.length raw₁.length)
    (show corner.val + 1 ≤ 4 by omega)
  rw [Nat.add_mul, one_mul] at hm
  dsimp only [minimumBase]
  omega
private theorem prefix_length (raw : RawCircuit) :
    (circuitUnaryPrefix raw.encode).length = raw.length := by
  simp only [RawCircuit.encode, circuitUnaryPrefix_encode, List.length_replicate]

section Samples
variable (out action source : List Bool) (raw₀ raw₁ : RawCircuit)
local notation "b" => List.length (pairFst source)
local notation "e₀" => List.length raw₀
local notation "e₁" => List.length raw₁
local notation "k" => dimension b e₀ e₁

private theorem jitter_sample (t : Fin 41) (offset : ℕ)
    (hi : offset < sampleWidth b e₀ e₁) (ho : out.length = sampleBase b e₀ e₁ t + offset)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (BrouwerNashJitterQuery.coefficientWord
      ![out, action, source, raw₀.encode, raw₁.encode]) =
      if offset < 2 then (sampleGate b raw₀ raw₁ t offset).coefficients r else 0 := by
  by_cases h : offset < 2
  · rw [ite_eq_left h]
    let axis : Fin 2 := ⟨offset, h⟩
    have he := jitter_at out action source raw₀.encode raw₁.encode e₀ e₁
      (prefix_length raw₀) (prefix_length raw₁) t axis r hr ho
    have haxis : jitter axis = offset := rfl
    rw [← haxis, sampleGate_jitter b raw₀ raw₁ t axis]
    exact he
  · rw [ite_eq_right h]
    apply jitter_zero out action source raw₀.encode raw₁.encode e₀ e₁
      (prefix_length raw₀) (prefix_length raw₁) r hr
    exact interval_excluded b e₀ e₁ out.length offset 0 2 t hi ho
      (by dsimp only [sampleWidth]; omega) (by omega)

private theorem extraction_sample (t : Fin 41) (offset : ℕ)
    (hi : offset < sampleWidth b e₀ e₁) (ho : out.length = sampleBase b e₀ e₁ t + offset)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (BrouwerNashExtractionQuery.coefficientWord
      ![out, action, source, raw₀.encode, raw₁.encode]) =
      if 2 ≤ offset ∧ offset < 2 + 4 * b then
        (sampleGate b raw₀ raw₁ t offset).coefficients r else 0 := by
  by_cases h : 2 ≤ offset ∧ offset < 2 + 4 * b
  · rw [ite_eq_left h]
    obtain ⟨axis, stage, j, hj, hoff, hg⟩ :=
      BrouwerNashExtractionQuery.sampleGate_extraction_of_interval b offset raw₀ raw₁ t h.1 h.2
    rw [hg]
    apply extraction_at out action source raw₀.encode raw₁.encode e₀ e₁
      (prefix_length raw₀) (prefix_length raw₁) t axis stage j hj r hr
    omega
  · rw [ite_eq_right h]
    apply extraction_zero out action source raw₀.encode raw₁.encode e₀ e₁
      (prefix_length raw₀) (prefix_length raw₁)
    simpa only [Nat.add_assoc] using interval_excluded b e₀ e₁ out.length offset 2
      (2 + 4 * b) t hi ho (by dsimp only [sampleWidth]; omega) (by omega)

private theorem increment_sample (t : Fin 41) (offset : ℕ)
    (hi : offset < sampleWidth b e₀ e₁) (ho : out.length = sampleBase b e₀ e₁ t + offset)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (BrouwerNashIncrementQuery.allCoefficientWord
      ![out, action, source, raw₀.encode, raw₁.encode]) =
      if 2 + 4 * b ≤ offset ∧ offset < weightBase b then
        (sampleGate b raw₀ raw₁ t offset).coefficients r else 0 := by
  by_cases h : 2 + 4 * b ≤ offset ∧ offset < weightBase b
  · rw [ite_eq_left h]
    obtain ⟨axis, stage, j, hj, hoff, hg⟩ :=
      BrouwerNashIncrementQuery.sampleGate_increment_of_interval b offset raw₀ raw₁ t h.1 h.2
    rw [hg]
    apply increment_at out action source raw₀.encode raw₁.encode e₀ e₁
      (prefix_length raw₀) (prefix_length raw₁) t axis stage j hj r hr
    omega
  · rw [ite_eq_right h]
    apply increment_zero out action source raw₀.encode raw₁.encode e₀ e₁
      (prefix_length raw₀) (prefix_length raw₁) r hr
    simpa only [weightBase, Nat.add_assoc] using interval_excluded b e₀ e₁ out.length offset
      (2 + 4 * b) (weightBase b) t hi ho
      (by dsimp only [weightBase, sampleWidth]; omega) (by omega)

private theorem fixed_sample (t : Fin 41) (offset : ℕ)
    (hi : offset < sampleWidth b e₀ e₁) (ho : out.length = sampleBase b e₀ e₁ t + offset)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (BrouwerNashInterpolationQuery.coefficientWord
      ![out, action, source, raw₀.encode, raw₁.encode]) =
      if (weightBase b ≤ offset ∧ offset < colorBase b) ∨ minimumBase b e₀ e₁ ≤ offset then
        (sampleGate b raw₀ raw₁ t offset).coefficients r else 0 := by
  by_cases h₀ : weightBase b ≤ offset ∧ offset < colorBase b
  · rw [ite_eq_left (Or.inl h₀)]
    obtain ⟨stage, hoff, hg⟩ := BrouwerNashQueryRegions.sampleGate_interpolation_of_interval
      b offset raw₀ raw₁ t h₀.1 h₀.2
    rw [hg]
    apply interpolation_at out action source raw₀.encode raw₁.encode e₀ e₁
      (prefix_length raw₀) (prefix_length raw₁) t stage r hr
    omega
  · by_cases h₁ : minimumBase b e₀ e₁ ≤ offset
    · rw [ite_eq_left (Or.inr h₁)]
      obtain ⟨corner, flag, temporary, hoff, hg⟩ :=
        BrouwerNashQueryRegions.sampleGate_minimum_of_interval b offset raw₀ raw₁ t h₁ hi
      rw [hg]
      apply minimum_at out action source raw₀.encode raw₁.encode e₀ e₁
        (prefix_length raw₀) (prefix_length raw₁) t corner flag temporary r hr
      omega
    · rw [ite_eq_right (by tauto)]
      apply fixed_zero out action source raw₀.encode raw₁.encode e₀ e₁
        (prefix_length raw₀) (prefix_length raw₁) r hr
      intro s
      constructor
      · exact interval_excluded b e₀ e₁ out.length offset (weightBase b) (colorBase b) t hi ho
          (by dsimp only [colorBase, weightBase, sampleWidth]; omega) (by omega) s
      · exact interval_excluded b e₀ e₁ out.length offset (minimumBase b e₀ e₁)
          (sampleWidth b e₀ e₁) t hi ho le_rfl (by omega) s

private theorem color_sample
    (hw₀ : raw₀.WellFormed (arity b)) (hw₁ : raw₁.WellFormed (arity b))
    (t : Fin 41) (offset : ℕ) (hi : offset < sampleWidth b e₀ e₁)
    (ho : out.length = sampleBase b e₀ e₁ t + offset)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (BrouwerNashColorQuery.coefficientWord
      ![out, action, source, raw₀.encode, raw₁.encode]) =
      if colorBase b ≤ offset ∧ offset < minimumBase b e₀ e₁ then
        (sampleGate b raw₀ raw₁ t offset).coefficients r else 0 := by
  by_cases h : colorBase b ≤ offset ∧ offset < minimumBase b e₀ e₁
  · rw [ite_eq_left h]
    exact BrouwerNashColorQuery.coefficientWord_eq_sampleGate
      ![out, action, source, raw₀.encode, raw₁.encode] raw₀ raw₁ rfl rfl hw₀ hw₁
      r hr t offset h.1 h.2 ho
  · rw [ite_eq_right h]
    apply color_zero out action source raw₀ raw₁ hw₀ hw₁ r hr
    exact interval_excluded b e₀ e₁ out.length offset (colorBase b) (minimumBase b e₀ e₁)
      t hi ho (by dsimp only [minimumBase, colorBase, weightBase, sampleWidth]; omega)
      (by omega)

private theorem coefficientWord_sample
    (hw₀ : raw₀.WellFormed (arity b)) (hw₁ : raw₁.WellFormed (arity b))
    (t : Fin 41) (offset : ℕ) (hi : offset < sampleWidth b e₀ e₁)
    (ho : out.length = sampleBase b e₀ e₁ t + offset)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (BrouwerNashSelector.coefficientWord
      ![out, action, source, raw₀.encode, raw₁.encode]) =
      (sampleGate b raw₀ raw₁ t offset).coefficients r := by
  rw [BrouwerNashSelector.coefficientWord_expansion,
    global_value out action source raw₀.encode raw₁.encode e₀ e₁
      (prefix_length raw₀) (prefix_length raw₁) r hr,
    jitter_sample out action source raw₀ raw₁ t offset hi ho r hr,
    extraction_sample out action source raw₀ raw₁ t offset hi ho r hr,
    increment_sample out action source raw₀ raw₁ t offset hi ho r hr,
    fixed_sample out action source raw₀ raw₁ t offset hi ho r hr,
    color_sample out action source raw₀ raw₁ hw₀ hw₁ t offset hi ho r hr]
  have hg : ¬ out.length < globalCount b := by
    dsimp only [sampleBase] at ho
    omega
  rw [ite_eq_right hg]
  have hwm : weightBase b ≤ colorBase b := by dsimp only [colorBase]; omega
  have hcm : colorBase b ≤ minimumBase b e₀ e₁ := by dsimp only [minimumBase]; omega
  split_ifs <;> dsimp only [weightBase] at * <;> omega

private theorem coefficientWord_outside
    (hw₀ : raw₀.WellFormed (arity b)) (hw₁ : raw₁.WellFormed (arity b))
    (hno : ∀ t : Fin 41,
      ¬ (sampleBase b e₀ e₁ t ≤ out.length ∧
        out.length < sampleBase b e₀ e₁ t + sampleWidth b e₀ e₁))
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (BrouwerNashSelector.coefficientWord
      ![out, action, source, raw₀.encode, raw₁.encode]) =
      if out.length < globalCount b then (globalGate b e₀ e₁ out.length).coefficients r
      else 0 := by
  have hj : binarySignedValue (BrouwerNashJitterQuery.coefficientWord
      ![out, action, source, raw₀.encode, raw₁.encode]) = 0 := by
    apply jitter_zero out action source raw₀.encode raw₁.encode e₀ e₁
      (prefix_length raw₀) (prefix_length raw₁) r hr
    intro t ht
    apply hno t
    dsimp only [sampleWidth]
    omega
  have he : binarySignedValue (BrouwerNashExtractionQuery.coefficientWord
      ![out, action, source, raw₀.encode, raw₁.encode]) = 0 := by
    apply extraction_zero out action source raw₀.encode raw₁.encode e₀ e₁
      (prefix_length raw₀) (prefix_length raw₁)
    intro t ht
    apply hno t
    dsimp only [sampleWidth]
    omega
  have hn : binarySignedValue (BrouwerNashIncrementQuery.allCoefficientWord
      ![out, action, source, raw₀.encode, raw₁.encode]) = 0 := by
    apply increment_zero out action source raw₀.encode raw₁.encode e₀ e₁
      (prefix_length raw₀) (prefix_length raw₁) r hr
    intro t ht
    apply hno t
    dsimp only [sampleWidth]
    omega
  have hf : binarySignedValue (BrouwerNashInterpolationQuery.coefficientWord
      ![out, action, source, raw₀.encode, raw₁.encode]) = 0 := by
    apply fixed_zero out action source raw₀.encode raw₁.encode e₀ e₁
      (prefix_length raw₀) (prefix_length raw₁) r hr
    intro t
    constructor
    · intro ht
      apply hno t
      dsimp only [colorBase, weightBase, sampleWidth] at ht ⊢
      omega
    · intro ht
      apply hno t
      omega
  have hc : binarySignedValue (BrouwerNashColorQuery.coefficientWord
      ![out, action, source, raw₀.encode, raw₁.encode]) = 0 := by
    apply color_zero out action source raw₀ raw₁ hw₀ hw₁ r hr
    intro t ht
    apply hno t
    dsimp only [minimumBase, colorBase, weightBase, sampleWidth] at ht ⊢
    omega
  rw [BrouwerNashSelector.coefficientWord_expansion, hj, he, hn, hf, hc]
  simp only [add_zero]
  exact global_value out action source raw₀.encode raw₁.encode e₀ e₁
    (prefix_length raw₀) (prefix_length raw₁) r hr
end Samples
private theorem outside_samples (b e₀ e₁ out : ℕ)
    (hglobal : ¬ out < globalCount b)
    (hsample : ¬ (out - globalCount b) / sampleWidth b e₀ e₁ < 41) :
    ∀ t : Fin 41, ¬ (sampleBase b e₀ e₁ t ≤ out ∧
      out < sampleBase b e₀ e₁ t + sampleWidth b e₀ e₁) := by
  have hmul := Nat.mul_le_of_le_div (sampleWidth b e₀ e₁) 41 (out - globalCount b)
    (show 41 ≤ (out - globalCount b) / sampleWidth b e₀ e₁ by omega)
  intro t hin
  have ht := Nat.mul_le_mul_right (sampleWidth b e₀ e₁)
    (show t.val + 1 ≤ 41 from Nat.succ_le_of_lt t.isLt)
  rw [Nat.add_mul, one_mul] at ht
  dsimp only [sampleBase] at hin
  omega

/-- The actual uniform scalar selector agrees with every gate of the canonical source program. -/
theorem coefficientWord_value (out action source code₀ code₁ : List Bool)
    (raw₀ raw₁ : RawCircuit) (hc₀ : code₀ = raw₀.encode) (hc₁ : code₁ = raw₁.encode)
    (hw₀ : raw₀.WellFormed (arity (pairFst source).length))
    (hw₁ : raw₁.WellFormed (arity (pairFst source).length))
    (i : Fin (dimension (pairFst source).length raw₀.length raw₁.length))
    (ho : out.length = i.val)
    (r : Fin (dimension (pairFst source).length raw₀.length raw₁.length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (BrouwerNashSelector.coefficientWord
      ![out, action, source, code₀, code₁]) =
      (program (pairFst source).length raw₀ raw₁ i).coefficients r := by
  subst code₀ code₁
  let b := (pairFst source).length
  let W := sampleWidth b raw₀.length raw₁.length
  have hW : 0 < W := by dsimp only [W, sampleWidth]; omega
  by_cases hg : i.val < globalCount b
  · have hno : ∀ t : Fin 41,
        ¬ (sampleBase b raw₀.length raw₁.length t ≤ out.length ∧
          out.length < sampleBase b raw₀.length raw₁.length t + W) := by
      intro t ht
      dsimp only [sampleBase] at ht
      omega
    have he := coefficientWord_outside out action source raw₀ raw₁ hw₀ hw₁ hno r hr
    rw [program, ite_eq_left hg]
    simpa only [ho, b, ite_eq_left hg] using he
  · by_cases hs : (i.val - globalCount b) / W < 41
    · let t : Fin 41 := ⟨(i.val - globalCount b) / W, hs⟩
      let offset := (i.val - globalCount b) % W
      have hi : offset < sampleWidth b raw₀.length raw₁.length := Nat.mod_lt _ hW
      have hout : out.length = sampleBase b raw₀.length raw₁.length t + offset := by
        have hd := Nat.mod_add_div (i.val - globalCount b) W
        rw [Nat.mul_comm] at hd
        dsimp only [sampleBase, t, offset, W]
        dsimp only [W] at hd
        omega
      rw [program, ite_eq_right hg, dite_eq_left hs]
      have he := coefficientWord_sample out action source raw₀ raw₁ hw₀ hw₁ t offset hi hout r hr
      simpa only [b, W, t, offset] using he
    · have hno := outside_samples b raw₀.length raw₁.length out.length
        (by rwa [ho]) (by rwa [ho])
      have he := coefficientWord_outside out action source raw₀ raw₁ hw₀ hw₁ hno r hr
      rw [program, ite_eq_right hg, dite_eq_right hs]
      have hgout : ¬ out.length < globalCount (pairFst source).length := by rwa [ho]
      simpa only [ite_eq_right hgout, BimatrixArithmeticGate.gate,
        BimatrixArithmeticGate.coefficients, ite_self, zero_add] using he
end GameTheory.Complexity.Backend.BrouwerNashSelectorCorrectness
