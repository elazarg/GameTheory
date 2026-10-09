import GameTheoryComplexity.Backend.BrouwerNashLayout
import GameTheoryComplexity.Backend.BimatrixRawGate
import Complexitylib.Circuits.Encoding.Shift
import GameTheory.Finite.BimatrixBinaryExtraction
import GameTheory.Finite.BimatrixDyadicGate
import GameTheory.Finite.BimatrixFeedbackGate
import GameTheory.Finite.BimatrixInterpolationGate
import GameTheory.Finite.BimatrixColorMeanGate

/-! A canonical paired-action program for jittered two-coordinate color feedback.
The numeric allocation is shared with the executable coefficient writer. Every block specializes
an existing affine or comparator factory, and malformed raw references emit affine zero. -/
namespace GameTheory.Complexity.Backend.BrouwerNashProgram
open _root_.Complexity.CircuitCode
open GameTheory.Finite GameTheory.Finite.BimatrixGateProgram
open scoped BigOperators
open BrouwerNashLayout

/-- Every natural wire query is total; allocated wires retain their exact indices. -/
def slot (b ell₀ ell₁ i : ℕ) : Fin (dimension b ell₀ ell₁) :=
  ⟨i % dimension b ell₀ ell₁, Nat.mod_lt _ (dimension_pos b ell₀ ell₁)⟩

@[simp] theorem slot_val (b ell₀ ell₁ i : ℕ) (hi : i < dimension b ell₀ ell₁) :
    (slot b ell₀ ell₁ i).val = i := Nat.mod_eq_of_lt hi

/-- Missing or out-of-range raw gates emit the canonical affine zero gate. -/
def guardedRaw {k : ℕ} (raw : RawGate) : Gate k :=
  if h : raw.WellFormedAt k then BimatrixRawGate.gate raw h
  else BimatrixArithmeticGate.gate (fun _ => 0) 0

/-- Aggregate two affine inputs, retaining both contributions when references coincide. -/
def affine₂ {k : ℕ} (a z : Fin k) (ca cz constant : ℤ) : Gate k :=
  BimatrixArithmeticGate.gate
    (fun j => (if j = a then ca else 0) + (if j = z then cz else 0)) constant

/-- The third-scale positive feedback uses exact divisibility of the allocated dimension. -/
def positiveGate (b ell₀ ell₁ : ℕ) : Gate (dimension b ell₀ ell₁) :=
  BimatrixArithmeticGate.gate (fun j =>
    if j = slot b ell₀ ell₁ (alpha (precision b))
    then 82 * (units b ell₀ ell₁ : ℤ) else 0) 0

/-- The two color components use the canonical displacement weights. -/
def componentWeight (axis flag : Fin 2) : ℤ := if axis = flag then 2 else 1

/-- Average all four weighted corner flags over the forty-one jitter samples. -/
def averageGate (b ell₀ ell₁ : ℕ) (axis : Fin 2) : Gate (dimension b ell₀ ell₁) :=
  BimatrixArithmeticGate.gate (fun j =>
    ∑ t : Fin 41, ∑ corner : Fin 4, ∑ flag : Fin 2,
      if j = slot b ell₀ ell₁
        (sampleBase b ell₀ ell₁ t + minimum b ell₀ ell₁ corner flag)
      then 2 * (units b ell₀ ell₁ : ℤ) * componentWeight axis flag else 0) 0

/-- Shared scaling, averaging and cyclic feedback blocks. -/
def globalGate (b ell₀ ell₁ i : ℕ) : Gate (dimension b ell₀ ell₁) :=
  let ref := slot b ell₀ ell₁
  if h : i < 2 then BimatrixFeedbackGate.doubleGate (ref (feedbackSub b ⟨i, h⟩))
  else if i = one then BimatrixArithmeticGate.gate (fun _ => 0) 2
  else if i = zero then BimatrixArithmeticGate.gate (fun _ => 0) 0
  else if i < positive b then BimatrixDyadicGate.halvingGate (ref (alpha (i - 4)))
  else if i = positive b then positiveGate b ell₀ ell₁
  else if i < precision b + 7 then averageGate b ell₀ ell₁ ⟨(i - (precision b + 5)) % 2,
    Nat.mod_lt _ (by decide)⟩
  else if i < 3 * precision b + 7 then
    let offset := i - (precision b + 7)
    let axis : Fin 2 := ⟨(offset / precision b) % 2, Nat.mod_lt _ (by decide)⟩
    BimatrixDyadicGate.halvingGate (ref (negative b axis (offset % precision b)))
  else
    let axis : Fin 2 := ⟨((i - (3 * precision b + 7)) / 2) % 2,
      Nat.mod_lt _ (by decide)⟩
    if i % 2 = (3 * precision b + 7) % 2 then
      BimatrixFeedbackGate.halfAddGate (ref (coordinate axis)) (ref (positive b))
    else BimatrixFeedbackGate.subtractHalfGate
      (ref (feedbackHalf b axis)) (ref (negative b axis (precision b)))

/-- A local sample reference is relocated to its absolute program position. -/
def sampleRef (b ell₀ ell₁ : ℕ) (t : Fin 41) (i : ℕ) : Fin (dimension b ell₀ ell₁) :=
  slot b ell₀ ell₁ (sampleBase b ell₀ ell₁ t + i)

/-- Original digits are reversed to little-endian coordinate order before incrementing. -/
def primaryBit (b : ℕ) (axis : Fin 2) (j : ℕ) : ℕ := digit b axis (b - 1 - j)

/-- Boolean ripple-increment blocks retain inline negation without extra wires. -/
def incrementGate (b ell₀ ell₁ : ℕ) (t : Fin 41)
    (axis : Fin 2) (j : ℕ) (stage : Fin 4) : Gate (dimension b ell₀ ell₁) :=
  let input := (sampleRef b ell₀ ell₁ t (primaryBit b axis j)).val
  let carryInput := if j = 0 then one else
    (sampleRef b ell₀ ell₁ t (increment b axis (j - 1) 3)).val
  guardedRaw (match stage.val with
  | 0 => ⟨.and, input, carryInput, false, true⟩
  | 1 => ⟨.and, input, carryInput, true, false⟩
  | 2 => ⟨.or, (sampleRef b ell₀ ell₁ t (increment b axis j 0)).val,
      (sampleRef b ell₀ ell₁ t (increment b axis j 1)).val, false, false⟩
  | _ => ⟨.and, input, carryInput, false, false⟩)

/-- Coordinate-copy inputs choose the lower prefix or its ripple increment. -/
def cornerBit (b ell₀ ell₁ : ℕ) (t : Fin 41) (corner : Fin 4)
    (axis : Fin 2) (j : ℕ) : Fin (dimension b ell₀ ell₁) :=
  let upper := if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
    else corner.val = 1 ∨ corner.val = 3
  if upper then
    if j = b then
      if b = 0 then slot b ell₀ ell₁ one
      else sampleRef b ell₀ ell₁ t (increment b axis (b - 1) 3)
    else sampleRef b ell₀ ell₁ t (increment b axis j 2)
  else if j = b then slot b ell₀ ell₁ zero
  else sampleRef b ell₀ ell₁ t (primaryBit b axis j)

/-- Copies and relocated raw color gates share the same absolute input offset. -/
def colorRegionGate (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (corner : Fin 4) (offset : ℕ) : Gate (dimension b raw₀.length raw₁.length) :=
  let ell₀ := raw₀.length
  let ell₁ := raw₁.length
  let n := arity b
  let ref := slot b ell₀ ell₁
  let copy (j : ℕ) := affine₂
    (cornerBit b ell₀ ell₁ t corner ⟨(j / (b + 1)) % 2, Nat.mod_lt _ (by decide)⟩
      (j % (b + 1))) (ref zero) (2 * (dimension b ell₀ ell₁ : ℤ)) 0 0
  let query (raw : RawCircuit) (flag : Fin 2) (j : ℕ) :=
    match raw[j]? with
    | none => BimatrixArithmeticGate.gate (fun _ => 0) 0
    | some gate => guardedRaw (gate.shift
        (sampleBase b ell₀ ell₁ t + colorInput b ell₀ ell₁ corner flag))
  if offset < n then copy offset
  else if offset < n + ell₀ then query raw₀ 0 (offset - n)
  else if offset < 2 * n + ell₀ then copy (offset - (n + ell₀))
  else query raw₁ 1 (offset - (2 * n + ell₀))

/-- Eight canonical affine blocks compute the rising-diagonal corner weights. -/
def interpolationGate (b ell₀ ell₁ : ℕ) (t : Fin 41) (stage : ℕ) :
    Gate (dimension b ell₀ ell₁) :=
  let ref := sampleRef b ell₀ ell₁ t
  let C := 2 * (dimension b ell₀ ell₁ : ℤ)
  let u := ref (remainder b 0 b)
  let v := ref (remainder b 1 b)
  match stage with
  | 0 => BimatrixInterpolationGate.complementGate u
  | 1 => BimatrixInterpolationGate.complementGate v
  | 2 => BimatrixMinGate.subtractionGate C (ref (complement b 0)) (ref (complement b 1))
  | 3 => BimatrixMinGate.subtractionGate C (ref (complement b 0))
      (ref (weightTemporary b false))
  | 4 => BimatrixMinGate.subtractionGate C u v
  | 5 => BimatrixMinGate.subtractionGate C u (ref (weightTemporary b true))
  | 6 => BimatrixMinGate.subtractionGate C u v
  | _ => BimatrixMinGate.subtractionGate C v u

/-- Two canonical subtraction blocks multiply a corner weight by its Boolean color flag. -/
def minimumGate (b ell₀ ell₁ : ℕ) (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (temporary : Bool) : Gate (dimension b ell₀ ell₁) :=
  let ref := sampleRef b ell₀ ell₁ t
  let colorLength := if flag.val = 0 then ell₀ else ell₁
  if temporary then BimatrixMinGate.subtractionGate (2 * (dimension b ell₀ ell₁ : ℤ))
    (ref (weight b corner)) (ref (colorGate b ell₀ ell₁ corner flag + (colorLength - 1)))
  else BimatrixMinGate.subtractionGate (2 * (dimension b ell₀ ell₁ : ℤ))
    (ref (weight b corner)) (ref (minimumTemporary b ell₀ ell₁ corner flag))

/-- One sample computes jitter, digits, corners, interpolation and weighted color flags. -/
def sampleGate (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41) (i : ℕ) :
    Gate (dimension b raw₀.length raw₁.length) :=
  let ell₀ := raw₀.length
  let ell₁ := raw₁.length
  let k := dimension b ell₀ ell₁
  let ref := sampleRef b ell₀ ell₁ t
  let shared := slot b ell₀ ell₁
  if h : i < 2 then affine₂ (shared (coordinate ⟨i, h⟩))
    (shared (alpha (precision b))) (2 * (k : ℤ))
      (2 * (k : ℤ) * ((t.val : ℤ) - 20)) 0
  else if i < 2 + 4 * b then
    let axis : Fin 2 := ⟨((i - 2) / (2 * b)) % 2, Nat.mod_lt _ (by decide)⟩
    let stage := (i - 2) % (2 * b)
    let j := stage / 2
    if stage % 2 = 0 then BimatrixBinaryExtraction.digitGate (ref (remainder b axis j))
    else BimatrixBinaryExtraction.remainderGate
      (ref (remainder b axis j)) (ref (digit b axis j))
  else if i < weightBase b then
    let offset := i - (2 + 4 * b)
    incrementGate b ell₀ ell₁ t
      ⟨(offset / (4 * b)) % 2, Nat.mod_lt _ (by decide)⟩
      ((offset % (4 * b)) / 4) ⟨offset % 4, Nat.mod_lt _ (by decide)⟩
  else if i < colorBase b then
    interpolationGate b ell₀ ell₁ t (i - weightBase b)
  else if i < minimumBase b ell₀ ell₁ then
    let offset := i - colorBase b
    colorRegionGate b raw₀ raw₁ t
      ⟨(offset / cornerWidth b ell₀ ell₁) % 4, Nat.mod_lt _ (by decide)⟩
      (offset % cornerWidth b ell₀ ell₁)
  else
    let offset := i - minimumBase b ell₀ ell₁
    let corner : Fin 4 := ⟨(offset / 4) % 4, Nat.mod_lt _ (by decide)⟩
    let flag : Fin 2 := ⟨(offset / 2) % 2, Nat.mod_lt _ (by decide)⟩
    minimumGate b ell₀ ell₁ t corner flag (decide (offset % 2 = 0))

/-- A total canonical mixed gate program on the shared numeric allocation. -/
def program (b : ℕ) (raw₀ raw₁ : RawCircuit) :
    Fin (dimension b raw₀.length raw₁.length) → Gate (dimension b raw₀.length raw₁.length) :=
  fun i =>
    if i.val < globalCount b then globalGate b raw₀.length raw₁.length i.val
    else
      let offset := i.val - globalCount b
      if h : offset / sampleWidth b raw₀.length raw₁.length < 41 then
        sampleGate b raw₀ raw₁ ⟨offset / sampleWidth b raw₀.length raw₁.length, h⟩
          (offset % sampleWidth b raw₀.length raw₁.length)
      else BimatrixArithmeticGate.gate (fun _ => 0) 0

/-- Shared output positions select their canonical shared gates. -/
theorem program_global (b : ℕ) (raw₀ raw₁ : RawCircuit) (i : ℕ)
    (hi : i < globalCount b) :
    program b raw₀ raw₁ (slot b raw₀.length raw₁.length i) =
      globalGate b raw₀.length raw₁.length i := by
  have hb : i < dimension b raw₀.length raw₁.length :=
    hi.trans_le ((Nat.le_add_right _ _).trans (allocated_lt_dimension _ _ _).le)
  simp only [program, slot_val _ _ _ _ hb, ite_eq_left hi]

/-- Every allocated local output selects the same canonical sample gate. -/
theorem program_sample (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41) (i : ℕ)
    (hi : i < sampleWidth b raw₀.length raw₁.length) :
    program b raw₀ raw₁ (sampleRef b raw₀.length raw₁.length t i) =
      sampleGate b raw₀ raw₁ t i := by
  have hW : 0 < sampleWidth b raw₀.length raw₁.length := by
    simp only [sampleWidth]
    omega
  have hd : (t.val * sampleWidth b raw₀.length raw₁.length + i) /
      sampleWidth b raw₀.length raw₁.length = t.val := by
    rw [Nat.mul_comm t.val _, Nat.mul_add_div hW, Nat.div_eq_of_lt hi, Nat.add_zero]
  have hm : (t.val * sampleWidth b raw₀.length raw₁.length + i) %
      sampleWidth b raw₀.length raw₁.length = i := by
    rw [Nat.mul_comm t.val _, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have hg : ¬ sampleBase b raw₀.length raw₁.length t + i < globalCount b := by
    simp only [sampleBase]
    omega
  have hv : (sampleRef b raw₀.length raw₁.length t i).val =
      sampleBase b raw₀.length raw₁.length t + i :=
    slot_val _ _ _ _ (sample_lt_dimension _ _ _ t i hi)
  unfold program
  rw [hv, ite_eq_right hg]
  have hoff : sampleBase b raw₀.length raw₁.length t + i - globalCount b =
      t.val * sampleWidth b raw₀.length raw₁.length + i := by
    simp only [sampleBase, Nat.add_assoc, Nat.add_sub_cancel_left]
  simp only [hoff, hd, hm, dite_eq_left t.isLt]

private theorem arithmetic_bound {k : ℕ} (a : Fin k → ℤ) (constant M : ℤ)
    (ha : ∀ j, |a j| ≤ M) (r : Fin (k * 2)) :
    |(BimatrixArithmeticGate.gate a constant).coefficients r| ≤ M + |constant| :=
  BimatrixArithmeticGate.coefficients_bound a constant M ha r

private theorem elementary_bound {k : ℕ} (hk : 0 < k) (a z : Fin k)
    (r : Fin (k * 2)) :
    |(BimatrixDyadicGate.halvingGate a).coefficients r| ≤ 100 * (k : ℤ) ∧
    |(BimatrixFeedbackGate.halfAddGate a z).coefficients r| ≤ 100 * (k : ℤ) ∧
    |(BimatrixFeedbackGate.subtractHalfGate a z).coefficients r| ≤ 100 * (k : ℤ) ∧
    |(BimatrixFeedbackGate.doubleGate a).coefficients r| ≤ 100 * (k : ℤ) ∧
    |(BimatrixBinaryExtraction.digitGate a).coefficients r| ≤ 100 * (k : ℤ) ∧
    |(BimatrixBinaryExtraction.remainderGate a z).coefficients r| ≤ 100 * (k : ℤ) ∧
    |(BimatrixInterpolationGate.complementGate a).coefficients r| ≤ 100 * (k : ℤ) ∧
    |(BimatrixMinGate.subtractionGate (2 * (k : ℤ)) a z).coefficients r| ≤
      100 * (k : ℤ) := by
  have hz : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [BimatrixDyadicGate.halvingGate, BimatrixDyadicGate.halvingCoefficients,
    BimatrixFeedbackGate.halfAddGate, BimatrixFeedbackGate.halfAddCoefficients,
    BimatrixFeedbackGate.subtractHalfGate, BimatrixFeedbackGate.subtractHalfCoefficients,
    BimatrixFeedbackGate.doubleGate, BimatrixFeedbackGate.doubleCoefficients,
    BimatrixBinaryExtraction.digitGate, BimatrixBinaryExtraction.remainderGate,
    BimatrixBinaryExtraction.remainderCoefficients, BimatrixInterpolationGate.complementGate,
    BimatrixInterpolationGate.complementCoefficients, BimatrixMinGate.subtractionGate,
    BimatrixMinGate.subtractionCoefficients, BimatrixArithmeticGate.gate,
    BimatrixArithmeticGate.coefficients]
  all_goals split_ifs <;> simp only [zero_add, add_zero, sub_zero, zero_sub, abs_zero, abs_neg,
    mul_zero, mul_one, abs_le] <;> omega

private theorem constant_bound {k : ℕ} (r : Fin (k * 2)) (v : ℤ)
    (hv : |v| ≤ 100 * (k : ℤ)) :
    |(BimatrixArithmeticGate.gate (fun _ => 0) v).coefficients r| ≤ 100 * (k : ℤ) := by
  simpa only [BimatrixArithmeticGate.gate, BimatrixArithmeticGate.coefficients,
    ite_self, zero_add] using hv

private theorem affine₂_bound {k : ℕ} (a z : Fin k) (ca cz constant : ℤ)
    (r : Fin (k * 2)) :
    |(affine₂ a z ca cz constant).coefficients r| ≤ |ca| + |cz| + |constant| := by
  apply arithmetic_bound
  intro j
  exact (abs_add_le _ _).trans (add_le_add
    (by split_ifs <;> simp only [le_refl, abs_zero, abs_nonneg])
    (by split_ifs <;> simp only [le_refl, abs_zero, abs_nonneg]))

private theorem guardedRaw_bound {k : ℕ} (hk : 0 < k) (raw : RawGate)
    (r : Fin (k * 2)) : |(guardedRaw raw).coefficients r| ≤ 100 * (k : ℤ) := by
  have hz : (0 : ℤ) < k := by exact_mod_cast hk
  unfold guardedRaw
  split_ifs with h
  · exact (BimatrixRawGate.coefficients_bound raw h r).trans (by omega)
  · exact constant_bound r 0 (by simp)

/-- Every ripple stage fits the shared signed coefficient capacity, including aliased inputs. -/
theorem incrementGate_bound (b ell₀ ell₁ : ℕ) (t : Fin 41)
    (axis : Fin 2) (j : ℕ) (stage : Fin 4) (r : Fin (dimension b ell₀ ell₁ * 2)) :
    |(incrementGate b ell₀ ell₁ t axis j stage).coefficients r| ≤
      100 * (dimension b ell₀ ell₁ : ℤ) := by
  unfold incrementGate
  apply guardedRaw_bound (dimension_pos b ell₀ ell₁)

private theorem positiveGate_bound (b ell₀ ell₁ : ℕ)
    (r : Fin (dimension b ell₀ ell₁ * 2)) :
    |(positiveGate b ell₀ ell₁).coefficients r| ≤ 100 * (dimension b ell₀ ell₁ : ℤ) := by
  have hU : (0 : ℤ) ≤ units b ell₀ ell₁ := Int.natCast_nonneg _
  unfold positiveGate
  have ha : ∀ j : Fin (dimension b ell₀ ell₁),
      |if j = slot b ell₀ ell₁ (alpha (precision b))
        then 82 * (units b ell₀ ell₁ : ℤ) else 0| ≤ 82 * (units b ell₀ ell₁ : ℤ) := by
    intro j
    split_ifs <;> simp only [abs_le, abs_zero] <;> omega
  have h := arithmetic_bound _ 0 (82 * (units b ell₀ ell₁ : ℤ)) ha r
  simp only [abs_zero, add_zero] at h
  apply h.trans
  simp only [dimension, Nat.cast_mul, Nat.cast_ofNat]
  omega

private theorem averageGate_bound (b ell₀ ell₁ : ℕ) (axis : Fin 2)
    (r : Fin (dimension b ell₀ ell₁ * 2)) :
    |(averageGate b ell₀ ell₁ axis).coefficients r| ≤
      100 * (dimension b ell₀ ell₁ : ℤ) := by
  have hU : (0 : ℤ) ≤ units b ell₀ ell₁ := Int.natCast_nonneg _
  have ha : ∀ j : Fin (dimension b ell₀ ell₁),
      |∑ t : Fin 41, ∑ corner : Fin 4, ∑ flag : Fin 2,
        if j = slot b ell₀ ell₁
          (sampleBase b ell₀ ell₁ t + minimum b ell₀ ell₁ corner flag)
        then 2 * (units b ell₀ ell₁ : ℤ) * componentWeight axis flag else 0| ≤
      1312 * (units b ell₀ ell₁ : ℤ) := by
    intro j
    calc
      _ ≤ ∑ t : Fin 41, |∑ corner : Fin 4, ∑ flag : Fin 2, _| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t : Fin 41, ∑ corner : Fin 4, ∑ flag : Fin 2,
          |if j = slot b ell₀ ell₁
            (sampleBase b ell₀ ell₁ t + minimum b ell₀ ell₁ corner flag)
            then 2 * (units b ell₀ ell₁ : ℤ) * componentWeight axis flag else 0| := by
        apply Finset.sum_le_sum
        intro t ht
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun corner hc => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _t : Fin 41, ∑ _corner : Fin 4, ∑ _flag : Fin 2,
          4 * (units b ell₀ ell₁ : ℤ) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro corner hc
        apply Finset.sum_le_sum
        intro flag hf
        simp only [componentWeight]
        split_ifs <;> simp only [abs_le, abs_zero] <;> omega
      _ = _ := by simp; ring
  have h := arithmetic_bound _ 0 (1312 * (units b ell₀ ell₁ : ℤ)) ha r
  change |(averageGate b ell₀ ell₁ axis).coefficients r| ≤ _ at h
  simp only [abs_zero, add_zero] at h
  apply h.trans
  simp only [dimension, Nat.cast_mul, Nat.cast_ofNat]
  omega

private theorem globalGate_bound (b ell₀ ell₁ i : ℕ)
    (r : Fin (dimension b ell₀ ell₁ * 2)) :
    |(globalGate b ell₀ ell₁ i).coefficients r| ≤ 100 * (dimension b ell₀ ell₁ : ℤ) := by
  have hk := dimension_pos b ell₀ ell₁
  have hz : (0 : ℤ) < dimension b ell₀ ell₁ := by exact_mod_cast hk
  dsimp only [globalGate]
  split_ifs
  · exact (elementary_bound hk _ (slot b ell₀ ell₁ zero) r).2.2.2.1
  · exact constant_bound r 2 (by norm_num; omega)
  · exact constant_bound r 0 (by simp)
  · exact (elementary_bound hk _ (slot b ell₀ ell₁ zero) r).1
  · exact positiveGate_bound b ell₀ ell₁ r
  · exact averageGate_bound b ell₀ ell₁ _ r
  · exact (elementary_bound hk _ (slot b ell₀ ell₁ zero) r).1
  · exact (elementary_bound hk _ _ r).2.1
  · exact (elementary_bound hk _ _ r).2.2.1

private theorem copy_bound {k : ℕ} (a z : Fin k) (r : Fin (k * 2)) :
    |(affine₂ a z (2 * (k : ℤ)) 0 0).coefficients r| ≤ 100 * (k : ℤ) := by
  have h := affine₂_bound a z (2 * (k : ℤ)) 0 0 r
  simp only [abs_zero, add_zero, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 * k)] at h
  omega

private theorem colorRegionGate_bound (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (corner : Fin 4) (offset : ℕ) (r : Fin (dimension b raw₀.length raw₁.length * 2)) :
    |(colorRegionGate b raw₀ raw₁ t corner offset).coefficients r| ≤
      100 * (dimension b raw₀.length raw₁.length : ℤ) := by
  dsimp only [colorRegionGate]
  split_ifs
  · exact copy_bound _ _ r
  · split
    · exact constant_bound r 0 (by simp)
    · exact @guardedRaw_bound (dimension b raw₀.length raw₁.length)
        (dimension_pos b raw₀.length raw₁.length) _ r
  · exact copy_bound _ _ r
  · split
    · exact constant_bound r 0 (by simp)
    · exact @guardedRaw_bound (dimension b raw₀.length raw₁.length)
        (dimension_pos b raw₀.length raw₁.length) _ r

private theorem jitter_bound {k : ℕ} (a z : Fin k) (t : Fin 41) (r : Fin (k * 2)) :
    |(affine₂ a z (2 * (k : ℤ)) (2 * (k : ℤ) * ((t.val : ℤ) - 20)) 0).coefficients r| ≤
      100 * (k : ℤ) := by
  have ht : (t.val : ℤ) ≤ 40 := by exact_mod_cast (show t.val ≤ 40 by omega)
  have ht0 : (0 : ℤ) ≤ t.val := Int.natCast_nonneg _
  have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg _
  have h := affine₂_bound a z (2 * (k : ℤ)) (2 * (k : ℤ) * ((t.val : ℤ) - 20)) 0 r
  have hp : |2 * (k : ℤ) * ((t.val : ℤ) - 20)| ≤ 40 * (k : ℤ) := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [abs_zero, add_zero, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 * k)] at h
  omega

private theorem interpolationGate_bound (b ell₀ ell₁ : ℕ) (t : Fin 41) (stage : ℕ)
    (r : Fin (dimension b ell₀ ell₁ * 2)) :
    |(interpolationGate b ell₀ ell₁ t stage).coefficients r| ≤
      100 * (dimension b ell₀ ell₁ : ℤ) := by
  have hk := dimension_pos b ell₀ ell₁
  dsimp only [interpolationGate]
  split
  · exact (elementary_bound hk _ (slot b ell₀ ell₁ zero) r).2.2.2.2.2.2.1
  · exact (elementary_bound hk _ (slot b ell₀ ell₁ zero) r).2.2.2.2.2.2.1
  · exact (elementary_bound hk _ _ r).2.2.2.2.2.2.2
  · exact (elementary_bound hk _ _ r).2.2.2.2.2.2.2
  · exact (elementary_bound hk _ _ r).2.2.2.2.2.2.2
  · exact (elementary_bound hk _ _ r).2.2.2.2.2.2.2
  · exact (elementary_bound hk _ _ r).2.2.2.2.2.2.2
  · exact (elementary_bound hk _ _ r).2.2.2.2.2.2.2

private theorem minimumGate_bound (b ell₀ ell₁ : ℕ) (t : Fin 41)
    (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    (r : Fin (dimension b ell₀ ell₁ * 2)) :
    |(minimumGate b ell₀ ell₁ t corner flag temporary).coefficients r| ≤
      100 * (dimension b ell₀ ell₁ : ℤ) := by
  have hk := dimension_pos b ell₀ ell₁
  dsimp only [minimumGate]
  split_ifs <;> exact (elementary_bound hk _ _ r).2.2.2.2.2.2.2
private theorem sampleGate_bound (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41) (i : ℕ)
    (r : Fin (dimension b raw₀.length raw₁.length * 2)) :
    |(sampleGate b raw₀ raw₁ t i).coefficients r| ≤
      100 * (dimension b raw₀.length raw₁.length : ℤ) := by
  have hk := dimension_pos b raw₀.length raw₁.length
  dsimp only [sampleGate]
  split_ifs
  · exact jitter_bound _ _ t r
  · exact (elementary_bound hk _ (slot b raw₀.length raw₁.length zero) r).2.2.2.2.1
  · exact (elementary_bound hk _ _ r).2.2.2.2.2.1
  · exact incrementGate_bound _ _ _ t _ _ _ r
  · exact interpolationGate_bound _ _ _ t _ r
  · exact colorRegionGate_bound _ _ _ t _ _ r
  · exact minimumGate_bound _ _ _ t _ _ _ r
/-- Every emitted coefficient satisfies a uniform linear cap, even for malformed circuits. -/
theorem coefficients_bound (b : ℕ) (raw₀ raw₁ : RawCircuit)
    (i : Fin (dimension b raw₀.length raw₁.length))
    (r : Fin (dimension b raw₀.length raw₁.length * 2)) :
    |(program b raw₀ raw₁ i).coefficients r| ≤
      100 * (dimension b raw₀.length raw₁.length : ℤ) := by
  dsimp only [program]
  split_ifs
  · exact globalGate_bound _ _ _ _ r
  · exact sampleGate_bound _ _ _ _ _ r
  · exact constant_bound r 0 (by simp)

/-- The shared constant-one block uses the canonical normalized affine offset. -/
theorem globalGate_one (b ell₀ ell₁ : ℕ) :
    globalGate b ell₀ ell₁ one = BimatrixArithmeticGate.gate (fun _ => 0) 2 := by
  simp [globalGate, one]

/-- The shared constant-zero block has zero coefficients. -/
theorem globalGate_zero (b ell₀ ell₁ : ℕ) :
    globalGate b ell₀ ell₁ zero = BimatrixArithmeticGate.gate (fun _ => 0) 0 := by
  simp [globalGate, one, zero]

/-- Consecutive alpha wires are exactly the existing dyadic halving gates. -/
theorem globalGate_alpha (b ell₀ ell₁ j : ℕ) (hj : j < precision b) :
    globalGate b ell₀ ell₁ (alpha (j + 1)) =
      BimatrixDyadicGate.halvingGate (slot b ell₀ ell₁ (alpha j)) := by
  have ha : alpha (j + 1) = 4 + j := by simp [alpha]; omega
  rw [ha]
  simp only [globalGate]
  have h1 : ¬4 + j < 2 := by omega
  have h2 : 4 + j ≠ one := by simp only [one]; omega
  have h3 : 4 + j ≠ zero := by simp only [zero]; omega
  have hp : 4 + j < positive b := by simp only [positive]; omega
  simp only [dite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left hp,
    Nat.add_sub_cancel_left]

/-- The positive feedback slot selects exact one-third scaling. -/
theorem globalGate_positive (b ell₀ ell₁ : ℕ) :
    globalGate b ell₀ ell₁ (positive b) = positiveGate b ell₀ ell₁ := by
  have hT : 50 ≤ precision b := by simp only [precision]; omega
  have h1 : ¬positive b < 2 := by simp only [positive]; omega
  have h2 : positive b ≠ one := by simp only [positive, one]; omega
  have h3 : positive b ≠ zero := by simp only [positive, zero]; omega
  simp only [globalGate, dite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
    lt_self_iff_false, ite_false, ite_true]

/-- The two coordinate outputs close the canonical three-block feedback cycles. -/
theorem globalGate_coordinate (b ell₀ ell₁ : ℕ) (axis : Fin 2) :
    globalGate b ell₀ ell₁ (coordinate axis) =
      BimatrixFeedbackGate.doubleGate (slot b ell₀ ell₁ (feedbackSub b axis)) := by
  dsimp only [globalGate, coordinate]
  exact dite_eq_left axis.isLt

/-- Local jitter gates use the shared coordinate and final alpha wire. -/
theorem sampleGate_jitter (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41) (axis : Fin 2) :
    sampleGate b raw₀ raw₁ t (jitter axis) =
      affine₂ (slot b raw₀.length raw₁.length (coordinate axis))
        (slot b raw₀.length raw₁.length (alpha (precision b)))
        (2 * (dimension b raw₀.length raw₁.length : ℤ))
        (2 * (dimension b raw₀.length raw₁.length : ℤ) * ((t.val : ℤ) - 20)) 0 := by
  dsimp only [sampleGate, jitter]
  exact dite_eq_left axis.isLt

/-- Interpolation slots select all eight canonical affine blocks. -/
theorem sampleGate_interpolation (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (stage : Fin 8) :
    sampleGate b raw₀ raw₁ t (weightBase b + stage.val) =
      interpolationGate b raw₀.length raw₁.length t stage.val := by
  have h1 : ¬weightBase b + stage.val < 2 := by simp only [weightBase]; omega
  have h2 : ¬weightBase b + stage.val < 2 + 4 * b := by simp only [weightBase]; omega
  have h3 : ¬weightBase b + stage.val < weightBase b := by omega
  have h4 : weightBase b + stage.val < colorBase b := by
    simp only [colorBase]
    have hs := stage.isLt
    omega
  simp only [sampleGate, dite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
    ite_eq_left h4, Nat.add_sub_cancel_left]

/-- A well-formed guarded raw slot is exactly the existing raw-gate translation. -/
theorem guardedRaw_eq {k : ℕ} (raw : RawGate) (h : raw.WellFormedAt k) :
    guardedRaw raw = BimatrixRawGate.gate raw h := by
  exact dite_eq_left h

/-- Each allocated color region retains its local circuit and input positions. -/
theorem sampleGate_colorRegion (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (corner : Fin 4) (offset : ℕ) (ho : offset < cornerWidth b raw₀.length raw₁.length) :
    sampleGate b raw₀ raw₁ t
      (colorBase b + corner.val * cornerWidth b raw₀.length raw₁.length + offset) =
      colorRegionGate b raw₀ raw₁ t corner offset := by
  have h1 : ¬colorBase b + corner.val * cornerWidth b raw₀.length raw₁.length + offset < 2 := by
    simp only [colorBase, weightBase]
    omega
  have h2 : ¬colorBase b + corner.val * cornerWidth b raw₀.length raw₁.length + offset <
      2 + 4 * b := by simp only [colorBase, weightBase]; omega
  have h3 : ¬colorBase b + corner.val * cornerWidth b raw₀.length raw₁.length + offset <
      weightBase b := by simp only [colorBase]; omega
  have h4 : ¬colorBase b + corner.val * cornerWidth b raw₀.length raw₁.length + offset <
      colorBase b := by omega
  have hW : 0 < cornerWidth b raw₀.length raw₁.length := by
    simp only [cornerWidth, arity]
    omega
  have h5 : colorBase b + corner.val * cornerWidth b raw₀.length raw₁.length + offset <
      minimumBase b raw₀.length raw₁.length := by
    have hm := Nat.mul_le_mul_right (cornerWidth b raw₀.length raw₁.length)
      (Nat.succ_le_of_lt corner.isLt)
    rw [Nat.succ_mul] at hm
    simp only [minimumBase]
    omega
  have hoff : colorBase b + corner.val * cornerWidth b raw₀.length raw₁.length + offset -
      colorBase b = corner.val * cornerWidth b raw₀.length raw₁.length + offset := by omega
  have hd : (corner.val * cornerWidth b raw₀.length raw₁.length + offset) /
      cornerWidth b raw₀.length raw₁.length = corner.val := by
    rw [Nat.mul_comm corner.val _, Nat.mul_add_div hW, Nat.div_eq_of_lt ho, Nat.add_zero]
  have hm : (corner.val * cornerWidth b raw₀.length raw₁.length + offset) %
      cornerWidth b raw₀.length raw₁.length = offset := by
    rw [Nat.mul_comm corner.val _, Nat.mul_add_mod, Nat.mod_eq_of_lt ho]
  simp only [sampleGate, dite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
    ite_eq_right h4, ite_eq_left h5, hoff, hd, hm, Nat.mod_eq_of_lt corner.isLt]

/-- Both scalar color circuits receive the same copied corner coordinate inputs. -/
theorem colorRegionGate_copy (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (corner : Fin 4) (flag : Fin 2) (j : ℕ) (hj : j < arity b) :
    colorRegionGate b raw₀ raw₁ t corner
      ((if flag.val = 0 then 0 else arity b + raw₀.length) + j) =
      affine₂ (cornerBit b raw₀.length raw₁.length t corner
        ⟨(j / (b + 1)) % 2, Nat.mod_lt _ (by decide)⟩ (j % (b + 1)))
        (slot b raw₀.length raw₁.length zero)
        (2 * (dimension b raw₀.length raw₁.length : ℤ)) 0 0 := by
  fin_cases flag
  · simp only [ite_true, zero_add, colorRegionGate, ite_eq_left hj]
  · have h1 : ¬arity b + raw₀.length + j < arity b := by omega
    have h2 : ¬arity b + raw₀.length + j < arity b + raw₀.length := by omega
    have h3 : arity b + raw₀.length + j < 2 * arity b + raw₀.length := by omega
    simp only [Nat.one_ne_zero, ite_false, colorRegionGate, ite_eq_right h1,
      ite_eq_right h2, ite_eq_left h3, Nat.add_sub_cancel_left]

/-- Raw scalar color gates use the absolute beginning of their copied-coordinate region. -/
theorem colorRegionGate_raw₀ (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (corner : Fin 4) (j : Fin raw₀.length) :
    colorRegionGate b raw₀ raw₁ t corner (arity b + j.val) =
      guardedRaw ((raw₀.get j).shift
        (sampleBase b raw₀.length raw₁.length t +
          colorInput b raw₀.length raw₁.length corner 0)) := by
  have h1 : ¬arity b + j.val < arity b := by omega
  have h2 : arity b + j.val < arity b + raw₀.length := by have hj := j.isLt; omega
  simp only [colorRegionGate, ite_eq_right h1, ite_eq_left h2, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem j.isLt]
  rfl

/-- The second scalar circuit has its own absolute input-copy offset. -/
theorem colorRegionGate_raw₁ (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (corner : Fin 4) (j : Fin raw₁.length) :
    colorRegionGate b raw₀ raw₁ t corner (2 * arity b + raw₀.length + j.val) =
      guardedRaw ((raw₁.get j).shift
        (sampleBase b raw₀.length raw₁.length t +
          colorInput b raw₀.length raw₁.length corner 1)) := by
  have h1 : ¬2 * arity b + raw₀.length + j.val < arity b := by omega
  have h2 : ¬2 * arity b + raw₀.length + j.val < arity b + raw₀.length := by omega
  have h3 : ¬2 * arity b + raw₀.length + j.val < 2 * arity b + raw₀.length := by omega
  simp only [colorRegionGate, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem j.isLt]
  rfl

/-- Every ripple-increment stage selects its canonical guarded Boolean gate. -/
theorem sampleGate_increment (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (axis : Fin 2) (j : ℕ) (hj : j < b) (stage : Fin 4) :
    sampleGate b raw₀ raw₁ t (increment b axis j stage) =
      incrementGate b raw₀.length raw₁.length t axis j stage := by
  have hb : 0 < 4 * b := by omega
  have hlocal : 4 * j + stage.val < 4 * b := by have hs := stage.isLt; omega
  have hm := Nat.mul_le_mul_right (4 * b) (show axis.val ≤ 1 by have ha := axis.isLt; omega)
  have h1 : ¬increment b axis j stage < 2 := by
    simp only [increment, incrementBase, Nat.mul_comm (4 * b) axis.val]
    omega
  have h2 : ¬increment b axis j stage < 2 + 4 * b := by
    simp only [increment, incrementBase, Nat.mul_comm (4 * b) axis.val]
    omega
  have h3 : increment b axis j stage < weightBase b := by
    simp only [increment, incrementBase, weightBase, Nat.mul_comm (4 * b) axis.val]
    omega
  have hoff : increment b axis j stage - (2 + 4 * b) =
      axis.val * (4 * b) + (4 * j + stage.val) := by
    simp only [increment, incrementBase, Nat.mul_comm (4 * b) axis.val]
    omega
  have hd : (axis.val * (4 * b) + (4 * j + stage.val)) / (4 * b) = axis.val := by
    rw [Nat.mul_comm axis.val _, Nat.mul_add_div hb, Nat.div_eq_of_lt hlocal, Nat.add_zero]
  have hr : (axis.val * (4 * b) + (4 * j + stage.val)) % (4 * b) = 4 * j + stage.val := by
    rw [Nat.mul_comm axis.val _, Nat.mul_add_mod, Nat.mod_eq_of_lt hlocal]
  have hjdiv : (4 * j + stage.val) / 4 = j := by have hs := stage.isLt; omega
  have hsmod : (axis.val * (4 * b) + (4 * j + stage.val)) % 4 = stage.val := by
    have hmul : axis.val * (4 * b) = 4 * (axis.val * b) := by ac_rfl
    rw [hmul, Nat.mul_add_mod]
    have hs := stage.isLt
    omega
  simp only [sampleGate, dite_eq_right h1, ite_eq_right h2, ite_eq_left h3, hoff,
    hd, hr, hjdiv, Nat.mod_eq_of_lt axis.isLt]
  congr 1
  apply Fin.ext
  exact hsmod

/-- The two local subtraction stages compute every corner-weight/color-flag minimum. -/
theorem sampleGate_minimum (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (corner : Fin 4) (flag : Fin 2) (temporary : Bool) :
    sampleGate b raw₀ raw₁ t (minimumTemporary b raw₀.length raw₁.length corner flag +
      if temporary then 0 else 1) =
      minimumGate b raw₀.length raw₁.length t corner flag temporary := by
  have hm : colorBase b ≤ minimumBase b raw₀.length raw₁.length := by
    simp only [minimumBase]
    omega
  have hb : weightBase b + 8 = colorBase b := rfl
  have hcorner := corner.isLt
  have hflag := flag.isLt
  have h1 : ¬minimumTemporary b raw₀.length raw₁.length corner flag +
      (if temporary then 0 else 1) < 2 := by
    simp only [minimumTemporary, minimumBase, colorBase, weightBase]
    split_ifs <;> omega
  have h2 : ¬minimumTemporary b raw₀.length raw₁.length corner flag +
      (if temporary then 0 else 1) < 2 + 4 * b := by
    simp only [minimumTemporary, minimumBase, colorBase, weightBase]
    split_ifs <;> omega
  have h3 : ¬minimumTemporary b raw₀.length raw₁.length corner flag +
      (if temporary then 0 else 1) < weightBase b := by
    simp only [minimumTemporary]
    split_ifs <;> omega
  have h4 : ¬minimumTemporary b raw₀.length raw₁.length corner flag +
      (if temporary then 0 else 1) < colorBase b := by
    simp only [minimumTemporary]
    split_ifs <;> omega
  have h5 : ¬minimumTemporary b raw₀.length raw₁.length corner flag +
      (if temporary then 0 else 1) < minimumBase b raw₀.length raw₁.length := by
    simp only [minimumTemporary]
    split_ifs <;> omega
  have hoff : minimumTemporary b raw₀.length raw₁.length corner flag +
      (if temporary then 0 else 1) - minimumBase b raw₀.length raw₁.length =
      4 * corner.val + 2 * flag.val + (if temporary then 0 else 1) := by
    simp only [minimumTemporary]
    split_ifs <;> omega
  have hc : ((4 * corner.val + 2 * flag.val + (if temporary then 0 else 1)) / 4) % 4 =
      corner.val := by split_ifs <;> omega
  have hf : ((4 * corner.val + 2 * flag.val + (if temporary then 0 else 1)) / 2) % 2 =
      flag.val := by split_ifs <;> omega
  have ht : decide ((4 * corner.val + 2 * flag.val + (if temporary then 0 else 1)) % 2 = 0) =
            temporary := by
    cases temporary
    · change decide ((4 * corner.val + 2 * flag.val + 1) % 2 = 0) = false
      apply decide_eq_false_iff_not.mpr
      omega
    · change decide ((4 * corner.val + 2 * flag.val + 0) % 2 = 0) = true
      apply decide_eq_true_eq.mpr
      omega
  simp only [sampleGate, dite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
    ite_eq_right h4, ite_eq_right h5, hoff, hc, hf, ht]

/-- Each digit/remainder pair uses the canonical extraction factories. -/
theorem sampleGate_extraction (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (axis : Fin 2) (j : ℕ) (hj : j < b) (stage : Fin 2) :
    sampleGate b raw₀ raw₁ t (digit b axis j + stage.val) =
      if stage.val = 0 then BimatrixBinaryExtraction.digitGate
        (sampleRef b raw₀.length raw₁.length t (remainder b axis j))
      else BimatrixBinaryExtraction.remainderGate
        (sampleRef b raw₀.length raw₁.length t (remainder b axis j))
        (sampleRef b raw₀.length raw₁.length t (digit b axis j)) := by
  have hb : 0 < 2 * b := by omega
  have hs := stage.isLt
  have hlocal : 2 * j + stage.val < 2 * b := by omega
  have hm := Nat.mul_le_mul_right (2 * b) (show axis.val ≤ 1 by have ha := axis.isLt; omega)
  have h1 : ¬digit b axis j + stage.val < 2 := by simp only [digit]; omega
  have h2 : digit b axis j + stage.val < 2 + 4 * b := by
    simp only [digit, Nat.mul_comm (2 * b) axis.val]
    omega
  have hoff : digit b axis j + stage.val - 2 = axis.val * (2 * b) + (2 * j + stage.val) := by
    simp only [digit, Nat.mul_comm (2 * b) axis.val]
    omega
  have hd : (axis.val * (2 * b) + (2 * j + stage.val)) / (2 * b) = axis.val := by
    rw [Nat.mul_comm axis.val _, Nat.mul_add_div hb, Nat.div_eq_of_lt hlocal, Nat.add_zero]
  have hr : (axis.val * (2 * b) + (2 * j + stage.val)) % (2 * b) = 2 * j + stage.val := by
    rw [Nat.mul_comm axis.val _, Nat.mul_add_mod, Nat.mod_eq_of_lt hlocal]
  have hjdiv : (2 * j + stage.val) / 2 = j := by omega
  have hsmod : (2 * j + stage.val) % 2 = stage.val := by omega
  simp only [sampleGate, dite_eq_right h1, ite_eq_left h2, hoff, hd, hr, hjdiv, hsmod,
    Nat.mod_eq_of_lt axis.isLt]

/-- The shared mean slots select their canonical weighted sums. -/
theorem globalGate_average (b ell₀ ell₁ : ℕ) (axis : Fin 2) :
    globalGate b ell₀ ell₁ (average b axis) = averageGate b ell₀ ell₁ axis := by
  have hT : 50 ≤ precision b := by simp only [precision]; omega
  have ha := axis.isLt
  have h1 : ¬average b axis < 2 := by simp only [average]; omega
  have h2 : average b axis ≠ one := by simp only [average, one]; omega
  have h3 : average b axis ≠ zero := by simp only [average, zero]; omega
  have h4 : ¬average b axis < positive b := by simp only [average, positive]; omega
  have h5 : average b axis ≠ positive b := by simp only [average, positive]; omega
  have h6 : average b axis < precision b + 7 := by simp only [average]; omega
  have hoff : average b axis - (precision b + 5) = axis.val := by simp only [average]; omega
  simp only [globalGate, dite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
    ite_eq_right h4, ite_eq_right h5, ite_eq_left h6, hoff, Nat.mod_eq_of_lt ha]

/-- Each negative feedback chain starts at its mean and halves at every allocated step. -/
theorem globalGate_negative (b ell₀ ell₁ j : ℕ) (axis : Fin 2) (hj : j < precision b) :
    globalGate b ell₀ ell₁ (negative b axis (j + 1)) =
      BimatrixDyadicGate.halvingGate (slot b ell₀ ell₁ (negative b axis j)) := by
  have hT : 50 ≤ precision b := by simp only [precision]; omega
  have ha := axis.isLt
  have ht : 0 < precision b := by omega
  have hm := Nat.mul_le_mul_right (precision b) (show axis.val ≤ 1 by omega)
  have hn : negative b axis (j + 1) = precision b + 7 + axis.val * precision b + j := by
    simp [negative]
  have h1 : ¬negative b axis (j + 1) < 2 := by rw [hn]; omega
  have h2 : negative b axis (j + 1) ≠ one := by rw [hn]; simp only [one]; omega
  have h3 : negative b axis (j + 1) ≠ zero := by rw [hn]; simp only [zero]; omega
  have h4 : ¬negative b axis (j + 1) < positive b := by rw [hn]; simp only [positive]; omega
  have h5 : negative b axis (j + 1) ≠ positive b := by rw [hn]; simp only [positive]; omega
  have h6 : ¬negative b axis (j + 1) < precision b + 7 := by rw [hn]; omega
  have h7 : negative b axis (j + 1) < 3 * precision b + 7 := by rw [hn]; omega
  have hoff : negative b axis (j + 1) - (precision b + 7) = axis.val * precision b + j := by
    rw [hn]
    omega
  have hd : (axis.val * precision b + j) / precision b = axis.val := by
    rw [Nat.mul_comm axis.val _, Nat.mul_add_div ht, Nat.div_eq_of_lt hj, Nat.add_zero]
  have hr : (axis.val * precision b + j) % precision b = j := by
    rw [Nat.mul_comm axis.val _, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  simp only [globalGate, dite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
    ite_eq_right h4, ite_eq_right h5, ite_eq_right h6, ite_eq_left h7,
    hoff, hd, hr, Nat.mod_eq_of_lt ha]

/-- Both auxiliary feedback slots select the existing half-add and half-subtract gates. -/
theorem globalGate_feedback (b ell₀ ell₁ : ℕ) (axis : Fin 2) (stage : Fin 2) :
    globalGate b ell₀ ell₁ (feedbackHalf b axis + stage.val) =
      if stage.val = 0 then BimatrixFeedbackGate.halfAddGate
        (slot b ell₀ ell₁ (coordinate axis)) (slot b ell₀ ell₁ (positive b))
      else BimatrixFeedbackGate.subtractHalfGate
        (slot b ell₀ ell₁ (feedbackHalf b axis))
        (slot b ell₀ ell₁ (negative b axis (precision b))) := by
  have hT : 50 ≤ precision b := by simp only [precision]; omega
  have ha := axis.isLt
  have hs := stage.isLt
  have h1 : ¬feedbackHalf b axis + stage.val < 2 := by simp only [feedbackHalf]; omega
  have h2 : feedbackHalf b axis + stage.val ≠ one := by simp only [feedbackHalf, one]; omega
  have h3 : feedbackHalf b axis + stage.val ≠ zero := by simp only [feedbackHalf, zero]; omega
  have h4 : ¬feedbackHalf b axis + stage.val < positive b := by
    simp only [feedbackHalf, positive]
    omega
  have h5 : feedbackHalf b axis + stage.val ≠ positive b := by
    simp only [feedbackHalf, positive]
    omega
  have h6 : ¬feedbackHalf b axis + stage.val < precision b + 7 := by
    simp only [feedbackHalf]
    omega
  have h7 : ¬feedbackHalf b axis + stage.val < 3 * precision b + 7 := by
    simp only [feedbackHalf]
    omega
  have hoff : feedbackHalf b axis + stage.val - (3 * precision b + 7) =
      2 * axis.val + stage.val := by simp only [feedbackHalf]; omega
  have hd : (2 * axis.val + stage.val) / 2 = axis.val := by omega
  have hp : (feedbackHalf b axis + stage.val) % 2 = (3 * precision b + 7) % 2 ↔
      stage.val = 0 := by simp only [feedbackHalf]; omega
  simp only [globalGate, dite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
    ite_eq_right h4, ite_eq_right h5, ite_eq_right h6, ite_eq_right h7,
    hoff, hd, Nat.mod_eq_of_lt ha, hp]

/-- The shared one wire is allocated for every dimension, including depth zero. -/
theorem one_lt_dimension (b ell₀ ell₁ : ℕ) : one < dimension b ell₀ ell₁ := by
  have h := allocated_lt_dimension b ell₀ ell₁
  simp only [one, globalCount, precision] at h ⊢
  omega

/-- Every ripple stage fits inside its sample before interpolation begins. -/
theorem increment_lt_sampleWidth (b ell₀ ell₁ : ℕ) (axis : Fin 2)
    (j : ℕ) (hj : j < b) (stage : Fin 4) :
    increment b axis j stage < sampleWidth b ell₀ ell₁ := by
  have hs := stage.isLt
  have hm := Nat.mul_le_mul_right (4 * b) (show axis.val ≤ 1 by have ha := axis.isLt; omega)
  simp only [increment, incrementBase, sampleWidth, Nat.mul_comm (4 * b) axis.val]
  omega

/-- Both weighted minimum stages fit inside the sample allocation. -/
theorem minimum_lt_sampleWidth (b ell₀ ell₁ : ℕ) (corner : Fin 4) (flag : Fin 2)
    (temporary : Bool) :
    minimumTemporary b ell₀ ell₁ corner flag + (if temporary then 0 else 1) <
      sampleWidth b ell₀ ell₁ := by
  have hc := corner.isLt
  have hf := flag.isLt
  simp only [minimumTemporary, minimumBase, colorBase, weightBase, sampleWidth]
  split_ifs <;> omega

/-- The shared averaging block is exactly the existing finite color-mean factory. -/
theorem averageGate_eq_meanGate (b ell₀ ell₁ : ℕ) (axis : Fin 2) :
    averageGate b ell₀ ell₁ axis = BimatrixColorMeanGate.meanGate (units b ell₀ ell₁)
      (fun t a => slot b ell₀ ell₁ (sampleBase b ell₀ ell₁ t + minimum b ell₀ ell₁ a axis))
      (fun t a => slot b ell₀ ell₁ (sampleBase b ell₀ ell₁ t +
        minimum b ell₀ ell₁ a ((![1, 0] : Fin 2 → Fin 2) axis))) := by
  unfold averageGate BimatrixColorMeanGate.meanGate
  apply congrArg (fun a => BimatrixArithmeticGate.gate a 0)
  funext j
  unfold BimatrixColorMeanGate.meanCoefficients
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro a ha
  fin_cases axis <;> simp only [Fin.sum_univ_two] <;>
    norm_num [componentWeight] <;> split_ifs <;> simp_all <;> ring

end GameTheory.Complexity.Backend.BrouwerNashProgram
