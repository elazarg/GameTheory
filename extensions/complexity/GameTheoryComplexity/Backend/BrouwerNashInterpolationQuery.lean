import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
import GameTheoryComplexity.Backend.BrouwerNashHeaders
import GameTheoryComplexity.Backend.BinarySignedFiniteSum
import GameTheoryComplexity.Backend.BinaryUnaryEncoding
import GameTheoryComplexity.Backend.BrouwerNashQueryRegions

/-! Fixed interpolation and weighted-minimum families query the actual paired-action
coefficients using unary references and signed indicator addition. Forty-one-sample scans
retain both input contributions, including aliased references and truncated circuit headers. -/

namespace GameTheory.Complexity.Backend.BrouwerNashInterpolationQuery
open _root_.Complexity _root_.Complexity.Cobham
open BrouwerNashCoefficientQuery
open scoped BigOperators

private def header (f : (Fin 3 → List Bool) → List Bool)
    (v : Fin 6 → List Bool) : List Bool := f ![v 3, v 4, v 5]
private theorem header_cobham {f : (Fin 3 → List Bool) → List Bool} (hf : Cobham f) :
    Cobham (header f) := (Cobham.comp₃ hf (.proj 3) (.proj 4) (.proj 5)).of_eq fun _ => rfl

private def depthR : (Fin 6 → List Bool) → List Bool :=
  header BrouwerNashHeaders.sourceDepthRuler
private theorem depthR_cobham : Cobham depthR :=
  header_cobham BrouwerNashHeaders.sourceDepthRuler_cobham
private def dimR : (Fin 6 → List Bool) → List Bool := header BrouwerNashHeaders.dimensionRuler
private theorem dimR_cobham : Cobham dimR := header_cobham BrouwerNashHeaders.dimensionRuler_cobham
private def cornerR : (Fin 6 → List Bool) → List Bool := header BrouwerNashHeaders.cornerRuler
private theorem cornerR_cobham : Cobham cornerR :=
  header_cobham BrouwerNashHeaders.cornerRuler_cobham
private def arityR : (Fin 6 → List Bool) → List Bool := header BrouwerNashHeaders.arityRuler
private theorem arityR_cobham : Cobham arityR := header_cobham BrouwerNashHeaders.arityRuler_cobham
private def startR (v : Fin 6 → List Bool) : List Bool :=
  header BrouwerNashHeaders.globalRuler v ++ smash (v 0) (header BrouwerNashHeaders.sampleRuler v)
private theorem startR_cobham : Cobham startR :=
  appendFn (header_cobham BrouwerNashHeaders.globalRuler_cobham)
    (Cobham.comp₂ Cobham.smash (.proj 0) (header_cobham BrouwerNashHeaders.sampleRuler_cobham))
private def weightR (v : Fin 6 → List Bool) : List Bool :=
  [false, false] ++ smash (depthR v) (List.replicate 12 true)
private theorem weightR_cobham : Cobham weightR :=
  appendFn (Cobham.const [false, false])
    (Cobham.comp₂ Cobham.smash depthR_cobham (Cobham.const (List.replicate 12 true)))
private def remainderR (axis : Fin 2) (v : Fin 6 → List Bool) : List Bool :=
  caseBit₀ (lenEqFlag (depthR v) []) (List.replicate axis.val false)
    ([false] ++ smash (depthR v) (List.replicate (2 + 2 * axis.val) true))
private theorem remainderR_cobham (axis : Fin 2) : Cobham (remainderR axis) :=
  Cobham.iteFn (lenEqFlag_mem depthR_cobham Cobham.empty)
    (Cobham.const (List.replicate axis.val false))
    (appendFn (Cobham.const [false]) (Cobham.comp₂ Cobham.smash depthR_cobham
      (Cobham.const (List.replicate (2 + 2 * axis.val) true))))
private def weightOffset (n : ℕ) (v : Fin 6 → List Bool) : List Bool :=
  weightR v ++ List.replicate n false
private theorem weightOffset_cobham (n : ℕ) : Cobham (weightOffset n) :=
  appendFn weightR_cobham (Cobham.const (List.replicate n false))

private def firstR (stage : Fin 8) : (Fin 6 → List Bool) → List Bool :=
  match stage.val with
  | 1 | 7 => remainderR 1
  | 2 | 3 => weightOffset 0
  | _ => remainderR 0
private def secondR (stage : Fin 8) : (Fin 6 → List Bool) → List Bool :=
  match stage.val with
  | 2 => weightOffset 1
  | 3 => weightOffset 2
  | 5 => weightOffset 4
  | 7 => remainderR 0
  | _ => remainderR 1
private theorem firstR_cobham (stage : Fin 8) : Cobham (firstR stage) := by
  fin_cases stage <;> first | exact remainderR_cobham _ | exact weightOffset_cobham _
private theorem secondR_cobham (stage : Fin 8) : Cobham (secondR stage) := by
  fin_cases stage <;> first | exact remainderR_cobham _ | exact weightOffset_cobham _

private def capacity (negative : Bool) (v : Fin 6 → List Bool) : List Bool :=
  negative :: false :: binaryLengthWord (dimR v)
private theorem capacity_cobham (negative : Bool) : Cobham (capacity negative) :=
  (Cobham.comp (.bit negative) fun _ : Fin 1 => Cobham.comp (.bit false) fun _ : Fin 1 =>
    Cobham.comp binaryLengthWord_cobham fun _ : Fin 1 => dimR_cobham).of_eq fun _ => rfl
private def point (input : (Fin 6 → List Bool) → List Bool) (negative : Bool)
    (v : Fin 6 → List Bool) : List Bool :=
  binarySignedIndicator ![v 2, startR v ++ input v, capacity negative v]
private theorem point_cobham {input : (Fin 6 → List Bool) → List Bool}
    (hi : Cobham input) (negative : Bool) : Cobham (point input negative) :=
  (Cobham.comp₃ binarySignedIndicator_cobham (.proj 2)
    (appendFn startR_cobham hi) (capacity_cobham negative)).of_eq fun _ => rfl

private def interpolationTerm (stage : Fin 8) (v : Fin 6 → List Bool) : List Bool :=
  let coefficient := if stage.val < 2 then
    binarySignedAdd [false, false, true] (point (firstR stage) true v)
    else binarySignedAdd (point (firstR stage) false v) (point (secondR stage) true v)
  caseBit₀ (lenEqFlag (v 1) (startR v ++ weightOffset stage.val v)) coefficient []
private theorem interpolationTerm_cobham (stage : Fin 8) : Cobham (interpolationTerm stage) := by
  have hv : Cobham fun v : Fin 6 → List Bool => if stage.val < 2 then
      binarySignedAdd [false, false, true] (point (firstR stage) true v)
      else binarySignedAdd (point (firstR stage) false v) (point (secondR stage) true v) := by
    split_ifs
    · exact Cobham.comp₂ binarySignedAdd_cobham (Cobham.const [false, false, true])
        (point_cobham (firstR_cobham stage) true)
    · exact Cobham.comp₂ binarySignedAdd_cobham
        (point_cobham (firstR_cobham stage) false) (point_cobham (secondR_cobham stage) true)
  exact (Cobham.iteFn (lenEqFlag_mem (.proj 1)
    (appendFn startR_cobham (weightOffset_cobham stage.val))) hv Cobham.empty).of_eq fun _ => rfl

/-- A fixed interpolation stage scans all forty-one sample placements. -/
def interpolationWord (stage : Fin 8) : (Fin 5 → List Bool) → List Bool :=
  binarySignedFiniteSum (interpolationTerm stage) 41
set_option maxRecDepth 4096 in
theorem interpolationWord_cobham (stage : Fin 8) : Cobham (interpolationWord stage) :=
  binarySignedFiniteSum_cobham (interpolationTerm_cobham stage) 41
theorem interpolationWord_mem_FPn (stage : Fin 8) : FPn (interpolationWord stage) :=
  cobham_iff_FPn.mp (interpolationWord_cobham stage)

private def minimumR (v : Fin 6 → List Bool) : List Bool :=
  weightOffset 8 v ++ smash (cornerR v) (List.replicate 4 true)
private theorem minimumR_cobham : Cobham minimumR :=
  appendFn (weightOffset_cobham 8)
    (Cobham.comp₂ Cobham.smash cornerR_cobham (Cobham.const (List.replicate 4 true)))
private def minimumOffset (corner : Fin 4) (flag : Fin 2) (n : ℕ)
    (v : Fin 6 → List Bool) : List Bool :=
  minimumR v ++ List.replicate (4 * corner.val + 2 * flag.val + n) false
private theorem minimumOffset_cobham (corner : Fin 4) (flag : Fin 2) (n : ℕ) :
    Cobham (minimumOffset corner flag n) :=
  appendFn minimumR_cobham (Cobham.const _)
private def colorR (corner : Fin 4) (flag : Fin 2) (v : Fin 6 → List Bool) : List Bool :=
  weightOffset 8 v ++ smash (cornerR v) (List.replicate corner.val true) ++
    (if flag.val = 0 then arityR v else
      arityR v ++ arityR v ++ circuitUnaryPrefix (v 4))
private theorem colorR_cobham (corner : Fin 4) (flag : Fin 2) : Cobham (colorR corner flag) := by
  have hb : Cobham fun v : Fin 6 → List Bool => if flag.val = 0 then arityR v else
      arityR v ++ arityR v ++ circuitUnaryPrefix (v 4) := by
    split_ifs
    · exact arityR_cobham
    · exact appendFn (appendFn arityR_cobham arityR_cobham)
        (Cobham.comp (FP_subset_CobhamFP circuitUnaryPrefix_mem_FP) fun _ : Fin 1 => .proj 4)
  exact appendFn (appendFn (weightOffset_cobham 8)
    (Cobham.comp₂ Cobham.smash cornerR_cobham (Cobham.const _))) hb
private def lastColorR (corner : Fin 4) (flag : Fin 2) (v : Fin 6 → List Bool) : List Bool :=
  colorR corner flag v ++ (circuitUnaryPrefix (if flag.val = 0 then v 4 else v 5)).tail
private theorem lastColorR_cobham (corner : Fin 4) (flag : Fin 2) :
    Cobham (lastColorR corner flag) := by
  have hi : Cobham fun v : Fin 6 → List Bool => if flag.val = 0 then v 4 else v 5 := by
    split_ifs <;> exact Cobham.proj _
  exact appendFn (colorR_cobham corner flag)
    (Cobham.tailFn (Cobham.comp (FP_subset_CobhamFP circuitUnaryPrefix_mem_FP)
      fun _ : Fin 1 => hi))
private def minimumSecondR (corner : Fin 4) (flag : Fin 2) (temporary : Bool) :
    (Fin 6 → List Bool) → List Bool :=
  if temporary then lastColorR corner flag else minimumOffset corner flag 0
private theorem minimumSecondR_cobham (corner : Fin 4) (flag : Fin 2) (temporary : Bool) :
    Cobham (minimumSecondR corner flag temporary) := by
  cases temporary
  · exact minimumOffset_cobham corner flag 0
  · exact lastColorR_cobham corner flag
private def minimumTerm (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    (v : Fin 6 → List Bool) : List Bool :=
  caseBit₀ (lenEqFlag (v 1)
    (startR v ++ minimumOffset corner flag (if temporary then 0 else 1) v))
    (binarySignedAdd (point (weightOffset ((![3, 5, 6, 7] : Fin 4 → ℕ) corner)) false v)
      (point (minimumSecondR corner flag temporary) true v)) []
private theorem minimumTerm_cobham (corner : Fin 4) (flag : Fin 2) (temporary : Bool) :
    Cobham (minimumTerm corner flag temporary) :=
  (Cobham.iteFn (lenEqFlag_mem (.proj 1)
    (appendFn startR_cobham (minimumOffset_cobham corner flag _)))
    (Cobham.comp₂ binarySignedAdd_cobham (point_cobham (weightOffset_cobham _) false)
      (point_cobham (minimumSecondR_cobham corner flag temporary) true)) Cobham.empty).of_eq
    fun _ => rfl

/-- A weighted-minimum stage scans its concrete placements in all forty-one samples. -/
def minimumWord (corner : Fin 4) (flag : Fin 2) (temporary : Bool) :
    (Fin 5 → List Bool) → List Bool := binarySignedFiniteSum (minimumTerm corner flag temporary) 41
set_option maxRecDepth 4096 in
theorem minimumWord_cobham (corner : Fin 4) (flag : Fin 2) (temporary : Bool) :
    Cobham (minimumWord corner flag temporary) :=
  binarySignedFiniteSum_cobham (minimumTerm_cobham corner flag temporary) 41
theorem minimumWord_mem_FPn (corner : Fin 4) (flag : Fin 2) (temporary : Bool) :
    FPn (minimumWord corner flag temporary) :=
  cobham_iff_FPn.mp (minimumWord_cobham corner flag temporary)
private theorem capacity_value (negative : Bool) (v : Fin 6 → List Bool) :
    binarySignedValue (capacity negative v) =
      if negative then -2 * ((dimR v).length : ℤ) else 2 * ((dimR v).length : ℤ) := by
  cases negative <;>
    simp only [capacity, binarySignedValue, List.headD_cons, Bool.false_eq_true, ite_false,
      ite_true, List.tail_cons, Nat.fromBitsLE_cons, zero_add, binaryLengthWord_value,
      Nat.cast_mul, Nat.cast_ofNat]; ring

private theorem startR_length (v : Fin 6 → List Bool) :
    (startR v).length = BrouwerNashLayout.globalCount (pairFst (v 3)).length +
      (v 0).length * BrouwerNashLayout.sampleWidth (pairFst (v 3)).length
        (circuitUnaryPrefix (v 4)).length (circuitUnaryPrefix (v 5)).length := by
  simp only [startR, List.length_append, smash_length, header,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rfl

private theorem weightR_length (v : Fin 6 → List Bool) :
    (weightR v).length = BrouwerNashLayout.weightBase (pairFst (v 3)).length := by
  simp only [weightR, List.length_append, List.length_cons, List.length_nil, smash_length,
    List.length_replicate, depthR, header, BrouwerNashHeaders.sourceDepthRuler,
    Matrix.cons_val_zero, BrouwerNashLayout.weightBase]
  omega

private theorem remainderR_length (axis : Fin 2) (v : Fin 6 → List Bool) :
    (remainderR axis v).length =
      BrouwerNashLayout.remainder (pairFst (v 3)).length axis (pairFst (v 3)).length := by
  have hd : (depthR v).length = (pairFst (v 3)).length := rfl
  rcases lenEqFlag_flag (depthR v) [] with he | he
  · have hz := (lenEqFlag_eq_true_iff _ _).mp he
    simp only [List.length_nil, hd] at hz
    simp only [remainderR, he, caseBit₀, Bool.cond_true, List.length_replicate,
      BrouwerNashLayout.remainder, hz, ite_true, BrouwerNashLayout.jitter]
  · have hz : (pairFst (v 3)).length ≠ 0 := by
      intro hz
      have ht := (lenEqFlag_eq_true_iff (depthR v) []).mpr (by simp [hd, hz])
      rw [he] at ht
      contradiction
    simp only [remainderR, he, caseBit₀, Bool.cond_false, List.length_append,
      List.length_cons, List.length_nil,
      smash_length, List.length_replicate, hd, BrouwerNashLayout.remainder, hz, ite_false]
    have hb : 1 ≤ (pairFst (v 3)).length := by omega
    fin_cases axis <;> norm_num <;> omega

private theorem subtraction_coefficients {k : ℕ} (a z : Fin k) (C : ℤ) (r : Fin (k * 2)) :
    (GameTheory.Finite.BimatrixMinGate.subtractionGate C a z).coefficients r =
      (if r = finProdFinEquiv (a, 1) then C else 0) +
      (if r = finProdFinEquiv (z, 1) then -C else 0) := by
  rcases finProdFinEquiv.surjective r with ⟨⟨j, bit⟩, rfl⟩
  fin_cases bit <;> simp [GameTheory.Finite.BimatrixMinGate.subtractionGate,
    GameTheory.Finite.BimatrixMinGate.subtractionCoefficients,
    GameTheory.Finite.BimatrixArithmeticGate.gate,
    GameTheory.Finite.BimatrixArithmeticGate.coefficients, sub_eq_add_neg]
  split_ifs <;> rfl

private theorem complement_coefficients {k : ℕ} (a : Fin k) (r : Fin (k * 2)) :
    (GameTheory.Finite.BimatrixInterpolationGate.complementGate a).coefficients r =
      2 + (if r = finProdFinEquiv (a, 1) then -2 * (k : ℤ) else 0) := by
  rcases finProdFinEquiv.surjective r with ⟨⟨j, bit⟩, rfl⟩
  fin_cases bit <;> simp [GameTheory.Finite.BimatrixInterpolationGate.complementGate,
    GameTheory.Finite.BimatrixInterpolationGate.complementCoefficients,
    GameTheory.Finite.BimatrixArithmeticGate.gate,
    GameTheory.Finite.BimatrixArithmeticGate.coefficients, add_comm]
section Correctness
variable (source code₀ code₁ out action : List Bool)
local notation "b" => List.length (pairFst source)
local notation "ell₀" => List.length (circuitUnaryPrefix code₀)
local notation "ell₁" => List.length (circuitUnaryPrefix code₁)
local notation "k" => BrouwerNashLayout.dimension b ell₀ ell₁

private theorem point_index (input : (Fin 6 → List Bool) → List Bool) (negative : Bool)
    (t : Fin 41) (a : ℕ) (ha : a < BrouwerNashLayout.sampleWidth b ell₀ ell₁)
    (hlen : (input ![List.replicate t.val false, out, action, source, code₀, code₁]).length = a)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (point input negative
      ![List.replicate t.val false, out, action, source, code₀, code₁]) =
      if r = finProdFinEquiv (BrouwerNashProgram.sampleRef b ell₀ ell₁ t a, 1) then
        (if negative then -2 * (k : ℤ) else 2 * (k : ℤ)) else 0 := by
  let v : Fin 6 → List Bool := ![List.replicate t.val false, out, action, source, code₀, code₁]
  have hs : (startR v).length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t := by
    rw [startR_length]
    simp only [v, Matrix.cons_val_zero, List.length_replicate]
    rfl
  have habs : (startR v ++ input v).length =
      (BrouwerNashProgram.sampleRef b ell₀ ell₁ t a).val := by
    rw [List.length_append, hs, hlen]
    exact (BrouwerNashProgram.slot_val _ _ _ _
      (BrouwerNashLayout.sample_lt_dimension _ _ _ t a ha)).symm
  have he := binarySignedIndicator_index action (startR v ++ input v) (capacity negative v)
    r (BrouwerNashProgram.sampleRef b ell₀ ell₁ t a) hr habs
  change binarySignedValue (binarySignedIndicator ![action, startR v ++ input v,
    capacity negative v]) = _
  rw [he, capacity_value]
  have hd : (dimR v).length = k := by
    rw [dimR, header, BrouwerNashHeaders.dimensionRuler_length]
    simp only [v, Matrix.cons_val_zero]
    rfl
  rw [hd]

private theorem interpolationTerm_coefficients (t : Fin 41) (stage : Fin 8)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (interpolationTerm stage
      ![List.replicate t.val false, out, action, source, code₀, code₁]) =
      if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.weightBase b + stage.val then
        (BrouwerNashProgram.interpolationGate b ell₀ ell₁ t stage.val).coefficients r
      else 0 := by
  let v : Fin 6 → List Bool := ![List.replicate t.val false, out, action, source, code₀, code₁]
  have hs : (startR v).length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t := by
    rw [startR_length]
    simp only [v, Matrix.cons_val_zero, List.length_replicate]
    rfl
  have hw : (weightR v).length = BrouwerNashLayout.weightBase b := weightR_length v
  have hrem (axis : Fin 2) :
      BrouwerNashLayout.remainder b axis b < BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
    fin_cases axis <;>
      simp only [BrouwerNashLayout.remainder, BrouwerNashLayout.jitter,
        BrouwerNashLayout.sampleWidth] <;>
      split_ifs <;> norm_num <;> omega
  have hweight (n : ℕ) (hn : n < 8) :
      BrouwerNashLayout.weightBase b + n < BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
    simp only [BrouwerNashLayout.weightBase, BrouwerNashLayout.sampleWidth]
    omega
  have hp (axis : Fin 2) (negative : Bool) := point_index source code₀ code₁ out action
    (remainderR axis) negative t (BrouwerNashLayout.remainder b axis b) (hrem axis)
    (remainderR_length axis v) r hr
  have hwp (n : ℕ) (hn : n < 8) (negative : Bool) := point_index source code₀ code₁ out action
    (weightOffset n) negative t (BrouwerNashLayout.weightBase b + n) (hweight n hn)
    (by rw [weightOffset, List.length_append, hw, List.length_replicate]) r hr
  change binarySignedValue (caseBit₀ (lenEqFlag out
    (startR v ++ weightOffset stage.val v)) _ []) = _
  rw [select_value]
  have hguard : (startR v ++ weightOffset stage.val v).length =
      BrouwerNashLayout.sampleBase b ell₀ ell₁ t + BrouwerNashLayout.weightBase b + stage.val := by
    rw [List.length_append, hs, weightOffset, List.length_append, hw, List.length_replicate]
    omega
  rw [hguard]
  apply congrArg (fun z : ℤ => if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
    BrouwerNashLayout.weightBase b + stage.val then z else 0)
  fin_cases stage <;>
    simp only [firstR, secondR, ite_true, ite_false, Nat.reduceLT,
      binarySignedAdd_value, BrouwerNashProgram.interpolationGate,
      complement_coefficients, subtraction_coefficients]
  all_goals first
  | rw [hp 0 true]; rfl
  | rw [hp 1 true]; rfl
  | rw [hwp 0 (by omega) false, hwp 1 (by omega) true]; rfl
  | rw [hwp 0 (by omega) false, hwp 2 (by omega) true]; rfl
  | rw [hp 0 false, hp 1 true]; rfl
  | rw [hp 0 false, hwp 4 (by omega) true]; rfl
  | rw [hp 1 false, hp 0 true]; rfl
/-- Each fixed interpolation family selects precisely its allocated canonical coefficients. -/
theorem interpolationWord_value (stage : Fin 8) (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (interpolationWord stage ![out, action, source, code₀, code₁]) =
      ∑ t : Fin 41, if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.weightBase b + stage.val then
        (BrouwerNashProgram.interpolationGate b ell₀ ell₁ t stage.val).coefficients r else 0 := by
  rw [interpolationWord, binarySignedFiniteSum_value, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  exact interpolationTerm_coefficients source code₀ code₁ out action t stage r hr

private theorem minimumR_length (v : Fin 6 → List Bool) :
    (minimumR v).length = BrouwerNashLayout.minimumBase (pairFst (v 3)).length
      (circuitUnaryPrefix (v 4)).length (circuitUnaryPrefix (v 5)).length := by
  rw [minimumR, List.length_append, weightOffset, List.length_append, weightR_length,
    List.length_replicate, smash_length, List.length_replicate, cornerR, header,
    BrouwerNashHeaders.cornerRuler_length]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, Matrix.cons_val_zero, BrouwerNashLayout.minimumBase,
    BrouwerNashLayout.colorBase, Nat.mul_comm]

private theorem lastColorR_length (corner : Fin 4) (flag : Fin 2) (v : Fin 6 → List Bool) :
    (lastColorR corner flag v).length =
      BrouwerNashLayout.colorGate (pairFst (v 3)).length
        (circuitUnaryPrefix (v 4)).length (circuitUnaryPrefix (v 5)).length corner flag +
          ((if flag.val = 0 then circuitUnaryPrefix (v 4)
            else circuitUnaryPrefix (v 5)).length - 1) := by
  fin_cases flag <;>
    simp only [lastColorR, colorR, List.length_append, weightOffset, weightR_length,
      List.length_replicate, smash_length, List.length_tail, ite_true, ite_false,
      Nat.reduceEqDiff, cornerR, arityR, header, BrouwerNashHeaders.cornerRuler_length,
      BrouwerNashHeaders.arityRuler_length, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, BrouwerNashLayout.colorGate, BrouwerNashLayout.colorInput,
      BrouwerNashLayout.colorBase, BrouwerNashLayout.arity, BrouwerNashLayout.weightBase]
  all_goals simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  all_goals ring

private theorem minimumTerm_coefficients (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (temporary : Bool) (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (minimumTerm corner flag temporary
      ![List.replicate t.val false, out, action, source, code₀, code₁]) =
      if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
            (if temporary then 0 else 1) then
        (BrouwerNashProgram.minimumGate b ell₀ ell₁ t corner flag temporary).coefficients r
      else 0 := by
  let v : Fin 6 → List Bool := ![List.replicate t.val false, out, action, source, code₀, code₁]
  let a := if temporary then BrouwerNashLayout.colorGate b ell₀ ell₁ corner flag +
    ((if flag.val = 0 then ell₀ else ell₁) - 1) else
      BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag
  have hs : (startR v).length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t := by
    rw [startR_length]
    simp only [v, Matrix.cons_val_zero, List.length_replicate]
    rfl
  have hweight : BrouwerNashLayout.weight b corner <
      BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
    fin_cases corner <;> simp only [BrouwerNashLayout.weight, BrouwerNashLayout.weightBase,
      BrouwerNashLayout.sampleWidth] <;> norm_num <;> omega
  have ha : a < BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
    cases temporary <;> fin_cases corner <;> fin_cases flag <;>
      simp only [a, ite_true, ite_false, Nat.reduceEqDiff, BrouwerNashLayout.colorGate,
        BrouwerNashLayout.colorInput, BrouwerNashLayout.minimumTemporary,
        BrouwerNashLayout.minimumBase, BrouwerNashLayout.colorBase, BrouwerNashLayout.weightBase,
        BrouwerNashLayout.arity, BrouwerNashLayout.cornerWidth, BrouwerNashLayout.sampleWidth] <;>
      norm_num <;> omega
  have hfirst : (weightOffset ((![3, 5, 6, 7] : Fin 4 → ℕ) corner) v).length =
      BrouwerNashLayout.weight b corner := by
    rw [weightOffset, List.length_append, weightR_length, List.length_replicate]
    rfl
  have hsecond : (minimumSecondR corner flag temporary v).length = a := by
    cases temporary
    · simp only [minimumSecondR, Bool.false_eq_true, ite_false]
      rw [minimumOffset, List.length_append, minimumR_length,
        List.length_replicate]
      change BrouwerNashLayout.minimumBase b ell₀ ell₁ +
        (4 * corner.val + 2 * flag.val + 0) =
          BrouwerNashLayout.minimumBase b ell₀ ell₁ + 2 * (2 * corner.val + flag.val)
      omega
    · simp only [minimumSecondR, ite_true]
      rw [lastColorR_length]
      simp only [a, ite_true, v]
      fin_cases flag <;> rfl
  have hp := point_index source code₀ code₁ out action
    (weightOffset ((![3, 5, 6, 7] : Fin 4 → ℕ) corner)) false t
    (BrouwerNashLayout.weight b corner) hweight hfirst r hr
  have hz := point_index source code₀ code₁ out action (minimumSecondR corner flag temporary)
    true t a ha hsecond r hr
  change binarySignedValue (caseBit₀ (lenEqFlag out
    (startR v ++ minimumOffset corner flag (if temporary then 0 else 1) v)) _ []) = _
  rw [select_value]
  have hguard : (startR v ++ minimumOffset corner flag (if temporary then 0 else 1) v).length =
      BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
        BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
          (if temporary then 0 else 1) := by
    rw [List.length_append, hs, minimumOffset, List.length_append, minimumR_length,
      List.length_replicate]
    change BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      (BrouwerNashLayout.minimumBase b ell₀ ell₁ +
        (4 * corner.val + 2 * flag.val + (if temporary then 0 else 1))) = _
    simp only [BrouwerNashLayout.minimumTemporary]
    omega
  rw [hguard]
  apply congrArg (fun z : ℤ => if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
    BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
      (if temporary then 0 else 1) then z else 0)
  rw [binarySignedAdd_value, hp, hz]
  cases temporary <;>
    simp only [BrouwerNashProgram.minimumGate, ite_true, ite_false, Bool.false_eq_true,
      subtraction_coefficients, a, neg_mul]

/-- Each weighted-minimum family selects its exact canonical signed subtraction coefficients. -/
theorem minimumWord_value (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (minimumWord corner flag temporary ![out, action, source, code₀, code₁]) =
      ∑ t : Fin 41, if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
            (if temporary then 0 else 1) then
        (BrouwerNashProgram.minimumGate b ell₀ ell₁ t corner flag temporary).coefficients r
      else 0 := by
  rw [minimumWord, binarySignedFiniteSum_value, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  exact minimumTerm_coefficients source code₀ code₁ out action t corner flag temporary r hr
private theorem sample_position_injective (offset : ℕ) :
    Function.Injective (fun t : Fin 41 => BrouwerNashLayout.sampleBase b ell₀ ell₁ t + offset) := by
  intro s t he
  apply Fin.ext
  apply Nat.mul_right_cancel (show 0 < BrouwerNashLayout.sampleWidth b ell₀ ell₁ by
    simp only [BrouwerNashLayout.sampleWidth]; omega)
  dsimp only [BrouwerNashLayout.sampleBase] at he
  omega

/-- A written interpolation output reads exactly its own canonical gate coefficient. -/
theorem interpolationWord_at (stage : Fin 8) (t : Fin 41) (r : Fin (k * 2))
    (hr : action.length = r.val)
    (hout : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.weightBase b + stage.val) :
    binarySignedValue (interpolationWord stage ![out, action, source, code₀, code₁]) =
      (BrouwerNashProgram.interpolationGate b ell₀ ell₁ t stage.val).coefficients r := by
  rw [interpolationWord_value source code₀ code₁ out action stage r hr]
  have heq (s : Fin 41) : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ s +
      BrouwerNashLayout.weightBase b + stage.val ↔ s = t := by
    constructor
    · intro hs
      apply sample_position_injective source code₀ code₁
        (BrouwerNashLayout.weightBase b + stage.val)
      dsimp only
      omega
    · rintro rfl
      exact hout
  simp only [heq]
  simp

/-- Interpolation families contribute zero outside their allocated outputs. -/
theorem interpolationWord_zero (stage : Fin 8) (r : Fin (k * 2)) (hr : action.length = r.val)
    (hout : ∀ t : Fin 41, out.length ≠ BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.weightBase b + stage.val) :
    binarySignedValue (interpolationWord stage ![out, action, source, code₀, code₁]) = 0 := by
  rw [interpolationWord_value source code₀ code₁ out action stage r hr]
  apply Finset.sum_eq_zero
  intro t _
  exact ite_eq_right (hout t)

/-- A weighted-minimum output reads exactly its own canonical gate coefficient. -/
theorem minimumWord_at (corner : Fin 4) (flag : Fin 2) (temporary : Bool) (t : Fin 41)
    (r : Fin (k * 2)) (hr : action.length = r.val)
    (hout : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
        (if temporary then 0 else 1)) :
    binarySignedValue (minimumWord corner flag temporary ![out, action, source, code₀, code₁]) =
      (BrouwerNashProgram.minimumGate b ell₀ ell₁ t corner flag temporary).coefficients r := by
  rw [minimumWord_value source code₀ code₁ out action corner flag temporary r hr]
  have heq (s : Fin 41) : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ s +
      BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
        (if temporary then 0 else 1) ↔ s = t := by
    constructor
    · intro hs
      apply sample_position_injective source code₀ code₁
        (BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
          (if temporary then 0 else 1))
      dsimp only
      omega
    · rintro rfl
      exact hout
  simp only [heq]
  simp

/-- Weighted-minimum families contribute zero outside their allocated outputs. -/
theorem minimumWord_zero (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    (r : Fin (k * 2)) (hr : action.length = r.val)
    (hout : ∀ t : Fin 41, out.length ≠ BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
        (if temporary then 0 else 1)) :
    binarySignedValue (minimumWord corner flag temporary ![out, action, source, code₀, code₁]) =
      0 := by
  rw [minimumWord_value source code₀ code₁ out action corner flag temporary r hr]
  apply Finset.sum_eq_zero
  intro t _
  exact ite_eq_right (hout t)
end Correctness
private def minimumQuery (index : Fin 16) : (Fin 5 → List Bool) → List Bool :=
  minimumWord ⟨index.val / 4, by omega⟩
    ⟨(index.val / 2) % 2, Nat.mod_lt _ (by decide)⟩ (decide (index.val % 2 = 0))

private def queries : List ((Fin 5 → List Bool) → List Bool) :=
  List.ofFn interpolationWord ++ List.ofFn minimumQuery

/-- All fixed interpolation and weighted-minimum stages, each scanned over forty-one samples. -/
def coefficientWord : (Fin 5 → List Bool) → List Bool := binarySignedQuerySum queries

/-- Fixed query composition retains actual polynomial-time certificates. -/
theorem coefficientWord_cobham : Cobham coefficientWord := by
  apply binarySignedQuerySum_cobham
  intro query hq
  simp only [queries, List.mem_append, List.mem_ofFn] at hq
  rcases hq with ⟨stage, rfl⟩ | ⟨index, rfl⟩
  · exact interpolationWord_cobham stage
  · exact minimumWord_cobham _ _ _

theorem coefficientWord_mem_FPn : FPn coefficientWord := cobham_iff_FPn.mp coefficientWord_cobham



private theorem minimumQuery_position (index : Fin 16) :
    2 * (2 * (index.val / 4) + (index.val / 2) % 2) +
      (if decide (index.val % 2 = 0) then 0 else 1) = index.val := by
  by_cases hp : index.val % 2 = 0
  · simp only [hp, decide_true, ite_true, add_zero]
    omega
  · simp only [hp, decide_false, Bool.false_eq_true, ite_false]
    omega

/-- The fixed family sum preserves every signed coefficient without normalization. -/
theorem coefficientWord_value (v : Fin 5 → List Bool) :
    binarySignedValue (coefficientWord v) =
      (∑ stage : Fin 8, binarySignedValue (interpolationWord stage v)) +
      ∑ index : Fin 16, binarySignedValue (minimumQuery index v) := by
  rw [coefficientWord, binarySignedQuerySum_value]
  simp only [queries, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply]

section CombinedCorrectness
variable (source code₀ code₁ out action : List Bool)
local notation "b" => List.length (pairFst source)
local notation "ell₀" => List.length (circuitUnaryPrefix code₀)
local notation "ell₁" => List.length (circuitUnaryPrefix code₁)
local notation "k" => BrouwerNashLayout.dimension b ell₀ ell₁

private theorem minimumQuery_value (index : Fin 16) (r : Fin (k * 2))
    (hr : action.length = r.val) :
    binarySignedValue (minimumQuery index ![out, action, source, code₀, code₁]) =
      ∑ t : Fin 41, if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.minimumBase b ell₀ ell₁ + index.val then
        (BrouwerNashProgram.minimumGate b ell₀ ell₁ t
          ⟨index.val / 4, by omega⟩ ⟨(index.val / 2) % 2, Nat.mod_lt _ (by decide)⟩
            (decide (index.val % 2 = 0))).coefficients r else 0 := by
  rw [minimumQuery, minimumWord_value source code₀ code₁ out action _ _ _ r hr]
  apply Finset.sum_congr rfl
  intro t _
  have he : BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.minimumTemporary b ell₀ ell₁
        ⟨index.val / 4, by omega⟩ ⟨(index.val / 2) % 2, Nat.mod_lt _ (by decide)⟩ +
          (if decide (index.val % 2 = 0) then 0 else 1) =
        BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.minimumBase b ell₀ ell₁ + index.val := by
    dsimp only [BrouwerNashLayout.minimumTemporary]
    have hp := minimumQuery_position index
    omega
  rw [he]

private theorem interpolation_local_lt (stage : Fin 8) :
    BrouwerNashLayout.weightBase b + stage.val < BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
  have hs := stage.isLt
  dsimp only [BrouwerNashLayout.weightBase, BrouwerNashLayout.sampleWidth]
  omega

private theorem minimum_local_lt (index : Fin 16) :
    BrouwerNashLayout.minimumBase b ell₀ ell₁ + index.val <
      BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
  have hs := index.isLt
  dsimp only [BrouwerNashLayout.minimumBase, BrouwerNashLayout.colorBase,
    BrouwerNashLayout.weightBase, BrouwerNashLayout.sampleWidth]
  omega

private theorem same_local (t t' : Fin 41) (i i' : ℕ)
    (hi : i < BrouwerNashLayout.sampleWidth b ell₀ ell₁)
    (hi' : i' < BrouwerNashLayout.sampleWidth b ell₀ ell₁)
    (ho : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t + i)
    (he : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t' + i') : i = i' :=
  (BrouwerNashQueryRegions.sampleOutput_injective b ell₀ ell₁ t t' i i'
    hi hi' (ho.symm.trans he)).2

/-- On an interpolation output, the combined fixed families emit its canonical coefficient. -/
theorem coefficientWord_interpolation_at (stage : Fin 8) (t : Fin 41) (r : Fin (k * 2))
    (hr : action.length = r.val)
    (ho : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      (BrouwerNashLayout.weightBase b + stage.val)) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      (BrouwerNashProgram.interpolationGate b ell₀ ell₁ t stage.val).coefficients r := by
  rw [coefficientWord_value]
  have hm (index : Fin 16) :
      binarySignedValue (minimumQuery index ![out, action, source, code₀, code₁]) = 0 := by
    rw [minimumQuery_value source code₀ code₁ out action index r hr]
    apply Finset.sum_eq_zero
    intro t' _
    apply ite_eq_right
    intro he
    have hx := same_local source code₀ code₁ out t t' _ _
      (interpolation_local_lt source code₀ code₁ stage)
      (minimum_local_lt source code₀ code₁ index) ho (by omega)
    have hs := stage.isLt
    dsimp only [BrouwerNashLayout.minimumBase, BrouwerNashLayout.colorBase] at hx
    omega
  simp only [hm, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single stage]
  · apply interpolationWord_at source code₀ code₁ out action stage t r hr
    omega
  · intro stage' _ hne
    apply interpolationWord_zero source code₀ code₁ out action stage' r hr
    intro t' he
    have hx := same_local source code₀ code₁ out t t' _ _
      (interpolation_local_lt source code₀ code₁ stage)
      (interpolation_local_lt source code₀ code₁ stage') ho (by omega)
    exact hne (Fin.ext (by omega))
  · simp
private theorem minimumQuery_at (index : Fin 16) (t : Fin 41) (r : Fin (k * 2))
    (hr : action.length = r.val)
    (ho : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      (BrouwerNashLayout.minimumBase b ell₀ ell₁ + index.val)) :
    binarySignedValue (minimumQuery index ![out, action, source, code₀, code₁]) =
      (BrouwerNashProgram.minimumGate b ell₀ ell₁ t
        ⟨index.val / 4, by omega⟩ ⟨(index.val / 2) % 2, Nat.mod_lt _ (by decide)⟩
          (decide (index.val % 2 = 0))).coefficients r := by
  rw [minimumQuery]
  apply minimumWord_at source code₀ code₁ out action _ _ _ t r hr
  dsimp only [BrouwerNashLayout.minimumTemporary]
  have hp := minimumQuery_position index
  omega

private theorem coefficientWord_minimumIndex_at (index : Fin 16) (t : Fin 41)
    (r : Fin (k * 2)) (hr : action.length = r.val)
    (ho : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      (BrouwerNashLayout.minimumBase b ell₀ ell₁ + index.val)) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      (BrouwerNashProgram.minimumGate b ell₀ ell₁ t
        ⟨index.val / 4, by omega⟩ ⟨(index.val / 2) % 2, Nat.mod_lt _ (by decide)⟩
          (decide (index.val % 2 = 0))).coefficients r := by
  rw [coefficientWord_value]
  have hz (stage : Fin 8) :
      binarySignedValue (interpolationWord stage ![out, action, source, code₀, code₁]) = 0 := by
    apply interpolationWord_zero source code₀ code₁ out action stage r hr
    intro t' he
    have hx := same_local source code₀ code₁ out t t' _ _
      (minimum_local_lt source code₀ code₁ index)
      (interpolation_local_lt source code₀ code₁ stage) ho (by omega)
    have hs := stage.isLt
    dsimp only [BrouwerNashLayout.minimumBase, BrouwerNashLayout.colorBase] at hx
    omega
  simp only [hz, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single index]
  · exact minimumQuery_at source code₀ code₁ out action index t r hr ho
  · intro index' _ hne
    rw [minimumQuery_value source code₀ code₁ out action index' r hr]
    apply Finset.sum_eq_zero
    intro t' _
    apply ite_eq_right
    intro he
    have hx := same_local source code₀ code₁ out t t' _ _
      (minimum_local_lt source code₀ code₁ index)
      (minimum_local_lt source code₀ code₁ index') ho (by omega)
    exact hne (Fin.ext (by omega))
  · simp

/-- On a weighted-minimum output, the combined fixed families emit its canonical coefficient. -/
theorem coefficientWord_minimum_at (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    (t : Fin 41) (r : Fin (k * 2)) (hr : action.length = r.val)
    (ho : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      (BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
        (if temporary then 0 else 1))) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) =
      (BrouwerNashProgram.minimumGate b ell₀ ell₁ t corner flag temporary).coefficients r := by
  have hc := corner.isLt
  have hf := flag.isLt
  let index : Fin 16 := ⟨4 * corner.val + 2 * flag.val + (if temporary then 0 else 1),
    by cases temporary <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega⟩
  have hd : index.val / 4 = corner.val := by
    dsimp only [index]
    cases temporary <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hflag : (index.val / 2) % 2 = flag.val := by
    dsimp only [index]
    cases temporary <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  have ht : decide (index.val % 2 = 0) = temporary := by
    dsimp only [index]
    cases temporary
    · apply decide_eq_false_iff_not.mpr
      change (4 * corner.val + 2 * flag.val + 1) % 2 ≠ 0
      omega
    · apply decide_eq_true_eq.mpr
      change (4 * corner.val + 2 * flag.val + 0) % 2 = 0
      omega
  have hout : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      (BrouwerNashLayout.minimumBase b ell₀ ell₁ + index.val) := by
    dsimp only [index]
    simp only [BrouwerNashLayout.minimumTemporary] at ho
    omega
  have hv := coefficientWord_minimumIndex_at source code₀ code₁ out action index t r hr hout
  have hec : (⟨index.val / 4, by omega⟩ : Fin 4) = corner := Fin.ext hd
  have hef : (⟨(index.val / 2) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = flag := Fin.ext hflag
  simpa only [hec, hef, ht] using hv

/-- Fixed families emit zero outside the interpolation and minimum intervals of every sample. -/
theorem coefficientWord_eq_zero_of_outside (r : Fin (k * 2)) (hr : action.length = r.val)
    (hno : ∀ t : Fin 41,
      ¬ (BrouwerNashLayout.sampleBase b ell₀ ell₁ t + BrouwerNashLayout.weightBase b ≤
        out.length ∧ out.length < BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.colorBase b) ∧
      ¬ (BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
        BrouwerNashLayout.minimumBase b ell₀ ell₁ ≤ out.length ∧
        out.length < BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.sampleWidth b ell₀ ell₁)) :
    binarySignedValue (coefficientWord ![out, action, source, code₀, code₁]) = 0 := by
  rw [coefficientWord_value]
  have hz (stage : Fin 8) :
      binarySignedValue (interpolationWord stage ![out, action, source, code₀, code₁]) = 0 := by
    apply interpolationWord_zero source code₀ code₁ out action stage r hr
    intro t he
    apply (hno t).1
    have hs := stage.isLt
    dsimp only [BrouwerNashLayout.colorBase]
    omega
  have hm (index : Fin 16) :
      binarySignedValue (minimumQuery index ![out, action, source, code₀, code₁]) = 0 := by
    rw [minimumQuery_value source code₀ code₁ out action index r hr]
    apply Finset.sum_eq_zero
    intro t _
    apply ite_eq_right
    intro he
    apply (hno t).2
    have hx := minimum_local_lt source code₀ code₁ index
    omega
  simp only [hz, hm, Finset.sum_const_zero, add_zero]
end CombinedCorrectness
end GameTheory.Complexity.Backend.BrouwerNashInterpolationQuery
