import GameTheoryComplexity.Backend.BrouwerNashQueryRegions
import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
import GameTheoryComplexity.Backend.BrouwerNashHeaders
import GameTheoryComplexity.Backend.BimatrixRawGateMachine
import GameTheoryComplexity.Backend.BinaryIndexedLookup
import GameTheoryComplexity.Backend.BinarySignedFiniteSum

/-! Polynomial coefficient queries for the canonical ripple-increment stages. Each source-bit
ordinal is scanned at its numeric placement, and literal raw-gate serialization preserves
inline negation and aliased references. The correctness lemmas identify every allocated output
and retain a total zero fallback elsewhere. -/
namespace GameTheory.Complexity.Backend.BrouwerNashIncrementQuery
open _root_.Complexity _root_.Complexity.Cobham _root_.Complexity.CircuitCode
open scoped BigOperators

private def header (f : (Fin 3 → List Bool) → List Bool)
    (v : Fin 7 → List Bool) : List Bool := f ![v 4, v 5, v 6]
private theorem header_cobham {f : (Fin 3 → List Bool) → List Bool} (hf : Cobham f) :
    Cobham (header f) := (Cobham.comp₃ hf (.proj 4) (.proj 5) (.proj 6)).of_eq fun _ => rfl
private def depthR : (Fin 7 → List Bool) → List Bool := header BrouwerNashHeaders.sourceDepthRuler
private theorem depthR_cobham : Cobham depthR :=
  header_cobham BrouwerNashHeaders.sourceDepthRuler_cobham
private def startR (v : Fin 7 → List Bool) : List Bool :=
  header BrouwerNashHeaders.globalRuler v ++ smash (v 1) (header BrouwerNashHeaders.sampleRuler v)
private theorem startR_cobham : Cobham startR :=
  appendFn (header_cobham BrouwerNashHeaders.globalRuler_cobham)
    (Cobham.comp₂ Cobham.smash (.proj 1) (header_cobham BrouwerNashHeaders.sampleRuler_cobham))
private def incrementBaseR (axis : Fin 2) (v : Fin 7 → List Bool) : List Bool :=
  [false, false] ++ smash (depthR v) (List.replicate (4 + 4 * axis.val) true)
private theorem incrementBaseR_cobham (axis : Fin 2) : Cobham (incrementBaseR axis) :=
  appendFn (Cobham.const [false, false]) (Cobham.comp₂ Cobham.smash depthR_cobham (Cobham.const _))
private def incrementR (axis : Fin 2) (stage : Fin 4) (v : Fin 7 → List Bool) : List Bool :=
  startR v ++ incrementBaseR axis v ++ smash (v 0) (List.replicate 4 true) ++
    List.replicate stage.val false
private theorem incrementR_cobham (axis : Fin 2) (stage : Fin 4) : Cobham (incrementR axis stage) :=
  appendFn (appendFn (appendFn startR_cobham (incrementBaseR_cobham axis))
    (Cobham.comp₂ Cobham.smash (.proj 0) (Cobham.const _))) (Cobham.const _)
private def primaryR (axis : Fin 2) (v : Fin 7 → List Bool) : List Bool :=
  startR v ++ [false, false] ++ smash (depthR v) (List.replicate (2 * axis.val) true) ++
    smash ((depthR v).drop ((v 0).length + 1)) [true, true]
private theorem primaryR_cobham (axis : Fin 2) : Cobham (primaryR axis) := by
  have hd : Cobham fun v : Fin 7 → List Bool => (depthR v).drop ((v 0).length + 1) :=
    (dropFn (appendFn (.proj 0) (Cobham.const [false])) depthR_cobham).of_eq
      fun _ => by simp
  exact appendFn (appendFn (appendFn startR_cobham (Cobham.const [false, false]))
    (Cobham.comp₂ Cobham.smash depthR_cobham (Cobham.const _)))
    (Cobham.comp₂ Cobham.smash hd (Cobham.const [true, true]))
private def carryR (axis : Fin 2) (v : Fin 7 → List Bool) : List Bool :=
  caseBit₀ (lenEqFlag (v 0) []) [false, false]
    (startR v ++ incrementBaseR axis v ++ smash (v 0).tail (List.replicate 4 true) ++
      [false, false, false])
private theorem carryR_cobham (axis : Fin 2) : Cobham (carryR axis) :=
  Cobham.iteFn (lenEqFlag_mem (.proj 0) Cobham.empty) (Cobham.const [false, false])
    (appendFn (appendFn (appendFn startR_cobham (incrementBaseR_cobham axis))
      (Cobham.comp₂ Cobham.smash (Cobham.tailFn (.proj 0)) (Cobham.const _))) (Cobham.const _))
private def firstR (axis : Fin 2) (stage : Fin 4) : (Fin 7 → List Bool) → List Bool :=
  if stage.val = 2 then incrementR axis 0 else primaryR axis
private def secondR (axis : Fin 2) (stage : Fin 4) : (Fin 7 → List Bool) → List Bool :=
  if stage.val = 2 then incrementR axis 1 else carryR axis
private theorem firstR_cobham (axis : Fin 2) (stage : Fin 4) : Cobham (firstR axis stage) := by
  unfold firstR
  split_ifs
  · exact incrementR_cobham axis 0
  · exact primaryR_cobham axis
private theorem secondR_cobham (axis : Fin 2) (stage : Fin 4) : Cobham (secondR axis stage) := by
  unfold secondR
  split_ifs
  · exact incrementR_cobham axis 1
  · exact carryR_cobham axis
private def unary (ruler : List Bool) : List Bool := smash [true] ruler
private theorem unary_fn {p : ℕ} {f : (Fin p → List Bool) → List Bool} (hf : Cobham f) :
    Cobham fun v => unary (f v) := Cobham.comp₂ Cobham.smash (Cobham.const [true]) hf
private def flags (stage : Fin 4) : List Bool :=
  match stage.val with
  | 0 => [true, false, true]
  | 1 => [true, true, false]
  | 2 => [false, false, false]
  | _ => [true, false, false]
private def suffix (axis : Fin 2) (stage : Fin 4) (v : Fin 7 → List Bool) : List Bool :=
  flags stage ++ unary (firstR axis stage v) ++ [false] ++ unary (secondR axis stage v) ++ [false]
private theorem suffix_cobham (axis : Fin 2) (stage : Fin 4) : Cobham (suffix axis stage) :=
  appendFn (appendFn (appendFn (appendFn (Cobham.const _) (unary_fn (firstR_cobham axis stage)))
    (Cobham.const [false])) (unary_fn (secondR_cobham axis stage))) (Cobham.const [false])
private def test (axis : Fin 2) (stage : Fin 4) (v : Fin 7 → List Bool) : List Bool :=
  andBit (lenEqFlag (v 2) (incrementR axis stage v)) (notBit (lenLeFlag (v 0) (depthR v)))
private theorem test_cobham (axis : Fin 2) (stage : Fin 4) : Cobham (test axis stage) :=
  Cobham.andFn (lenEqFlag_mem (.proj 2) (incrementR_cobham axis stage))
    (Cobham.notFn (lenLeFlag_mem (.proj 0) depthR_cobham))
private def term (axis : Fin 2) (stage : Fin 4) (v : Fin 7 → List Bool) : List Bool :=
  BimatrixRawGateMachine.coefficientWord
    ![header BrouwerNashHeaders.dimensionRuler v, suffix axis stage v, v 3]
private theorem term_cobham (axis : Fin 2) (stage : Fin 4) : Cobham (term axis stage) :=
  (Cobham.comp₃ BimatrixRawGateMachine.coefficientWord_cobham
    (header_cobham BrouwerNashHeaders.dimensionRuler_cobham) (suffix_cobham axis stage)
    (.proj 3)).of_eq fun _ => rfl

private def indexedWord (axis : Fin 2) (stage : Fin 4) (v : Fin 6 → List Bool) : List Bool :=
  binaryIndexedLookup (test axis stage) (term axis stage)
    (BrouwerNashHeaders.sourceDepthRuler ![v 3, v 4, v 5])
    (BrouwerNashHeaders.widthRuler ![v 3, v 4, v 5]) v
private theorem indexedWord_cobham (axis : Fin 2) (stage : Fin 4) :
    Cobham (indexedWord axis stage) := by
  have hc : Cobham fun v : Fin 6 → List Bool =>
      BrouwerNashHeaders.sourceDepthRuler ![v 3, v 4, v 5] :=
    Cobham.comp₃ BrouwerNashHeaders.sourceDepthRuler_cobham (.proj 3) (.proj 4) (.proj 5)
  have hw : Cobham fun v : Fin 6 → List Bool =>
      BrouwerNashHeaders.widthRuler ![v 3, v 4, v 5] :=
    Cobham.comp₃ BrouwerNashHeaders.widthRuler_cobham (.proj 3) (.proj 4) (.proj 5)
  have hg : ∀ i : Fin 8, Cobham fun v : Fin 6 → List Bool =>
      (Fin.cons (BrouwerNashHeaders.sourceDepthRuler ![v 3, v 4, v 5])
        (Fin.cons (BrouwerNashHeaders.widthRuler ![v 3, v 4, v 5]) v) : Fin 8 → List Bool) i := by
    intro i
    exact Fin.cases hc (fun j => Fin.cases hw (fun a => .proj a) j) i
  exact (Cobham.comp (binaryIndexedLookup_cobham (test_cobham axis stage)
    (term_cobham axis stage)) hg).of_eq fun _ => rfl

/-- A ripple stage scans source-bit depth at each of the forty-one sample placements. -/
def coefficientWord (axis : Fin 2) (stage : Fin 4) : (Fin 5 → List Bool) → List Bool :=
  binarySignedFiniteSum (indexedWord axis stage) 41
theorem coefficientWord_cobham (axis : Fin 2) (stage : Fin 4) :
    Cobham (coefficientWord axis stage) :=
  binarySignedFiniteSum_cobham (indexedWord_cobham axis stage) 41
theorem coefficientWord_mem_FPn (axis : Fin 2) (stage : Fin 4) :
    FPn (coefficientWord axis stage) :=
  cobham_iff_FPn.mp (coefficientWord_cobham axis stage)

/-- Add all eight fixed ripple families without imposing representation choices on clients. -/
def allCoefficientWord : (Fin 5 → List Bool) → List Bool :=
  binarySignedQuerySum [coefficientWord 0 0, coefficientWord 0 1,
    coefficientWord 0 2, coefficientWord 0 3, coefficientWord 1 0,
    coefficientWord 1 1, coefficientWord 1 2, coefficientWord 1 3]
theorem allCoefficientWord_cobham : Cobham allCoefficientWord := by
  apply binarySignedQuerySum_cobham
  intro query hquery
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hquery
  rcases hquery with h | h | h | h | h | h | h | h <;>
    subst query <;> exact coefficientWord_cobham _ _
theorem allCoefficientWord_mem_FPn : FPn allCoefficientWord :=
  cobham_iff_FPn.mp allCoefficientWord_cobham
private def raw (axis : Fin 2) (stage : Fin 4) (v : Fin 7 → List Bool) : RawGate :=
  ⟨if stage.val = 2 then .or else .and, (firstR axis stage v).length,
    (secondR axis stage v).length, decide (stage.val = 1), decide (stage.val = 0)⟩
private theorem suffix_encode (axis : Fin 2) (stage : Fin 4) (v : Fin 7 → List Bool) :
    suffix axis stage v = (raw axis stage v).encode := by
  fin_cases stage <;> simp [suffix, flags, raw, RawGate.encode, RawGate.opBit,
    unary, _root_.Complexity.smash, NatCode.encode, List.append_assoc]

private theorem startR_length (v : Fin 7 → List Bool) :
    (startR v).length = BrouwerNashLayout.globalCount (pairFst (v 4)).length +
      (v 1).length * BrouwerNashLayout.sampleWidth (pairFst (v 4)).length
        (circuitUnaryPrefix (v 5)).length (circuitUnaryPrefix (v 6)).length := by
  simp only [startR, List.length_append, smash_length, header,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rfl
private theorem incrementBaseR_length (axis : Fin 2) (v : Fin 7 → List Bool) :
    (incrementBaseR axis v).length =
      BrouwerNashLayout.incrementBase (pairFst (v 4)).length axis := by
  simp only [incrementBaseR, List.length_append, List.length_cons, List.length_nil,
    smash_length, List.length_replicate, depthR, header, BrouwerNashHeaders.sourceDepthRuler,
    Matrix.cons_val_zero, BrouwerNashLayout.incrementBase]
  ring
private theorem incrementR_length (axis : Fin 2) (stage : Fin 4) (v : Fin 7 → List Bool) :
    (incrementR axis stage v).length = (startR v).length +
      BrouwerNashLayout.increment (pairFst (v 4)).length axis (v 0).length stage := by
  simp only [incrementR, List.length_append, incrementBaseR_length, smash_length,
    List.length_replicate, BrouwerNashLayout.increment]
  omega
private theorem primaryR_length (axis : Fin 2) (v : Fin 7 → List Bool) :
    (primaryR axis v).length = (startR v).length +
      BrouwerNashProgram.primaryBit (pairFst (v 4)).length axis (v 0).length := by
  have hd : (depthR v).length = (pairFst (v 4)).length := rfl
  simp only [primaryR, List.length_append, List.length_cons, List.length_nil, smash_length,
    List.length_replicate, List.length_drop, hd, BrouwerNashProgram.primaryBit,
    BrouwerNashLayout.digit]
  have hs : (pairFst (v 4)).length - ((v 0).length + 1) =
      (pairFst (v 4)).length - 1 - (v 0).length := by omega
  rw [hs]
  ring
private theorem carryR_length (axis : Fin 2) (v : Fin 7 → List Bool) :
    (carryR axis v).length = if (v 0).length = 0 then BrouwerNashLayout.one else
      (startR v).length + BrouwerNashLayout.increment (pairFst (v 4)).length axis
        ((v 0).length - 1) 3 := by
  rcases lenEqFlag_flag (v 0) [] with he | he
  · have hz := (lenEqFlag_eq_true_iff _ _).mp he
    simp only [List.length_nil] at hz
    simp only [carryR, he, caseBit₀, Bool.cond_true, hz, ite_true,
      BrouwerNashLayout.one, List.length_cons, List.length_nil]
  · have hz : (v 0).length ≠ 0 := by
      intro hz
      have ht := (lenEqFlag_eq_true_iff (v 0) []).mpr (by simp [hz])
      rw [he] at ht
      contradiction
    simp only [carryR, he, caseBit₀, Bool.cond_false, hz, ite_false, List.length_append,
      incrementBaseR_length, smash_length, List.length_tail, List.length_replicate,
      List.length_cons, List.length_nil, BrouwerNashLayout.increment]
    norm_num
    omega

private theorem lenEq_value (a b : List Bool) : lenEqFlag a b = [decide (a.length = b.length)] := by
  rcases lenEqFlag_flag a b with h | h
  · rw [h]; simp [(lenEqFlag_eq_true_iff a b).mp h]
  · rw [h]
    have hn : a.length ≠ b.length := by
      intro he
      have ht := (lenEqFlag_eq_true_iff a b).mpr he
      rw [h] at ht
      contradiction
    simp [hn]
private theorem lenLe_value (a b : List Bool) : lenLeFlag a b = [decide (b.length ≤ a.length)] := by
  rcases lenLeFlag_flag a b with h | h
  · rw [h]; simp [(lenLeFlag_eq_true_iff a b).mp h]
  · rw [h]
    have hn : ¬ b.length ≤ a.length := by
      intro he
      have ht := (lenLeFlag_eq_true_iff a b).mpr he
      rw [h] at ht
      contradiction
    simp [hn]
private theorem test_value (axis : Fin 2) (stage : Fin 4) (v : Fin 7 → List Bool) :
    test axis stage v = [decide ((v 2).length = (startR v).length +
      BrouwerNashLayout.increment (pairFst (v 4)).length axis (v 0).length stage ∧
        (v 0).length < (pairFst (v 4)).length)] := by
  rw [test, lenEq_value, incrementR_length, lenLe_value]
  have hd : (depthR v).length = (pairFst (v 4)).length := rfl
  rw [hd]
  by_cases ho : (v 2).length = (startR v).length +
      BrouwerNashLayout.increment (pairFst (v 4)).length axis (v 0).length stage <;>
    by_cases hn : (pairFst (v 4)).length ≤ (v 0).length <;>
      simp [ho, hn, show (v 0).length < (pairFst (v 4)).length ↔
        ¬ (pairFst (v 4)).length ≤ (v 0).length from lt_iff_not_ge,
        andBit, notBit, caseBit₀]

section Correctness
variable (source code₀ code₁ out action : List Bool)
local notation "b" => List.length (pairFst source)
local notation "ell₀" => List.length (circuitUnaryPrefix code₀)
local notation "ell₁" => List.length (circuitUnaryPrefix code₁)
local notation "k" => BrouwerNashLayout.dimension b ell₀ ell₁

private theorem raw_coefficients_congr {d e : ℕ} (hde : d = e) (g : RawGate)
    (hd : g.WellFormedAt d) (he : g.WellFormedAt e)
    (i : Fin (d * 2)) (j : Fin (e * 2)) (hij : i.val = j.val) :
    BimatrixRawGate.coefficients g hd i = BimatrixRawGate.coefficients g he j := by
  subst e
  have hi : i = j := Fin.ext hij
  subst j
  rfl
private theorem term_coefficients (axis : Fin 2) (stage : Fin 4) (j : List Bool)
    (hj : j.length < b) (t : Fin 41) (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (term axis stage
      ![j, List.replicate t.val false, out, action, source, code₀, code₁]) =
      (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j.length stage).coefficients r := by
  let v : Fin 7 → List Bool := ![j, List.replicate t.val false, out, action, source, code₀, code₁]
  have hv₀ : v 0 = j := rfl
  have hv₁ : v 1 = List.replicate t.val false := rfl
  have hv₄ : v 4 = source := rfl
  have hv₅ : v 5 = code₀ := rfl
  have hv₆ : v 6 = code₁ := rfl
  have hs : (startR v).length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t := by
    rw [startR_length]
    rw [hv₁, hv₄, hv₅, hv₆, List.length_replicate]
    rfl
  have hp : BrouwerNashProgram.primaryBit b axis j.length <
      BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
    fin_cases axis <;>
      simp only [BrouwerNashProgram.primaryBit, BrouwerNashLayout.digit,
        BrouwerNashLayout.sampleWidth] <;> norm_num <;> omega
  have hprimary : (primaryR axis v).length =
      (BrouwerNashProgram.sampleRef b ell₀ ell₁ t
        (BrouwerNashProgram.primaryBit b axis j.length)).val := by
    rw [primaryR_length, hs, hv₄, hv₀]
    exact (BrouwerNashProgram.slot_val _ _ _ _
      (BrouwerNashLayout.sample_lt_dimension _ _ _ t _ hp)).symm
  have hi (s : Fin 4) : (incrementR axis s v).length =
      (BrouwerNashProgram.sampleRef b ell₀ ell₁ t
        (BrouwerNashLayout.increment b axis j.length s)).val := by
    rw [incrementR_length, hs, hv₄, hv₀]
    exact (BrouwerNashProgram.slot_val _ _ _ _ (BrouwerNashLayout.sample_lt_dimension _ _ _ t _
      (BrouwerNashProgram.increment_lt_sampleWidth _ _ _ axis _ hj s))).symm
  have hc : (carryR axis v).length = if j.length = 0 then BrouwerNashLayout.one else
      (BrouwerNashProgram.sampleRef b ell₀ ell₁ t
        (BrouwerNashLayout.increment b axis (j.length - 1) 3)).val := by
    rw [carryR_length, hs, hv₄, hv₀]
    split_ifs with hz
    · rfl
    · exact (BrouwerNashProgram.slot_val _ _ _ _ (BrouwerNashLayout.sample_lt_dimension _ _ _ t _
        (BrouwerNashProgram.increment_lt_sampleWidth b ell₀ ell₁ axis
          (j.length - 1) (by omega) 3))).symm
  have hfirst : (firstR axis stage v).length < k := by
    rw [firstR]
    split_ifs
    · rw [hi]
      exact Fin.isLt _
    · rw [hprimary]
      exact Fin.isLt _
  have hsecond : (secondR axis stage v).length < k := by
    rw [secondR]
    split_ifs
    · rw [hi]
      exact Fin.isLt _
    · rw [hc]
      split_ifs
      · exact BrouwerNashProgram.one_lt_dimension _ _ _
      · exact Fin.isLt _
  have href : (raw axis stage v).WellFormedAt k := ⟨hfirst, hsecond⟩
  have hdim : (header BrouwerNashHeaders.dimensionRuler v).length = k := by
    rw [header, BrouwerNashHeaders.dimensionRuler_length]
    rfl
  change binarySignedValue (BimatrixRawGateMachine.coefficientWord
    ![header BrouwerNashHeaders.dimensionRuler v, suffix axis stage v, action]) = _
  rw [suffix_encode]
  have href' : (raw axis stage v).WellFormedAt
      (header BrouwerNashHeaders.dimensionRuler v).length := by rwa [hdim]
  let r' : Fin ((header BrouwerNashHeaders.dimensionRuler v).length * 2) :=
    ⟨r.val, by rw [hdim]; exact r.isLt⟩
  have he := BimatrixRawGateMachine.coefficientWord_encode
    (header BrouwerNashHeaders.dimensionRuler v) action (raw axis stage v) href' [] r' hr
  rw [List.append_nil] at he
  rw [he]
  have hg : BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j.length stage =
      BrouwerNashProgram.guardedRaw (raw axis stage v) := by
    unfold BrouwerNashProgram.incrementGate
    apply congrArg BrouwerNashProgram.guardedRaw
    fin_cases stage <;>
      simp only [raw, firstR, secondR, Nat.reduceEqDiff, hprimary, hc, hi,
        decide_true, decide_false, ite_true, ite_false]
  rw [hg, BrouwerNashProgram.guardedRaw_eq _ href]
  change BimatrixRawGate.coefficients (raw axis stage v) href' r' =
    BimatrixRawGate.coefficients (raw axis stage v) href r
  exact raw_coefficients_congr hdim (raw axis stage v) href' href r' r rfl

private theorem indexedWord_value (axis : Fin 2) (stage : Fin 4) (t : Fin 41)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (indexedWord axis stage
      ![List.replicate t.val false, out, action, source, code₀, code₁]) =
      ∑ j ∈ Finset.range b, if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.increment b axis j stage then
        (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j stage).coefficients r else 0 := by
  let hit := fun j => decide (out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
    BrouwerNashLayout.increment b axis j stage ∧ j < b)
  let value := fun j =>
    (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j stage).coefficients r
  have hw : 0 < (BrouwerNashHeaders.widthRuler ![source, code₀, code₁]).length := by
    rw [BrouwerNashHeaders.widthRuler_length]
    omega
  have hx := binaryIndexedLookup_sum_value (test axis stage) (term axis stage)
    (BrouwerNashHeaders.widthRuler ![source, code₀, code₁])
    ![List.replicate t.val false, out, action, source, code₀, code₁] hit value
    (by
      intro ordinal
      change test axis stage ![ordinal, List.replicate t.val false, out, action,
        source, code₀, code₁] = _
      rw [test_value, startR_length]
      have h₁ : (![ordinal, List.replicate t.val false, out, action,
          source, code₀, code₁] : Fin 7 → List Bool) 1 = List.replicate t.val false := rfl
      have h₂ : (![ordinal, List.replicate t.val false, out, action,
          source, code₀, code₁] : Fin 7 → List Bool) 2 = out := rfl
      have h₄ : (![ordinal, List.replicate t.val false, out, action,
          source, code₀, code₁] : Fin 7 → List Bool) 4 = source := rfl
      have h₅ : (![ordinal, List.replicate t.val false, out, action,
          source, code₀, code₁] : Fin 7 → List Bool) 5 = code₀ := rfl
      have h₆ : (![ordinal, List.replicate t.val false, out, action,
          source, code₀, code₁] : Fin 7 → List Bool) 6 = code₁ := rfl
      rw [h₁, h₂, h₄, h₅, h₆, List.length_replicate]
      change [decide (out.length = BrouwerNashLayout.globalCount b + t.val *
        BrouwerNashLayout.sampleWidth b ell₀ ell₁ +
          BrouwerNashLayout.increment b axis ordinal.length stage ∧ ordinal.length < b)] = _
      rfl)
    (by
      intro ordinal hhit
      have hj := (of_decide_eq_true hhit).2
      exact term_coefficients source code₀ code₁ out action axis stage ordinal hj t r hr)
    hw (BrouwerNashHeaders.sourceDepthRuler ![source, code₀, code₁])
    (by
      intro i _ _
      apply BrouwerNashHeaders.widthRuler_fits
      rw [BrouwerNashHeaders.dimensionRuler_length]
      have hb := BrouwerNashProgram.incrementGate_bound b ell₀ ell₁ t axis i stage r
      rw [← Int.natCast_natAbs] at hb
      exact_mod_cast hb)
    (by
      intro i _ j _ hi hj
      have hi' := (of_decide_eq_true hi).1
      have hj' := (of_decide_eq_true hj).1
      dsimp only [BrouwerNashLayout.increment] at hi' hj'
      omega)
  change binarySignedValue (binaryIndexedLookup (test axis stage) (term axis stage)
    (BrouwerNashHeaders.sourceDepthRuler ![source, code₀, code₁])
    (BrouwerNashHeaders.widthRuler ![source, code₀, code₁])
    ![List.replicate t.val false, out, action, source, code₀, code₁]) = _
  rw [hx]
  change (∑ j ∈ Finset.range b, if hit j then value j else 0) = _
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [hit, value]
  simp only [Finset.mem_range.mp hj, and_true, decide_eq_true_eq]

/-- Each ripple family emits exactly the guarded coefficients of its canonical raw gates. -/
theorem coefficientWord_value (axis : Fin 2) (stage : Fin 4)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (coefficientWord axis stage ![out, action, source, code₀, code₁]) =
      ∑ t : Fin 41, ∑ j ∈ Finset.range b,
        if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.increment b axis j stage then
          (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j stage).coefficients r else 0 := by
  rw [coefficientWord, binarySignedFiniteSum_value, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  exact indexedWord_value source code₀ code₁ out action axis stage t r hr
/-- A valid ripple output selects exactly its own canonical stage, including aliased inputs. -/
theorem coefficientWord_at (axis : Fin 2) (stage : Fin 4) (t : Fin 41) (j : ℕ)
    (hj : j < b) (hout : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.increment b axis j stage) (r : Fin (k * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord axis stage ![out, action, source, code₀, code₁]) =
      (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j stage).coefficients r := by
  rw [coefficientWord_value source code₀ code₁ out action axis stage r hr]
  have hhit (s : Fin 41) (i : ℕ) (hi : i < b)
      (he : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ s +
        BrouwerNashLayout.increment b axis i stage) : s = t ∧ i = j := by
    have hh := BrouwerNashQueryRegions.sampleOutput_injective b ell₀ ell₁ s t _ _
      (BrouwerNashProgram.increment_lt_sampleWidth b ell₀ ell₁ axis i hi stage)
      (BrouwerNashProgram.increment_lt_sampleWidth b ell₀ ell₁ axis j hj stage)
      (he.symm.trans hout)
    refine ⟨hh.1, ?_⟩
    dsimp only [BrouwerNashLayout.increment] at hh
    omega
  rw [Finset.sum_eq_single t]
  · rw [Finset.sum_eq_single j]
    · simp only [hout, ite_true]
    · intro i hi hne
      apply ite_eq_right
      intro he
      exact hne (hhit t i (Finset.mem_range.mp hi) he).2
    · simp [hj]
  · intro s _ hne
    apply Finset.sum_eq_zero
    intro i hi
    apply ite_eq_right
    intro he
    exact hne (hhit s i (Finset.mem_range.mp hi) he).1
  · simp

/-- Outputs outside a ripple family retain the total zero fallback. -/
theorem coefficientWord_zero (axis : Fin 2) (stage : Fin 4)
    (hno : ∀ t : Fin 41, ∀ j < b, out.length ≠
      BrouwerNashLayout.sampleBase b ell₀ ell₁ t + BrouwerNashLayout.increment b axis j stage)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (coefficientWord axis stage ![out, action, source, code₀, code₁]) = 0 := by
  rw [coefficientWord_value source code₀ code₁ out action axis stage r hr]
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro j hj
  exact ite_eq_right (hno t j (Finset.mem_range.mp hj))
/-- The complete increment query sums the canonical gates at every allocated ripple output. -/
theorem allCoefficientWord_value (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (allCoefficientWord ![out, action, source, code₀, code₁]) =
      ∑ axis : Fin 2, ∑ stage : Fin 4, ∑ t : Fin 41, ∑ j ∈ Finset.range b,
        if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.increment b axis j stage then
          (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j stage).coefficients r else 0 := by
  rw [allCoefficientWord, binarySignedQuerySum_value]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    coefficientWord_value source code₀ code₁ out action _ _ r hr,
    Fin.sum_univ_two, Fin.sum_univ_four]
  ring
private theorem increment_index_injective (a a' : Fin 2) (s s' : Fin 4)
    (i j : ℕ) (hi : i < b) (hj : j < b)
    (he : BrouwerNashLayout.increment b a i s = BrouwerNashLayout.increment b a' j s') :
    a = a' ∧ i = j ∧ s = s' := by
  have hs := s.isLt
  have hs' := s'.isLt
  fin_cases a <;> fin_cases a' <;>
    simp only [BrouwerNashLayout.increment, BrouwerNashLayout.incrementBase,
      mul_zero, mul_one, add_zero] at he
  · exact ⟨rfl, by omega, Fin.ext (by omega)⟩
  · omega
  · omega
  · exact ⟨rfl, by omega, Fin.ext (by omega)⟩

/-- Across all ripple families, an allocated output selects its own gate exactly once. -/
theorem allCoefficientWord_at (axis : Fin 2) (stage : Fin 4) (t : Fin 41) (j : ℕ)
    (hj : j < b) (hout : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.increment b axis j stage) (r : Fin (k * 2))
    (hr : action.length = r.val) :
    binarySignedValue (allCoefficientWord ![out, action, source, code₀, code₁]) =
      (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j stage).coefficients r := by
  rw [allCoefficientWord_value source code₀ code₁ out action r hr]
  have hhit (a : Fin 2) (st : Fin 4) (s : Fin 41) (i : ℕ) (hi : i < b)
      (he : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ s +
        BrouwerNashLayout.increment b a i st) : a = axis ∧ st = stage := by
    have hh := BrouwerNashQueryRegions.sampleOutput_injective b ell₀ ell₁ s t _ _
      (BrouwerNashProgram.increment_lt_sampleWidth b ell₀ ell₁ a i hi st)
      (BrouwerNashProgram.increment_lt_sampleWidth b ell₀ ell₁ axis j hj stage)
      (he.symm.trans hout)
    have heq := increment_index_injective source a axis st stage i j hi hj hh.2
    exact ⟨heq.1, heq.2.2⟩
  rw [Finset.sum_eq_single axis]
  · rw [Finset.sum_eq_single stage]
    · rw [← coefficientWord_value source code₀ code₁ out action axis stage r hr]
      exact coefficientWord_at source code₀ code₁ out action axis stage t j hj hout r hr
    · intro st _ hne
      apply Finset.sum_eq_zero
      intro s _
      apply Finset.sum_eq_zero
      intro i hi
      apply ite_eq_right
      intro he
      exact hne (hhit axis st s i (Finset.mem_range.mp hi) he).2
    · simp
  · intro a _ hne
    apply Finset.sum_eq_zero
    intro st _
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro i hi
    apply ite_eq_right
    intro he
    exact hne (hhit a st s i (Finset.mem_range.mp hi) he).1
  · simp

/-- The total increment query vanishes outside every allocated ripple output. -/
theorem allCoefficientWord_zero
    (hno : ∀ (axis : Fin 2) (stage : Fin 4) (t : Fin 41) (j : ℕ), j < b →
      out.length ≠ BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
        BrouwerNashLayout.increment b axis j stage)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (allCoefficientWord ![out, action, source, code₀, code₁]) = 0 := by
  rw [allCoefficientWord_value source code₀ code₁ out action r hr]
  apply Finset.sum_eq_zero
  intro axis _
  apply Finset.sum_eq_zero
  intro stage _
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro j hj
  exact ite_eq_right (hno axis stage t j (Finset.mem_range.mp hj))
/-- Every ripple output lies in its sample's contiguous increment interval. -/
theorem allCoefficientWord_zero_of_outside
    (hno : ∀ t : Fin 41, ¬ (BrouwerNashLayout.sampleBase b ell₀ ell₁ t + 2 + 4 * b ≤
      out.length ∧ out.length < BrouwerNashLayout.sampleBase b ell₀ ell₁ t + 2 + 12 * b))
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (allCoefficientWord ![out, action, source, code₀, code₁]) = 0 := by
  apply allCoefficientWord_zero source code₀ code₁ out action ?_ r hr
  intro axis stage t j hj he
  apply hno t
  have ha := axis.isLt
  have hs := stage.isLt
  have hm := Nat.mul_le_mul_left (4 * b) (show axis.val ≤ 1 by omega)
  dsimp only [BrouwerNashLayout.increment, BrouwerNashLayout.incrementBase] at he
  omega
end Correctness
/-- The contiguous ripple interval consists exactly of four-stage bits on two axes. -/
theorem exists_incrementSlot (b i : ℕ) (hlo : 2 + 4 * b ≤ i) (hhi : i < 2 + 12 * b) :
    ∃ (axis : Fin 2) (stage : Fin 4) (j : ℕ), j < b ∧
      i = BrouwerNashLayout.increment b axis j stage := by
  by_cases hfirst : i < 2 + 8 * b
  · refine ⟨0, ⟨(i - (2 + 4 * b)) % 4, Nat.mod_lt _ (by omega)⟩,
      (i - (2 + 4 * b)) / 4, ?_, ?_⟩
    · omega
    · simp only [BrouwerNashLayout.increment, BrouwerNashLayout.incrementBase,
        Fin.val_zero, mul_zero, add_zero]
      omega
  · refine ⟨1, ⟨(i - (2 + 8 * b)) % 4, Nat.mod_lt _ (by omega)⟩,
      (i - (2 + 8 * b)) / 4, ?_, ?_⟩
    · omega
    · simp only [BrouwerNashLayout.increment, BrouwerNashLayout.incrementBase,
        Fin.val_one, mul_one]
      omega

/-- Every increment slot is the canonical raw ripple gate at its decoded numeric stage. -/
theorem sampleGate_increment_of_interval (b i : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (hlo : 2 + 4 * b ≤ i) (hhi : i < 2 + 12 * b) :
    ∃ (axis : Fin 2) (stage : Fin 4) (j : ℕ), j < b ∧
      i = BrouwerNashLayout.increment b axis j stage ∧
      BrouwerNashProgram.sampleGate b raw₀ raw₁ t i =
        BrouwerNashProgram.incrementGate b raw₀.length raw₁.length t axis j stage := by
  obtain ⟨axis, stage, j, hj, hi⟩ := exists_incrementSlot b i hlo hhi
  refine ⟨axis, stage, j, hj, hi, ?_⟩
  rw [hi]
  exact BrouwerNashProgram.sampleGate_increment b raw₀ raw₁ t axis j hj stage
end GameTheory.Complexity.Backend.BrouwerNashIncrementQuery
