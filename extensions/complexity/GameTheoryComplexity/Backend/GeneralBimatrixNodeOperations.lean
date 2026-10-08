import GameTheoryComplexity.Backend.GeneralBimatrixNodeValidation
import GameTheoryComplexity.Backend.BimatrixNodeOperations

/-! Certified port operations driven by the serialized integer dictionary.
The selected row ordinal is converted to its canonical variable position by
membership lookup before exchanging node bits. Switching and color share the
same recovered entering position.
-/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

/-- Convert the selected dictionary row into its canonical leaving-variable position. -/
def generalBimatrixNodeLeavingPosition (v : Fin 2 → List Bool) : List Bool :=
  (binarySubsetNth ![generalBimatrixNodeData v 1,
    (generalBimatrixDictionarySelectedRow (generalBimatrixNodeData v)).tail]).tail

theorem generalBimatrixNodeLeavingPosition_cobham : Cobham generalBimatrixNodeLeavingPosition :=
  Cobham.tailFn (Cobham.comp₂ binarySubsetNth_cobham (generalBimatrixNodeData_cobham 1)
    (Cobham.tailFn (Cobham.comp generalBimatrixDictionarySelectedRow_cobham generalBimatrixNodeData_cobham)))

theorem generalBimatrixNodeLeavingPosition_mem_FPn : FPn generalBimatrixNodeLeavingPosition :=
  cobham_iff_FPn.mp generalBimatrixNodeLeavingPosition_cobham

/-- Exchange the selected leaving variable for the entering variable of a node word. -/
def generalBimatrixPivotWord (v : Fin 2 → List Bool) : List Bool :=
  bimatrixNodeExchangeWord ![generalBimatrixDimensionWord (v 0), v 1,
    generalBimatrixNodeLeavingPosition v, generalBimatrixNodeData v 2]

theorem generalBimatrixPivotWord_cobham : Cobham generalBimatrixPivotWord := by
  apply Cobham.comp bimatrixNodeExchangeWord_cobham
  intro i
  fin_cases i
  · exact Cobham.comp generalBimatrixDimensionWord_cobham fun _ => .proj 0
  · exact .proj 1
  · exact generalBimatrixNodeLeavingPosition_cobham
  · exact generalBimatrixNodeData_cobham 2

theorem generalBimatrixPivotWord_mem_FPn : FPn generalBimatrixPivotWord :=
  cobham_iff_FPn.mp generalBimatrixPivotWord_cobham

theorem generalBimatrixPivotWord_length (v : Fin 2 → List Bool) :
    (generalBimatrixPivotWord v).length = (v 1).length := bimatrixNodeExchangeWord_length _

/-- Switch the recovered entering variable to its internal twin, retaining endpoints. -/
def generalBimatrixSwitchWord (v : Fin 2 → List Bool) : List Bool :=
  bimatrixNodeSwitchWord ![generalBimatrixDimensionWord (v 0), v 1, generalBimatrixNodeData v 2]

theorem generalBimatrixSwitchWord_cobham : Cobham generalBimatrixSwitchWord :=
  Cobham.comp₃ bimatrixNodeSwitchWord_cobham
    (Cobham.comp generalBimatrixDimensionWord_cobham fun _ => .proj 0)
    (.proj 1) (generalBimatrixNodeData_cobham 2)

theorem generalBimatrixSwitchWord_mem_FPn : FPn generalBimatrixSwitchWord :=
  cobham_iff_FPn.mp generalBimatrixSwitchWord_cobham

theorem generalBimatrixSwitchWord_length (v : Fin 2 → List Bool) :
    (generalBimatrixSwitchWord v).length = (v 1).length := bimatrixNodeSwitchWord_length _

/-- Switching a canonical node word computes the canonical port switch. -/
theorem generalBimatrixSwitchWord_encode {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {d : Fin (m + n)} (input : List Bool) (hk : (generalBimatrixDimensionWord input).length = m + n)
    (hd : d.val = 0) (port : BimatrixPathPort A B d) :
    generalBimatrixSwitchWord ![input, encode port] = encode port.switch :=
  bimatrixNodeSwitchWord_encode _ _ hk hd port (generalBimatrixNodeData_entering input hk hd port)

private theorem subset_ordinal_length {m n : ℕ} (s : Finset (BimatrixVariable m n))
    {k : ℕ} (hs : s.card = k) (j : Fin k) (ordinal : List Bool) (ho : ordinal.length = j.val) :
    (binarySubsetNth ![membershipWord s, ordinal]).tail.length = (index (s.orderEmbOfFin hs j)).val := by
  let v := s.orderEmbOfFin hs j
  obtain ⟨hbit, hrank⟩ := (selected_variable_iff s hs j v).mp rfl
  have hpos : binarySubsetNthPosition ![membershipWord s, ordinal] = some (index v).val := by
    apply (binarySubsetNth_value _ _).mpr
    refine ⟨?_, hbit, ?_⟩
    · simpa only [Matrix.cons_val_zero, membershipWord, List.length_ofFn] using (index v).isLt
    · change ((membershipWord s).take (index v).val).count true = ordinal.length
      simpa only [ho] using hrank
  change (if (binarySubsetNth _).headD false then some (binarySubsetNth _).tail.length else none) = some _ at hpos
  split at hpos
  · exact Option.some.inj hpos
  · contradiction

/-- A correctly selected dictionary ordinal identifies the corresponding basis variable. -/
theorem generalBimatrixNodeLeavingPosition_length {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {d : Fin (m + n)} (input : List Bool) (hk : (generalBimatrixDimensionWord input).length = m + n)
    (port : BimatrixPathPort A B d) (l : Fin (m + n))
    (hs : binarySignedRowSelectedIndex (generalBimatrixDictionarySelectedRow
      (generalBimatrixNodeData ![input, encode port])) = some l.val) :
    (generalBimatrixNodeLeavingPosition ![input, encode port]).length =
      (index (port.toPivotPort.leavingVariable l)).val := by
  have hlen : (generalBimatrixDictionarySelectedRow
      (generalBimatrixNodeData ![input, encode port])).tail.length = l.val := by
    unfold binarySignedRowSelectedIndex at hs
    split at hs
    · exact Option.some.inj hs
    · contradiction
  unfold generalBimatrixNodeLeavingPosition
  rw [generalBimatrixNodeData_basis input hk port]
  exact subset_ordinal_length port.node.basis.basic port.node.basis.cardinality l _ hlen

/-- The selected canonical leaving row drives precisely the canonical pivot. -/
theorem generalBimatrixPivotWord_encode_of_selected {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {d : Fin (m + n)} (input : List Bool) (hk : (generalBimatrixDimensionWord input).length = m + n)
    (hd : d.val = 0) (port : BimatrixPathPort A B d)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j)
    (hs : binarySignedRowSelectedIndex (generalBimatrixDictionarySelectedRow
      (generalBimatrixNodeData ![input, encode port])) =
        some (port.toPivotPort.leavingRow hm hn hA hB).val) :
    generalBimatrixPivotWord ![input, encode port] = encode (port.pivot hm hn hA hB) :=
  bimatrixNodeExchangeWord_encode _ _ _ hk hd port hm hn hA hB
    (generalBimatrixNodeLeavingPosition_length input hk port _ hs)
    (generalBimatrixNodeData_entering input hk hd port)

open GameTheory.Math

/-- Positive-payoff ports always select their unique canonical symbolic leaving row. -/
theorem generalBimatrixDictionarySelectedRow_eq_some (input : List Bool)
    (port : BimatrixPivotPort
      (fun i : Fin (generalRowCount input) => fun j : Fin (generalColCount input) =>
        decodeGeneralPayoff false input i.val j.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
      (fun i : Fin (generalRowCount input) => fun j : Fin (generalColCount input) =>
        decodeGeneralPayoff true input i.val j.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)))
    (hm : 0 < generalRowCount input) (hn : 0 < generalColCount input)
    (hA : ∀ i : Fin (generalRowCount input), ∀ j : Fin (generalColCount input),
      0 < decodeGeneralPayoff false input i.val j.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
    (hB : ∀ i : Fin (generalRowCount input), ∀ j : Fin (generalColCount input),
      0 < decodeGeneralPayoff true input i.val j.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
    (entering : List Bool) (he : entering.length = (index port.entering).val) :
    binarySignedRowSelectedIndex (generalBimatrixDictionarySelectedRow
      ![input, membershipWord port.basis.basic, entering]) =
        some (port.leavingRow hm hn hA hB).val := by
  let params := ![input, membershipWord port.basis.basic, entering]
  let dim := generalBimatrixDictionaryDimension params
  let W := generalBimatrixDictionaryWidth params
  let C := generalBimatrixDictionaryCoefficients params
  let D := generalBimatrixDictionaryDirection params
  have hdim : dim.length = generalRowCount input + generalColCount input :=
    generalBimatrixDimensionWord_length input
  have hnotnone : binarySignedRowSelectedIndex (generalBimatrixDictionarySelectedRow params) ≠ none := by
    intro hnone
    have hnondir := (binarySignedRowSelect_none ![dim, true :: dim, W, C, D]).mp hnone
    obtain ⟨i, hi⟩ := port.basis.exists_positive_direction hm hn hA hB port.entering
    have hib : i.val < dim.length := by rw [hdim]; exact i.isLt
    have hle := hnondir ⟨i.val, hib⟩
    change binarySignedRowValue W D i.val ≤ 0 at hle
    rw [generalBimatrixDictionaryDirection_value input port.basis entering port.entering he i] at hle
    have hleq : (IntegerDictionaryComputation.direction port.basis.integerMatrix
      (fun j => bimatrixIntegerColumns
        (fun r c => decodeGeneralPayoff false input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
        (fun r c => decodeGeneralPayoff true input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)) j port.entering) i : ℚ) ≤ 0 := by
      exact_mod_cast hle
    have hd : (0 : ℚ) < (IntegerCramerComputation.denominator port.basis.integerMatrix : ℚ) := by
      rw [IntegerCramerComputation.denominator_eq]
      exact_mod_cast IntegerCramerEncoding.denominator_pos _ port.basis.integerMatrix_det_ne_zero
    have hdir := IntegerDictionaryComputation.direction_decode port.basis.integerMatrix
      (fun j => bimatrixIntegerColumns
        (fun r c => decodeGeneralPayoff false input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
        (fun r c => decodeGeneralPayoff true input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)) j port.entering)
      port.basis.integerMatrix_det_ne_zero i
    rw [port.basis.integerMatrix_map] at hdir
    simp only [bimatrixIntegerColumns_cast] at hdir
    rw [← hdir] at hi
    exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg hleq hd.le)) hi
  cases hselect : binarySignedRowSelectedIndex (generalBimatrixDictionarySelectedRow params) with
  | none => exact (hnotnone hselect).elim
  | some s =>
    have hsmem := binarySignedRowSelect_mem ![dim, true :: dim, W, C, D] s hselect
    have hslt : s < generalRowCount input + generalColCount input := by simpa only [Matrix.cons_val_zero, hdim] using hsmem
    let l : Fin (generalRowCount input + generalColCount input) := ⟨s, hslt⟩
    have hleave := generalBimatrixDictionarySelectedRow_spec input port.basis entering port.entering he l hselect
    rw [port.basis.integerMatrix_map] at hleave
    simp only [bimatrixIntegerColumns_cast] at hleave
    have heq : l = port.leavingRow hm hn hA hB :=
      (port.basis.exists_unique_leavingRow hm hn hA hB port.entering).choose_spec.2 l hleave
    exact congrArg (fun j => some j.val) heq
/-- Serialized valid games compute the canonical positive-shifted pivot without extra selection premises. -/
theorem generalBimatrixPivotWord_encode (input : List Bool) (hi : GeneralInstanceValid input)
    {d : Fin (generalRowCount input + generalColCount input)} (hd : d.val = 0)
    (port : BimatrixPathPort
      (fun i : Fin (generalRowCount input) => fun j : Fin (generalColCount input) =>
        decodeGeneralPayoff false input i.val j.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
      (fun i : Fin (generalRowCount input) => fun j : Fin (generalColCount input) =>
        decodeGeneralPayoff true input i.val j.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)) d) :
    generalBimatrixPivotWord ![input, encode port] = encode (port.pivot hi.1 hi.2.1
      (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le)
      (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le)) := by
  let hA := fun i : Fin (generalRowCount input) => fun j : Fin (generalColCount input) =>
    payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le
  let hB := fun i : Fin (generalRowCount input) => fun j : Fin (generalColCount input) =>
    payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le
  apply generalBimatrixPivotWord_encode_of_selected input (generalBimatrixDimensionWord_length input)
    hd port hi.1 hi.2.1 hA hB
  have hparams : generalBimatrixNodeData ![input, encode port] =
      ![input, membershipWord port.node.basis.basic, generalBimatrixNodeData ![input, encode port] 2] := by
    funext i
    fin_cases i
    · rfl
    · exact generalBimatrixNodeData_basis input (generalBimatrixDimensionWord_length input) port
    · rfl
  rw [hparams]
  exact generalBimatrixDictionarySelectedRow_eq_some input port.toPivotPort hi.1 hi.2.1 hA hB _
    (generalBimatrixNodeData_entering input (generalBimatrixDimensionWord_length input) hd port)
end GameTheory.Complexity.Backend
