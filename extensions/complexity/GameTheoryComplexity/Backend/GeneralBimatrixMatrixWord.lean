module

public import GameTheoryComplexity.Backend.GeneralBimatrixColumnWord
public import GameTheoryComplexity.Backend.BinarySubsetMachine
public import GameTheoryComplexity.Backend.BinaryUnaryArithmetic
public import GameTheoryComplexity.Backend.BinarySignedMatrixMachine
public import GameTheoryComplexity.Backend.WordFold
public import GameTheoryComplexity.Backend.GeneralBimatrixEndpoint
public import GameTheory.Finite.BimatrixPathBinaryCodec

@[expose] public section

/-! Packed canonical basis matrices for shifted rectangular bimatrix games.
Selected columns are located by their Boolean membership ordinal. Both matrix
loops use explicit dimension rulers, and every signed entry has the supplied
fixed field width. Malformed selections return zero entries. -/
namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec GameTheory.Math.CanonicalDictionary

/-- The dimension ruler of the complementary system. -/
def generalBimatrixDimensionWord (input : List Bool) : List Bool :=
  generalRowRuler input ++ generalColRuler input

@[simp] theorem generalBimatrixDimensionWord_length (input : List Bool) :
    (generalBimatrixDimensionWord input).length = generalRowCount input + generalColCount input := by
  simp only [generalBimatrixDimensionWord, List.length_append, generalRowCount, generalColCount]

/-- One selected integer entry. Arguments are row ruler, column ordinal ruler,
raw membership bits and game instance. Failed ordinal lookup returns zero. -/
def generalBimatrixBasisEntryWord (v : Fin 4 → List Bool) : List Bool :=
  let found := binarySubsetNth ![v 2, v 1]
  if found.headD false then
    generalBimatrixColumnWord ![v 0, binaryHalfRuler found.tail,
      binaryLengthParity found.tail, v 3]
  else [false]

/-- Canonical candidate matrix, without feasibility or invertibility assumptions. -/
abbrev generalBimatrixCandidateMatrix (input : List Bool)
    (s : Finset (BimatrixVariable (generalRowCount input) (generalColCount input)))
    (hs : s.card = generalRowCount input + generalColCount input) :=
  candidateMatrix
    (fun i j => decodeGeneralPayoff false input i.val j.val +
      ((2 : ℤ) ^ generalCoefficientBits input + 1))
    (fun i j => decodeGeneralPayoff true input i.val j.val +
      ((2 : ℤ) ^ generalCoefficientBits input + 1)) s hs

/-- Membership ordinal lookup recovers precisely the canonically sorted basis column. -/
theorem generalBimatrixCandidateEntryWord_integer_of_lengths (input : List Bool)
    (s : Finset (BimatrixVariable (generalRowCount input) (generalColCount input)))
    (hs : s.card = generalRowCount input + generalColCount input)
    (i j : Fin (generalRowCount input + generalColCount input)) (row ordinal : List Bool)
    (hrow : row.length = i.val) (hordinal : ordinal.length = j.val) :
    binarySignedValue (generalBimatrixBasisEntryWord
      ![row, ordinal, membershipWord s, input]) = generalBimatrixCandidateMatrix input s hs i j := by
  let v := s.orderEmbOfFin hs j
  let found := binarySubsetNth ![membershipWord s, ordinal]
  have hv : v = s.orderEmbOfFin hs j := rfl
  obtain ⟨hbit, hrank⟩ := (selected_variable_iff s hs j v).mp hv
  have hpos : binarySubsetNthPosition
      ![membershipWord s, ordinal] = some (index v).val := by
    apply (binarySubsetNth_value _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Matrix.cons_val_zero, membershipWord, List.length_ofFn] using (index v).isLt
    · exact hbit
    · change ((membershipWord s).take (index v).val).count true =
        ordinal.length
      simpa only [hordinal] using hrank
  change (if found.headD false then some found.tail.length else none) = some (index v).val at hpos
  have hhead : found.headD false = true := by
    cases hh : found.headD false <;> simp_all
  have hlen : found.tail.length = (index v).val := by simpa only [hhead, ↓reduceIte, Option.some.injEq] using hpos
  have hhalf : binaryHalfRuler found.tail = List.replicate (ofLex v).1.val true := by
    rw [binaryHalfRuler_value, hlen]
    congr 1
    cases hb : (ofLex v).2 <;> simp [index, hb, Nat.add_div]
  have hkind : binaryLengthParity found.tail = [(ofLex v).2] := by
    rw [binaryLengthParity_value, hlen]
    cases hb : (ofLex v).2 <;> simp [index, hb, Nat.add_mod]
  change binarySignedValue (if found.headD false then
    generalBimatrixColumnWord ![row,
      binaryHalfRuler found.tail, binaryLengthParity found.tail, input] else [false]) = _
  simp only [hhead, ↓reduceIte]
  rw [hhalf, hkind]
  have hrowWord : binarySignedValue (generalBimatrixColumnWord
      ![row, List.replicate (ofLex v).1.val true, [(ofLex v).2], input]) =
      binarySignedValue (generalBimatrixColumnWord
        ![List.replicate i.val true, List.replicate (ofLex v).1.val true, [(ofLex v).2], input]) := by
    simp only [generalBimatrixColumnWord_value, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, List.length_replicate, hrow]
  rw [hrowWord, generalBimatrixColumnWord_integer]
  exact congrArg (GameTheory.Finite.bimatrixIntegerColumns _ _ i) (toLex_ofLex v)

theorem generalBimatrixCandidateEntryWord_integer (input : List Bool)
    (s : Finset (BimatrixVariable (generalRowCount input) (generalColCount input)))
    (hs : s.card = generalRowCount input + generalColCount input)
    (i j : Fin (generalRowCount input + generalColCount input)) :
    binarySignedValue (generalBimatrixBasisEntryWord
      ![List.replicate i.val true, List.replicate j.val true,
        membershipWord s, input]) = generalBimatrixCandidateMatrix input s hs i j :=
  generalBimatrixCandidateEntryWord_integer_of_lengths input s hs i j _ _
    (List.length_replicate ..) (List.length_replicate ..)

private abbrev entryTerm (v : Fin 4 → List Bool) : List Bool :=
  generalBimatrixBasisEntryWord ![v 1, v 0, v 2, v 3]

/-- One packed row. Arguments are row ruler, field-width ruler, membership and input. -/
def generalBimatrixBasisRowWord (v : Fin 4 → List Bool) : List Bool :=
  binarySignedTable
    (fun args : Fin 4 → List Bool => generalBimatrixBasisEntryWord ![args 1, args 0, args 2, args 3])
    (generalBimatrixDimensionWord (v 3)) (v 1) ![v 0, v 2, v 3]

@[simp] theorem generalBimatrixBasisRowWord_length (v : Fin 4 → List Bool) :
    (generalBimatrixBasisRowWord v).length =
      (generalRowCount (v 3) + generalColCount (v 3)) * (v 1).length := by
  rw [generalBimatrixBasisRowWord, binarySignedTable_length, generalBimatrixDimensionWord_length]

private def rows (clock width members input : List Bool) : List Bool :=
  WordFold.suffixFold
    (fun params : Fin 3 → List Bool => fun suffix state _ =>
      state ++ generalBimatrixBasisRowWord ![suffix, params 0, params 1, params 2])
    ![width, members, input] [] clock

private theorem rows_length (clock width members input : List Bool) :
    (rows clock width members input).length = clock.length *
      (generalRowCount input + generalColCount input) * width.length := by
  induction clock with
  | nil => simp [rows]
  | cons b r ih =>
    simp only [rows, WordFold.suffixFold_cons]
    change (rows r width members input ++ generalBimatrixBasisRowWord ![r, width, members, input]).length = _
    rw [List.length_append, ih, generalBimatrixBasisRowWord_length]
    change r.length * (generalRowCount input + generalColCount input) * width.length +
      (generalRowCount input + generalColCount input) * width.length =
      (r.length + 1) * (generalRowCount input + generalColCount input) * width.length
    ring

/-- A row-major packed matrix. Arguments are field width, membership and input. -/
def generalBimatrixBasisMatrixWord (v : Fin 3 → List Bool) : List Bool :=
  WordFold.suffixFold
    (fun params : Fin 3 → List Bool => fun suffix state _ =>
      state ++ generalBimatrixBasisRowWord ![suffix, params 0, params 1, params 2])
    ![v 0, v 1, v 2] [] (generalBimatrixDimensionWord (v 2))

@[simp] theorem generalBimatrixBasisMatrixWord_length (v : Fin 3 → List Bool) :
    (generalBimatrixBasisMatrixWord v).length =
      (generalRowCount (v 2) + generalColCount (v 2)) ^ 2 * (v 0).length := by
  change (rows (generalBimatrixDimensionWord (v 2)) (v 0) (v 1) (v 2)).length = _
  rw [rows_length, generalBimatrixDimensionWord_length]
  ring

private theorem entryWord_of_none (v : Fin 4 → List Bool)
    (h : binarySubsetNthPosition ![v 2, v 1] = none) :
    generalBimatrixBasisEntryWord v = [false] := by
  let found := binarySubsetNth ![v 2, v 1]
  change (if found.headD false then some found.tail.length else none) = none at h
  change (if found.headD false then _ else [false]) = [false]
  cases hf : found with
  | nil => rfl
  | cons b xs =>
    cases b
    · rfl
    · simp [hf] at h

theorem generalBimatrixCandidateRowWord_integer (input : List Bool)
    (s : Finset (BimatrixVariable (generalRowCount input) (generalColCount input)))
    (hs : s.card = generalRowCount input + generalColCount input)
    (i j : Fin (generalRowCount input + generalColCount input))
    (row fieldWidth : List Bool) (hrow : row.length = i.val)
    (hw : 0 < fieldWidth.length)
    (hb : ∀ r c, (generalBimatrixCandidateMatrix input s hs r c).natAbs < 2 ^ (fieldWidth.length - 1)) :
    binarySignedRowValue fieldWidth (generalBimatrixBasisRowWord
      ![row, fieldWidth, membershipWord s, input]) j.val = generalBimatrixCandidateMatrix input s hs i j := by
  let f : ℕ → ℤ := fun t => if ht : t < generalRowCount input + generalColCount input then
    generalBimatrixCandidateMatrix input s hs i ⟨t, ht⟩ else 0
  have hterm (r : List Bool) : binarySignedValue
      (entryTerm (Fin.cons r ![row, membershipWord s, input])) = f r.length := by
    change binarySignedValue (generalBimatrixBasisEntryWord
      ![row, r, membershipWord s, input]) = f r.length
    by_cases ht : r.length < generalRowCount input + generalColCount input
    · dsimp only [f]
      rw [dite_eq_left ht]
      exact generalBimatrixCandidateEntryWord_integer_of_lengths input s hs i ⟨r.length, ht⟩
        row r hrow rfl
    · have hn : binarySubsetNthPosition ![membershipWord s, r] = none := by
        apply (binarySubsetNth_none _).mpr
        change (membershipWord s).count true ≤ r.length
        rw [membershipWord_count, hs]
        omega
      rw [entryWord_of_none ![row, r, membershipWord s, input] hn]
      simp only [f, ht, ↓reduceDIte]
      rfl
  have hbound (t : ℕ) (ht : t < (generalBimatrixDimensionWord input).length) :
      (f t).natAbs < 2 ^ (fieldWidth.length - 1) := by
    have ht' : t < generalRowCount input + generalColCount input := by simpa using ht
    dsimp only [f]
    rw [dite_eq_left ht']
    exact hb i ⟨t, ht'⟩
  have hval := binarySignedTable_value (p := 3) entryTerm fieldWidth
    ![row, membershipWord s, input] f hterm hw
    (generalBimatrixDimensionWord input) hbound j.val (by rw [generalBimatrixDimensionWord_length]; exact j.isLt)
  dsimp only [f] at hval
  rw [dite_eq_left j.isLt] at hval
  exact hval

private theorem rows_integer (input : List Bool)
    (s : Finset (BimatrixVariable (generalRowCount input) (generalColCount input)))
    (hs : s.card = generalRowCount input + generalColCount input) (fieldWidth : List Bool)
    (hw : 0 < fieldWidth.length)
    (hb : ∀ r c, (generalBimatrixCandidateMatrix input s hs r c).natAbs < 2 ^ (fieldWidth.length - 1))
    (clock : List Bool) (hc : clock.length ≤ generalRowCount input + generalColCount input)
    (i : Fin clock.length) (j : Fin (generalRowCount input + generalColCount input)) :
    binarySignedRowValue fieldWidth (rows clock fieldWidth (membershipWord s) input)
      (i.val * (generalRowCount input + generalColCount input) + j.val) =
      generalBimatrixCandidateMatrix input s hs ⟨i.val, i.isLt.trans_le hc⟩ j := by
  induction clock with
  | nil => exact i.elim0
  | cons b r ih =>
    have hr : r.length ≤ generalRowCount input + generalColCount input := by
      simp only [List.length_cons] at hc
      omega
    simp only [rows, WordFold.suffixFold_cons]
    change binarySignedRowValue fieldWidth
      (rows r fieldWidth (membershipWord s) input ++
        generalBimatrixBasisRowWord ![r, fieldWidth, membershipWord s, input])
      (i.val * (generalRowCount input + generalColCount input) + j.val) = _
    by_cases hi : i.val < r.length
    · rw [rowValue_append_left]
      · exact ih hr ⟨i.val, hi⟩
      · rw [rows_length]
        apply Nat.mul_le_mul_right
        have him := Nat.mul_le_mul_right (generalRowCount input + generalColCount input)
          (by omega : i.val + 1 ≤ r.length)
        have hj := j.isLt
        nlinarith
    · have hieq : i.val = r.length := by have h := i.isLt; simp only [List.length_cons] at h; omega
      unfold binarySignedRowValue
      have hindex : (i.val * (generalRowCount input + generalColCount input) + j.val) * fieldWidth.length =
          (rows r fieldWidth (membershipWord s) input).length + j.val * fieldWidth.length := by
        rw [rows_length, hieq]
        ring
      rw [hindex, List.drop_append, List.drop_of_length_le (by omega), List.nil_append,
        Nat.add_sub_cancel_left]
      exact generalBimatrixCandidateRowWord_integer input s hs
        ⟨i.val, i.isLt.trans_le hc⟩ j r fieldWidth hieq.symm hw hb

/-- Every packed row-major field is the exact integer entry of the canonical basis.
The supplied width must cover each magnitude; this controls truncation explicitly. -/
theorem generalBimatrixCandidateMatrixWord_integer (input : List Bool)
    (s : Finset (BimatrixVariable (generalRowCount input) (generalColCount input)))
    (hs : s.card = generalRowCount input + generalColCount input) (fieldWidth : List Bool)
    (hw : 0 < fieldWidth.length)
    (hb : ∀ r c, (generalBimatrixCandidateMatrix input s hs r c).natAbs < 2 ^ (fieldWidth.length - 1))
    (i j : Fin (generalRowCount input + generalColCount input)) :
    binarySignedRowValue fieldWidth (generalBimatrixBasisMatrixWord
      ![fieldWidth, membershipWord s, input])
      (i.val * (generalRowCount input + generalColCount input) + j.val) = generalBimatrixCandidateMatrix input s hs i j := by
  exact rows_integer input s hs fieldWidth hw hb (generalBimatrixDimensionWord input)
    (by simp) ⟨i.val, by rw [generalBimatrixDimensionWord_length]; exact i.isLt⟩ j

theorem generalBimatrixBasisEntryWord_integer_of_lengths (input : List Bool)
    (basis : GeneralBimatrixShiftedBasis input)
    (i j : Fin (generalRowCount input + generalColCount input)) (row ordinal : List Bool)
    (hrow : row.length = i.val) (hordinal : ordinal.length = j.val) :
    binarySignedValue (generalBimatrixBasisEntryWord
      ![row, ordinal, membershipWord basis.basic, input]) = basis.integerMatrix i j :=
  generalBimatrixCandidateEntryWord_integer_of_lengths input basis.basic basis.cardinality
    i j row ordinal hrow hordinal

theorem generalBimatrixBasisEntryWord_integer (input : List Bool)
    (basis : GeneralBimatrixShiftedBasis input)
    (i j : Fin (generalRowCount input + generalColCount input)) :
    binarySignedValue (generalBimatrixBasisEntryWord
      ![List.replicate i.val true, List.replicate j.val true,
        membershipWord basis.basic, input]) = basis.integerMatrix i j :=
  generalBimatrixCandidateEntryWord_integer input basis.basic basis.cardinality i j

theorem generalBimatrixBasisRowWord_integer (input : List Bool)
    (basis : GeneralBimatrixShiftedBasis input)
    (i j : Fin (generalRowCount input + generalColCount input))
    (row fieldWidth : List Bool) (hrow : row.length = i.val)
    (hw : 0 < fieldWidth.length)
    (hb : ∀ r c, (basis.integerMatrix r c).natAbs < 2 ^ (fieldWidth.length - 1)) :
    binarySignedRowValue fieldWidth (generalBimatrixBasisRowWord
      ![row, fieldWidth, membershipWord basis.basic, input]) j.val = basis.integerMatrix i j :=
  generalBimatrixCandidateRowWord_integer input basis.basic basis.cardinality
    i j row fieldWidth hrow hw hb

theorem generalBimatrixBasisMatrixWord_integer (input : List Bool)
    (basis : GeneralBimatrixShiftedBasis input) (fieldWidth : List Bool)
    (hw : 0 < fieldWidth.length)
    (hb : ∀ r c, (basis.integerMatrix r c).natAbs < 2 ^ (fieldWidth.length - 1))
    (i j : Fin (generalRowCount input + generalColCount input)) :
    binarySignedRowValue fieldWidth (generalBimatrixBasisMatrixWord
      ![fieldWidth, membershipWord basis.basic, input])
      (i.val * (generalRowCount input + generalColCount input) + j.val) = basis.integerMatrix i j :=
  generalBimatrixCandidateMatrixWord_integer input basis.basic basis.cardinality
    fieldWidth hw hb i j

@[fun_prop] theorem generalBimatrixDimensionWord_polyTime :
    ComputableInPolyTime (fun v : Fin 1 → List Bool => generalBimatrixDimensionWord (v 0))
      (encPi encBits) encBits :=
  .bitsAppend generalRowRuler_polyTime generalColRuler_polyTime

@[fun_prop] theorem generalBimatrixBasisEntryWord_polyTime :
    ComputableInPolyTime generalBimatrixBasisEntryWord (encPi encBits) encBits := by
  have hnargs : ComputableInPolyTime (fun v : Fin 4 → List Bool => ![v 2, v 1])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 1
  have hn := binarySubsetNth_polyTime.comp hnargs
  have htail := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hn
  have hhalf := binaryHalfRuler_polyTime.comp htail
  have hparity := binaryLengthParity_polyTime.comp htail
  have hcargs : ComputableInPolyTime
      (fun v : Fin 4 → List Bool => ![v 0, binaryHalfRuler (binarySubsetNth ![v 2, v 1]).tail,
        binaryLengthParity (binarySubsetNth ![v 2, v 1]).tail, v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact hhalf
    · exact hparity
    · exact .pi_apply encBits 3
  have hhead : ComputableInPolyTime
      (fun v : Fin 4 → List Bool => (binarySubsetNth ![v 2, v 1]).headD false)
      (encPi encBits) encBool := (ComputableInPolyTime.headD false).comp hn
  have h := hhead.ite
    (generalBimatrixColumnWord_polyTime.comp hcargs) (.const [false])
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq (g := generalBimatrixBasisEntryWord)
  intro v
  rfl

private theorem entryTerm_polyTime :
    ComputableInPolyTime entryTerm (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 4 → List Bool => ![v 1, v 0, v 2, v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
  exact generalBimatrixBasisEntryWord_polyTime.comp hargs

@[fun_prop] theorem generalBimatrixBasisRowWord_polyTime :
    ComputableInPolyTime generalBimatrixBasisRowWord (encPi encBits) encBits := by
  have hinput : ComputableInPolyTime (fun v : Fin 4 → List Bool => ![v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact .pi_apply encBits (3 : Fin 4)
  have hclock0 := generalBimatrixDimensionWord_polyTime.comp hinput
  have hclock : ComputableInPolyTime
      (fun v : Fin 4 → List Bool => generalBimatrixDimensionWord (v 3))
      (encPi encBits) encBits := by
    apply ComputableInPolyTime.of_tidy
    apply hclock0.tidy.of_enc_eq
    intro v
    rfl
  have htable := binarySignedTable_polyTime (p := 3) (term := entryTerm) entryTerm_polyTime
  have hargs : ComputableInPolyTime
      (fun v : Fin 4 → List Bool => ![generalBimatrixDimensionWord (v 3), v 1, v 0, v 2, v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hclock
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
  have htable' := htable.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply htable'.tidy.of_enc_eq
  intro v
  change generalBimatrixBasisRowWord v = binarySignedTable entryTerm
    (generalBimatrixDimensionWord (v 3)) (v 1)
    (Fin.tail (Fin.tail (![generalBimatrixDimensionWord (v 3), v 1, v 0, v 2, v 3] : Fin 5 → List Bool)))
  unfold generalBimatrixBasisRowWord
  apply congrArg (binarySignedTable entryTerm (generalBimatrixDimensionWord (v 3)) (v 1))
  funext i
  fin_cases i <;> rfl

private theorem matrixRowsStep_polyTime :
    ComputableInPolyTime
      (fun p : ((Fin 3 → List Bool) × (List Bool × List Bool)) × Bool =>
        p.1.2.2 ++ generalBimatrixBasisRowWord ![p.1.2.1, p.1.1 0, p.1.1 1, p.1.1 2])
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool) encBits := by
  have hp : ComputableInPolyTime
      (fun p : ((Fin 3 → List Bool) × (List Bool × List Bool)) × Bool => p.1)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool)
      (encPair (encPi encBits) (encPair encBits encBits)) := .fst _ _
  have hparams : ComputableInPolyTime
      (fun p : ((Fin 3 → List Bool) × (List Bool × List Bool)) × Bool => p.1.1)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool)
      (encPi encBits) := (ComputableInPolyTime.fst _ _).comp hp
  have hparts : ComputableInPolyTime
      (fun p : ((Fin 3 → List Bool) × (List Bool × List Bool)) × Bool => p.1.2)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool)
      (encPair encBits encBits) := (ComputableInPolyTime.snd _ _).comp hp
  have hsuffix := (ComputableInPolyTime.fst encBits encBits).comp hparts
  have hstate := (ComputableInPolyTime.snd encBits encBits).comp hparts
  have hargs : ComputableInPolyTime
      (fun p : ((Fin 3 → List Bool) × (List Bool × List Bool)) × Bool =>
        ![p.1.2.1, p.1.1 0, p.1.1 1, p.1.1 2])
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool)
      (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hsuffix
    · exact (ComputableInPolyTime.pi_apply encBits (0 : Fin 3)).comp hparams
    · exact (ComputableInPolyTime.pi_apply encBits (1 : Fin 3)).comp hparams
    · exact (ComputableInPolyTime.pi_apply encBits (2 : Fin 3)).comp hparams
  exact .bitsAppend hstate (generalBimatrixBasisRowWord_polyTime.comp hargs)

@[fun_prop] theorem generalBimatrixBasisMatrixWord_polyTime :
    ComputableInPolyTime generalBimatrixBasisMatrixWord (encPi encBits) encBits := by
  have hcontext : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => ![v 0, v 1, v 2]) (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
  have hinput : ComputableInPolyTime (fun v : Fin 3 → List Bool => ![v 2])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact .pi_apply encBits (2 : Fin 3)
  have hclock0 := generalBimatrixDimensionWord_polyTime.comp hinput
  have hclock : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => generalBimatrixDimensionWord (v 2))
      (encPi encBits) encBits := by
    apply ComputableInPolyTime.of_tidy
    apply hclock0.tidy.of_enc_eq
    intro v
    rfl
  have hwidth : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hbound := (hclock.polyBounded_length.mul hclock.polyBounded_length).mul
    hwidth.polyBounded_length
  apply WordFold.suffixFold_polyTime hcontext hclock (.const []) matrixRowsStep_polyTime hbound
  intro v suffix hsub
  change (rows suffix (v 0) (v 1) (v 2)).length ≤ _
  rw [rows_length]
  change suffix.length * (generalRowCount (v 2) + generalColCount (v 2)) * (v 0).length ≤
    (generalBimatrixDimensionWord (v 2)).length *
      (generalBimatrixDimensionWord (v 2)).length * (v 0).length
  rw [generalBimatrixDimensionWord_length]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by simpa using hsub.length_le))

end GameTheory.Complexity.Backend
