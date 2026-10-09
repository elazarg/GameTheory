import GameTheoryComplexity.Backend.GeneralBimatrixColumnWord
import GameTheoryComplexity.Backend.BinarySubsetMachine
import GameTheoryComplexity.Backend.BinaryUnaryArithmetic
import GameTheoryComplexity.Backend.BinarySignedMatrixMachine
import GameTheoryComplexity.Backend.GeneralBimatrixEndpoint
import GameTheory.Finite.BimatrixPathBinaryCodec

/-! Packed canonical basis matrices for shifted rectangular bimatrix games.
Selected columns are located by their Boolean membership ordinal. Both matrix
loops use explicit dimension rulers, and every signed entry has the supplied
fixed field width. Malformed selections return zero entries. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec GameTheory.Math.CanonicalDictionary

/-- The dimension ruler of the complementary system. -/
def generalBimatrixDimensionWord (input : List Bool) : List Bool :=
  generalRowRuler input ++ generalColRuler input

@[simp] theorem generalBimatrixDimensionWord_length (input : List Bool) :
    (generalBimatrixDimensionWord input).length = generalRowCount input + generalColCount input := by
  simp only [generalBimatrixDimensionWord, List.length_append, generalRowCount, generalColCount]

theorem generalBimatrixDimensionWord_cobham : Cobham fun v : Fin 1 → List Bool =>
    generalBimatrixDimensionWord (v 0) := Cobham.appendFn generalRowRuler_cobham generalColRuler_cobham

/-- One selected integer entry. Arguments are row ruler, column ordinal ruler,
raw membership bits and game instance. Failed ordinal lookup returns zero. -/
def generalBimatrixBasisEntryWord (v : Fin 4 → List Bool) : List Bool :=
  let found := binarySubsetNth ![v 2, v 1]
  caseBit₀ found
    (generalBimatrixColumnWord ![v 0, binaryHalfRuler found.tail,
      binaryLengthParity found.tail, v 3]) [false]

theorem generalBimatrixBasisEntryWord_cobham : Cobham generalBimatrixBasisEntryWord := by
  have hn : Cobham fun v : Fin 4 → List Bool => binarySubsetNth ![v 2, v 1] :=
    Cobham.comp₂ binarySubsetNth_cobham (.proj 2) (.proj 1)
  have hh := Cobham.comp binaryHalfRuler_cobham (fun _ => Cobham.tailFn hn)
  have hp := Cobham.comp binaryLengthParity_cobham (fun _ => Cobham.tailFn hn)
  have hc : Cobham fun v : Fin 4 → List Bool =>
      generalBimatrixColumnWord ![v 0, binaryHalfRuler (binarySubsetNth ![v 2, v 1]).tail,
        binaryLengthParity (binarySubsetNth ![v 2, v 1]).tail, v 3] :=
    Cobham.comp generalBimatrixColumnWord_cobham (fun i => by
      fin_cases i
      · exact Cobham.proj 0
      · exact hh
      · exact hp
      · exact Cobham.proj 3)
  exact (Cobham.iteFn hn hc (Cobham.const [false])).of_eq fun _ => rfl

theorem generalBimatrixBasisEntryWord_mem_FPn : FPn generalBimatrixBasisEntryWord :=
  cobham_iff_FPn.mp generalBimatrixBasisEntryWord_cobham

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
  change binarySignedValue (caseBit₀ found
    (generalBimatrixColumnWord ![row,
      binaryHalfRuler found.tail, binaryLengthParity found.tail, input]) [false]) = _
  have hcase {x a b : List Bool} (hx : x.headD false = true) : caseBit₀ x a b = a := by
    cases x with
    | nil => simp at hx
    | cons c x => cases c <;> simp_all [caseBit₀]
  rw [hcase hhead, hhalf, hkind]
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

private def entryTerm (v : Fin 4 → List Bool) : List Bool :=
  generalBimatrixBasisEntryWord ![v 1, v 0, v 2, v 3]

private theorem entryTerm_cobham : Cobham entryTerm :=
  (Cobham.comp generalBimatrixBasisEntryWord_cobham (fun i => Cobham.proj (![1, 0, 2, 3] i))).of_eq
    fun _ => rfl

/-- One packed row. Arguments are row ruler, field-width ruler, membership and input. -/
def generalBimatrixBasisRowWord (v : Fin 4 → List Bool) : List Bool :=
  binarySignedTable entryTerm (generalBimatrixDimensionWord (v 3)) (v 1) ![v 0, v 2, v 3]

@[simp] theorem generalBimatrixBasisRowWord_length (v : Fin 4 → List Bool) :
    (generalBimatrixBasisRowWord v).length =
      (generalRowCount (v 3) + generalColCount (v 3)) * (v 1).length := by
  rw [generalBimatrixBasisRowWord, binarySignedTable_length, generalBimatrixDimensionWord_length]

theorem generalBimatrixBasisRowWord_cobham : Cobham generalBimatrixBasisRowWord := by
  have hk : Cobham fun v : Fin 4 → List Bool => generalBimatrixDimensionWord (v 3) :=
    (Cobham.comp generalBimatrixDimensionWord_cobham fun _ => Cobham.proj 3).of_eq fun _ => rfl
  let g : Fin 5 → (Fin 4 → List Bool) → List Bool := fun i v =>
    ![generalBimatrixDimensionWord (v 3), v 1, v 0, v 2, v 3] i
  have hg : ∀ i, Cobham (g i) := fun i => by
      fin_cases i
      · exact hk
      · exact Cobham.proj 1
      · exact Cobham.proj 0
      · exact Cobham.proj 2
      · exact Cobham.proj 3
  have h := Cobham.comp (gs := g) (binarySignedTable_cobham entryTerm_cobham) hg
  exact h.of_eq fun v => by
    congr 1

private def rowStep (v : Fin 5 → List Bool) : List Bool :=
  v 1 ++ generalBimatrixBasisRowWord ![v 0, v 2, v 3, v 4]

private def rows (clock width members input : List Bool) : List Bool :=
  recNotation (fun _ : Fin 3 → List Bool => []) rowStep rowStep clock ![width, members, input]

private theorem rows_length (clock width members input : List Bool) :
    (rows clock width members input).length = clock.length *
      (generalRowCount input + generalColCount input) * width.length := by
  induction clock with
  | nil => simp [rows, recNotation]
  | cons b r ih =>
    simp only [rows, recNotation_cons, Bool.cond_self]
    change (rows r width members input ++ generalBimatrixBasisRowWord ![r, width, members, input]).length = _
    rw [List.length_append, ih, generalBimatrixBasisRowWord_length]
    change r.length * (generalRowCount input + generalColCount input) * width.length +
      (generalRowCount input + generalColCount input) * width.length =
      (r.length + 1) * (generalRowCount input + generalColCount input) * width.length
    ring

/-- A row-major packed matrix. Arguments are field width, membership and input. -/
def generalBimatrixBasisMatrixWord (v : Fin 3 → List Bool) : List Bool :=
  rows (generalBimatrixDimensionWord (v 2)) (v 0) (v 1) (v 2)

@[simp] theorem generalBimatrixBasisMatrixWord_length (v : Fin 3 → List Bool) :
    (generalBimatrixBasisMatrixWord v).length =
      (generalRowCount (v 2) + generalColCount (v 2)) ^ 2 * (v 0).length := by
  rw [generalBimatrixBasisMatrixWord, rows_length, generalBimatrixDimensionWord_length]
  ring

theorem generalBimatrixBasisMatrixWord_cobham : Cobham generalBimatrixBasisMatrixWord := by
  have hs : Cobham rowStep := Cobham.appendFn (.proj 1)
    (Cobham.comp generalBimatrixBasisRowWord_cobham (fun i => by
      fin_cases i
      · exact Cobham.proj 0
      · exact Cobham.proj 2
      · exact Cobham.proj 3
      · exact Cobham.proj 4))
  have hbound : Cobham fun v : Fin 4 → List Bool =>
      smash (v 0) (smash (generalBimatrixDimensionWord (v 3)) (v 1)) := by
    have hk' : Cobham fun v : Fin 4 → List Bool => generalBimatrixDimensionWord (v 3) :=
      (Cobham.comp generalBimatrixDimensionWord_cobham fun _ => Cobham.proj 3).of_eq fun _ => rfl
    exact Cobham.comp₂ Cobham.smash (.proj 0) (Cobham.comp₂ Cobham.smash hk' (.proj 1))
  have hr : Cobham fun v : Fin 4 → List Bool => rows (v 0) (v 1) (v 2) (v 3) := by
    exact (Cobham.boundedRec Cobham.empty hs hs hbound (fun r p => by
      have hp : p = ![p 0, p 1, p 2] := by ext i; fin_cases i <;> rfl
      rw [hp]
      change (rows r (p 0) (p 1) (p 2)).length ≤ _
      rw [rows_length, smash_length, smash_length, generalBimatrixDimensionWord_length]
      change r.length * (generalRowCount (p 2) + generalColCount (p 2)) * (p 0).length ≤
        r.length * ((generalRowCount (p 2) + generalColCount (p 2)) * (p 0).length)
      exact (Nat.mul_assoc _ _ _).le)).of_eq fun v => by
        congr 1
        ext i
        fin_cases i <;> rfl
  have hk' : Cobham fun v : Fin 3 → List Bool => generalBimatrixDimensionWord (v 2) :=
    (Cobham.comp generalBimatrixDimensionWord_cobham fun _ => Cobham.proj 2).of_eq fun _ => rfl
  let g : Fin 4 → (Fin 3 → List Bool) → List Bool := fun i v =>
    ![generalBimatrixDimensionWord (v 2), v 0, v 1, v 2] i
  have hg : ∀ i, Cobham (g i) := fun i => by
    fin_cases i
    · exact hk'
    · exact Cobham.proj 0
    · exact Cobham.proj 1
    · exact Cobham.proj 2
  exact (Cobham.comp (gs := g) hr hg).of_eq fun _ => rfl

theorem generalBimatrixBasisMatrixWord_mem_FPn : FPn generalBimatrixBasisMatrixWord :=
  cobham_iff_FPn.mp generalBimatrixBasisMatrixWord_cobham

private theorem entryWord_of_none (v : Fin 4 → List Bool)
    (h : binarySubsetNthPosition ![v 2, v 1] = none) :
    generalBimatrixBasisEntryWord v = [false] := by
  let found := binarySubsetNth ![v 2, v 1]
  change (if found.headD false then some found.tail.length else none) = none at h
  change caseBit₀ found _ [false] = [false]
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
      rw [entryWord_of_none _ hn]
      simp only [f, ht, ↓reduceDIte]
      rfl
  have hbound (t : ℕ) (ht : t < (generalBimatrixDimensionWord input).length) :
      (f t).natAbs < 2 ^ (fieldWidth.length - 1) := by
    have ht' : t < generalRowCount input + generalColCount input := by simpa using ht
    dsimp only [f]
    rw [dite_eq_left ht']
    exact hb i ⟨t, ht'⟩
  have hval := binarySignedTable_value entryTerm fieldWidth
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
    simp only [rows, recNotation_cons, Bool.cond_self]
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

end GameTheory.Complexity.Backend
