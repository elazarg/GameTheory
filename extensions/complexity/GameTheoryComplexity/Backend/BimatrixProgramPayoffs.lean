import GameTheoryComplexity.Backend.BimatrixProgramCodec
import GameTheoryComplexity.Backend.BinaryUnaryArithmetic
import GameTheoryComplexity.Backend.BinarySignedAddition
import GameTheoryComplexity.Backend.BinaryUnaryEncoding

/-! Certified entry queries for the canonical mixed-gate game's integer payoffs.
All loops are controlled by word lengths, and signed padding is interpreted exactly. -/
namespace GameTheory.Complexity.Backend.BimatrixProgramPayoffs
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite

/-- Signed twice the decoded output count. -/
def capacityWord (tape : List Bool) : List Bool :=
  false :: false :: binaryLengthWord (BimatrixProgramCodec.dimension tape)

private def sameBlock (r s : List Bool) : List Bool :=
  lenEqFlag (binaryHalfRuler r) (binaryHalfRuler s)
private def oppositeKind (r s : List Bool) : List Bool :=
  orBit (andBit (binaryLengthParity r) (notBit (binaryLengthParity s)))
    (andBit (notBit (binaryLengthParity r)) (binaryLengthParity s))
private def ownOutput (r s : List Bool) : List Bool :=
  andBit (sameBlock r s) (binaryLengthParity r)
private def positivePart (q : List Bool) : List Bool := caseBit₀ (bitAt [] q) [] q
private def negativePart (q : List Bool) : List Bool :=
  caseBit₀ (bitAt [] q) (binarySignedNeg q) []

/-- Row payoff query on row-action, column-action, and program tape. -/
def rowEntry (v : Fin 3 → List Bool) : List Bool :=
  binarySignedAdd
    (caseBit₀ (sameBlock (v 0) (v 1)) (BimatrixProgramCodec.baselineWord (v 2)) [])
    (caseBit₀ (andBit (sameBlock (v 0) (v 1)) (oppositeKind (v 0) (v 1)))
      (capacityWord (v 2)) [])

/-- Column payoff query on row-action, column-action, and program tape. -/
def columnEntry (v : Fin 3 → List Bool) : List Bool :=
  let q := BimatrixProgramCodec.coefficientField ![v 2, binaryHalfRuler (v 1), v 0]
  let feedback := caseBit₀ (ownOutput (v 0) (v 1)) (capacityWord (v 2)) []
  binarySignedAdd
    (caseBit₀ (sameBlock (v 0) (v 1))
      (binarySignedNeg (BimatrixProgramCodec.baselineWord (v 2))) [])
    (caseBit₀ (binaryLengthParity (v 1))
      (binarySignedAdd (negativePart q) feedback)
      (binarySignedAdd (positivePart q)
        (caseBit₀ (BimatrixProgramCodec.kindFlag ![v 2, binaryHalfRuler (v 1)]) feedback [])))

private theorem lenEq_value (a b : List Bool) :
    lenEqFlag a b = [decide (a.length = b.length)] := by
  rcases lenEqFlag_flag a b with h | h
  · rw [h]
    simp [(lenEqFlag_eq_true_iff a b).mp h]
  · rw [h]
    have hn : a.length ≠ b.length := by
      intro he
      have ht := (lenEqFlag_eq_true_iff a b).mpr he
      rw [h] at ht
      contradiction
    simp [hn]

private theorem select_value (P : Prop) [Decidable P] (x : List Bool) :
    binarySignedValue (caseBit₀ [decide P] x []) = if P then binarySignedValue x else 0 := by
  by_cases h : P <;> simp [h, caseBit₀, binarySignedValue, Nat.fromBitsLE, Nat.fromBits]

private theorem positivePart_value (q : List Bool) :
    binarySignedValue (positivePart q) = max (binarySignedValue q) 0 := by
  cases q with
  | nil => rfl
  | cons b q =>
    cases b <;> simp [positivePart, bitAt, caseBit₀, binarySignedValue,
      Nat.fromBitsLE, Nat.fromBits]

private theorem negativePart_value (q : List Bool) :
    binarySignedValue (negativePart q) = max (-binarySignedValue q) 0 := by
  cases q with
  | nil => rfl
  | cons b q =>
    cases b
    · simp [negativePart, bitAt, caseBit₀, binarySignedValue, Nat.fromBitsLE, Nat.fromBits]
    · change binarySignedValue (binarySignedNeg (true :: q)) = _
      rw [binarySignedNeg_value]
      simp [binarySignedValue]

/-- The response capacity is exactly twice the decoded dimension. -/
theorem capacityWord_value (tape : List Bool) :
    binarySignedValue (capacityWord tape) = 2 * (BimatrixProgramCodec.dimension tape).length := by
  simp only [capacityWord, binarySignedValue, List.headD_cons, Bool.false_eq_true,
    ite_false, List.tail_cons, Nat.fromBitsLE_cons, zero_add,
    binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]

/-- The capacity word has length bounded by its explicit dimension ruler. -/
theorem capacityWord_length (tape : List Bool) :
    (capacityWord tape).length ≤ (BimatrixProgramCodec.dimension tape).length + 3 := by
  have h := binaryLengthWord_length (BimatrixProgramCodec.dimension tape)
  simp only [capacityWord, List.length_cons]
  omega

private theorem sameBlock_value (r s : List Bool) :
    sameBlock r s = [decide (r.length / 2 = s.length / 2)] := by
  rw [sameBlock, lenEq_value, binaryHalfRuler_length, binaryHalfRuler_length]

private theorem oppositeKind_value (r s : List Bool) :
    oppositeKind r s = [decide (r.length % 2 ≠ s.length % 2)] := by
  have hr : r.length % 2 < 2 := Nat.mod_lt _ (by omega)
  have hs : s.length % 2 < 2 := Nat.mod_lt _ (by omega)
  rw [oppositeKind, binaryLengthParity_value, binaryLengthParity_value]
  rcases Nat.mod_two_eq_zero_or_one r.length with hr | hr <;>
    rcases Nat.mod_two_eq_zero_or_one s.length with hs | hs <;>
      simp [hr, hs, andBit, orBit, notBit, caseBit₀]

private theorem ownOutput_value (r s : List Bool) :
    ownOutput r s = [decide (r.length / 2 = s.length / 2 ∧ r.length % 2 = 1)] := by
  rw [ownOutput, sameBlock_value, binaryLengthParity_value]
  by_cases he : r.length / 2 = s.length / 2 <;>
    by_cases ho : r.length % 2 = 1 <;> simp [he, ho, andBit, caseBit₀]

/-- The capacity word is computed by a polynomial-time string machine. -/
theorem capacityWord_cobham :
    Cobham fun v : Fin 1 → List Bool => capacityWord (v 0) :=
  appendFn (Cobham.const [false, false])
    (Cobham.comp binaryLengthWord_cobham fun _ : Fin 1 =>
      BimatrixProgramCodec.dimension_cobham)

private theorem sameBlock_fn {n : ℕ} {r s : (Fin n → List Bool) → List Bool}
    (hr : Cobham r) (hs : Cobham s) : Cobham fun v => sameBlock (r v) (s v) :=
  lenEqFlag_mem (Cobham.comp binaryHalfRuler_cobham fun _ : Fin 1 => hr)
    (Cobham.comp binaryHalfRuler_cobham fun _ : Fin 1 => hs)

private theorem parity_fn {n : ℕ} {r : (Fin n → List Bool) → List Bool}
    (hr : Cobham r) : Cobham fun v => binaryLengthParity (r v) :=
  Cobham.comp binaryLengthParity_cobham fun _ : Fin 1 => hr

private theorem oppositeKind_fn {n : ℕ} {r s : (Fin n → List Bool) → List Bool}
    (hr : Cobham r) (hs : Cobham s) : Cobham fun v => oppositeKind (r v) (s v) :=
  Cobham.orFn (Cobham.andFn (parity_fn hr) (Cobham.notFn (parity_fn hs)))
    (Cobham.andFn (Cobham.notFn (parity_fn hr)) (parity_fn hs))

/-- The row payoff entry is an actual polynomial-time query. -/
theorem rowEntry_cobham : Cobham rowEntry := by
  have hH : Cobham fun v : Fin 3 → List Bool => BimatrixProgramCodec.baselineWord (v 2) :=
    Cobham.comp BimatrixProgramCodec.baselineWord_cobham fun _ : Fin 1 => .proj 2
  have hC : Cobham fun v : Fin 3 → List Bool => capacityWord (v 2) :=
    Cobham.comp capacityWord_cobham fun _ : Fin 1 => .proj 2
  have hsame := sameBlock_fn (Cobham.proj (0 : Fin 3)) (Cobham.proj (1 : Fin 3))
  exact Cobham.comp₂ binarySignedAdd_cobham (Cobham.iteFn hsame hH Cobham.empty)
    (Cobham.iteFn (Cobham.andFn hsame (oppositeKind_fn (.proj 0) (.proj 1))) hC Cobham.empty)

theorem rowEntry_mem_FPn : FPn rowEntry := cobham_iff_FPn.mp rowEntry_cobham

/-- The column payoff entry is an actual polynomial-time query. -/
theorem columnEntry_cobham : Cobham columnEntry := by
  have hhalf : Cobham fun v : Fin 3 → List Bool => binaryHalfRuler (v 1) :=
    Cobham.comp binaryHalfRuler_cobham fun _ : Fin 1 => .proj 1
  have hq := Cobham.comp₃ BimatrixProgramCodec.coefficientField_cobham (.proj 2) hhalf (.proj 0)
  have hk := Cobham.comp₂ BimatrixProgramCodec.kindFlag_cobham (.proj 2) hhalf
  have hH : Cobham fun v : Fin 3 → List Bool => BimatrixProgramCodec.baselineWord (v 2) :=
    Cobham.comp BimatrixProgramCodec.baselineWord_cobham fun _ : Fin 1 => .proj 2
  have hC : Cobham fun v : Fin 3 → List Bool => capacityWord (v 2) :=
    Cobham.comp capacityWord_cobham fun _ : Fin 1 => .proj 2
  have hsame := sameBlock_fn (Cobham.proj (0 : Fin 3)) (Cobham.proj (1 : Fin 3))
  have hfeedback := Cobham.iteFn (Cobham.andFn hsame (parity_fn (.proj 0))) hC Cobham.empty
  have hsign := Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) hq
  have hp := Cobham.iteFn hsign Cobham.empty hq
  have hn := Cobham.iteFn hsign
    (Cobham.comp binarySignedNeg_cobham fun _ : Fin 1 => hq) Cobham.empty
  exact Cobham.comp₂ binarySignedAdd_cobham
    (Cobham.iteFn hsame (Cobham.comp binarySignedNeg_cobham fun _ : Fin 1 => hH) Cobham.empty)
    (Cobham.iteFn (parity_fn (.proj 1))
      (Cobham.comp₂ binarySignedAdd_cobham hn hfeedback)
      (Cobham.comp₂ binarySignedAdd_cobham hp (Cobham.iteFn hk hfeedback Cobham.empty)))

theorem columnEntry_mem_FPn : FPn columnEntry := cobham_iff_FPn.mp columnEntry_cobham

/-- Total row-entry arithmetic, also describing out-of-range query rulers. -/
theorem rowEntry_value (r s tape : List Bool) :
    binarySignedValue (rowEntry ![r, s, tape]) =
      (if r.length / 2 = s.length / 2 then BimatrixProgramCodec.baseline tape else 0) +
      (if r.length / 2 = s.length / 2 ∧ r.length % 2 ≠ s.length % 2
        then 2 * (BimatrixProgramCodec.dimension tape).length else 0) := by
  change binarySignedValue (binarySignedAdd _ _) = _
  rw [binarySignedAdd_value, sameBlock_value, oppositeKind_value]
  have hz : binarySignedValue [] = 0 := rfl
  by_cases he : r.length / 2 = s.length / 2 <;>
    by_cases ho : r.length % 2 ≠ s.length % 2 <;>
      simp [he, ho, andBit, caseBit₀, capacityWord_value,
        BimatrixProgramCodec.baseline, hz]

/-- Total column-entry arithmetic with the canonical packed coefficient value. -/
theorem columnEntry_value (r s tape : List Bool) :
    let q := binarySignedRowValue (BimatrixProgramCodec.width tape)
      (BimatrixProgramCodec.coefficientTape tape)
      ((s.length / 2) * ((BimatrixProgramCodec.dimension tape).length * 2) + r.length)
    let C : ℤ := 2 * (BimatrixProgramCodec.dimension tape).length
    let feedback : ℤ := if r.length / 2 = s.length / 2 ∧ r.length % 2 = 1 then C else 0
    binarySignedValue (columnEntry ![r, s, tape]) =
      (if r.length / 2 = s.length / 2 then -BimatrixProgramCodec.baseline tape else 0) +
      (if s.length % 2 = 1 then max (-q) 0 + feedback
       else max q 0 + if (BimatrixProgramCodec.kindFlags tape)[s.length / 2]?.getD false
         then feedback else 0) := by
  have hq := BimatrixProgramCodec.coefficientField_value ![tape, binaryHalfRuler s, r]
  change binarySignedValue (BimatrixProgramCodec.coefficientField
    ![tape, binaryHalfRuler s, r]) = binarySignedRowValue (BimatrixProgramCodec.width tape)
      (BimatrixProgramCodec.coefficientTape tape)
      ((binaryHalfRuler s).length * ((BimatrixProgramCodec.dimension tape).length * 2) +
        r.length) at hq
  rw [binaryHalfRuler_length] at hq
  have hk := BimatrixProgramCodec.kindFlag_value ![tape, binaryHalfRuler s]
  change BimatrixProgramCodec.kindFlag ![tape, binaryHalfRuler s] =
    [(BimatrixProgramCodec.kindFlags tape)[(binaryHalfRuler s).length]?.getD false] at hk
  rw [binaryHalfRuler_length] at hk
  dsimp only
  change binarySignedValue (binarySignedAdd
    (caseBit₀ (sameBlock r s) (binarySignedNeg (BimatrixProgramCodec.baselineWord tape)) [])
    (caseBit₀ (binaryLengthParity s)
      (binarySignedAdd
        (negativePart (BimatrixProgramCodec.coefficientField ![tape, binaryHalfRuler s, r]))
        (caseBit₀ (ownOutput r s) (capacityWord tape) []))
      (binarySignedAdd
        (positivePart (BimatrixProgramCodec.coefficientField ![tape, binaryHalfRuler s, r]))
        (caseBit₀ (BimatrixProgramCodec.kindFlag ![tape, binaryHalfRuler s])
          (caseBit₀ (ownOutput r s) (capacityWord tape) []) [])))) = _
  rw [binarySignedAdd_value, sameBlock_value, ownOutput_value,
    binaryLengthParity_value, hk]
  have hz : binarySignedValue [] = 0 := rfl
  by_cases he : r.length / 2 = s.length / 2 <;>
    by_cases hr : r.length % 2 = 1 <;>
    by_cases hs : s.length % 2 = 1 <;>
    cases hd : (BimatrixProgramCodec.kindFlags tape)[s.length / 2]?.getD false <;>
      simp [he, hr, hs, caseBit₀, binarySignedAdd_value,
        binarySignedNeg_value, positivePart_value, negativePart_value, hq,
        capacityWord_value, BimatrixProgramCodec.baseline, hz]

/-- On bounded action indices the row query is the canonical affine row payoff. -/
theorem rowEntry_eq_rowPayoff (tape r s : List Bool)
    (ri si : Fin ((BimatrixProgramCodec.dimension tape).length * 2))
    (hr : r.length = ri.val) (hs : s.length = si.val) :
    binarySignedValue (rowEntry ![r, s, tape]) =
      BimatrixAffineGate.rowPayoff (BimatrixProgramCodec.baseline tape)
        (2 * (BimatrixProgramCodec.dimension tape).length) ri si := by
  obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective ri
  obtain ⟨⟨j, c⟩, rfl⟩ := finProdFinEquiv.surjective si
  have hrd : r.length / 2 = i.val := by
    rw [hr]
    change (b.val + 2 * i.val) / 2 = i.val
    omega
  have hsd : s.length / 2 = j.val := by
    rw [hs]
    change (c.val + 2 * j.val) / 2 = j.val
    omega
  have hrm : r.length % 2 = b.val := by
    rw [hr]
    change (b.val + 2 * i.val) % 2 = b.val
    omega
  have hsm : s.length % 2 = c.val := by
    rw [hs]
    change (c.val + 2 * j.val) % 2 = c.val
    omega
  rw [rowEntry_value, hrd, hsd, hrm, hsm]
  fin_cases b <;> fin_cases c <;> by_cases hij : i = j <;>
    simp [BimatrixAffineGate.rowPayoff, BimatrixAffineGate.rowPerturbation,
      BimatrixBlockGame.matchingBlockPayoff, BimatrixBlockGame.pairedBlock,
      finProdFinEquiv.injective.eq_iff, Fin.val_inj, hij, eq_comm]

/-- On bounded action indices the column query is the canonical mixed-program payoff. -/
theorem columnEntry_eq_columnPayoff (tape r s : List Bool)
    (ri si : Fin ((BimatrixProgramCodec.dimension tape).length * 2))
    (hr : r.length = ri.val) (hs : s.length = si.val) :
    binarySignedValue (columnEntry ![r, s, tape]) =
      BimatrixGateProgram.columnPayoff (BimatrixProgramCodec.baseline tape)
        (2 * (BimatrixProgramCodec.dimension tape).length) (BimatrixProgramCodec.decode tape)
        ri si := by
  obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective ri
  obtain ⟨⟨j, c⟩, rfl⟩ := finProdFinEquiv.surjective si
  have hrd : r.length / 2 = i.val := by
    rw [hr]
    change (b.val + 2 * i.val) / 2 = i.val
    omega
  have hsd : s.length / 2 = j.val := by
    rw [hs]
    change (c.val + 2 * j.val) / 2 = j.val
    omega
  have hrm : r.length % 2 = b.val := by
    rw [hr]
    change (b.val + 2 * i.val) % 2 = b.val
    omega
  have hsm : s.length % 2 = c.val := by
    rw [hs]
    change (c.val + 2 * j.val) % 2 = c.val
    omega
  rw [columnEntry_value]
  rw [hrd, hsd, hrm, hsm, hr]
  fin_cases b <;> fin_cases c <;> by_cases hij : i = j <;>
    cases hk : (BimatrixProgramCodec.kindFlags tape)[j.val]?.getD false <;>
      simp [BimatrixGateProgram.columnPayoff, BimatrixAffineGate.columnPayoff,
        BimatrixAffineGate.columnPerturbation, BimatrixGateProgram.positiveCoefficients,
        BimatrixGateProgram.negativeCoefficients, BimatrixBlockGame.matchingBlockPayoff,
        BimatrixBlockGame.pairedBlock, BimatrixProgramCodec.decode, hk,
        finProdFinEquiv.injective.eq_iff, Fin.val_inj, hij, eq_comm]

private theorem select_length (flag x y : List Bool) :
    (caseBit₀ flag x y).length ≤ max x.length y.length := by
  cases flag with
  | nil => exact le_max_right _ _
  | cons b flag => cases b <;> simp [caseBit₀]

/-- Every row query has a word-length bound independent of the action rulers. -/
theorem rowEntry_length (v : Fin 3 → List Bool) :
    (rowEntry v).length ≤ (BimatrixProgramCodec.baselineWord (v 2)).length +
      (BimatrixProgramCodec.dimension (v 2)).length + 5 := by
  have hH := select_length (sameBlock (v 0) (v 1))
    (BimatrixProgramCodec.baselineWord (v 2)) []
  have hC := select_length (andBit (sameBlock (v 0) (v 1)) (oppositeKind (v 0) (v 1)))
    (capacityWord (v 2)) []
  have hc := capacityWord_length (v 2)
  have ha := binarySignedAdd_length
    (caseBit₀ (sameBlock (v 0) (v 1)) (BimatrixProgramCodec.baselineWord (v 2)) [])
    (caseBit₀ (andBit (sameBlock (v 0) (v 1)) (oppositeKind (v 0) (v 1)))
      (capacityWord (v 2)) [])
  simp only [List.length_nil, max_zero] at hH hC
  exact ha.trans (by omega)

/-- Every column query has a word-length bound independent of the action rulers. -/
theorem columnEntry_length (v : Fin 3 → List Bool) :
    (columnEntry v).length ≤ (BimatrixProgramCodec.baselineWord (v 2)).length +
      (BimatrixProgramCodec.width (v 2)).length +
      (BimatrixProgramCodec.dimension (v 2)).length + 8 := by
  let q := BimatrixProgramCodec.coefficientField ![v 2, binaryHalfRuler (v 1), v 0]
  let feedback := caseBit₀ (ownOutput (v 0) (v 1)) (capacityWord (v 2)) []
  have hq : q.length ≤ (BimatrixProgramCodec.width (v 2)).length :=
    binarySignedRowField_length _
  have hf : feedback.length ≤ (BimatrixProgramCodec.dimension (v 2)).length + 3 := by
    have hs := select_length (ownOutput (v 0) (v 1)) (capacityWord (v 2)) []
    have hc := capacityWord_length (v 2)
    simp only [List.length_nil, max_zero] at hs
    exact hs.trans hc
  have hp : (positivePart q).length ≤ q.length := by
    have hs := select_length (bitAt [] q) [] q
    simpa only [positivePart, List.length_nil, zero_max] using hs
  have hn : (negativePart q).length ≤ q.length + 1 := by
    have hs := select_length (bitAt [] q) (binarySignedNeg q) []
    simp only [List.length_nil, max_zero] at hs
    exact hs.trans (binarySignedNeg_length q)
  have hk : (caseBit₀ (BimatrixProgramCodec.kindFlag ![v 2, binaryHalfRuler (v 1)])
      feedback []).length ≤ feedback.length := by
    simpa only [List.length_nil, max_zero] using select_length
      (BimatrixProgramCodec.kindFlag ![v 2, binaryHalfRuler (v 1)]) feedback []
  have hneg := binarySignedAdd_length (negativePart q) feedback
  have hpos := binarySignedAdd_length (positivePart q)
    (caseBit₀ (BimatrixProgramCodec.kindFlag ![v 2, binaryHalfRuler (v 1)]) feedback [])
  have hi := select_length (binaryLengthParity (v 1))
    (binarySignedAdd (negativePart q) feedback)
    (binarySignedAdd (positivePart q)
      (caseBit₀ (BimatrixProgramCodec.kindFlag ![v 2, binaryHalfRuler (v 1)]) feedback []))
  have hbase := select_length (sameBlock (v 0) (v 1))
    (binarySignedNeg (BimatrixProgramCodec.baselineWord (v 2))) []
  have hH := binarySignedNeg_length (BimatrixProgramCodec.baselineWord (v 2))
  simp only [List.length_nil, max_zero] at hbase
  have ha := binarySignedAdd_length
    (caseBit₀ (sameBlock (v 0) (v 1))
      (binarySignedNeg (BimatrixProgramCodec.baselineWord (v 2))) [])
    (caseBit₀ (binaryLengthParity (v 1))
      (binarySignedAdd (negativePart q) feedback)
      (binarySignedAdd (positivePart q)
        (caseBit₀ (BimatrixProgramCodec.kindFlag ![v 2, binaryHalfRuler (v 1)]) feedback [])))
  exact ha.trans (by omega)

end GameTheory.Complexity.Backend.BimatrixProgramPayoffs
