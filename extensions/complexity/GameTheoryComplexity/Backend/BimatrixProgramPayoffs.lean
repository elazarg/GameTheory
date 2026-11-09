module

public import GameTheoryComplexity.Backend.BimatrixProgramCodec
public import GameTheoryComplexity.Backend.BinaryUnaryArithmetic
public import GameTheoryComplexity.Backend.BinarySignedAddition
public import GameTheoryComplexity.Backend.BinaryUnaryEncoding

@[expose] public section

/-! Integer payoff queries for the canonical mixed-gate game use explicit
action ruler lengths. Total queries retain signed padding and the codec's
truncated-field and missing-kind behavior. -/

namespace GameTheory.Complexity.Backend.BimatrixProgramPayoffs

open Turing.MultiTapeTM
open GameTheory.Finite

/-- Signed twice the decoded output count. -/
def capacityWord (tape : List Bool) : List Bool :=
  false :: false :: binaryLengthWord (BimatrixProgramCodec.dimension tape)

private def positivePart (q : List Bool) : List Bool := if q.headD false then [] else q

private def negativePart (q : List Bool) : List Bool :=
  if q.headD false then binarySignedNeg q else []

/-- Row payoff query on a row ruler, a column ruler, and a program tape. -/
def rowEntry (r s tape : List Bool) : List Bool :=
  binarySignedAdd
    (if r.length / 2 = s.length / 2 then BimatrixProgramCodec.baselineWord tape else [])
    (if r.length / 2 = s.length / 2 ∧ r.length % 2 ≠ s.length % 2 then capacityWord tape else [])

/-- Column payoff query on a row ruler, a column ruler, and a program tape. -/
def columnEntry (r s tape : List Bool) : List Bool :=
  let q := BimatrixProgramCodec.coefficientField tape (binaryHalfRuler s) r
  let feedback :=
    if r.length / 2 = s.length / 2 ∧ r.length % 2 = 1 then capacityWord tape else []
  binarySignedAdd
    (if r.length / 2 = s.length / 2 then
      binarySignedNeg (BimatrixProgramCodec.baselineWord tape) else [])
    (if s.length % 2 = 1 then
      binarySignedAdd (if q.headD false then binarySignedNeg q else []) feedback
    else
      binarySignedAdd (if q.headD false then [] else q)
        (if BimatrixProgramCodec.kindFlag tape (binaryHalfRuler s) then feedback else []))

private theorem positivePart_value (q : List Bool) :
    binarySignedValue (positivePart q) = max (binarySignedValue q) 0 := by
  cases q with
  | nil => rfl
  | cons b q =>
    cases b
    · simp [positivePart, binarySignedValue]
    · simp [positivePart, binarySignedValue, ofBits]

private theorem negativePart_value (q : List Bool) :
    binarySignedValue (negativePart q) = max (-binarySignedValue q) 0 := by
  cases q with
  | nil => rfl
  | cons b q =>
    cases b
    · simp [negativePart, binarySignedValue, ofBits]
    · change binarySignedValue (binarySignedNeg (true :: q)) = _
      rw [binarySignedNeg_value]
      simp [binarySignedValue]

/-- The response capacity is exactly twice the decoded dimension. -/
theorem capacityWord_value (tape : List Bool) :
    binarySignedValue (capacityWord tape) = 2 * (BimatrixProgramCodec.dimension tape).length := by
  change (ofBits (false :: binaryLengthWord (BimatrixProgramCodec.dimension tape)) : ℤ) = _
  have h : ofBits (false :: binaryLengthWord (BimatrixProgramCodec.dimension tape)) =
      2 * (BimatrixProgramCodec.dimension tape).length := by
    change Nat.bit false (ofBits (binaryLengthWord (BimatrixProgramCodec.dimension tape))) = _
    rw [binaryLengthWord_value, Nat.bit_false_apply]
  exact_mod_cast h

/-- The capacity encoding is bounded by the explicit dimension ruler. -/
theorem capacityWord_length (tape : List Bool) :
    (capacityWord tape).length ≤ (BimatrixProgramCodec.dimension tape).length + 3 := by
  have h := binaryLengthWord_length (BimatrixProgramCodec.dimension tape)
  simp only [capacityWord, List.length_cons]
  omega

/-- Total row-entry arithmetic also covers out-of-range action rulers. -/
theorem rowEntry_value (r s tape : List Bool) :
    binarySignedValue (rowEntry r s tape) =
      (if r.length / 2 = s.length / 2 then BimatrixProgramCodec.baseline tape else 0) +
      (if r.length / 2 = s.length / 2 ∧ r.length % 2 ≠ s.length % 2
        then 2 * (BimatrixProgramCodec.dimension tape).length else 0) := by
  rw [rowEntry, binarySignedAdd_value]
  have hz : binarySignedValue [] = 0 := rfl
  by_cases he : r.length / 2 = s.length / 2 <;>
    by_cases ho : r.length % 2 ≠ s.length % 2 <;>
      simp [he, ho, capacityWord_value, BimatrixProgramCodec.baseline, hz]

/-- Total column-entry arithmetic retains the canonical packed coefficient interpretation. -/
theorem columnEntry_value (r s tape : List Bool) :
    let q := binarySignedRowValue (BimatrixProgramCodec.width tape)
      (BimatrixProgramCodec.coefficientTape tape)
      ((s.length / 2) * ((BimatrixProgramCodec.dimension tape).length * 2) + r.length)
    let C : ℤ := 2 * (BimatrixProgramCodec.dimension tape).length
    let feedback : ℤ := if r.length / 2 = s.length / 2 ∧ r.length % 2 = 1 then C else 0
    binarySignedValue (columnEntry r s tape) =
      (if r.length / 2 = s.length / 2 then -BimatrixProgramCodec.baseline tape else 0) +
      (if s.length % 2 = 1 then max (-q) 0 + feedback
       else max q 0 + if (BimatrixProgramCodec.kindFlags tape).getD (s.length / 2) false
         then feedback else 0) := by
  have hq := BimatrixProgramCodec.coefficientField_value tape (binaryHalfRuler s) r
  rw [binaryHalfRuler_length] at hq
  dsimp only
  change binarySignedValue (binarySignedAdd
    (if r.length / 2 = s.length / 2 then
      binarySignedNeg (BimatrixProgramCodec.baselineWord tape) else [])
    (if s.length % 2 = 1 then
      binarySignedAdd
        (negativePart (BimatrixProgramCodec.coefficientField tape (binaryHalfRuler s) r))
        (if r.length / 2 = s.length / 2 ∧ r.length % 2 = 1 then capacityWord tape else [])
    else
      binarySignedAdd
        (positivePart (BimatrixProgramCodec.coefficientField tape (binaryHalfRuler s) r))
        (if BimatrixProgramCodec.kindFlag tape (binaryHalfRuler s) then
          (if r.length / 2 = s.length / 2 ∧ r.length % 2 = 1 then capacityWord tape else [])
        else []))) = _
  rw [binarySignedAdd_value]
  have hz : binarySignedValue [] = 0 := rfl
  by_cases he : r.length / 2 = s.length / 2 <;>
    by_cases hr : r.length % 2 = 1 <;>
    by_cases hs : s.length % 2 = 1 <;>
    cases hd : (BimatrixProgramCodec.kindFlags tape)[s.length / 2]?.getD false <;>
      simp [he, hr, hs, hd, binarySignedAdd_value, binarySignedNeg_value,
        positivePart_value, negativePart_value, hq, capacityWord_value,
        BimatrixProgramCodec.baseline, BimatrixProgramCodec.kindFlag, binaryHalfRuler_length, hz]

/-- Bounded action rulers recover the canonical affine row payoff. -/
theorem rowEntry_eq_rowPayoff (tape r s : List Bool)
    (ri si : Fin ((BimatrixProgramCodec.dimension tape).length * 2))
    (hr : r.length = ri.val) (hs : s.length = si.val) :
    binarySignedValue (rowEntry r s tape) =
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

/-- Bounded action rulers recover the canonical mixed-program column payoff. -/
theorem columnEntry_eq_columnPayoff (tape r s : List Bool)
    (ri si : Fin ((BimatrixProgramCodec.dimension tape).length * 2))
    (hr : r.length = ri.val) (hs : s.length = si.val) :
    binarySignedValue (columnEntry r s tape) =
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

/-- Row query size is bounded independently of both action rulers. -/
theorem rowEntry_length (r s tape : List Bool) :
    (rowEntry r s tape).length ≤ (BimatrixProgramCodec.baselineWord tape).length +
      (BimatrixProgramCodec.dimension tape).length + 5 := by
  have hH : (if r.length / 2 = s.length / 2 then
      BimatrixProgramCodec.baselineWord tape else []).length ≤
      (BimatrixProgramCodec.baselineWord tape).length := by split <;> simp
  have hC : (if r.length / 2 = s.length / 2 ∧ r.length % 2 ≠ s.length % 2 then
      capacityWord tape else []).length ≤ (capacityWord tape).length := by split <;> simp
  have hc := capacityWord_length tape
  have h := binarySignedAdd_length
    (if r.length / 2 = s.length / 2 then BimatrixProgramCodec.baselineWord tape else [])
    (if r.length / 2 = s.length / 2 ∧ r.length % 2 ≠ s.length % 2 then capacityWord tape else [])
  exact h.trans (by omega)

/-- Column query size depends only on the explicit program headers. -/
theorem columnEntry_length (r s tape : List Bool) :
    (columnEntry r s tape).length ≤ (BimatrixProgramCodec.baselineWord tape).length +
      (BimatrixProgramCodec.width tape).length +
      (BimatrixProgramCodec.dimension tape).length + 8 := by
  let q := BimatrixProgramCodec.coefficientField tape (binaryHalfRuler s) r
  let feedback : List Bool :=
    if r.length / 2 = s.length / 2 ∧ r.length % 2 = 1 then capacityWord tape else []
  let base : List Bool :=
    if r.length / 2 = s.length / 2 then
      binarySignedNeg (BimatrixProgramCodec.baselineWord tape) else []
  let kindFeedback : List Bool :=
    if BimatrixProgramCodec.kindFlag tape (binaryHalfRuler s) then feedback else []
  have hq : q.length ≤ (BimatrixProgramCodec.width tape).length :=
    BimatrixProgramCodec.coefficientField_length _ _ _
  have hf : feedback.length ≤ (BimatrixProgramCodec.dimension tape).length + 3 := by
    have hs : feedback.length ≤ (capacityWord tape).length := by
      dsimp only [feedback]
      split <;> simp
    exact hs.trans (capacityWord_length tape)
  have hp : (positivePart q).length ≤ q.length := by
    unfold positivePart
    split <;> simp
  have hn : (negativePart q).length ≤ q.length + 1 := by
    unfold negativePart
    split
    · exact binarySignedNeg_length q
    · simp
  have hk : kindFeedback.length ≤ feedback.length := by
    dsimp only [kindFeedback]
    split <;> simp
  have hb : base.length ≤ (BimatrixProgramCodec.baselineWord tape).length + 1 := by
    dsimp only [base]
    split
    · exact binarySignedNeg_length _
    · simp
  have hneg := binarySignedAdd_length (negativePart q) feedback
  have hpos := binarySignedAdd_length (positivePart q) kindFeedback
  have hi : (if s.length % 2 = 1 then binarySignedAdd (negativePart q) feedback
      else binarySignedAdd (positivePart q) kindFeedback).length ≤
      max (binarySignedAdd (negativePart q) feedback).length
        (binarySignedAdd (positivePart q) kindFeedback).length := by
    split
    · exact le_max_left _ _
    · exact le_max_right _ _
  have h := binarySignedAdd_length base
    (if s.length % 2 = 1 then binarySignedAdd (negativePart q) feedback
      else binarySignedAdd (positivePart q) kindFeedback)
  exact h.trans (by omega)

/-- Capacity words retain the actual encoding of their tape producer. -/
@[fun_prop] theorem capacityWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {tape : Input → List Bool} (ht : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => capacityWord (tape a)) input encBits :=
  ComputableInPolyTime.bitsCons (.const false) (ComputableInPolyTime.bitsCons (.const false)
    (binaryLengthWord_polyTime.comp (BimatrixProgramCodec.dimension_polyTime ht)))

private theorem actionGuards_polyTime {Input : Type} {input : Input ↪ List Bool}
    {r s : Input → List Bool}
    (hr : ComputableInPolyTime r input encBits) (hs : ComputableInPolyTime s input encBits) :
    ComputableInPolyTime (fun a => decide ((r a).length / 2 = (s a).length / 2)) input encBool ∧
    ComputableInPolyTime (fun a => decide ((r a).length % 2 ≠ (s a).length % 2)) input encBool ∧
    ComputableInPolyTime (fun a => decide ((r a).length % 2 = 1)) input encBool ∧
    ComputableInPolyTime (fun a => decide ((s a).length % 2 = 1)) input encBool := by
  have hrl := ComputableInPolyTime.length_bits_comp hr
  have hsl := ComputableInPolyTime.length_bits_comp hs
  have hrh := (ComputableInPolyTime.unary_div_const 2).comp hrl
  have hsh := (ComputableInPolyTime.unary_div_const 2).comp hsl
  have hrm := ComputableInPolyTime.unary_mod.comp (hrl.prod (ComputableInPolyTime.const 2))
  have hsm := ComputableInPolyTime.unary_mod.comp (hsl.prod (ComputableInPolyTime.const 2))
  exact ⟨ComputableInPolyTime.decide_eq' hrh hsh,
    ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.decide_ne hrm.tidy hsm.tidy),
    ComputableInPolyTime.decide_eq' hrm (ComputableInPolyTime.const 1),
    ComputableInPolyTime.decide_eq' hsm (ComputableInPolyTime.const 1)⟩

/-- Total row payoff queries compose with all three certified word producers. -/
@[fun_prop] theorem rowEntry_polyTime {Input : Type} {input : Input ↪ List Bool}
    {r s tape : Input → List Bool}
    (hr : ComputableInPolyTime r input encBits) (hs : ComputableInPolyTime s input encBits)
    (ht : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => rowEntry (r a) (s a) (tape a)) input encBits := by
  have hg := actionGuards_polyTime hr hs
  exact binarySignedAdd_polyTime
    (hg.1.ite_decide (BimatrixProgramCodec.baselineWord_polyTime ht) (.const []))
    ((ComputableInPolyTime.decide_and hg.1 hg.2.1).ite_decide
      (capacityWord_polyTime ht) (.const []))

/-- Column payoff queries charge action guards, packed lookup, and signed arithmetic. -/
@[fun_prop] theorem columnEntry_polyTime {Input : Type} {input : Input ↪ List Bool}
    {r s tape : Input → List Bool}
    (hr : ComputableInPolyTime r input encBits) (hs : ComputableInPolyTime s input encBits)
    (ht : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => columnEntry (r a) (s a) (tape a)) input encBits := by
  have hg := actionGuards_polyTime hr hs
  have hhalf := binaryHalfRuler_polyTime.comp hs
  have hq := BimatrixProgramCodec.coefficientField_polyTime ht hhalf hr
  have hk := BimatrixProgramCodec.kindFlag_polyTime ht hhalf
  have hfeedback := (ComputableInPolyTime.decide_and hg.1 hg.2.2.1).ite_decide
    (capacityWord_polyTime ht) (ComputableInPolyTime.const [])
  have hsign : ComputableInPolyTime (fun a : Input =>
      (BimatrixProgramCodec.coefficientField (tape a) (binaryHalfRuler (s a)) (r a)).headD false)
      input encBool := (ComputableInPolyTime.headD false).comp hq
  have hpositive := hsign.ite (ComputableInPolyTime.const []) hq
  have hnegative := hsign.ite (binarySignedNeg_polyTime hq) (ComputableInPolyTime.const [])
  exact binarySignedAdd_polyTime
    (hg.1.ite_decide
      (binarySignedNeg_polyTime (BimatrixProgramCodec.baselineWord_polyTime ht)) (.const []))
    (hg.2.2.2.ite_decide (binarySignedAdd_polyTime hnegative hfeedback)
      (binarySignedAdd_polyTime hpositive (hk.ite hfeedback (.const []))))

end GameTheory.Complexity.Backend.BimatrixProgramPayoffs
