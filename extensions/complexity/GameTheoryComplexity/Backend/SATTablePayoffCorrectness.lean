import GameTheoryComplexity.Backend.SATTablePayoff
import GameTheoryComplexity.Backend.SATTableScannerCorrectness
import GameTheory.Core.SatisfiabilityGameEncoding
import GameTheory.Core.SatisfiabilityGamePayoff
import GameTheory.Finite.BimatrixTable
import GameTheoryComplexity.Backend.SATReductionSemantic

/-! Exact agreement between the polynomial-time payoff emitter and the canonical
literal/clause game. The result identifies every serialized integer table entry.
-/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.SatisfiabilityGame GameTheory.Finite.BimatrixTable

private theorem tally_replicate (width : List Bool) (positive negative : ℕ)
    (hp : positive ≤ width.length) (hn : negative ≤ width.length) :
    satTallyPair width (List.replicate positive true) (List.replicate negative true) =
      (List.replicate positive true ++ List.replicate (width.length - positive) false) ++
        (List.replicate negative true ++ List.replicate (width.length - negative) false) := by
  rw [satTallyPair, padTo_eq_append _ _ (by simpa using hp),
    padTo_eq_append _ _ (by simpa using hn)]
  simp only [List.length_replicate]

private theorem tally_constant (input : List Bool) (z : ℤ)
    (hp : z.toNat ≤ 4 * (input.length + 1) + 3)
    (hn : (-z).toNat ≤ 4 * (input.length + 1) + 3) :
    satTallyPair (satTallyWidth input) (List.replicate z.toNat true) (List.replicate (-z).toNat true) =
      encodeEntry (4 * (input.length + 1) + 1) z := by
  rw [tally_replicate _ _ _ (by simpa using hp) (by simpa using hn), satTallyWidth_length]
  unfold encodeEntry
  congr 2

private theorem tally_two_sub (input : List Bool) :
    satTallyPair (satTallyWidth input)
      ([true, true].drop (satUnaryN input).length) ((satUnaryN input).drop 2) =
      encodeEntry (4 * (input.length + 1) + 1) (2 - (input.length + 1 : ℕ)) := by
  have hp : (2 - (input.length + 1 : ℕ) : ℤ).toNat = 2 - (input.length + 1) := by omega
  have hn : (-(2 - (input.length + 1 : ℕ) : ℤ)).toNat = (input.length + 1) - 2 := by omega
  rw [satUnaryN_length, satUnaryN_eq]
  change satTallyPair (satTallyWidth input)
    ((List.replicate 2 true).drop (input.length + 1)) ((List.replicate (input.length + 1) true).drop 2) = _
  rw [List.drop_replicate, List.drop_replicate, ← hp, ← hn]
  apply tally_constant <;> omega

private theorem incidence_word (input : List Bool) (c v : Fin (input.length + 1)) (b : Bool) :
    andBit (satSyntaxWord input) [scanIncidence v.val b c.val input] =
      [satIncidence input c v b] := by
  cases hd : _root_.Complexity.SAT.CNF.decode? input with
  | none => simp [satSyntaxWord, hd, satIncidence, andBit, caseBit₀]
  | some φ =>
      rw [scanIncidence_eq_satIncidence input φ hd]
      cases satIncidence input c v b <;>
        simp [satSyntaxWord, hd, andBit, caseBit₀]

private theorem eqFlag_unary (i j : ℕ) :
    eqFlag (List.replicate i true) (List.replicate j true) = [decide (i = j)] := by
  simpa using eqFlag_as_bool (List.replicate i true) (List.replicate j true)

private theorem notLenLeFlag_unary (i j : ℕ) :
    notBit (lenLeFlag (List.replicate i true) (List.replicate j true)) = [decide (i < j)] := by
  rw [lenLeFlag_as_bool]
  simp only [List.length_replicate]
  by_cases h : i < j
  · have hn : ¬j ≤ i := by omega
    simp [notBit, caseBit₀, h, hn]
  · have hn : j ≤ i := by omega
    simp [notBit, caseBit₀, h, hn]

private theorem caseBit_decide (p : Prop) [Decidable p] (x y : List Bool) :
    caseBit₀ [decide p] x y = if p then x else y := by
  by_cases h : p <;> simp [h, caseBit₀]

private theorem caseBit_unary (p : Prop) [Decidable p] (i j : ℕ) :
    caseBit₀ [decide p] (List.replicate i true) (List.replicate j true) =
      List.replicate (if p then i else j) true := by
  by_cases h : p <;> simp [h, caseBit₀]

private theorem andFlag_bool (a b : Bool) : andBit [a] [b] = [a && b] := by
  cases a <;> cases b <;> rfl

private theorem notFlag_bool (a : Bool) : notBit [a] = [!a] := by cases a <;> rfl

private theorem encodeEntry_ite (q : ℕ) (p : Prop) [Decidable p] (x y : ℤ) :
    encodeEntry q (if p then x else y) = if p then encodeEntry q x else encodeEntry q y :=
  apply_ite (encodeEntry q) p x y

private theorem satPayoffCell_unary (input : List Bool) (i j : ℕ) :
    satPayoffCell satSyntaxWord ![List.replicate i true, List.replicate j true, input] =
      encodeEntry (4 * (input.length + 1) + 1)
        (let n := input.length + 1
         let colVar := if j < n then j else j - n
         if i = 4 * n then (if j = 4 * n then 0 else 1)
         else if i < 2 * n then
           (if j < 2 * n then
             if (if i < n then i else i - n) = colVar ∧ decide (i < n) ≠ decide (j < n) then -2 else 1
            else -2)
         else if i < 3 * n then
           (if j < 2 * n then (if i - 2 * n = colVar then 2 - n else 2) else -2)
         else if i < 4 * n then
           (if j < 2 * n then
             (if (_root_.Complexity.SAT.CNF.decode? input).isSome &&
               scanIncidence colVar (decide (j < n)) (i - 3 * n) input then 2 - n else 2)
            else -2)
         else -2) := by
  have hz0 := tally_constant input 0 (by omega) (by omega)
  have hz1 := tally_constant input 1 (by omega) (by omega)
  have hz2 := tally_constant input 2 (by omega) (by omega)
  have hzm2 := tally_constant input (-2) (by omega) (by omega)
  norm_num at hz0 hz1 hz2 hzm2
  unfold satPayoffCell
  change (let n := satUnaryN input; let n2 := n ++ n; let n3 := n2 ++ n; let n4 := n3 ++ n;
    let width := satTallyWidth input; let row := List.replicate i true; let col := List.replicate j true;
    let rowPositive := notBit (lenLeFlag row n); let colPositive := notBit (lenLeFlag col n);
    let rowVar := caseBit₀ rowPositive row (row.drop n.length);
    let colVar := caseBit₀ colPositive col (col.drop n.length);
    let rowLiteral := notBit (lenLeFlag row n2); let colLiteral := notBit (lenLeFlag col n2);
    let z0 := satTallyPair width [] []; let z1 := satTallyPair width [true] [];
    let z2 := satTallyPair width [true, true] []; let zm2 := satTallyPair width [] [true, true];
    let z2n := satTallyPair width ([true, true].drop n.length) (n.drop 2);
    let opposed := andBit (eqFlag rowVar colVar) (notBit (eqFlag rowPositive colPositive));
    let incidence := andBit (satSyntaxWord input)
      (incidenceVerdictWord ![colVar, colPositive, row.drop n3.length, input]);
    caseBit₀ (eqFlag row n4) (caseBit₀ (eqFlag col n4) z0 z1)
      (caseBit₀ rowLiteral (caseBit₀ colLiteral (caseBit₀ opposed zm2 z1) zm2)
        (caseBit₀ (notBit (lenLeFlag row n3))
          (caseBit₀ colLiteral (caseBit₀ (eqFlag (row.drop n2.length) colVar) z2n z2) zm2)
          (caseBit₀ (notBit (lenLeFlag row n4))
            (caseBit₀ colLiteral (caseBit₀ incidence z2n z2) zm2) zm2)))) = _
  dsimp only
  rw [hz0, hz1, hz2, hzm2, tally_two_sub]
  rw [satUnaryN_eq]
  simp only [← List.replicate_add]
  have h2 : (input.length + 1) + (input.length + 1) = 2 * (input.length + 1) := by omega
  have h3 : 2 * (input.length + 1) + (input.length + 1) = 3 * (input.length + 1) := by omega
  have h4 : 3 * (input.length + 1) + (input.length + 1) = 4 * (input.length + 1) := by omega
  simp only [h2, h3, h4, notLenLeFlag_unary, List.length_replicate, List.drop_replicate,
    caseBit_unary, eqFlag_unary]
  rw [incidenceVerdictWord_eq]
  simp only [eqFlag_as_bool, List.cons.injEq, and_true, andFlag_bool, notFlag_bool, satSyntaxWord_eq]
  simp only [caseBit₀, Bool.cond_decide]
  simp only [← decide_not, ← Bool.decide_and, Bool.cond_eq_ite, encodeEntry_ite, decide_eq_true_eq]

/-- Every in-range cell emitted by the certified machine is exactly the canonical
literal/clause game's integer payoff encoding. -/
theorem satPayoffCell_eq (input : List Bool) (i j : ℕ)
    (hi : i < 4 * (input.length + 1) + 1) (hj : j < 4 * (input.length + 1) + 1) :
    satPayoffCell satSyntaxWord ![List.replicate i true, List.replicate j true, input] =
      encodeEntry (4 * (input.length + 1) + 1) (satTablePayoff input i j) := by
  rw [satPayoffCell_unary]
  unfold satTablePayoff
  rw [payoffInt_actionAt (satIncidence input) i j (by omega) (by omega)]
  congr 1
  have h4 : 3 * (input.length + 1) + (input.length + 1) = 4 * (input.length + 1) := by omega
  simp only [indexedPayoff, h4]
  by_cases hf : i = 4 * (input.length + 1)
  · simp [hf]
  by_cases hl : i < 2 * (input.length + 1)
  · simp [hf, hl]
  by_cases hv : i < 3 * (input.length + 1)
  · simp [hf, hl, hv]
  by_cases hc : i < 4 * (input.length + 1)
  · by_cases hjl : j < 2 * (input.length + 1)
    · have hci : i - 3 * (input.length + 1) < input.length + 1 := by omega
      have hvi : (if j < input.length + 1 then j else j - (input.length + 1)) < input.length + 1 := by
        split_ifs <;> omega
      have hword := incidence_word input ⟨i - 3 * (input.length + 1), hci⟩
        ⟨if j < input.length + 1 then j else j - (input.length + 1), hvi⟩
        (decide (j < input.length + 1))
      rw [satSyntaxWord_eq, andFlag_bool] at hword
      have hbool := (List.cons.inj hword).1
      simp only [clauseAt, dite_eq_left hci, dite_eq_left hvi]
      simp only [hf, hl, hv, hc, hjl, ↓reduceIte]
      exact congrArg (fun b : Bool => if b then (2 - (input.length + 1 : ℕ) : ℤ) else 2) hbool
    · simp [hf, hl, hv, hc, hjl]
  · simp [hf, hl, hv, hc]

/-- The actual polynomial-time emitted string is the complete canonical table
serialization used by the SAT many-one reduction. -/
theorem satTableEncode_eq (input : List Bool) : satTableEncode input = satTableReduction input := by
  unfold satTableEncode satTableReduction encodeTable
  rw [satUnaryQ_eq, satTableDimension_eq, payoffTable_replicate]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  congr 2
  apply List.flatMap_congr
  intro i hi
  apply List.flatMap_congr
  intro j hj
  exact satPayoffCell_eq input i j (List.mem_range.mp hi) (List.mem_range.mp hj)

end GameTheory.Complexity.Backend
