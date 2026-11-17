module

public import GameTheoryComplexity.Backend.SATTablePayoff
public import GameTheoryComplexity.Backend.SATGame
public import GameTheory.Core.SatisfiabilityGameEncoding
public import GameTheory.Core.SatisfiabilityGamePayoff
public import GameTheory.Finite.BimatrixTable
public import GameTheoryComplexity.Backend.SATReductionSemantic

@[expose] public section

/-! Every cell emitted by the native polynomial-time traversal agrees with the
canonical literal/clause game. The full serialization theorem covers every raw
source word, including words rejected by the CNF decoder.
-/

namespace GameTheory.Complexity.Backend

open GameTheory.SatisfiabilityGame GameTheory.Finite.BimatrixTable

private theorem tally_constant (input : List Bool) (z : ℤ)
    (hp : z.toNat ≤ 4 * (input.length + 1) + 3)
    (hn : (-z).toNat ≤ 4 * (input.length + 1) + 3) :
    satTallyPair (4 * (input.length + 1) + 3) z.toNat (-z).toNat =
      encodeEntry (4 * (input.length + 1) + 1) z := by
  simp only [satTallyPair, Nat.min_eq_left hp, Nat.min_eq_left hn]
  rfl

private theorem tally_two_sub (input : List Bool) :
    satTallyPair (4 * (input.length + 1) + 3) (2 - (input.length + 1)) (input.length + 1 - 2) =
      encodeEntry (4 * (input.length + 1) + 1) (2 - (input.length + 1 : ℕ)) := by
  have hp : (2 - (input.length + 1 : ℕ) : ℤ).toNat = 2 - (input.length + 1) := by omega
  have hn : (-(2 - (input.length + 1 : ℕ) : ℤ)).toNat = (input.length + 1) - 2 := by omega
  rw [← hp, ← hn]
  apply tally_constant <;> omega

private theorem incidence_bool (input : List Bool) (clause var : Fin (input.length + 1))
    (sign : Bool) :
    (SATWords.syntaxValid input && scanIncidence var.val sign clause.val input) =
      satIncidence input clause var sign := by
  cases hd : SATWords.decodeFormula? input with
  | none => simp [SATWords.syntaxValid_eq_decodeFormula, hd, satIncidence]
  | some formula =>
      rw [scanIncidence_eq_satIncidence input formula hd]
      cases satIncidence input clause var sign <;>
        simp [SATWords.syntaxValid_eq_decodeFormula, hd]

private theorem encodeEntry_ite (q : ℕ) (p : Prop) [Decidable p] (x y : ℤ) :
    encodeEntry q (if p then x else y) = if p then encodeEntry q x else encodeEntry q y :=
  apply_ite (encodeEntry q) p x y

private theorem satPayoffCell_scalar (input : List Bool) (i j : ℕ) :
    satPayoffCell SATWords.syntaxValid input i j =
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
             (if SATWords.syntaxValid input &&
               scanIncidence colVar (decide (j < n)) (i - 3 * n) input then 2 - n else 2)
            else -2)
         else -2) := by
  have hz0 := tally_constant input 0 (by omega) (by omega)
  have hz1 := tally_constant input 1 (by omega) (by omega)
  have hz2 := tally_constant input 2 (by omega) (by omega)
  have hzm2 := tally_constant input (-2) (by omega) (by omega)
  norm_num at hz0 hz1 hz2 hzm2
  dsimp only [satPayoffCell]
  rw [hz0, hz1, hz2, hzm2, tally_two_sub]
  simp only [encodeEntry_ite]

/-- Every in-range emitted cell is exactly the canonical game's integer payoff encoding. -/
theorem satPayoffCell_eq (input : List Bool) (i j : ℕ)
    (hi : i < 4 * (input.length + 1) + 1) (hj : j < 4 * (input.length + 1) + 1) :
    satPayoffCell SATWords.syntaxValid input i j =
      encodeEntry (4 * (input.length + 1) + 1) (satTablePayoff input i j) := by
  rw [satPayoffCell_scalar]
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
      have hbool := incidence_bool input ⟨i - 3 * (input.length + 1), hci⟩
        ⟨if j < input.length + 1 then j else j - (input.length + 1), hvi⟩
        (decide (j < input.length + 1))
      simp only [clauseAt, dite_eq_left hci, dite_eq_left hvi]
      simp only [hf, hl, hv, hc, hjl, ↓reduceIte]
      exact congrArg (fun bit : Bool => if bit then (2 - (input.length + 1 : ℕ) : ℤ) else 2) hbool
    · simp [hf, hl, hv, hc, hjl]
  · simp [hf, hl, hv, hc]

/-- The actual native polynomial-time output is the full canonical table serialization. -/
theorem satTableEncode_eq (input : List Bool) : satTableEncode input = satTableReduction input := by
  unfold satTableEncode satTableReduction encodeTable payoffTable payoffRow
  rw [satTableDimension_eq]
  simp only [List.append_assoc, List.singleton_append]
  congr 2
  apply List.flatMap_congr
  intro i hi
  apply List.flatMap_congr
  intro j hj
  exact satPayoffCell_eq input i j (List.mem_range.mp hi) (List.mem_range.mp hj)

end GameTheory.Complexity.Backend
