module

public import GameTheoryComplexity.Backend.BimatrixProgramPayoffs
public import GameTheoryComplexity.Backend.GeneralBimatrixPayoffEmission

@[expose] public section

/-! The integer game writer materializes the canonical mixed-gate payoffs in
row-major order. Every cell contains fixed-width positive and negative magnitude
fields. Action rulers retain the source dimension bits, and all malformed
program tapes use the codec's total interpretation. -/

namespace GameTheory.Complexity.Backend.BimatrixProgramMachine

open Cslib.BitString Turing.MultiTapeTM

/-- Two action positions are allocated for every decoded output block. -/
def actions (tape : List Bool) : List Bool :=
  BimatrixProgramCodec.dimension tape ++ BimatrixProgramCodec.dimension tape

/-- A magnitude width sufficient for every payoff, including malformed tapes. -/
def payoffWidth (tape : List Bool) : List Bool :=
  BimatrixProgramCodec.baselineWord tape ++ BimatrixProgramCodec.width tape ++
    BimatrixProgramCodec.dimension tape ++ [false, false, false, false, false,
      false, false, false, false, false]

private def entry (columnPlayer : Bool) (r s tape : List Bool) : List Bool :=
  if columnPlayer then BimatrixProgramPayoffs.columnEntry r s tape
  else BimatrixProgramPayoffs.rowEntry r s tape

private def cell (columnPlayer : Bool) (tape r s : List Bool) : List Bool :=
  let word := entry columnPlayer r s tape
  generalSignedMagnitude true (payoffWidth tape) word ++
    generalSignedMagnitude false (payoffWidth tape) word

private def row (columnPlayer : Bool) (tape r : List Bool) : List Bool :=
  (List.range (actions tape).length).flatMap fun j =>
    cell columnPlayer tape r ((actions tape).drop ((actions tape).length - j))

/-- Materialize one payoff matrix with two magnitude fields for every cell. -/
def matrix (columnPlayer : Bool) (tape : List Bool) : List Bool :=
  let ruler := actions tape
  let width := payoffWidth tape
  (List.range ruler.length).flatMap fun i =>
    (List.range ruler.length).flatMap fun j =>
      let r := ruler.drop (ruler.length - i)
      let s := ruler.drop (ruler.length - j)
      let word := if columnPlayer then BimatrixProgramPayoffs.columnEntry r s tape
        else BimatrixProgramPayoffs.rowEntry r s tape
      generalSignedMagnitude true width word ++ generalSignedMagnitude false width word

/-- Write the canonical rectangular game input for the decoded program. -/
def instanceWord (tape : List Bool) : List Bool :=
  generalInstanceWord (actions tape).length (actions tape).length (payoffWidth tape).length
    (matrix false tape ++ matrix true tape)

/-- The action count is exactly twice the decoded block count. -/
theorem actions_length (tape : List Bool) :
    (actions tape).length = (BimatrixProgramCodec.dimension tape).length * 2 := by
  simp [actions, Nat.mul_two]

/-- The magnitude width includes all decoded size headers and a fixed safety margin. -/
theorem payoffWidth_length (tape : List Bool) :
    (payoffWidth tape).length = (BimatrixProgramCodec.baselineWord tape).length +
      (BimatrixProgramCodec.width tape).length +
      (BimatrixProgramCodec.dimension tape).length + 10 := by
  simp [payoffWidth, Nat.add_assoc]

private theorem cell_length (columnPlayer : Bool) (tape r s : List Bool) :
    (cell columnPlayer tape r s).length = 2 * (payoffWidth tape).length := by
  simp [cell, Nat.two_mul]

private theorem row_length (columnPlayer : Bool) (tape r : List Bool) :
    (row columnPlayer tape r).length =
      (actions tape).length * (2 * (payoffWidth tape).length) := by
  have h := GameTheory.Math.FixedBlockList.length_flatMap_fixed
    (List.range (actions tape).length)
    (fun j => cell columnPlayer tape r ((actions tape).drop ((actions tape).length - j)))
    (2 * (payoffWidth tape).length) (fun _ _ => cell_length _ _ _ _)
  rw [List.length_range] at h
  exact h

/-- Every matrix contains the complete row-major buffer of fixed-width cells. -/
theorem matrix_length (columnPlayer : Bool) (tape : List Bool) :
    (matrix columnPlayer tape).length =
      (actions tape).length * ((actions tape).length * (2 * (payoffWidth tape).length)) := by
  change ((List.range (actions tape).length).flatMap
    (fun i => row columnPlayer tape ((actions tape).drop ((actions tape).length - i)))).length = _
  have h := GameTheory.Math.FixedBlockList.length_flatMap_fixed
    (List.range (actions tape).length)
    (fun i => row columnPlayer tape ((actions tape).drop ((actions tape).length - i)))
    ((actions tape).length * (2 * (payoffWidth tape).length))
    (fun _ _ => row_length _ _ _)
  simpa only [List.length_range] using h

private theorem entry_fit (columnPlayer : Bool) (r s tape : List Bool) :
    (binarySignedValue (entry columnPlayer r s tape)).natAbs <
      2 ^ (payoffWidth tape).length := by
  have hl : (entry columnPlayer r s tape).length ≤ (payoffWidth tape).length := by
    rw [payoffWidth_length]
    cases columnPlayer
    · exact (BimatrixProgramPayoffs.rowEntry_length r s tape).trans (by omega)
    · exact (BimatrixProgramPayoffs.columnEntry_length r s tape).trans (by omega)
  rw [binarySignedValue_natAbs]
  have h : ofBits (entry columnPlayer r s tape).tail <
      2 ^ (entry columnPlayer r s tape).tail.length := Nat.foldr_bit_lt _
  exact h.trans_le (Nat.pow_le_pow_right (by decide) (by
    simp only [List.length_tail]
    omega))

/-- Positive program dimension always produces a well-formed game instance. -/
theorem instanceWord_valid (tape : List Bool)
    (hk : 0 < (BimatrixProgramCodec.dimension tape).length) :
    GeneralInstanceValid (instanceWord tape) := by
  have hw : 0 < (payoffWidth tape).length := by rw [payoffWidth_length]; omega
  have ha : 0 < (actions tape).length := by rw [actions_length]; omega
  simp only [GeneralInstanceValid, instanceWord, generalRowCount, generalColCount,
    generalCoefficientBits, generalInstanceWord_row, generalInstanceWord_col,
    generalInstanceWord_bits, List.length_replicate]
  refine ⟨ha, ha, hw, ?_⟩
  simp only [generalInstanceWord, List.length_append, List.length_replicate,
    List.length_singleton, matrix_length]
  ring

private theorem matrix_row (columnPlayer : Bool) (tape : List Bool) (i : ℕ)
    (hi : i < (actions tape).length) :
    ((matrix columnPlayer tape).drop (i * ((actions tape).length *
      (2 * (payoffWidth tape).length)))).take
      ((actions tape).length * (2 * (payoffWidth tape).length)) =
      row columnPlayer tape ((actions tape).drop ((actions tape).length - i)) := by
  change (((List.range (actions tape).length).flatMap
    (fun i => row columnPlayer tape ((actions tape).drop ((actions tape).length - i)))).drop
    (i * ((actions tape).length * (2 * (payoffWidth tape).length)))).take _ = _
  have h := GameTheory.Math.FixedBlockList.block_flatMap_fixed
    (List.range (actions tape).length)
    (fun i => row columnPlayer tape ((actions tape).drop ((actions tape).length - i)))
    ((actions tape).length * (2 * (payoffWidth tape).length)) (fun _ _ => row_length _ _ _)
    i (by simpa only [List.length_range] using hi)
  simpa only [List.getElem_range] using h

private theorem row_cell (columnPlayer : Bool) (tape r : List Bool) (j : ℕ)
    (hj : j < (actions tape).length) :
    ((row columnPlayer tape r).drop (j * (2 * (payoffWidth tape).length))).take
      (2 * (payoffWidth tape).length) =
      cell columnPlayer tape r ((actions tape).drop ((actions tape).length - j)) := by
  have h := GameTheory.Math.FixedBlockList.block_flatMap_fixed
    (List.range (actions tape).length)
    (fun j => cell columnPlayer tape r ((actions tape).drop ((actions tape).length - j)))
    (2 * (payoffWidth tape).length) (fun _ _ => cell_length _ _ _ _)
    j (by simpa only [List.length_range] using hj)
  simpa only [row, List.getElem_range] using h

private theorem matrix_cell (columnPlayer : Bool) (tape : List Bool) (i j : ℕ)
    (hi : i < (actions tape).length) (hj : j < (actions tape).length) :
    ((matrix columnPlayer tape).drop
      ((i * (actions tape).length + j) * (2 * (payoffWidth tape).length))).take
      (2 * (payoffWidth tape).length) =
      generalSignedMagnitude true (payoffWidth tape) (entry columnPlayer
        ((actions tape).drop ((actions tape).length - i))
        ((actions tape).drop ((actions tape).length - j)) tape) ++
      generalSignedMagnitude false (payoffWidth tape) (entry columnPlayer
        ((actions tape).drop ((actions tape).length - i))
        ((actions tape).drop ((actions tape).length - j)) tape) := by
  have h := congrArg (fun x : List Bool =>
    (x.drop (j * (2 * (payoffWidth tape).length))).take (2 * (payoffWidth tape).length))
    (matrix_row columnPlayer tape i hi)
  rw [List.drop_take, List.drop_drop, List.take_take] at h
  have hm : 2 * (payoffWidth tape).length ≤
      (actions tape).length * (2 * (payoffWidth tape).length) -
        j * (2 * (payoffWidth tape).length) := by
    have hb := Nat.mul_le_mul_right (2 * (payoffWidth tape).length) (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at hb
    omega
  rw [Nat.min_eq_left hm, ← Nat.mul_assoc, ← Nat.add_mul] at h
  exact h.trans (row_cell columnPlayer tape
    ((actions tape).drop ((actions tape).length - i)) j hj)

private theorem matrix_magnitude (columnPlayer positive : Bool) (tape : List Bool) (i j : ℕ)
    (hi : i < (actions tape).length) (hj : j < (actions tape).length) :
    ((matrix columnPlayer tape).drop
      ((2 * (i * (actions tape).length + j) + (if positive then 0 else 1)) *
        (payoffWidth tape).length)).take (payoffWidth tape).length =
      generalSignedMagnitude positive (payoffWidth tape) (entry columnPlayer ((actions tape).drop ((actions tape).length - i))
        ((actions tape).drop ((actions tape).length - j)) tape) := by
  let word := entry columnPlayer ((actions tape).drop ((actions tape).length - i))
        ((actions tape).drop ((actions tape).length - j)) tape
  have h := congrArg (fun x : List Bool =>
    (x.drop (if positive then 0 else (payoffWidth tape).length)).take (payoffWidth tape).length)
    (matrix_cell columnPlayer tape i j hi hj)
  rw [List.drop_take, List.drop_drop, List.take_take] at h
  cases positive
  · have hm : (payoffWidth tape).length ≤
        2 * (payoffWidth tape).length - (payoffWidth tape).length := by omega
    simp only [Bool.false_eq_true, ite_false, Nat.min_eq_left hm] at h
    have he : (i * (actions tape).length + j) * (2 * (payoffWidth tape).length) +
        (payoffWidth tape).length =
        (2 * (i * (actions tape).length + j) + 1) * (payoffWidth tape).length := by ring
    rw [he] at h
    have hd : (generalSignedMagnitude true (payoffWidth tape) word ++
        generalSignedMagnitude false (payoffWidth tape) word).drop (payoffWidth tape).length =
        generalSignedMagnitude false (payoffWidth tape) word := by
      simpa only [generalSignedMagnitude_length, Nat.add_zero, List.drop_zero] using
        (List.drop_length_add_append (l₁ := generalSignedMagnitude true (payoffWidth tape) word)
          (l₂ := generalSignedMagnitude false (payoffWidth tape) word) 0)
    have ht : (generalSignedMagnitude false (payoffWidth tape) word).take
        (payoffWidth tape).length = generalSignedMagnitude false (payoffWidth tape) word := by
      simpa only [generalSignedMagnitude_length] using
        (List.take_length (l := generalSignedMagnitude false (payoffWidth tape) word))
    rw [hd, ht] at h
    simpa only [Bool.false_eq_true, ite_false] using h

  · have hm : (payoffWidth tape).length ≤ 2 * (payoffWidth tape).length := by omega
    simp only [ite_true, Nat.sub_zero, Nat.add_zero, Nat.min_eq_left hm] at h
    have he : (i * (actions tape).length + j) * (2 * (payoffWidth tape).length) =
        (2 * (i * (actions tape).length + j)) * (payoffWidth tape).length := by ring
    rw [he] at h
    have ht : (generalSignedMagnitude true (payoffWidth tape) word ++
        generalSignedMagnitude false (payoffWidth tape) word).take (payoffWidth tape).length =
        generalSignedMagnitude true (payoffWidth tape) word := by
      simpa only [generalSignedMagnitude_length] using (List.take_append_length
        (l₁ := generalSignedMagnitude true (payoffWidth tape) word)
        (l₂ := generalSignedMagnitude false (payoffWidth tape) word))
    rw [List.drop_zero, ht] at h
    simpa only [ite_true, Nat.add_zero] using h

private theorem cellIndex_lt (n i j : ℕ) (hi : i < n) (hj : j < n) : i * n + j < n * n := by
  calc
    i * n + j < i * n + n := Nat.add_lt_add_left hj _
    _ = (i + 1) * n := (Nat.succ_mul i n).symm
    _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)

private theorem instanceWord_field (columnPlayer positive : Bool) (tape : List Bool) (i j : ℕ)
    (hi : i < (actions tape).length) (hj : j < (actions tape).length) :
    generalPayoffField columnPlayer positive (instanceWord tape) i j =
      generalSignedMagnitude positive (payoffWidth tape) (entry columnPlayer ((actions tape).drop ((actions tape).length - i))
        ((actions tape).drop ((actions tape).length - j)) tape) := by
  have hw : 0 < (payoffWidth tape).length := by rw [payoffWidth_length]; omega
  have hp := cellIndex_lt (actions tape).length i j hi hj
  simp only [generalPayoffField, generalBinaryField, instanceWord, generalCoefficientBits,
    generalRowCount, generalColCount, generalInstanceWord_row, generalInstanceWord_col,
    generalInstanceWord_bits, generalInstanceWord_payload, List.length_replicate]
  cases columnPlayer
  · have hl : (payoffWidth tape).length ≤ (matrix false tape).length -
        ((2 * (i * (actions tape).length + j) + (if positive then 0 else 1)) *
          (payoffWidth tape).length) := by
      have ha : 2 * (i * (actions tape).length + j) + (if positive then 0 else 1) + 1 ≤
          2 * ((actions tape).length * (actions tape).length) := by
        cases positive <;> simp <;> omega
      have hb := Nat.mul_le_mul_right (payoffWidth tape).length ha
      have hb' : ((2 * (i * (actions tape).length + j) + (if positive then 0 else 1)) *
          (payoffWidth tape).length) + (payoffWidth tape).length ≤ (matrix false tape).length := by
        rw [matrix_length]
        convert hb using 1 <;> ring
      omega
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
    rw [List.drop_append_of_le_length (by omega)]
    rw [List.take_append_of_le_length (by simpa only [List.length_drop] using hl)]
    exact matrix_magnitude false positive tape i j hi hj
  · have he :
        (2 * ((actions tape).length * (actions tape).length + i * (actions tape).length + j) +
          (if positive then 0 else 1)) * (payoffWidth tape).length =
        (matrix false tape).length +
          (2 * (i * (actions tape).length + j) + (if positive then 0 else 1)) *
            (payoffWidth tape).length := by rw [matrix_length]; ring
    simp only [ite_true]
    rw [he, List.drop_length_add_append]
    exact matrix_magnitude true positive tape i j hi hj

private theorem instanceWord_payoff (columnPlayer : Bool) (tape : List Bool) (i j : ℕ)
    (hi : i < (actions tape).length) (hj : j < (actions tape).length) :
    decodeGeneralPayoff columnPlayer (instanceWord tape) i j =
      binarySignedValue (entry columnPlayer ((actions tape).drop ((actions tape).length - i))
        ((actions tape).drop ((actions tape).length - j)) tape) := by
  rw [decodeGeneralPayoff, instanceWord_field columnPlayer true tape i j hi hj,
    instanceWord_field columnPlayer false tape i j hi hj]
  exact generalSignedMagnitude_value _ _ (entry_fit _ _ _ _)

/-- The emitted row payoff is the canonical affine payoff on bounded actions. -/
theorem instanceWord_rowPayoff (tape : List Bool)
    (ri si : Fin ((BimatrixProgramCodec.dimension tape).length * 2)) :
    decodeGeneralPayoff false (instanceWord tape) ri.val si.val =
      GameTheory.Finite.BimatrixAffineGate.rowPayoff (BimatrixProgramCodec.baseline tape)
        (2 * (BimatrixProgramCodec.dimension tape).length) ri si := by
  have hi : ri.val < (actions tape).length := by simpa only [actions_length] using ri.isLt
  have hj : si.val < (actions tape).length := by simpa only [actions_length] using si.isLt
  rw [instanceWord_payoff false tape ri.val si.val hi hj]
  apply BimatrixProgramPayoffs.rowEntry_eq_rowPayoff
  all_goals simp only [List.length_drop]; omega

/-- The emitted column payoff is the canonical decoded mixed-gate payoff. -/
theorem instanceWord_columnPayoff (tape : List Bool)
    (ri si : Fin ((BimatrixProgramCodec.dimension tape).length * 2)) :
    decodeGeneralPayoff true (instanceWord tape) ri.val si.val =
      GameTheory.Finite.BimatrixGateProgram.columnPayoff (BimatrixProgramCodec.baseline tape)
        (2 * (BimatrixProgramCodec.dimension tape).length) (BimatrixProgramCodec.decode tape)
        ri si := by
  have hi : ri.val < (actions tape).length := by simpa only [actions_length] using ri.isLt
  have hj : si.val < (actions tape).length := by simpa only [actions_length] using si.isLt
  rw [instanceWord_payoff true tape ri.val si.val hi hj]
  apply BimatrixProgramPayoffs.columnEntry_eq_columnPayoff
  all_goals simp only [List.length_drop]; omega

/-- The action ruler is computed under the tape producer's actual input encoding. -/
@[fun_prop] theorem actions_polyTime {Input : Type} {input : Input ↪ List Bool}
    {tape : Input → List Bool} (ht : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => actions (tape a)) input encBits :=
  ComputableInPolyTime.bitsAppend (BimatrixProgramCodec.dimension_polyTime ht)
    (BimatrixProgramCodec.dimension_polyTime ht)

/-- The complete magnitude ruler is polynomial in the encoded tape producer. -/
@[fun_prop] theorem payoffWidth_polyTime {Input : Type} {input : Input ↪ List Bool}
    {tape : Input → List Bool} (ht : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => payoffWidth (tape a)) input encBits :=
  ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend (BimatrixProgramCodec.baselineWord_polyTime ht)
        (BimatrixProgramCodec.width_polyTime ht)) (BimatrixProgramCodec.dimension_polyTime ht))
    (ComputableInPolyTime.const [false, false, false, false, false,
      false, false, false, false, false])

private theorem entry_polyTime (columnPlayer : Bool)
    {Input : Type} {input : Input ↪ List Bool} {r s tape : Input → List Bool}
    (hr : ComputableInPolyTime r input encBits) (hs : ComputableInPolyTime s input encBits)
    (ht : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => entry columnPlayer (r a) (s a) (tape a)) input encBits := by
  cases columnPlayer
  · exact BimatrixProgramPayoffs.rowEntry_polyTime hr hs ht
  · exact BimatrixProgramPayoffs.columnEntry_polyTime hr hs ht

private theorem cell_polyTime (columnPlayer : Bool)
    {Input : Type} {input : Input ↪ List Bool} {tape r s : Input → List Bool}
    (ht : ComputableInPolyTime tape input encBits)
    (hr : ComputableInPolyTime r input encBits) (hs : ComputableInPolyTime s input encBits) :
    ComputableInPolyTime (fun a => cell columnPlayer (tape a) (r a) (s a)) input encBits := by
  have he := entry_polyTime columnPlayer hr hs ht
  have hw := payoffWidth_polyTime ht
  exact ComputableInPolyTime.bitsAppend (generalSignedMagnitude_polyTime true hw he)
    (generalSignedMagnitude_polyTime false hw he)

private theorem row_polyTime (columnPlayer : Bool)
    {Input : Type} {input : Input ↪ List Bool} {tape r : Input → List Bool}
    (ht : ComputableInPolyTime tape input encBits) (hr : ComputableInPolyTime r input encBits) :
    ComputableInPolyTime (fun a => row columnPlayer (tape a) (r a)) input encBits := by
  have ha := actions_polyTime ht
  have hi := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.range).comp
    (ComputableInPolyTime.length_bits_comp ha)
  change ComputableInPolyTime (fun a =>
    (List.range (actions (tape a)).length).flatMap fun j =>
      cell columnPlayer (tape a) (r a) ((actions (tape a)).drop ((actions (tape a)).length - j)))
    input encBits
  refine ComputableInPolyTime.flatMapToBitsWithInput
    (f := fun (a : Input) (j : ℕ) =>
      cell columnPlayer (tape a) (r a) ((actions (tape a)).drop ((actions (tape a)).length - j)))
    hi ?_
  have hsource : ComputableInPolyTime (fun p : Input × ℕ => p.1)
      (encPair input encUnary) input := ComputableInPolyTime.fst input encUnary
  have hindex : ComputableInPolyTime (fun p : Input × ℕ => p.2)
      (encPair input encUnary) encUnary := ComputableInPolyTime.snd input encUnary
  have ht' := ht.comp hsource
  have hr' := hr.comp hsource
  have ha' := actions_polyTime ht'
  have hdrop := ComputableInPolyTime.bitsDropWithInput ha'
    (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.length_bits_comp ha') hindex)
  exact cell_polyTime columnPlayer ht' hr' hdrop

/-- Complete row-major matrices charge every captured tape and ordinal context. -/
@[fun_prop] theorem matrix_polyTime (columnPlayer : Bool)
    {Input : Type} {input : Input ↪ List Bool} {tape : Input → List Bool}
    (ht : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => matrix columnPlayer (tape a)) input encBits := by
  have ha := actions_polyTime ht
  have hi := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.range).comp
    (ComputableInPolyTime.length_bits_comp ha)
  change ComputableInPolyTime (fun a =>
    (List.range (actions (tape a)).length).flatMap fun i =>
      row columnPlayer (tape a) ((actions (tape a)).drop ((actions (tape a)).length - i)))
    input encBits
  refine ComputableInPolyTime.flatMapToBitsWithInput
    (f := fun (a : Input) (i : ℕ) =>
      row columnPlayer (tape a) ((actions (tape a)).drop ((actions (tape a)).length - i)))
    hi ?_
  have hsource : ComputableInPolyTime (fun p : Input × ℕ => p.1)
      (encPair input encUnary) input := ComputableInPolyTime.fst input encUnary
  have hindex : ComputableInPolyTime (fun p : Input × ℕ => p.2)
      (encPair input encUnary) encUnary := ComputableInPolyTime.snd input encUnary
  have ht' := ht.comp hsource
  have ha' := actions_polyTime ht'
  have hdrop := ComputableInPolyTime.bitsDropWithInput ha'
    (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.length_bits_comp ha') hindex)
  exact row_polyTime columnPlayer ht' hdrop

/-- The full game writer is polynomial-time on every encoded input producer. -/
@[fun_prop] theorem instanceWord_polyTime
    {Input : Type} {input : Input ↪ List Bool} {tape : Input → List Bool}
    (ht : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => instanceWord (tape a)) input encBits := by
  have ha := (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.length_bits_comp (actions_polyTime ht))
  have hw := (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.length_bits_comp (payoffWidth_polyTime ht))
  have hp := ComputableInPolyTime.bitsAppend (matrix_polyTime false ht) (matrix_polyTime true ht)
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend
        (ComputableInPolyTime.bitsAppend
          (ComputableInPolyTime.bitsAppend
            (ComputableInPolyTime.bitsAppend ha (.const [false])) ha) (.const [false])) hw)
      (.const [false])) hp

end GameTheory.Complexity.Backend.BimatrixProgramMachine
