import GameTheoryComplexity.Backend.BimatrixProgramPayoffs
import GameTheoryComplexity.Backend.GeneralBimatrixPayoffEmission

/-! A polynomial-time writer of the integer game for a packed mixed-gate program.
The emitted rectangular codec uses exact fixed-width positive and negative magnitudes. -/
namespace GameTheory.Complexity.Backend.BimatrixProgramMachine
open _root_.Complexity _root_.Complexity.Cobham

/-- Explicit action-count clock: two actions for each output block. -/
def actions (tape : List Bool) : List Bool :=
  BimatrixProgramCodec.dimension tape ++ BimatrixProgramCodec.dimension tape

/-- A magnitude width sufficient for every payoff, even on malformed program tapes. -/
def payoffWidth (tape : List Bool) : List Bool :=
  BimatrixProgramCodec.baselineWord tape ++ BimatrixProgramCodec.width tape ++
    BimatrixProgramCodec.dimension tape ++ [false, false, false, false, false,
      false, false, false, false, false]

private def entry (columnPlayer : Bool) (v : Fin 3 → List Bool) : List Bool :=
  if columnPlayer then BimatrixProgramPayoffs.columnEntry v else BimatrixProgramPayoffs.rowEntry v

private def cell (columnPlayer : Bool) (v : Fin 3 → List Bool) : List Bool :=
  let word := entry columnPlayer ![v 1, v 0, v 2]
  generalSignedMagnitude true (payoffWidth (v 2)) word ++
    generalSignedMagnitude false (payoffWidth (v 2)) word

private def row (columnPlayer : Bool) (v : Fin 2 → List Bool) : List Bool :=
  binarySignedTable (cell columnPlayer) (actions (v 1))
    (payoffWidth (v 1) ++ payoffWidth (v 1)) v

/-- Materialize one payoff matrix with two magnitude fields per cell. -/
def matrix (columnPlayer : Bool) (tape : List Bool) : List Bool :=
  binarySignedTable (row columnPlayer) (actions tape)
    (smash (actions tape) (payoffWidth tape ++ payoffWidth tape)) ![tape]

/-- Write a canonical rectangular game input for the decoded program. -/
def instanceWord (tape : List Bool) : List Bool :=
  generalInstanceWord (actions tape).length (actions tape).length (payoffWidth tape).length
    (matrix false tape ++ matrix true tape)

theorem actions_length (tape : List Bool) :
    (actions tape).length = (BimatrixProgramCodec.dimension tape).length * 2 := by
  simp [actions, Nat.mul_two]

theorem payoffWidth_length (tape : List Bool) :
    (payoffWidth tape).length = (BimatrixProgramCodec.baselineWord tape).length +
      (BimatrixProgramCodec.width tape).length +
      (BimatrixProgramCodec.dimension tape).length + 10 := by
  simp [payoffWidth, Nat.add_assoc]

private theorem cell_length (columnPlayer : Bool) (v : Fin 3 → List Bool) :
    (cell columnPlayer v).length = 2 * (payoffWidth (v 2)).length := by
  simp [cell, Nat.two_mul]

private theorem row_length (columnPlayer : Bool) (v : Fin 2 → List Bool) :
    (row columnPlayer v).length = (actions (v 1)).length *
      (2 * (payoffWidth (v 1)).length) := by
  simp [row, Nat.two_mul]

/-- Exact matrix buffer size. -/
theorem matrix_length (columnPlayer : Bool) (tape : List Bool) :
    (matrix columnPlayer tape).length =
      (actions tape).length * ((actions tape).length * (2 * (payoffWidth tape).length)) := by
  simp [matrix, smash_length, Nat.two_mul]

private theorem actions_cobham : Cobham fun v : Fin 1 → List Bool => actions (v 0) :=
  appendFn BimatrixProgramCodec.dimension_cobham BimatrixProgramCodec.dimension_cobham

private theorem payoffWidth_cobham : Cobham fun v : Fin 1 → List Bool => payoffWidth (v 0) :=
  appendFn (appendFn (appendFn BimatrixProgramCodec.baselineWord_cobham
    BimatrixProgramCodec.width_cobham) BimatrixProgramCodec.dimension_cobham)
    (Cobham.const [false, false, false, false, false, false, false, false, false, false])

private theorem entry_cobham (columnPlayer : Bool) : Cobham (entry columnPlayer) := by
  cases columnPlayer
  · exact BimatrixProgramPayoffs.rowEntry_cobham
  · exact BimatrixProgramPayoffs.columnEntry_cobham

private theorem cell_cobham (columnPlayer : Bool) : Cobham (cell columnPlayer) := by
  have he : Cobham fun v : Fin 3 → List Bool => entry columnPlayer ![v 1, v 0, v 2] :=
    Cobham.comp₃ (entry_cobham columnPlayer) (.proj 1) (.proj 0) (.proj 2)
  have hw : Cobham fun v : Fin 3 → List Bool => payoffWidth (v 2) :=
    Cobham.comp payoffWidth_cobham fun _ : Fin 1 => .proj 2
  exact appendFn (Cobham.comp₂ (generalSignedMagnitude_cobham true) hw he)
    (Cobham.comp₂ (generalSignedMagnitude_cobham false) hw he)

private theorem row_cobham (columnPlayer : Bool) : Cobham (row columnPlayer) := by
  have ha : Cobham fun v : Fin 2 → List Bool => actions (v 1) :=
    Cobham.comp actions_cobham fun _ : Fin 1 => .proj 1
  have hw : Cobham fun v : Fin 2 → List Bool => payoffWidth (v 1) :=
    Cobham.comp payoffWidth_cobham fun _ : Fin 1 => .proj 1
  let args : Fin 4 → (Fin 2 → List Bool) → List Bool :=
    ![fun v => actions (v 1), fun v => payoffWidth (v 1) ++ payoffWidth (v 1),
      fun v => v 0, fun v => v 1]
  have hargs : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i
    · exact ha
    · exact appendFn hw hw
    all_goals exact .proj _
  exact (Cobham.comp (binarySignedTable_cobham (cell_cobham columnPlayer)) hargs).of_eq
    fun v => by
      congr 1
      ext i
      fin_cases i <;> rfl

/-- Each complete payoff matrix has an actual polynomial-time string machine. -/
theorem matrix_cobham (columnPlayer : Bool) :
    Cobham fun v : Fin 1 → List Bool => matrix columnPlayer (v 0) := by
  let args : Fin 3 → (Fin 1 → List Bool) → List Bool :=
    ![fun v => actions (v 0),
      fun v => smash (actions (v 0)) (payoffWidth (v 0) ++ payoffWidth (v 0)), fun v => v 0]
  have hargs : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i
    · exact actions_cobham
    · exact Cobham.comp₂ Cobham.smash actions_cobham
        (appendFn payoffWidth_cobham payoffWidth_cobham)
    · exact .proj 0
  exact (Cobham.comp (binarySignedTable_cobham (row_cobham columnPlayer)) hargs).of_eq
    fun v => by
      congr 1
      ext i
      fin_cases i
      rfl

/-- The full game writer is polynomial time on every tape. -/
theorem instanceWord_mem_FP : instanceWord ∈ FP := by
  have ha : Cobham fun v : Fin 1 → List Bool => List.replicate (actions (v 0)).length true :=
    (Cobham.comp₂ Cobham.smash (Cobham.const [true]) actions_cobham).of_eq fun v => by
      simp [_root_.Complexity.smash]
  have hw : Cobham fun v : Fin 1 → List Bool => List.replicate (payoffWidth (v 0)).length true :=
    (Cobham.comp₂ Cobham.smash (Cobham.const [true]) payoffWidth_cobham).of_eq fun v => by
      simp [_root_.Complexity.smash]
  exact CobhamFP_subset_FP ((appendFn (appendFn (appendFn (appendFn (appendFn
    (appendFn ha (Cobham.const [false])) ha) (Cobham.const [false])) hw)
    (Cobham.const [false])) (appendFn (matrix_cobham false) (matrix_cobham true))).of_eq
      fun v => by simp only [instanceWord, generalInstanceWord, List.append_assoc])

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

private theorem entry_fit (columnPlayer : Bool) (v : Fin 3 → List Bool) :
    (binarySignedValue (entry columnPlayer v)).natAbs < 2 ^ (payoffWidth (v 2)).length := by
  have hl : (entry columnPlayer v).length ≤ (payoffWidth (v 2)).length := by
    rw [payoffWidth_length]
    cases columnPlayer
    · exact (BimatrixProgramPayoffs.rowEntry_length v).trans (by omega)
    · exact (BimatrixProgramPayoffs.columnEntry_length v).trans (by omega)
  rw [binarySignedValue_natAbs]
  exact (Nat.fromBitsLE_lt_pow_length _).trans_le
    (Nat.pow_le_pow_right (by omega) (by simpa only [List.length_tail] using
      (Nat.sub_le (entry columnPlayer v).length 1).trans hl))

private theorem matrix_row (columnPlayer : Bool) (tape : List Bool) (i : ℕ)
    (hi : i < (actions tape).length) :
    ((matrix columnPlayer tape).drop (i * ((actions tape).length *
      (2 * (payoffWidth tape).length)))).take
      ((actions tape).length * (2 * (payoffWidth tape).length)) =
      row columnPlayer ![(actions tape).drop ((actions tape).length - i), tape] := by
  have h := binarySignedTable_field (row columnPlayer) (actions tape)
    (smash (actions tape) (payoffWidth tape ++ payoffWidth tape)) ![tape] i hi
  simp only [smash_length, List.length_append] at h
  have hp : Fin.cons ((actions tape).drop ((actions tape).length - i)) ![tape] =
      ![(actions tape).drop ((actions tape).length - i), tape] := by
    ext a
    fin_cases a <;> rfl
  rw [hp] at h
  rw [binarySignedFixed_eq_of_length] at h
  · simpa only [matrix, Nat.two_mul] using h
  · rw [row_length]
    change (actions tape).length * (2 * (payoffWidth tape).length) = _
    simp only [smash_length, List.length_append, Nat.two_mul]

private theorem row_cell (columnPlayer : Bool) (v : Fin 2 → List Bool) (j : ℕ)
    (hj : j < (actions (v 1)).length) :
    ((row columnPlayer v).drop (j * (2 * (payoffWidth (v 1)).length))).take
      (2 * (payoffWidth (v 1)).length) =
      cell columnPlayer ![(actions (v 1)).drop ((actions (v 1)).length - j), v 0, v 1] := by
  have h := binarySignedTable_field (cell columnPlayer) (actions (v 1))
    (payoffWidth (v 1) ++ payoffWidth (v 1)) v j hj
  have hp : Fin.cons ((actions (v 1)).drop ((actions (v 1)).length - j)) v =
      ![(actions (v 1)).drop ((actions (v 1)).length - j), v 0, v 1] := by
    ext a
    fin_cases a <;> rfl
  rw [hp, binarySignedFixed_eq_of_length] at h
  · simpa only [row, List.length_append, Nat.two_mul] using h
  · rw [cell_length]
    change 2 * (payoffWidth (v 1)).length = _
    simp only [List.length_append, Nat.two_mul]

/-- Exact byte extraction of a materialized pair of magnitude fields. -/
private theorem matrix_cell (columnPlayer : Bool) (tape : List Bool) (i j : ℕ)
    (hi : i < (actions tape).length) (hj : j < (actions tape).length) :
    ((matrix columnPlayer tape).drop
      ((i * (actions tape).length + j) * (2 * (payoffWidth tape).length))).take
      (2 * (payoffWidth tape).length) =
      generalSignedMagnitude true (payoffWidth tape) (entry columnPlayer
        ![(actions tape).drop ((actions tape).length - i),
          (actions tape).drop ((actions tape).length - j), tape]) ++
      generalSignedMagnitude false (payoffWidth tape) (entry columnPlayer
        ![(actions tape).drop ((actions tape).length - i),
          (actions tape).drop ((actions tape).length - j), tape]) := by
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
  exact h.trans (row_cell columnPlayer
    ![(actions tape).drop ((actions tape).length - i), tape] j hj)

private theorem matrix_magnitude (columnPlayer positive : Bool) (tape : List Bool) (i j : ℕ)
    (hi : i < (actions tape).length) (hj : j < (actions tape).length) :
    ((matrix columnPlayer tape).drop
      ((2 * (i * (actions tape).length + j) + (if positive then 0 else 1)) *
        (payoffWidth tape).length)).take (payoffWidth tape).length =
      generalSignedMagnitude positive (payoffWidth tape) (entry columnPlayer
        ![(actions tape).drop ((actions tape).length - i),
          (actions tape).drop ((actions tape).length - j), tape]) := by
  let word := entry columnPlayer ![(actions tape).drop ((actions tape).length - i),
    (actions tape).drop ((actions tape).length - j), tape]
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

/-- The rectangular codec extracts the exact emitted magnitude field. -/
private theorem instanceWord_field (columnPlayer positive : Bool) (tape : List Bool) (i j : ℕ)
    (hi : i < (actions tape).length) (hj : j < (actions tape).length) :
    generalPayoffField columnPlayer positive (instanceWord tape) i j =
      generalSignedMagnitude positive (payoffWidth tape) (entry columnPlayer
        ![(actions tape).drop ((actions tape).length - i),
          (actions tape).drop ((actions tape).length - j), tape]) := by
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

/-- Decoding the written game gives the exact integer entry, with no overflow premises. -/
private theorem instanceWord_payoff (columnPlayer : Bool) (tape : List Bool) (i j : ℕ)
    (hi : i < (actions tape).length) (hj : j < (actions tape).length) :
    decodeGeneralPayoff columnPlayer (instanceWord tape) i j =
      binarySignedValue (entry columnPlayer ![(actions tape).drop ((actions tape).length - i),
        (actions tape).drop ((actions tape).length - j), tape]) := by
  rw [decodeGeneralPayoff, instanceWord_field columnPlayer true tape i j hi hj,
    instanceWord_field columnPlayer false tape i j hi hj]
  exact generalSignedMagnitude_value _ _ (entry_fit _ _)

/-- The written row payoff is exactly the canonical affine game on decoded actions. -/
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

/-- The written column payoff is exactly the canonical decoded mixed-gate program game. -/
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

end GameTheory.Complexity.Backend.BimatrixProgramMachine
