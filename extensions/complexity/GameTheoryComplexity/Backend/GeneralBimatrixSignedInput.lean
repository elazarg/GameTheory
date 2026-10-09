import GameTheoryComplexity.Backend.GeneralBimatrixVerifier
import GameTheoryComplexity.Backend.BinarySignedAddition

/-! Certified signed words for the decoded rectangular game and its positive shift.
The input codec remains a pair of unsigned magnitude fields; only internal
arithmetic uses sign-header words.
-/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- Decode both magnitude fields into one exact signed arithmetic word. -/
def generalSignedPayoffWord (columnPlayer : Bool) (v : Fin 3 → List Bool) : List Bool :=
  binarySignedSub (false :: generalPayoffWord columnPlayer true v)
    (false :: generalPayoffWord columnPlayer false v)

private theorem payoffWord_field (columnPlayer positive : Bool) (v : Fin 3 → List Bool) :
    generalPayoffWord columnPlayer positive v =
      generalPayoffField columnPlayer positive (v 2) (v 0).length (v 1).length := by
  cases columnPlayer <;> cases positive <;>
    simp [generalPayoffWord, generalPayoffField, generalBinaryField,
      generalRowCount, generalColCount, generalCoefficientBits, smash_length]
  all_goals (congr 2; ring)

theorem generalSignedPayoffWord_value (columnPlayer : Bool) (v : Fin 3 → List Bool) :
    binarySignedValue (generalSignedPayoffWord columnPlayer v) =
      decodeGeneralPayoff columnPlayer (v 2) (v 0).length (v 1).length := by
  rw [generalSignedPayoffWord, binarySignedSub_value, payoffWord_field, payoffWord_field]
  rfl

theorem generalSignedPayoffWord_cobham (columnPlayer : Bool) :
    Cobham (generalSignedPayoffWord columnPlayer) :=
  (Cobham.comp₂ binarySignedSub_cobham
    (Cobham.comp (.bit false) fun _ => generalPayoffWord_cobham columnPlayer true)
    (Cobham.comp (.bit false) fun _ => generalPayoffWord_cobham columnPlayer false)).of_eq fun _ => rfl

theorem generalSignedPayoffWord_mem_FPn (columnPlayer : Bool) :
    FPn (generalSignedPayoffWord columnPlayer) :=
  cobham_iff_FPn.mp (generalSignedPayoffWord_cobham columnPlayer)

/-- The fixed positive payoff shift, represented directly in binary. -/
def generalPositiveShiftWord (input : List Bool) : List Bool :=
  false :: binaryCertificateAdd ![[true], padTo (generalBitsRuler input) [] ++ [true]]

private theorem powerWord_value (ruler : List Bool) :
    Nat.fromBitsLE (padTo ruler [] ++ [true]) = 2 ^ ruler.length := by
  rw [padTo_eq_append _ _ (by simp)]
  simp only [List.length_nil, Nat.sub_zero, List.nil_append]
  induction ruler.length with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, Nat.fromBitsLE_cons, pow_succ]
    simp only [Bool.false_eq_true, ↓reduceIte, zero_add, ih]
    omega

theorem generalPositiveShiftWord_value (input : List Bool) :
    binarySignedValue (generalPositiveShiftWord input) =
      (2 : ℤ) ^ generalCoefficientBits input + 1 := by
  simp only [generalPositiveShiftWord, binarySignedValue, List.headD_cons, List.tail_cons,
    Bool.false_eq_true, ↓reduceIte, binaryCertificateAdd_value, powerWord_value]
  change ((1 + 2 ^ (generalBitsRuler input).length : ℕ) : ℤ) = _
  simp [generalCoefficientBits, Nat.cast_add, Nat.cast_pow, add_comm]

theorem generalPositiveShiftWord_cobham : Cobham fun v : Fin 1 → List Bool =>
    generalPositiveShiftWord (v 0) :=
  (Cobham.comp (.bit false) fun _ => Cobham.comp₂ binaryCertificateAdd_cobham
    (Cobham.const [true])
    (Cobham.appendFn (Cobham.padFn generalBitsRuler_cobham Cobham.empty)
      (Cobham.const [true]))).of_eq fun _ => rfl

/-- Add the canonical strictly positive shift used by the complementary path. -/
def generalShiftedPayoffWord (columnPlayer : Bool) (v : Fin 3 → List Bool) : List Bool :=
  binarySignedAdd (generalSignedPayoffWord columnPlayer v) (generalPositiveShiftWord (v 2))

theorem generalShiftedPayoffWord_value (columnPlayer : Bool) (v : Fin 3 → List Bool) :
    binarySignedValue (generalShiftedPayoffWord columnPlayer v) =
      decodeGeneralPayoff columnPlayer (v 2) (v 0).length (v 1).length +
        ((2 : ℤ) ^ generalCoefficientBits (v 2) + 1) := by
  rw [generalShiftedPayoffWord, binarySignedAdd_value, generalSignedPayoffWord_value,
    generalPositiveShiftWord_value]

/-- Even malformed input fields obey the uniform shifted-entry magnitude bound. -/
theorem generalShiftedPayoffWord_bound (columnPlayer : Bool) (v : Fin 3 → List Bool) :
    (binarySignedValue (generalShiftedPayoffWord columnPlayer v)).natAbs <
      2 ^ (generalCoefficientBits (v 2) + 2) := by
  rw [generalShiftedPayoffWord_value]
  have h := decodeGeneralPayoff_natAbs_lt columnPlayer (v 2) (v 0).length (v 1).length
  have hs : ((2 : ℤ) ^ generalCoefficientBits (v 2) + 1).natAbs =
      2 ^ generalCoefficientBits (v 2) + 1 := by
    rw [show (2 : ℤ) ^ generalCoefficientBits (v 2) + 1 =
      ((2 ^ generalCoefficientBits (v 2) + 1 : ℕ) : ℤ) by simp]
    exact Int.natAbs_natCast _
  have hb := Int.natAbs_add_le
    (decodeGeneralPayoff columnPlayer (v 2) (v 0).length (v 1).length)
    ((2 : ℤ) ^ generalCoefficientBits (v 2) + 1)
  rw [hs] at hb
  rw [pow_add]
  norm_num only [pow_two] at *
  have hp : 0 < 2 ^ generalCoefficientBits (v 2) := by positivity
  nlinarith

theorem generalShiftedPayoffWord_cobham (columnPlayer : Bool) :
    Cobham (generalShiftedPayoffWord columnPlayer) := by
  have hp : Cobham fun v : Fin 3 → List Bool => generalPositiveShiftWord (v 2) :=
    (Cobham.comp generalPositiveShiftWord_cobham fun _ => Cobham.proj 2).of_eq fun _ => rfl
  exact (Cobham.comp₂ binarySignedAdd_cobham (generalSignedPayoffWord_cobham columnPlayer)
    hp).of_eq fun _ => rfl

theorem generalShiftedPayoffWord_mem_FPn (columnPlayer : Bool) :
    FPn (generalShiftedPayoffWord columnPlayer) :=
  cobham_iff_FPn.mp (generalShiftedPayoffWord_cobham columnPlayer)

end GameTheory.Complexity.Backend
