module

public import GameTheoryComplexity.Backend.GeneralBimatrixVerifierMachine
public import GameTheoryComplexity.Backend.BinarySignedAddition

@[expose] public section

/-! Certified signed words for the decoded rectangular game and its positive shift.
The input codec remains a pair of unsigned magnitude fields; only internal
arithmetic uses sign-header words.
-/
namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM

/-- Decode both magnitude fields into one exact signed arithmetic word. -/
def generalSignedPayoffWord (columnPlayer : Bool) (v : Fin 3 → List Bool) : List Bool :=
  binarySignedSub (false :: generalPayoffWord columnPlayer true v)
    (false :: generalPayoffWord columnPlayer false v)

private theorem payoffWord_field (columnPlayer positive : Bool) (v : Fin 3 → List Bool) :
    generalPayoffWord columnPlayer positive v =
      generalPayoffField columnPlayer positive (v 2) (v 0).length (v 1).length := by
  cases columnPlayer <;> cases positive <;>
    simp [generalPayoffWord, generalPayoffField, generalBinaryField,
      generalRowCount, generalColCount, generalCoefficientBits]
  all_goals (congr 2; ring)

theorem generalSignedPayoffWord_value (columnPlayer : Bool) (v : Fin 3 → List Bool) :
    binarySignedValue (generalSignedPayoffWord columnPlayer v) =
      decodeGeneralPayoff columnPlayer (v 2) (v 0).length (v 1).length := by
  rw [generalSignedPayoffWord, binarySignedSub_value, payoffWord_field, payoffWord_field]
  rfl

/-- The fixed positive payoff shift, represented directly in binary. -/
def generalPositiveShiftWord (input : List Bool) : List Bool :=
  false :: binaryCertificateAdd ![[true], List.replicate (generalBitsRuler input).length false ++ [true]]

private theorem powerWord_value (ruler : List Bool) :
    ofBits (List.replicate ruler.length false ++ [true]) = 2 ^ ruler.length := by
  induction ruler.length with
  | zero => rfl
  | succ n ih =>
    change Nat.bit false (ofBits (List.replicate n false ++ [true])) = _
    rw [ih, Nat.bit_val]
    simp [pow_succ, Nat.mul_comm]

theorem generalPositiveShiftWord_value (input : List Bool) :
    binarySignedValue (generalPositiveShiftWord input) =
      (2 : ℤ) ^ generalCoefficientBits input + 1 := by
  simp only [generalPositiveShiftWord, binarySignedValue, List.headD_cons, List.tail_cons,
    Bool.false_eq_true, ↓reduceIte, binaryCertificateAdd_value, powerWord_value]
  change ((1 + 2 ^ (generalBitsRuler input).length : ℕ) : ℤ) = _
  simp [generalCoefficientBits, Nat.cast_add, Nat.cast_pow, add_comm]

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

@[fun_prop] theorem generalSignedPayoffWord_polyTime (columnPlayer : Bool) :
    ComputableInPolyTime (generalSignedPayoffWord columnPlayer) (encPi encBits) encBits := by
  exact binarySignedSub_polyTime
    (.bitsCons (.const false) (generalPayoffWord_polyTime columnPlayer true))
    (.bitsCons (.const false) (generalPayoffWord_polyTime columnPlayer false))

@[fun_prop] theorem generalPositiveShiftWord_polyTime :
    ComputableInPolyTime (fun v : Fin 1 → List Bool => generalPositiveShiftWord (v 0))
      (encPi encBits) encBits := by
  have hpower := ComputableInPolyTime.bitsAppend
    ((ComputableInPolyTime.bitsReplicate false).comp
      (ComputableInPolyTime.length_bits_comp generalBitsRuler_polyTime))
    (ComputableInPolyTime.const [true])
  have hargs : ComputableInPolyTime
      (fun v : Fin 1 → List Bool =>
        ![[true], List.replicate (generalBitsRuler (v 0)).length false ++ [true]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .const [true]
    · exact hpower
  exact .bitsCons (.const false) (binaryCertificateAdd_polyTime.comp hargs)

@[fun_prop] theorem generalShiftedPayoffWord_polyTime (columnPlayer : Bool) :
    ComputableInPolyTime (generalShiftedPayoffWord columnPlayer) (encPi encBits) encBits := by
  have hinput : ComputableInPolyTime (fun v : Fin 3 → List Bool => ![v 2])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact .pi_apply encBits (2 : Fin 3)
  have h := binarySignedAdd_polyTime (generalSignedPayoffWord_polyTime columnPlayer)
    (generalPositiveShiftWord_polyTime.comp hinput)
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq (g := generalShiftedPayoffWord columnPlayer)
  intro v
  rfl

end GameTheory.Complexity.Backend
