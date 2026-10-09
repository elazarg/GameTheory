import GameTheoryComplexity.Backend.BinaryUnaryEncoding
import GameTheoryComplexity.Backend.BinarySignedArithmetic
import GameTheory.Math.GridBrouwerErrorBudget

/-! Integer reward words with polynomial bit length for robust grid gate computations.
The precision clock controls padding; multiplication operates on binary words. -/
namespace GameTheory.Complexity.Backend.BrouwerNashRewardMachine
open _root_.Complexity _root_.Complexity.Cobham

/-- Exponent clock for the dyadic error budget, from precision and dimension rulers. -/
def clock (v : Fin 2 → List Bool) : List Bool :=
  smash (v 0 ++ v 1 ++ List.replicate 10 false) (List.replicate 100 true)

private def factor (k : List Bool) : List Bool :=
  binaryCertificateAdd ![binaryWordMul (binaryLengthWord k)
    (binaryWordMul (binaryLengthWord k) [false, true, true, false, false, true, true]), [true]]

/-- Positive signed reward `(102 k² + 1) 2^Q`. -/
def reward (v : Fin 2 → List Bool) : List Bool :=
  false :: (List.replicate (clock v).length false ++ factor (v 1))

@[simp] theorem clock_length (v : Fin 2 → List Bool) :
    (clock v).length = 100 * ((v 0).length + (v 1).length + 10) := by
  simp only [clock, smash_length, List.length_append, List.length_replicate]
  omega

private theorem factor_value (k : List Bool) :
    Nat.fromBitsLE (factor k) = k.length * (100 * k.length + 2 * k.length) + 1 := by
  rw [factor, binaryCertificateAdd_value, binaryWordMul_value, binaryWordMul_value,
    binaryLengthWord_value]
  change k.length * (k.length * 102) + 1 = _
  ring

private theorem zero_value (n : ℕ) : Nat.fromBitsLE (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, Nat.fromBitsLE_cons, ih]

/-- The emitted word denotes exactly the integer reward schedule. -/
theorem reward_value (v : Fin 2 → List Bool) :
    binarySignedValue (reward v) =
      ((v 1).length * (100 * (v 1).length + 2 * (v 1).length) + 1 : ℤ) *
        2 ^ (100 * ((v 0).length + (v 1).length + 10)) := by
  simp only [reward, binarySignedValue, List.headD_cons, List.tail_cons,
    Bool.false_eq_true, ite_false, fromBitsLE_append, zero_value,
    List.length_replicate, zero_add, factor_value, clock_length,
    Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_comm _ _

/-- Matching rewards strictly dominate the perturbation scale, including empty rulers. -/
theorem reward_dominates (v : Fin 2 → List Bool) :
    ((v 1).length : ℤ) * (100 * (v 1).length + 2 * (v 1).length) <
      binarySignedValue (reward v) := by
  rw [reward_value]
  have hk : (0 : ℤ) ≤ (v 1).length := Nat.cast_nonneg _
  have hs : 0 ≤ ((v 1).length : ℤ) * (100 * (v 1).length + 2 * (v 1).length) := by
    nlinarith only [hk]
  have hp : (1 : ℤ) ≤ 2 ^ (100 * ((v 0).length + (v 1).length + 10)) :=
    one_le_pow₀ (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤
    ((v 1).length : ℤ) * (100 * (v 1).length + 2 * (v 1).length) + 1 by omega)
  rw [mul_one] at hh
  omega

/-- The reward has linear bit length in the supplied rulers. -/
theorem reward_length (v : Fin 2 → List Bool) :
    (reward v).length ≤ 100 * ((v 0).length + (v 1).length + 10) +
      4 * (v 1).length + 13 := by
  have hn := binaryLengthWord_length (v 1)
  have hs := binaryWordMul_length (binaryLengthWord (v 1))
    [false, true, true, false, false, true, true]
  have hm := binaryWordMul_length (binaryLengthWord (v 1))
    (binaryWordMul (binaryLengthWord (v 1)) [false, true, true, false, false, true, true])
  simp only [List.length_cons, List.length_nil] at hs
  simp only [reward, List.length_cons, List.length_append, List.length_replicate,
    clock_length, factor, binaryCertificateAdd_length, List.length_nil]
  omega

/-- The emitted schedule bounds the actual normalized gate error. -/
theorem reward_error_bound (v : Fin 2 → List Bool) (hk : 1 ≤ (v 1).length) :
    0 ≤ ((v 1).length : ℚ) * (102 * (v 1).length) /
      (binarySignedValue (reward v) : ℚ) ∧
    ((v 1).length : ℚ) * (102 * (v 1).length) /
      (binarySignedValue (reward v) : ℚ) ≤
        1 / (2 : ℚ) ^ (100 * ((v 0).length + (v 1).length + 10)) := by
  rw [reward_value]
  exact GameTheory.Math.bimatrix_integer_reward_error_bound (v 1).length
    (100 * ((v 0).length + (v 1).length + 10)) hk

/-- The exponent clock is a fixed composition of certified length operations. -/
theorem clock_cobham : Cobham clock :=
  (Cobham.comp₂ Cobham.smash
    (appendFn (appendFn (.proj 0) (.proj 1)) (Cobham.const (List.replicate 10 false)))
    (Cobham.const (List.replicate 100 true))).of_eq fun _ => rfl

private theorem factor_cobham : Cobham fun v : Fin 1 → List Bool => factor (v 0) := by
  have hn : Cobham fun v : Fin 1 → List Bool => binaryLengthWord (v 0) :=
    binaryLengthWord_cobham
  have hs := Cobham.comp₂ binaryWordMul_cobham hn
    (Cobham.const [false, true, true, false, false, true, true])
  have hm := Cobham.comp₂ binaryWordMul_cobham hn hs
  exact (Cobham.comp₂ binaryCertificateAdd_cobham hm (Cobham.const [true])).of_eq
    fun _ => rfl

/-- The baseline producer is polynomial time at arity two. -/
theorem reward_cobham : Cobham reward := by
  have hf := Cobham.comp factor_cobham (fun _ : Fin 1 => (Cobham.proj 1 :
    Cobham fun v : Fin 2 → List Bool => v 1))
  exact (Cobham.comp (.bit false) fun _ : Fin 1 =>
    appendFn (Cobham.zeroBlockFn clock_cobham) hf).of_eq fun _ => rfl

theorem reward_mem_FPn : FPn reward := cobham_iff_FPn.mp reward_cobham

end GameTheory.Complexity.Backend.BrouwerNashRewardMachine
