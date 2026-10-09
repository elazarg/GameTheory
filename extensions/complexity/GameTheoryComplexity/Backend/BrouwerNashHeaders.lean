import GameTheoryComplexity.Backend.BrouwerNashLayout
import GameTheoryComplexity.Backend.BrouwerNashRewardMachine
import GameTheoryComplexity.Backend.CircuitCodeShift

/-! Polynomial header producers for a source and its two compiled coordinate-color circuits.
Only encoded circuit header lengths determine the gate layout. -/
namespace GameTheory.Complexity.Backend.BrouwerNashHeaders
open _root_.Complexity _root_.Complexity.Cobham

private def scale (n : ℕ) (r : List Bool) : List Bool := smash r (List.replicate n true)
private def b (v : Fin 3 → List Bool) : List Bool := pairFst (v 0)
private def precision (v : Fin 3 → List Bool) : List Bool :=
  scale 5 (b v ++ List.replicate 10 false)
private def arity (v : Fin 3 → List Bool) : List Bool := scale 2 (b v ++ [false])
private def global (v : Fin 3 → List Bool) : List Bool :=
  scale 3 (precision v) ++ List.replicate 11 false
private def corner (v : Fin 3 → List Bool) : List Bool :=
  scale 2 (arity v) ++ circuitUnaryPrefix (v 1) ++ circuitUnaryPrefix (v 2)
private def sample (v : Fin 3 → List Bool) : List Bool :=
  List.replicate 26 false ++ scale 12 (b v) ++ scale 4 (corner v)

/-- A positive multiple of123 reserves the complete source-dependent layout. -/
def dimensionRuler (v : Fin 3 → List Bool) : List Bool :=
  scale 123 (global v ++ scale 41 (sample v) ++ [false])
/-- This width fits every coefficient bounded by one hundred times the dimension. -/
def widthRuler (v : Fin 3 → List Bool) : List Bool :=
  dimensionRuler v ++ List.replicate 10 false
/-- The signed reward uses the same dimension and source precision. -/
def baselineWord (v : Fin 3 → List Bool) : List Bool :=
  BrouwerNashRewardMachine.reward ![b v, dimensionRuler v]

/-- The ruler length agrees with the single canonical wire allocation. -/
theorem dimensionRuler_length (v : Fin 3 → List Bool) :
    (dimensionRuler v).length = BrouwerNashLayout.dimension (pairFst (v 0)).length
      (circuitUnaryPrefix (v 1)).length (circuitUnaryPrefix (v 2)).length := by
  simp only [dimensionRuler, scale, global, precision, sample, corner, arity, b,
    smash_length, List.length_replicate, List.length_append, List.length_singleton,
    BrouwerNashLayout.dimension, BrouwerNashLayout.units, BrouwerNashLayout.globalCount,
    BrouwerNashLayout.precision, BrouwerNashLayout.sampleWidth, BrouwerNashLayout.cornerWidth,
    BrouwerNashLayout.arity]
  ring

/-- Positive game dimensions are guaranteed even for malformed circuit words. -/
theorem dimensionRuler_pos (v : Fin 3 → List Bool) : 0 < (dimensionRuler v).length := by
  rw [dimensionRuler_length]
  exact BrouwerNashLayout.dimension_pos _ _ _

@[simp] theorem widthRuler_length (v : Fin 3 → List Bool) :
    (widthRuler v).length = (dimensionRuler v).length + 10 := by
  simp only [widthRuler, List.length_append, List.length_replicate]

private theorem coefficient_capacity (k : ℕ) : 100 * k < 2 ^ (k + 9) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hpow : 512 ≤ 2 ^ (k + 9) := by
      change 2 ^ 9 ≤ 2 ^ (k + 9)
      exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 9 ≤ k + 9)
    rw [show k + 1 + 9 = (k + 9) + 1 by omega, pow_succ]
    omega

/-- Fixed signed coefficient fields fit the program's uniform hundred-dimension bound. -/
theorem widthRuler_fits (v : Fin 3 → List Bool) (q : ℤ)
    (hq : q.natAbs ≤ 100 * (dimensionRuler v).length) :
    q.natAbs < 2 ^ ((widthRuler v).length - 1) := by
  rw [widthRuler_length, show (dimensionRuler v).length + 10 - 1 =
    (dimensionRuler v).length + 9 by omega]
  exact hq.trans_lt (coefficient_capacity _)

/-- The baseline matches the exact integer reward for the emitted dimension. -/
theorem baselineWord_value (v : Fin 3 → List Bool) :
    binarySignedValue (baselineWord v) =
      ((dimensionRuler v).length *
        (100 * (dimensionRuler v).length + 2 * (dimensionRuler v).length) + 1 : ℤ) *
      2 ^ (100 * ((pairFst (v 0)).length + (dimensionRuler v).length + 10)) := by
  simpa only [baselineWord, b, Matrix.cons_val_zero, Matrix.cons_val_one]
    using BrouwerNashRewardMachine.reward_value ![pairFst (v 0), dimensionRuler v]

private theorem scale_cobham {n a : ℕ} {f : (Fin a → List Bool) → List Bool}
    (hf : Cobham f) : Cobham fun v => scale n (f v) :=
  (Cobham.comp₂ Cobham.smash hf (Cobham.const (List.replicate n true))).of_eq fun _ => rfl

private theorem b_cobham : Cobham b :=
  (Cobham.comp (FP_subset_CobhamFP pairFst_mem_FP) fun _ : Fin 1 =>
    (Cobham.proj 0 : Cobham fun v : Fin 3 → List Bool => v 0)).of_eq fun _ => rfl
private theorem precision_cobham : Cobham precision :=
  scale_cobham (appendFn b_cobham (Cobham.const (List.replicate 10 false)))
private theorem arity_cobham : Cobham arity :=
  scale_cobham (appendFn b_cobham (Cobham.const [false]))
private theorem global_cobham : Cobham global :=
  appendFn (scale_cobham precision_cobham) (Cobham.const (List.replicate 11 false))
private theorem corner_cobham : Cobham corner :=
  appendFn (appendFn (scale_cobham arity_cobham)
    (Cobham.comp (FP_subset_CobhamFP circuitUnaryPrefix_mem_FP) fun _ : Fin 1 => (.proj 1)))
    (Cobham.comp (FP_subset_CobhamFP circuitUnaryPrefix_mem_FP) fun _ : Fin 1 => (.proj 2))
private theorem sample_cobham : Cobham sample :=
  appendFn (appendFn (Cobham.const (List.replicate 26 false)) (scale_cobham b_cobham))
    (scale_cobham corner_cobham)

theorem dimensionRuler_cobham : Cobham dimensionRuler :=
  scale_cobham (appendFn (appendFn global_cobham (scale_cobham sample_cobham))
    (Cobham.const [false]))
theorem widthRuler_cobham : Cobham widthRuler :=
  appendFn dimensionRuler_cobham (Cobham.const (List.replicate 10 false))
theorem baselineWord_cobham : Cobham baselineWord :=
  (Cobham.comp₂ BrouwerNashRewardMachine.reward_cobham b_cobham
    dimensionRuler_cobham).of_eq fun _ => rfl

theorem dimensionRuler_mem_FPn : FPn dimensionRuler := cobham_iff_FPn.mp dimensionRuler_cobham
theorem widthRuler_mem_FPn : FPn widthRuler := cobham_iff_FPn.mp widthRuler_cobham
theorem baselineWord_mem_FPn : FPn baselineWord := cobham_iff_FPn.mp baselineWord_cobham

/-- Specialize a header producer to the source and its two compiled color circuits. -/
def sourceFn (producer : (Fin 3 → List Bool) → List Bool)
    (codes : Fin 2 → List Bool → List Bool) (source : List Bool) : List Bool :=
  producer ![source, codes 0 source, codes 1 source]

/-- Actual compiled-circuit producers compose with the uniform header machines. -/
theorem sourceFn_mem_FP {producer : (Fin 3 → List Bool) → List Bool}
    (hp : Cobham producer) (codes : Fin 2 → List Bool → List Bool)
    (hc : ∀ i, codes i ∈ FP) : sourceFn producer codes ∈ FP := by
  apply CobhamFP_subset_FP
  exact (Cobham.comp₃ hp (.proj 0) (FP_subset_CobhamFP (hc 0))
    (FP_subset_CobhamFP (hc 1))).of_eq fun _ => rfl

end GameTheory.Complexity.Backend.BrouwerNashHeaders
