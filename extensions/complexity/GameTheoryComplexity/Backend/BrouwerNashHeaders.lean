import GameTheoryComplexity.Backend.BrouwerNashLayout
import GameTheoryComplexity.Backend.BrouwerNashRewardMachine
import GameTheoryComplexity.Backend.CircuitCodeShift

/-! Polynomial header producers for a source and its two compiled coordinate-color circuits.
Only encoded circuit header lengths determine the gate layout. -/
namespace GameTheory.Complexity.Backend.BrouwerNashHeaders
open _root_.Complexity _root_.Complexity.Cobham

private def scale (n : ℕ) (r : List Bool) : List Bool := smash r (List.replicate n true)
/-- Source grid precision, supplied by the canonical outer pair. -/
def sourceDepthRuler (v : Fin 3 → List Bool) : List Bool := pairFst (v 0)
/-- Dyadic halving-chain length. -/
def precisionRuler (v : Fin 3 → List Bool) : List Bool :=
  scale 5 (sourceDepthRuler v ++ List.replicate 10 false)
/-- Two extended coordinate fields for a compiled color circuit. -/
def arityRuler (v : Fin 3 → List Bool) : List Bool := scale 2 (sourceDepthRuler v ++ [false])
/-- Shared constant, mean, scaling and feedback region. -/
def globalRuler (v : Fin 3 → List Bool) : List Bool :=
  scale 3 (precisionRuler v) ++ List.replicate 11 false
/-- Coordinate copies and the two compiled circuits for one corner. -/
def cornerRuler (v : Fin 3 → List Bool) : List Bool :=
  scale 2 (arityRuler v) ++ circuitUnaryPrefix (v 1) ++ circuitUnaryPrefix (v 2)
/-- Extraction, increment, interpolation and color work for one jitter sample. -/
def sampleRuler (v : Fin 3 → List Bool) : List Bool :=
  List.replicate 26 false ++ scale 12 (sourceDepthRuler v) ++ scale 4 (cornerRuler v)

/-- Allocated shared and sample wires, with one spare unit before dimension scaling. -/
def unitsRuler (v : Fin 3 → List Bool) : List Bool :=
  globalRuler v ++ scale 41 (sampleRuler v) ++ [false]

/-- The allocated game dimension is one hundred twenty-three times the unit ruler. -/
def dimensionRuler (v : Fin 3 → List Bool) : List Bool := scale 123 (unitsRuler v)
/-- This width fits every coefficient bounded by one hundred times the dimension. -/
def widthRuler (v : Fin 3 → List Bool) : List Bool :=
  dimensionRuler v ++ List.replicate 10 false
/-- The signed reward uses the same dimension and source precisionRuler. -/
def baselineWord (v : Fin 3 → List Bool) : List Bool :=
  BrouwerNashRewardMachine.reward ![sourceDepthRuler v, dimensionRuler v]

@[simp] theorem sourceDepthRuler_length (v : Fin 3 → List Bool) :
    (sourceDepthRuler v).length = (pairFst (v 0)).length := rfl

@[simp] theorem precisionRuler_length (v : Fin 3 → List Bool) :
    (precisionRuler v).length = BrouwerNashLayout.precision (pairFst (v 0)).length := by
  simp only [precisionRuler, scale, sourceDepthRuler, smash_length,
    List.length_append, List.length_replicate, BrouwerNashLayout.precision]
  omega

@[simp] theorem arityRuler_length (v : Fin 3 → List Bool) :
    (arityRuler v).length = BrouwerNashLayout.arity (pairFst (v 0)).length := by
  simp only [arityRuler, scale, sourceDepthRuler, smash_length,
    List.length_append, List.length_singleton, List.length_replicate, BrouwerNashLayout.arity]
  omega

@[simp] theorem globalRuler_length (v : Fin 3 → List Bool) :
    (globalRuler v).length = BrouwerNashLayout.globalCount (pairFst (v 0)).length := by
  simp only [globalRuler, scale, smash_length, List.length_append, List.length_replicate,
    precisionRuler_length, BrouwerNashLayout.globalCount]
  omega

@[simp] theorem cornerRuler_length (v : Fin 3 → List Bool) :
    (cornerRuler v).length = BrouwerNashLayout.cornerWidth (pairFst (v 0)).length
      (circuitUnaryPrefix (v 1)).length (circuitUnaryPrefix (v 2)).length := by
  simp only [cornerRuler, scale, smash_length, List.length_append, List.length_replicate,
    arityRuler_length, BrouwerNashLayout.cornerWidth]
  omega

@[simp] theorem sampleRuler_length (v : Fin 3 → List Bool) :
    (sampleRuler v).length = BrouwerNashLayout.sampleWidth (pairFst (v 0)).length
      (circuitUnaryPrefix (v 1)).length (circuitUnaryPrefix (v 2)).length := by
  simp only [sampleRuler, scale, sourceDepthRuler, smash_length, List.length_append,
    List.length_replicate, cornerRuler_length, BrouwerNashLayout.sampleWidth]
  omega

@[simp] theorem unitsRuler_length (v : Fin 3 → List Bool) :
    (unitsRuler v).length = BrouwerNashLayout.units (pairFst (v 0)).length
      (circuitUnaryPrefix (v 1)).length (circuitUnaryPrefix (v 2)).length := by
  simp only [unitsRuler, scale, smash_length, List.length_append,
    List.length_replicate, List.length_singleton, globalRuler_length, sampleRuler_length,
    BrouwerNashLayout.units]
  omega

/-- The ruler length agrees with the single canonical wire allocation. -/
theorem dimensionRuler_length (v : Fin 3 → List Bool) :
    (dimensionRuler v).length = BrouwerNashLayout.dimension (pairFst (v 0)).length
      (circuitUnaryPrefix (v 1)).length (circuitUnaryPrefix (v 2)).length := by
  simp only [dimensionRuler, unitsRuler, scale, globalRuler, precisionRuler, sampleRuler,
    cornerRuler, arityRuler, sourceDepthRuler,
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
  simpa only [baselineWord, sourceDepthRuler, Matrix.cons_val_zero, Matrix.cons_val_one]
    using BrouwerNashRewardMachine.reward_value ![pairFst (v 0), dimensionRuler v]

private theorem scale_cobham {n a : ℕ} {f : (Fin a → List Bool) → List Bool}
    (hf : Cobham f) : Cobham fun v => scale n (f v) :=
  (Cobham.comp₂ Cobham.smash hf (Cobham.const (List.replicate n true))).of_eq fun _ => rfl

theorem sourceDepthRuler_cobham : Cobham sourceDepthRuler :=
  (Cobham.comp (FP_subset_CobhamFP pairFst_mem_FP) fun _ : Fin 1 =>
    (Cobham.proj 0 : Cobham fun v : Fin 3 → List Bool => v 0)).of_eq fun _ => rfl
theorem precisionRuler_cobham : Cobham precisionRuler :=
  scale_cobham (appendFn sourceDepthRuler_cobham (Cobham.const (List.replicate 10 false)))
theorem arityRuler_cobham : Cobham arityRuler :=
  scale_cobham (appendFn sourceDepthRuler_cobham (Cobham.const [false]))
theorem globalRuler_cobham : Cobham globalRuler :=
  appendFn (scale_cobham precisionRuler_cobham) (Cobham.const (List.replicate 11 false))
theorem cornerRuler_cobham : Cobham cornerRuler :=
  appendFn (appendFn (scale_cobham arityRuler_cobham)
    (Cobham.comp (FP_subset_CobhamFP circuitUnaryPrefix_mem_FP) fun _ : Fin 1 => (.proj 1)))
    (Cobham.comp (FP_subset_CobhamFP circuitUnaryPrefix_mem_FP) fun _ : Fin 1 => (.proj 2))
theorem sampleRuler_cobham : Cobham sampleRuler :=
  appendFn (appendFn (Cobham.const (List.replicate 26 false))
    (scale_cobham sourceDepthRuler_cobham))
    (scale_cobham cornerRuler_cobham)

/-- The allocated-prefix ruler is produced by polynomial length operations. -/
theorem unitsRuler_cobham : Cobham unitsRuler :=
  appendFn (appendFn globalRuler_cobham (scale_cobham sampleRuler_cobham))
    (Cobham.const [false])

theorem dimensionRuler_cobham : Cobham dimensionRuler := scale_cobham unitsRuler_cobham
theorem widthRuler_cobham : Cobham widthRuler :=
  appendFn dimensionRuler_cobham (Cobham.const (List.replicate 10 false))
theorem baselineWord_cobham : Cobham baselineWord :=
  (Cobham.comp₂ BrouwerNashRewardMachine.reward_cobham sourceDepthRuler_cobham
    dimensionRuler_cobham).of_eq fun _ => rfl

theorem dimensionRuler_mem_FPn : FPn dimensionRuler := cobham_iff_FPn.mp dimensionRuler_cobham
theorem widthRuler_mem_FPn : FPn widthRuler := cobham_iff_FPn.mp widthRuler_cobham
theorem baselineWord_mem_FPn : FPn baselineWord := cobham_iff_FPn.mp baselineWord_cobham

/-- Specialize a header producer to the source and its two compiled color circuits. -/
def sourceFn (producer : (Fin 3 → List Bool) → List Bool)
    (codes : Fin 2 → List Bool → List Bool) (source : List Bool) : List Bool :=
  producer ![source, codes 0 source, codes 1 source]

/-- Decoded circuit counts recover the canonical source-dependent program dimension. -/
theorem sourceDimension_length_of_decode (codes : Fin 2 → List Bool → List Bool)
    (source : List Bool) (raw₀ raw₁ : CircuitCode.RawCircuit)
    (hd₀ : CircuitCode.RawCircuit.decode? (codes 0 source) = some raw₀)
    (hd₁ : CircuitCode.RawCircuit.decode? (codes 1 source) = some raw₁) :
    (sourceFn dimensionRuler codes source).length =
      BrouwerNashLayout.dimension (pairFst source).length raw₀.length raw₁.length := by
  have h := dimensionRuler_length ![source, codes 0 source, codes 1 source]
  change (sourceFn dimensionRuler codes source).length = BrouwerNashLayout.dimension
    (pairFst source).length (circuitUnaryPrefix (codes 0 source)).length
      (circuitUnaryPrefix (codes 1 source)).length at h
  rwa [circuitUnaryPrefix_length_of_decode _ _ hd₀,
    circuitUnaryPrefix_length_of_decode _ _ hd₁] at h

/-- Actual compiled-circuit producers compose with the uniform header machines. -/
theorem sourceFn_mem_FP {producer : (Fin 3 → List Bool) → List Bool}
    (hp : Cobham producer) (codes : Fin 2 → List Bool → List Bool)
    (hc : ∀ i, codes i ∈ FP) : sourceFn producer codes ∈ FP := by
  apply CobhamFP_subset_FP
  exact (Cobham.comp₃ hp (.proj 0) (FP_subset_CobhamFP (hc 0))
    (FP_subset_CobhamFP (hc 1))).of_eq fun _ => rfl

end GameTheory.Complexity.Backend.BrouwerNashHeaders
