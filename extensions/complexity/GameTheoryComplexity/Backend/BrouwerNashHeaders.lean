module

public import GameTheoryComplexity.Backend.BrouwerNashLayout
public import GameTheoryComplexity.Backend.BrouwerNashRewardMachine
public import GameTheoryComplexity.Backend.CircuitCodeShift
public import GameTheoryComplexity.Backend.CircuitWords

@[expose] public section

/-! Header words allocate the source's precision and the two compiled coordinate-color
circuits. Their bits, including copied malformed circuit prefixes, remain available to
coefficient queries; the layout depends only on their lengths. -/
namespace GameTheory.Complexity.Backend.BrouwerNashHeaders
open Turing.MultiTapeTM

/-- Source grid precision is supplied by the canonical outer pair. -/
def sourceDepthRuler (source : List Bool) : List Bool := CircuitWords.first source

/-- Dyadic halving-chain length. -/
def precisionRuler (source : List Bool) : List Bool :=
  List.replicate (5 * ((sourceDepthRuler source).length + 10)) true

/-- Two extended coordinate fields for a compiled color circuit. -/
def arityRuler (source : List Bool) : List Bool :=
  List.replicate (2 * ((sourceDepthRuler source).length + 1)) true

/-- Shared constant, mean, scaling and feedback region. -/
def globalRuler (source : List Bool) : List Bool :=
  List.replicate (3 * (precisionRuler source).length) true ++ List.replicate 11 false

/-- Coordinate copies and both unmodified circuit-count prefixes for one corner. -/
def cornerRuler (source code₀ code₁ : List Bool) : List Bool :=
  List.replicate (2 * (arityRuler source).length) true ++
    circuitUnaryPrefix code₀ ++ circuitUnaryPrefix code₁

/-- Extraction, increment, interpolation and color work for one jitter sample. -/
def sampleRuler (source code₀ code₁ : List Bool) : List Bool :=
  List.replicate 26 false ++ List.replicate (12 * (sourceDepthRuler source).length) true ++
    List.replicate (4 * (cornerRuler source code₀ code₁).length) true

/-- Shared and sample wires leave one spare unit before dimension scaling. -/
def unitsRuler (source code₀ code₁ : List Bool) : List Bool :=
  globalRuler source ++ List.replicate (41 * (sampleRuler source code₀ code₁).length) true ++ [false]

/-- The game dimension is one hundred twenty-three times the unit ruler. -/
def dimensionRuler (source code₀ code₁ : List Bool) : List Bool :=
  List.replicate (123 * (unitsRuler source code₀ code₁).length) true

/-- This width fits every coefficient bounded by one hundred times the dimension. -/
def widthRuler (source code₀ code₁ : List Bool) : List Bool :=
  dimensionRuler source code₀ code₁ ++ List.replicate 10 false

/-- The signed reward uses the same dimension and source precision. -/
def baselineWord (source code₀ code₁ : List Bool) : List Bool :=
  BrouwerNashRewardMachine.reward (sourceDepthRuler source) (dimensionRuler source code₀ code₁)

@[simp] theorem sourceDepthRuler_length (source : List Bool) :
    (sourceDepthRuler source).length = (CircuitWords.first source).length := rfl

@[simp] theorem precisionRuler_length (source : List Bool) :
    (precisionRuler source).length = BrouwerNashLayout.precision (CircuitWords.first source).length := by
  simp only [precisionRuler, List.length_replicate, sourceDepthRuler, BrouwerNashLayout.precision]

@[simp] theorem arityRuler_length (source : List Bool) :
    (arityRuler source).length = BrouwerNashLayout.arity (CircuitWords.first source).length := by
  simp only [arityRuler, List.length_replicate, sourceDepthRuler, BrouwerNashLayout.arity]

@[simp] theorem globalRuler_length (source : List Bool) :
    (globalRuler source).length = BrouwerNashLayout.globalCount (CircuitWords.first source).length := by
  simp only [globalRuler, List.length_append, List.length_replicate,
    precisionRuler_length, BrouwerNashLayout.globalCount]

@[simp] theorem cornerRuler_length (source code₀ code₁ : List Bool) :
    (cornerRuler source code₀ code₁).length = BrouwerNashLayout.cornerWidth
      (CircuitWords.first source).length (circuitUnaryPrefix code₀).length
      (circuitUnaryPrefix code₁).length := by
  simp only [cornerRuler, List.length_append, List.length_replicate,
    arityRuler_length, BrouwerNashLayout.cornerWidth]

@[simp] theorem sampleRuler_length (source code₀ code₁ : List Bool) :
    (sampleRuler source code₀ code₁).length = BrouwerNashLayout.sampleWidth
      (CircuitWords.first source).length (circuitUnaryPrefix code₀).length
      (circuitUnaryPrefix code₁).length := by
  simp only [sampleRuler, List.length_append, List.length_replicate,
    sourceDepthRuler, cornerRuler_length, BrouwerNashLayout.sampleWidth]

@[simp] theorem unitsRuler_length (source code₀ code₁ : List Bool) :
    (unitsRuler source code₀ code₁).length = BrouwerNashLayout.units
      (CircuitWords.first source).length (circuitUnaryPrefix code₀).length
      (circuitUnaryPrefix code₁).length := by
  simp only [unitsRuler, List.length_append, List.length_replicate, List.length_singleton,
    globalRuler_length, sampleRuler_length, BrouwerNashLayout.units]

/-- The ruler length agrees with the canonical wire allocation. -/
theorem dimensionRuler_length (source code₀ code₁ : List Bool) :
    (dimensionRuler source code₀ code₁).length = BrouwerNashLayout.dimension
      (CircuitWords.first source).length (circuitUnaryPrefix code₀).length
      (circuitUnaryPrefix code₁).length := by
  simp only [dimensionRuler, List.length_replicate, unitsRuler_length, BrouwerNashLayout.dimension]

/-- Game dimensions are positive even for malformed circuit words. -/
theorem dimensionRuler_pos (source code₀ code₁ : List Bool) :
    0 < (dimensionRuler source code₀ code₁).length := by
  rw [dimensionRuler_length]
  exact BrouwerNashLayout.dimension_pos _ _ _

@[simp] theorem widthRuler_length (source code₀ code₁ : List Bool) :
    (widthRuler source code₀ code₁).length = (dimensionRuler source code₀ code₁).length + 10 := by
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

/-- Signed coefficient fields fit the program's uniform hundred-dimension bound. -/
theorem widthRuler_fits (source code₀ code₁ : List Bool) (q : ℤ)
    (hq : q.natAbs ≤ 100 * (dimensionRuler source code₀ code₁).length) :
    q.natAbs < 2 ^ ((widthRuler source code₀ code₁).length - 1) := by
  rw [widthRuler_length, show (dimensionRuler source code₀ code₁).length + 10 - 1 =
    (dimensionRuler source code₀ code₁).length + 9 by omega]
  exact hq.trans_lt (coefficient_capacity _)

/-- The baseline denotes the exact integer reward for the emitted dimension. -/
theorem baselineWord_value (source code₀ code₁ : List Bool) :
    binarySignedValue (baselineWord source code₀ code₁) =
      ((dimensionRuler source code₀ code₁).length *
        (100 * (dimensionRuler source code₀ code₁).length +
          2 * (dimensionRuler source code₀ code₁).length) + 1 : ℤ) *
      2 ^ (100 * ((CircuitWords.first source).length +
        (dimensionRuler source code₀ code₁).length + 10)) := by
  exact BrouwerNashRewardMachine.reward_value (sourceDepthRuler source)
    (dimensionRuler source code₀ code₁)

/-- Specialize a three-word producer to a source and its two compiled color circuits. -/
def sourceFn (producer : List Bool → List Bool → List Bool → List Bool)
    (codes : Fin 2 → List Bool → List Bool) (source : List Bool) : List Bool :=
  producer source (codes 0 source) (codes 1 source)

/-- Successful circuit decodes recover the source-dependent program dimension. -/
theorem sourceDimension_length_of_decode (codes : Fin 2 → List Bool → List Bool)
    (source : List Bool) (gates₀ gates₁ : List (CircuitFormat.signature.Op × List ℕ))
    (hd₀ : CircuitFormat.decode? (codes 0 source) = some gates₀)
    (hd₁ : CircuitFormat.decode? (codes 1 source) = some gates₁) :
    (sourceFn dimensionRuler codes source).length =
      BrouwerNashLayout.dimension (CircuitWords.first source).length gates₀.length gates₁.length := by
  have h := dimensionRuler_length source (codes 0 source) (codes 1 source)
  change (sourceFn dimensionRuler codes source).length = BrouwerNashLayout.dimension
    (CircuitWords.first source).length (circuitUnaryPrefix (codes 0 source)).length
      (circuitUnaryPrefix (codes 1 source)).length at h
  rwa [circuitUnaryPrefix_length_of_decode _ _ hd₀,
    circuitUnaryPrefix_length_of_decode _ _ hd₁] at h

@[fun_prop] theorem sourceDepthRuler_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source : Input → List Bool} (hs : ComputableInPolyTime source input encBits) :
    ComputableInPolyTime (fun a => sourceDepthRuler (source a)) input encBits :=
  CircuitWords.first_polyTime.comp hs

@[fun_prop] theorem precisionRuler_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source : Input → List Bool} (hs : ComputableInPolyTime source input encBits) :
    ComputableInPolyTime (fun a => precisionRuler (source a)) input encBits := by
  exact (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 5)
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.length_bits_comp (sourceDepthRuler_polyTime hs))
        (ComputableInPolyTime.const 10)))

@[fun_prop] theorem arityRuler_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source : Input → List Bool} (hs : ComputableInPolyTime source input encBits) :
    ComputableInPolyTime (fun a => arityRuler (source a)) input encBits := by
  exact (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.length_bits_comp (sourceDepthRuler_polyTime hs))
        (ComputableInPolyTime.const 1)))

@[fun_prop] theorem globalRuler_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source : Input → List Bool} (hs : ComputableInPolyTime source input encBits) :
    ComputableInPolyTime (fun a => globalRuler (source a)) input encBits := by
  exact ComputableInPolyTime.bitsAppend
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 3)
        (ComputableInPolyTime.length_bits_comp (precisionRuler_polyTime hs))))
    (ComputableInPolyTime.const (List.replicate 11 false))

@[fun_prop] theorem cornerRuler_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits) :
    ComputableInPolyTime (fun a => cornerRuler (source a) (code₀ a) (code₁ a)) input encBits := by
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      ((ComputableInPolyTime.bitsReplicate true).comp
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
          (ComputableInPolyTime.length_bits_comp (arityRuler_polyTime hs))))
      (circuitUnaryPrefix_polyTime hc₀))
    (circuitUnaryPrefix_polyTime hc₁)

@[fun_prop] theorem sampleRuler_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits) :
    ComputableInPolyTime (fun a => sampleRuler (source a) (code₀ a) (code₁ a)) input encBits := by
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const (List.replicate 26 false))
      ((ComputableInPolyTime.bitsReplicate true).comp
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 12)
          (ComputableInPolyTime.length_bits_comp (sourceDepthRuler_polyTime hs)))))
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 4)
        (ComputableInPolyTime.length_bits_comp (cornerRuler_polyTime hs hc₀ hc₁))))

@[fun_prop] theorem unitsRuler_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits) :
    ComputableInPolyTime (fun a => unitsRuler (source a) (code₀ a) (code₁ a)) input encBits := by
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend (globalRuler_polyTime hs)
      ((ComputableInPolyTime.bitsReplicate true).comp
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 41)
          (ComputableInPolyTime.length_bits_comp (sampleRuler_polyTime hs hc₀ hc₁)))))
    (ComputableInPolyTime.const [false])

@[fun_prop] theorem dimensionRuler_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits) :
    ComputableInPolyTime (fun a => dimensionRuler (source a) (code₀ a) (code₁ a)) input encBits := by
  exact (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 123)
      (ComputableInPolyTime.length_bits_comp (unitsRuler_polyTime hs hc₀ hc₁)))

@[fun_prop] theorem widthRuler_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits) :
    ComputableInPolyTime (fun a => widthRuler (source a) (code₀ a) (code₁ a)) input encBits := by
  exact ComputableInPolyTime.bitsAppend (dimensionRuler_polyTime hs hc₀ hc₁)
    (ComputableInPolyTime.const (List.replicate 10 false))

@[fun_prop] theorem baselineWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits) :
    ComputableInPolyTime (fun a => baselineWord (source a) (code₀ a) (code₁ a)) input encBits := by
  exact BrouwerNashRewardMachine.reward_polyTime (sourceDepthRuler_polyTime hs)
    (dimensionRuler_polyTime hs hc₀ hc₁)

/-- Actual circuit producers compose through their ordinary native computation context. -/
@[fun_prop] theorem sourceFn_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source : Input → List Bool}
    {producer : List Bool → List Bool → List Bool → List Bool}
    (hp : ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) =>
      producer p.1 p.2.1 p.2.2) (encPair encBits (encPair encBits encBits)) encBits)
    (codes : Fin 2 → List Bool → List Bool)
    (hc : ∀ i, ComputableInPolyTime (codes i) encBits encBits)
    (hs : ComputableInPolyTime source input encBits) :
    ComputableInPolyTime (fun a => sourceFn producer codes (source a)) input encBits := by
  exact hp.comp (hs.prod (((hc 0).comp hs).prod ((hc 1).comp hs)))

end GameTheory.Complexity.Backend.BrouwerNashHeaders
