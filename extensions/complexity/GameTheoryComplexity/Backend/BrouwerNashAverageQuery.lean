module

public import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
public import GameTheoryComplexity.Backend.BrouwerNashProgram
public import GameTheoryComplexity.Backend.BrouwerNashHeaders
public import GameTheoryComplexity.Backend.BinarySignedIndicator
public import GameTheoryComplexity.Backend.BinaryUnaryEncoding
public import GameTheoryComplexity.Backend.BinarySignedFiniteSum

@[expose] public section

/-! Mean queries visit both component flags, all four corners, and all forty-one
samples in their original nested addition order. Captured source and circuit words
are charged together with each query ruler. -/
namespace GameTheory.Complexity.Backend.BrouwerNashAverageQuery
open Turing.MultiTapeTM
open scoped BigOperators

local notation "SourceContext" => (List Bool × (List Bool × List Bool))
local notation "sourceEncoding" => encPair encBits (encPair encBits encBits)
local notation "FlagContext" => (SourceContext × (List Bool × (List Bool × List Bool)))
local notation "flagEncoding" =>
  encPair sourceEncoding (encPair encBits (encPair encBits encBits))
local notation "CornerContext" => (SourceContext × (List Bool × List Bool))
local notation "cornerEncoding" => encPair sourceEncoding (encPair encBits encBits)
local notation "SampleContext" => (SourceContext × List Bool)
local notation "sampleEncoding" => encPair sourceEncoding encBits

/-- One component flag contributes a signed indicator with its original padded scalar. -/
def flagWord (axis : Bool) (ordinal corner sample action source code₀ code₁ : List Bool) : List Bool :=
  let sampleRuler := BrouwerNashHeaders.sampleRuler source code₀ code₁
  let input := BrouwerNashHeaders.globalRuler source ++
    List.replicate (sample.length * sampleRuler.length) true ++ sampleRuler.drop 16 ++
    List.replicate (corner.length * 4) true ++ List.replicate (ordinal.length * 2) true ++ [false]
  let units := binaryLengthWord (BrouwerNashHeaders.unitsRuler source code₀ code₁)
  let flag := decide (ordinal.length % 2 = 1)
  let scalar := if (if axis then flag else !flag) then
    [false, false, false] ++ units else [false, false] ++ units
  binarySignedIndicator ![action, input, scalar]

/-- Both component flags retain ascending false-bit ordinal rulers. -/
def flagsWord (axis : Bool) (corner sample action source code₀ code₁ : List Bool) : List Bool :=
  binarySignedFiniteSum (fun ordinal (context : FlagContext) =>
    flagWord axis ordinal context.2.2.2 context.2.2.1 context.2.1
      context.1.1 context.1.2.1 context.1.2.2) 2
    ((source, (code₀, code₁)), (action, (sample, corner)))

/-- The four corners retain the two-flag scan at each corner. -/
def cornersWord (axis : Bool) (sample action source code₀ code₁ : List Bool) : List Bool :=
  binarySignedFiniteSum (fun corner (context : CornerContext) =>
    flagsWord axis corner context.2.2 context.2.1
      context.1.1 context.1.2.1 context.1.2.2) 4
    ((source, (code₀, code₁)), (action, sample))

/-- All forty-one samples retain their complete corner and flag contributions. -/
def samplesWord (axis : Bool) (action source code₀ code₁ : List Bool) : List Bool :=
  binarySignedFiniteSum (fun sample (context : SampleContext) =>
    cornersWord axis sample context.2 context.1.1 context.1.2.1 context.1.2.2) 41
    ((source, (code₀, code₁)), action)

/-- Query both shared means from source, circuit codes, output, and action words. -/
def coefficientWord (source code₀ code₁ out action : List Bool) : List Bool :=
  let precision := BrouwerNashHeaders.precisionRuler source
  binarySignedAdd
    (if out.length = (precision ++ List.replicate 5 false).length then
      samplesWord false action source code₀ code₁ else [])
    (if out.length = (precision ++ List.replicate 6 false).length then
      samplesWord true action source code₀ code₁ else [])

@[fun_prop] theorem flagWord_polyTime (axis : Bool) {Input : Type} {input : Input ↪ List Bool}
    {ordinal corner sample action source code₀ code₁ : Input → List Bool}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime corner input encBits)
    (ht : ComputableInPolyTime sample input encBits)
    (ha : ComputableInPolyTime action input encBits)
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits) :
    ComputableInPolyTime (fun a => flagWord axis (ordinal a) (corner a) (sample a)
      (action a) (source a) (code₀ a) (code₁ a)) input encBits := by
  have hsample := BrouwerNashHeaders.sampleRuler_polyTime hs hc₀ hc₁
  have hstart := ComputableInPolyTime.bitsAppend (BrouwerNashHeaders.globalRuler_polyTime hs)
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp ht)
        (ComputableInPolyTime.length_bits_comp hsample)))
  have hdrop := ComputableInPolyTime.bitsDropWithInput hsample (ComputableInPolyTime.const 16)
  have hcorner := (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp hc)
      (ComputableInPolyTime.const 4))
  have hflag := (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp hi)
      (ComputableInPolyTime.const 2))
  have hindex := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsAppend hstart hdrop) hcorner)
        hflag) (ComputableInPolyTime.const [false])
  have hunits := binaryLengthWord_polyTime.comp
    (BrouwerNashHeaders.unitsRuler_polyTime hs hc₀ hc₁)
  have hmod := ComputableInPolyTime.unary_mod.comp
    ((ComputableInPolyTime.length_bits_comp hi).prod (ComputableInPolyTime.const 2))
  have hodd := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.decide_eq encUnary).comp (hmod.tidy.prod (.const 1)))
  have hcondition : ComputableInPolyTime (fun a =>
      if axis then decide ((ordinal a).length % 2 = 1)
      else !(decide ((ordinal a).length % 2 = 1))) input encBool := by
    cases axis
    · exact (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bool_not).comp hodd
    · exact hodd
  have hscalar := hcondition.ite
    (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [false, false, false]) hunits)
    (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [false, false]) hunits)
  have hargs : ComputableInPolyTime (fun a : Input =>
      ![action a,
        BrouwerNashHeaders.globalRuler (source a) ++
          List.replicate ((sample a).length *
            (BrouwerNashHeaders.sampleRuler (source a) (code₀ a) (code₁ a)).length) true ++
          (BrouwerNashHeaders.sampleRuler (source a) (code₀ a) (code₁ a)).drop 16 ++
          List.replicate ((corner a).length * 4) true ++
          List.replicate ((ordinal a).length * 2) true ++ [false],
        if (if axis then decide ((ordinal a).length % 2 = 1)
          else !(decide ((ordinal a).length % 2 = 1))) then
          [false, false, false] ++ binaryLengthWord
            (BrouwerNashHeaders.unitsRuler (source a) (code₀ a) (code₁ a))
        else [false, false] ++ binaryLengthWord
          (BrouwerNashHeaders.unitsRuler (source a) (code₀ a) (code₁ a))])
      input (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact ha
    · simpa only [Matrix.cons_val_succ', Matrix.cons_val_zero', Function.comp_apply] using hindex
    · simpa only [Matrix.cons_val_succ', Matrix.cons_val_zero', Function.comp_apply] using hscalar
  exact binarySignedIndicator_polyTime.comp hargs

private theorem flagCallback_polyTime (axis : Bool) :
    ComputableInPolyTime (fun p : FlagContext × List Bool =>
      flagWord axis p.2 p.1.2.2.2 p.1.2.2.1 p.1.2.1
        p.1.1.1 p.1.1.2.1 p.1.1.2.2)
      (encPair flagEncoding encBits) encBits := by
  have hcontext := ComputableInPolyTime.fst flagEncoding encBits
  have hi := ComputableInPolyTime.snd flagEncoding encBits
  exact flagWord_polyTime axis hi hcontext.snd'.snd'.snd' hcontext.snd'.snd'.fst'
    hcontext.snd'.fst' hcontext.fst'.fst' hcontext.fst'.snd'.fst' hcontext.fst'.snd'.snd'

@[fun_prop] theorem flagsWord_polyTime (axis : Bool) {Input : Type} {input : Input ↪ List Bool}
    {corner sample action source code₀ code₁ : Input → List Bool}
    (hc : ComputableInPolyTime corner input encBits)
    (ht : ComputableInPolyTime sample input encBits)
    (ha : ComputableInPolyTime action input encBits)
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits) :
    ComputableInPolyTime (fun a => flagsWord axis (corner a) (sample a)
      (action a) (source a) (code₀ a) (code₁ a)) input encBits :=
  binarySignedFiniteSum_polyTime (flagCallback_polyTime axis) 2
    ((hs.prod (hc₀.prod hc₁)).prod (ha.prod (ht.prod hc)))

private theorem cornerCallback_polyTime (axis : Bool) :
    ComputableInPolyTime (fun p : CornerContext × List Bool =>
      flagsWord axis p.2 p.1.2.2 p.1.2.1 p.1.1.1 p.1.1.2.1 p.1.1.2.2)
      (encPair cornerEncoding encBits) encBits := by
  have hcontext := ComputableInPolyTime.fst cornerEncoding encBits
  have hc := ComputableInPolyTime.snd cornerEncoding encBits
  exact flagsWord_polyTime axis hc hcontext.snd'.snd' hcontext.snd'.fst'
    hcontext.fst'.fst' hcontext.fst'.snd'.fst' hcontext.fst'.snd'.snd'

@[fun_prop] theorem cornersWord_polyTime (axis : Bool) {Input : Type} {input : Input ↪ List Bool}
    {sample action source code₀ code₁ : Input → List Bool}
    (ht : ComputableInPolyTime sample input encBits)
    (ha : ComputableInPolyTime action input encBits)
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits) :
    ComputableInPolyTime (fun a => cornersWord axis (sample a) (action a)
      (source a) (code₀ a) (code₁ a)) input encBits :=
  binarySignedFiniteSum_polyTime (cornerCallback_polyTime axis) 4
    ((hs.prod (hc₀.prod hc₁)).prod (ha.prod ht))

private theorem sampleCallback_polyTime (axis : Bool) :
    ComputableInPolyTime (fun p : SampleContext × List Bool =>
      cornersWord axis p.2 p.1.2 p.1.1.1 p.1.1.2.1 p.1.1.2.2)
      (encPair sampleEncoding encBits) encBits := by
  have hcontext := ComputableInPolyTime.fst sampleEncoding encBits
  have ht := ComputableInPolyTime.snd sampleEncoding encBits
  exact cornersWord_polyTime axis ht hcontext.snd'
    hcontext.fst'.fst' hcontext.fst'.snd'.fst' hcontext.fst'.snd'.snd'

@[fun_prop] theorem samplesWord_polyTime (axis : Bool) {Input : Type} {input : Input ↪ List Bool}
    {action source code₀ code₁ : Input → List Bool}
    (ha : ComputableInPolyTime action input encBits)
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits) :
    ComputableInPolyTime (fun a => samplesWord axis (action a) (source a) (code₀ a) (code₁ a))
      input encBits :=
  binarySignedFiniteSum_polyTime (sampleCallback_polyTime axis) 41
    ((hs.prod (hc₀.prod hc₁)).prod ha)

/-- Every source, circuit word, and query ruler contributes to the native running-time bound. -/
@[fun_prop] theorem coefficientWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => coefficientWord (source a) (code₀ a) (code₁ a)
      (out a) (action a)) input encBits := by
  have hp := BrouwerNashHeaders.precisionRuler_polyTime hs
  have hguard (offset : ℕ) := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.decide_eq encUnary).comp
      ((ComputableInPolyTime.length_bits_comp ho).tidy.prod
        (ComputableInPolyTime.length_bits_comp (ComputableInPolyTime.bitsAppend hp
          (ComputableInPolyTime.const (List.replicate offset false)))).tidy))
  exact (binarySignedAdd_polyTime
    ((hguard 5).ite (samplesWord_polyTime false ha hs hc₀ hc₁) (ComputableInPolyTime.const []))
    ((hguard 6).ite (samplesWord_polyTime true ha hs hc₀ hc₁) (ComputableInPolyTime.const []))).of_enc_eq
      (fun a => by simp only [coefficientWord, Function.comp_apply, decide_eq_true_eq])

private theorem scalar_two (r : List Bool) :
    binarySignedValue (false :: false :: binaryLengthWord r) = 2 * (r.length : ℤ) := by
  change ((2 * ofBits (binaryLengthWord r) : ℕ) : ℤ) = _
  rw [binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]

private theorem scalar_four (r : List Bool) :
    binarySignedValue (false :: false :: false :: binaryLengthWord r) =
      4 * (r.length : ℤ) := by
  change ((2 * (2 * ofBits (binaryLengthWord r)) : ℕ) : ℤ) = _
  rw [binaryLengthWord_value, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem flagTerm_value (axis : Bool) (action source code₀ code₁ : List Bool)
    (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
    binarySignedValue (flagWord axis (List.replicate flag.val false)
      (List.replicate corner.val false) (List.replicate t.val false) action source code₀ code₁) =
      if action.length / 2 = BrouwerNashLayout.sampleBase (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
          BrouwerNashLayout.minimum (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length corner flag ∧
          action.length % 2 = 1
      then 2 * (BrouwerNashLayout.units (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) *
        BrouwerNashProgram.componentWeight (if axis then 1 else 0) flag else 0 := by
  change binarySignedValue (binarySignedIndicator ![action,
    BrouwerNashHeaders.globalRuler source ++
      List.replicate ((List.replicate t.val false).length *
        (BrouwerNashHeaders.sampleRuler source code₀ code₁).length) true ++
      (BrouwerNashHeaders.sampleRuler source code₀ code₁).drop 16 ++
      List.replicate ((List.replicate corner.val false).length * 4) true ++
      List.replicate ((List.replicate flag.val false).length * 2) true ++ [false],
    if (if axis then decide ((List.replicate flag.val false).length % 2 = 1)
      else !(decide ((List.replicate flag.val false).length % 2 = 1))) then
      [false, false, false] ++ binaryLengthWord
        (BrouwerNashHeaders.unitsRuler source code₀ code₁)
    else [false, false] ++ binaryLengthWord
        (BrouwerNashHeaders.unitsRuler source code₀ code₁)]) = _
  rw [binarySignedIndicator_value]
  simp only [List.length_append, List.length_replicate, List.length_drop,
    List.length_cons, List.length_nil, BrouwerNashHeaders.globalRuler_length,
    BrouwerNashHeaders.sampleRuler_length]
  change (if action.length / 2 =
      BrouwerNashLayout.globalCount (CircuitWords.first source).length +
      t.val * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
      (BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length - 16) +
      corner.val * 4 + flag.val * 2 + 1 ∧ action.length % 2 = 1 then _ else 0) = _
  have hlen : BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length - 16 =
      BrouwerNashLayout.minimumBase (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    simp only [BrouwerNashLayout.sampleWidth, BrouwerNashLayout.minimumBase,
      BrouwerNashLayout.colorBase, BrouwerNashLayout.weightBase]
    omega
  rw [hlen]
  have hindex : BrouwerNashLayout.globalCount (CircuitWords.first source).length +
      t.val * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
      BrouwerNashLayout.minimumBase (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
      corner.val * 4 + flag.val * 2 + 1 =
      BrouwerNashLayout.sampleBase (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
      BrouwerNashLayout.minimum (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length corner flag := by
    simp only [BrouwerNashLayout.sampleBase, BrouwerNashLayout.minimum,
      BrouwerNashLayout.minimumTemporary]
    omega
  rw [hindex]
  cases axis <;> fin_cases flag <;>
    simp only [BrouwerNashProgram.componentWeight] <;> norm_num <;>
    simp only [scalar_two, scalar_four, BrouwerNashHeaders.unitsRuler_length] <;>
    congr 1 <;> ring_nf

private theorem samples_value (axis : Bool) (action source code₀ code₁ : List Bool) :
    binarySignedValue (samplesWord axis action source code₀ code₁) =
      ∑ t : Fin 41, ∑ corner : Fin 4, ∑ flag : Fin 2,
        if action.length / 2 = BrouwerNashLayout.sampleBase (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
            BrouwerNashLayout.minimum (CircuitWords.first source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length corner flag ∧
            action.length % 2 = 1
        then 2 * (BrouwerNashLayout.units (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) *
          BrouwerNashProgram.componentWeight (if axis then 1 else 0) flag else 0 := by
  simp only [samplesWord, binarySignedFiniteSum_value, cornersWord, flagsWord]
  simp only [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro corner _
  apply Finset.sum_congr rfl
  intro flag _
  exact flagTerm_value axis action source code₀ code₁ t corner flag

private theorem samples_coefficients (axis : Bool) (action source code₀ code₁ : List Bool)
    (r : Fin (BrouwerNashLayout.dimension (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (samplesWord axis action source code₀ code₁) =
      (BrouwerNashProgram.averageGate (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
        (if axis then 1 else 0)).coefficients r := by
  rw [samples_value, hr]
  rcases finProdFinEquiv.surjective r with ⟨⟨a, bit⟩, rfl⟩
  by_cases hb : bit = 0
  · subst bit
    have hzero : (finProdFinEquiv (a, (0 : Fin 2))).val % 2 = 0 := by
      change (0 + 2 * a.val) % 2 = 0
      omega
    simp only [hzero, Nat.zero_ne_one, and_false, ite_false, Finset.sum_const_zero]
    dsimp only [BrouwerNashProgram.averageGate, GameTheory.Finite.BimatrixArithmeticGate.gate]
    exact (GameTheory.Finite.BimatrixArithmeticGate.coefficients_zero _ 0 a).symm
  · have hb : bit = 1 := by
      apply Fin.ext
      have hlt := bit.isLt
      have hne : bit.val ≠ 0 := fun h => hb (Fin.ext h)
      omega
    subst bit
    have hmod : (finProdFinEquiv (a, (1 : Fin 2))).val % 2 = 1 := by
      change (1 + 2 * a.val) % 2 = 1
      omega
    have hdiv : (finProdFinEquiv (a, (1 : Fin 2))).val / 2 = a.val := by
      change (1 + 2 * a.val) / 2 = a.val
      omega
    dsimp only [BrouwerNashProgram.averageGate, GameTheory.Finite.BimatrixArithmeticGate.gate]
    rw [GameTheory.Finite.BimatrixArithmeticGate.coefficients_one, add_zero]
    simp only [hmod, hdiv, and_true]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro corner _
    apply Finset.sum_congr rfl
    intro flag _
    have hb := BrouwerNashLayout.sample_lt_dimension (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
      (BrouwerNashLayout.minimum (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length corner flag)
      (BrouwerNashProgram.minimum_lt_sampleWidth _ _ _ corner flag false)
    have he : a.val =
        BrouwerNashLayout.sampleBase (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
        BrouwerNashLayout.minimum (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length corner flag ↔
        a = BrouwerNashProgram.slot (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
        (BrouwerNashLayout.sampleBase (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
        BrouwerNashLayout.minimum (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length corner flag) := by
      rw [Fin.ext_iff, BrouwerNashProgram.slot_val _ _ _ _ hb]
    simp only [he]

/-- Both mean slots agree with the canonical gate coefficients; every other output gives zero. -/
theorem coefficientWord_value (out action source code₀ code₁ : List Bool)
    (r : Fin (BrouwerNashLayout.dimension (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord source code₀ code₁ out action) =
      (if out.length = BrouwerNashLayout.average (CircuitWords.first source).length 0 then
        (BrouwerNashProgram.averageGate (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length 0).coefficients r
      else 0) +
      (if out.length = BrouwerNashLayout.average (CircuitWords.first source).length 1 then
        (BrouwerNashProgram.averageGate (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length 1).coefficients r
      else 0) := by
  change binarySignedValue (binarySignedAdd
    (if out.length = (BrouwerNashHeaders.precisionRuler source ++ List.replicate 5 false).length then
      samplesWord false action source code₀ code₁ else [])
    (if out.length = (BrouwerNashHeaders.precisionRuler source ++ List.replicate 6 false).length then
      samplesWord true action source code₀ code₁ else [])) = _
  rw [binarySignedAdd_value, BrouwerNashCoefficientQuery.select_value,
    BrouwerNashCoefficientQuery.select_value,
    samples_coefficients false _ _ _ _ r hr, samples_coefficients true _ _ _ _ r hr]
  simp only [List.length_append, List.length_replicate, BrouwerNashHeaders.precisionRuler_length]
  rfl

end GameTheory.Complexity.Backend.BrouwerNashAverageQuery
