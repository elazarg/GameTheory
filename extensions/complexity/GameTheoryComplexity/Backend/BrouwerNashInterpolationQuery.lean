module

public import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
public import GameTheoryComplexity.Backend.BrouwerNashHeaders
public import GameTheoryComplexity.Backend.BinarySignedFiniteSum
public import GameTheoryComplexity.Backend.BinaryUnaryEncoding
public import GameTheoryComplexity.Backend.BrouwerNashQueryRegions

@[expose] public section

/-! Interpolation and weighted-minimum queries retain both signed input contributions.
Fixed sample scans use false ordinal rulers, and query families retain their original
right-fold addition order, including aliases and truncated circuit headers. -/
namespace GameTheory.Complexity.Backend.BrouwerNashInterpolationQuery
open Turing.MultiTapeTM
open BrouwerNashCoefficientQuery
open scoped BigOperators

local notation "QueryContext" =>
  ((List Bool × (List Bool × List Bool)) × (List Bool × (List Bool × List Bool)))
local notation "queryEncoding" =>
  encPair (encPair encBits (encPair encBits encBits))
    (encPair encBits (encPair encBits encBits))
local notation "SumContext" =>
  ((List Bool × (List Bool × List Bool)) × (List Bool × List Bool))
local notation "sumEncoding" =>
  encPair (encPair encBits (encPair encBits encBits)) (encPair encBits encBits)

private def depthR (v : QueryContext) : List Bool := BrouwerNashHeaders.sourceDepthRuler v.1.1
private def dimR (v : QueryContext) : List Bool :=
  BrouwerNashHeaders.dimensionRuler v.1.1 v.1.2.1 v.1.2.2
private def cornerR (v : QueryContext) : List Bool :=
  BrouwerNashHeaders.cornerRuler v.1.1 v.1.2.1 v.1.2.2
private def arityR (v : QueryContext) : List Bool := BrouwerNashHeaders.arityRuler v.1.1
private def startR (v : QueryContext) : List Bool :=
  BrouwerNashHeaders.globalRuler v.1.1 ++ List.replicate
    (v.2.1.length * (BrouwerNashHeaders.sampleRuler v.1.1 v.1.2.1 v.1.2.2).length) true
private def weightR (v : QueryContext) : List Bool :=
  [false, false] ++ List.replicate ((depthR v).length * 12) true
private def remainderR (axis : Fin 2) (v : QueryContext) : List Bool :=
  if (depthR v).length = 0 then List.replicate axis.val false
  else [false] ++ List.replicate ((depthR v).length * (2 + 2 * axis.val)) true
private def weightOffset (n : ℕ) (v : QueryContext) : List Bool :=
  weightR v ++ List.replicate n false
private def firstR (stage : Fin 8) : QueryContext → List Bool :=
  match stage.val with
  | 1 | 7 => remainderR 1
  | 2 | 3 => weightOffset 0
  | _ => remainderR 0
private def secondR (stage : Fin 8) : QueryContext → List Bool :=
  match stage.val with
  | 2 => weightOffset 1
  | 3 => weightOffset 2
  | 5 => weightOffset 4
  | 7 => remainderR 0
  | _ => remainderR 1
private def capacity (negative : Bool) (v : QueryContext) : List Bool :=
  negative :: false :: binaryLengthWord (dimR v)
private def point (input : QueryContext → List Bool) (negative : Bool)
    (v : QueryContext) : List Bool :=
  binarySignedIndicator ![v.2.2.2, startR v ++ input v, capacity negative v]
private def interpolationTerm (stage : Fin 8) (v : QueryContext) : List Bool :=
  let coefficient := if stage.val < 2 then
    binarySignedAdd [false, false, true] (point (firstR stage) true v)
    else binarySignedAdd (point (firstR stage) false v) (point (secondR stage) true v)
  if v.2.2.1.length = (startR v ++ weightOffset stage.val v).length then coefficient else []

/-- One sample's fixed interpolation stage, with both input references retained. -/
def indexedInterpolationWord (stage : Fin 8) (ordinal : List Bool) (context : SumContext) : List Bool :=
  let source := context.1.1
  let code₀ := context.1.2.1
  let code₁ := context.1.2.2
  let depth := BrouwerNashHeaders.sourceDepthRuler source
  let dim := BrouwerNashHeaders.dimensionRuler source code₀ code₁
  let start := BrouwerNashHeaders.globalRuler source ++ List.replicate
    (ordinal.length * (BrouwerNashHeaders.sampleRuler source code₀ code₁).length) true
  let weight := [false, false] ++ List.replicate (depth.length * 12) true
  let remainder (axis : Fin 2) := if depth.length = 0 then List.replicate axis.val false
    else [false] ++ List.replicate (depth.length * (2 + 2 * axis.val)) true
  let first := match stage.val with
    | 1 | 7 => remainder 1
    | 2 | 3 => weight ++ List.replicate 0 false
    | _ => remainder 0
  let second := match stage.val with
    | 2 => weight ++ List.replicate 1 false
    | 3 => weight ++ List.replicate 2 false
    | 5 => weight ++ List.replicate 4 false
    | 7 => remainder 0
    | _ => remainder 1
  let point (ruler : List Bool) (negative : Bool) := binarySignedIndicator
    ![context.2.2, start ++ ruler, negative :: false :: binaryLengthWord dim]
  let coefficient := if stage.val < 2 then binarySignedAdd [false, false, true] (point first true)
    else binarySignedAdd (point first false) (point second true)
  if context.2.1.length = (start ++ (weight ++ List.replicate stage.val false)).length then coefficient else []

private theorem indexedInterpolationWord_eq (stage : Fin 8) (ordinal : List Bool) (context : SumContext) :
    indexedInterpolationWord stage ordinal context =
      interpolationTerm stage (context.1, (ordinal, context.2)) := by
  fin_cases stage <;> rfl

/-- A fixed interpolation stage scans all forty-one sample placements. -/
def interpolationWord (stage : Fin 8) (source code₀ code₁ out action : List Bool) : List Bool :=
  binarySignedFiniteSum (indexedInterpolationWord stage) 41 ((source, (code₀, code₁)), (out, action))

private def minimumR (v : QueryContext) : List Bool :=
  weightOffset 8 v ++ List.replicate ((cornerR v).length * 4) true
private def minimumOffset (corner : Fin 4) (flag : Fin 2) (n : ℕ) (v : QueryContext) : List Bool :=
  minimumR v ++ List.replicate (4 * corner.val + 2 * flag.val + n) false
private def colorR (corner : Fin 4) (flag : Fin 2) (v : QueryContext) : List Bool :=
  weightOffset 8 v ++ List.replicate ((cornerR v).length * corner.val) true ++
    (if flag.val = 0 then arityR v else arityR v ++ arityR v ++ circuitUnaryPrefix v.1.2.1)
private def lastColorR (corner : Fin 4) (flag : Fin 2) (v : QueryContext) : List Bool :=
  colorR corner flag v ++ (circuitUnaryPrefix (if flag.val = 0 then v.1.2.1 else v.1.2.2)).tail
private def minimumSecondR (corner : Fin 4) (flag : Fin 2) (temporary : Bool) : QueryContext → List Bool :=
  if temporary then lastColorR corner flag else minimumOffset corner flag 0
private def minimumTerm (corner : Fin 4) (flag : Fin 2) (temporary : Bool) (v : QueryContext) : List Bool :=
  if v.2.2.1.length = (startR v ++ minimumOffset corner flag (if temporary then 0 else 1) v).length then
    binarySignedAdd (point (weightOffset ((![3, 5, 6, 7] : Fin 4 → ℕ) corner)) false v)
      (point (minimumSecondR corner flag temporary) true v) else []

/-- One sample's weighted-minimum subtraction, including a possibly aliased input. -/
def indexedMinimumWord (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    (ordinal : List Bool) (context : SumContext) : List Bool :=
  let source := context.1.1
  let code₀ := context.1.2.1
  let code₁ := context.1.2.2
  let depth := BrouwerNashHeaders.sourceDepthRuler source
  let dim := BrouwerNashHeaders.dimensionRuler source code₀ code₁
  let start := BrouwerNashHeaders.globalRuler source ++ List.replicate
    (ordinal.length * (BrouwerNashHeaders.sampleRuler source code₀ code₁).length) true
  let weight := [false, false] ++ List.replicate (depth.length * 12) true
  let weightOffset (n : ℕ) := weight ++ List.replicate n false
  let minimum := weightOffset 8 ++ List.replicate
    ((BrouwerNashHeaders.cornerRuler source code₀ code₁).length * 4) true
  let minimumOffset (n : ℕ) := minimum ++ List.replicate (4 * corner.val + 2 * flag.val + n) false
  let color := weightOffset 8 ++ List.replicate
    ((BrouwerNashHeaders.cornerRuler source code₀ code₁).length * corner.val) true ++
    (if flag.val = 0 then BrouwerNashHeaders.arityRuler source else
      BrouwerNashHeaders.arityRuler source ++ BrouwerNashHeaders.arityRuler source ++ circuitUnaryPrefix code₀)
  let lastColor := color ++ (circuitUnaryPrefix (if flag.val = 0 then code₀ else code₁)).tail
  let second := if temporary then lastColor else minimumOffset 0
  let point (ruler : List Bool) (negative : Bool) := binarySignedIndicator
    ![context.2.2, start ++ ruler, negative :: false :: binaryLengthWord dim]
  let coefficient := binarySignedAdd (point (weightOffset ((![3, 5, 6, 7] : Fin 4 → ℕ) corner)) false)
    (point second true)
  if context.2.1.length = (start ++ minimumOffset (if temporary then 0 else 1)).length then coefficient else []

private theorem indexedMinimumWord_eq (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    (ordinal : List Bool) (context : SumContext) :
    indexedMinimumWord corner flag temporary ordinal context =
      minimumTerm corner flag temporary (context.1, (ordinal, context.2)) := by
  cases temporary <;> rfl

/-- A weighted-minimum stage scans its concrete placements in all forty-one samples. -/
def minimumWord (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    (source code₀ code₁ out action : List Bool) : List Bool :=
  binarySignedFiniteSum (indexedMinimumWord corner flag temporary) 41
    ((source, (code₀, code₁)), (out, action))

private theorem depthR_polyTime {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => depthR (context a)) input encBits :=
  BrouwerNashHeaders.sourceDepthRuler_polyTime hc.fst'.fst'

private theorem dimR_polyTime {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => dimR (context a)) input encBits :=
  BrouwerNashHeaders.dimensionRuler_polyTime hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd'

private theorem cornerR_polyTime {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => cornerR (context a)) input encBits :=
  BrouwerNashHeaders.cornerRuler_polyTime hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd'

private theorem arityR_polyTime {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => arityR (context a)) input encBits :=
  BrouwerNashHeaders.arityRuler_polyTime hc.fst'.fst'

private theorem startR_polyTime {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => startR (context a)) input encBits := by
  exact ComputableInPolyTime.bitsAppend (BrouwerNashHeaders.globalRuler_polyTime hc.fst'.fst')
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp hc.snd'.fst')
        (ComputableInPolyTime.length_bits_comp (BrouwerNashHeaders.sampleRuler_polyTime
          hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd'))))

private theorem weightR_polyTime {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => weightR (context a)) input encBits := by
  exact ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [false, false])
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp (depthR_polyTime hc))
        (ComputableInPolyTime.const 12)))

private theorem remainderR_polyTime (axis : Fin 2) {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => remainderR axis (context a)) input encBits := by
  have hlength := ComputableInPolyTime.length_bits_comp (depthR_polyTime hc)
  have heq := hlength.decide_eq' (ComputableInPolyTime.const 0)
  have hno := ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [false])
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' hlength (ComputableInPolyTime.const (2 + 2 * axis.val))))
  exact (heq.ite (ComputableInPolyTime.const (List.replicate axis.val false)) hno).of_enc_eq
    (fun a => by simp only [remainderR, Function.comp_apply, decide_eq_true_eq])

private theorem weightOffset_polyTime (n : ℕ) {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => weightOffset n (context a)) input encBits :=
  ComputableInPolyTime.bitsAppend (weightR_polyTime hc) (ComputableInPolyTime.const (List.replicate n false))

private theorem firstR_polyTime (stage : Fin 8) {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => firstR stage (context a)) input encBits := by
  fin_cases stage <;> first | exact remainderR_polyTime _ hc | exact weightOffset_polyTime _ hc

private theorem secondR_polyTime (stage : Fin 8) {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => secondR stage (context a)) input encBits := by
  fin_cases stage <;> first | exact remainderR_polyTime _ hc | exact weightOffset_polyTime _ hc

private theorem capacity_polyTime (negative : Bool) {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => capacity negative (context a)) input encBits := by
  have h := ComputableInPolyTime.bitsCons (ComputableInPolyTime.const negative)
    (ComputableInPolyTime.bitsCons (ComputableInPolyTime.const false)
      (binaryLengthWord_polyTime.comp (dimR_polyTime hc)))
  exact h.of_enc_eq (fun a => by dsimp only [capacity, Function.comp_apply])

private theorem point_polyTime {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} {ruler : QueryContext → List Bool}
    (hc : ComputableInPolyTime context input queryEncoding)
    (hr : ComputableInPolyTime (fun a => ruler (context a)) input encBits) (negative : Bool) :
    ComputableInPolyTime (fun a => point ruler negative (context a)) input encBits := by
  have hposition := ComputableInPolyTime.bitsAppend (startR_polyTime hc) hr
  have hcapacity := capacity_polyTime negative hc
  have hargs : ComputableInPolyTime
      (fun a : Input => ![(context a).2.2.2, startR (context a) ++ ruler (context a), capacity negative (context a)])
      input (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hc.snd'.snd'.snd'
    · exact hposition
    · simpa only [Matrix.cons_val_succ', Matrix.cons_val_zero', Function.comp_apply] using hcapacity
  exact binarySignedIndicator_polyTime.comp hargs

private theorem interpolationTerm_polyTime (stage : Fin 8) {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => interpolationTerm stage (context a)) input encBits := by
  have hvalue : ComputableInPolyTime (fun a : Input => if stage.val < 2 then
      binarySignedAdd [false, false, true] (point (firstR stage) true (context a))
      else binarySignedAdd (point (firstR stage) false (context a))
        (point (secondR stage) true (context a))) input encBits := by
    by_cases hs : stage.val < 2
    · simpa only [hs, ↓reduceIte] using binarySignedAdd_polyTime (ComputableInPolyTime.const [false, false, true])
        (point_polyTime hc (firstR_polyTime stage hc) true)
    · simpa only [hs, ↓reduceIte] using binarySignedAdd_polyTime
        (point_polyTime hc (firstR_polyTime stage hc) false)
        (point_polyTime hc (secondR_polyTime stage hc) true)
  have houtput := ComputableInPolyTime.bitsAppend (startR_polyTime hc) (weightOffset_polyTime stage.val hc)
  have heq := (ComputableInPolyTime.length_bits_comp hc.snd'.snd'.fst').decide_eq'
    (ComputableInPolyTime.length_bits_comp houtput)
  exact (heq.ite hvalue (ComputableInPolyTime.const [])).of_enc_eq
    (fun a => by simp only [interpolationTerm, decide_eq_true_eq])

/-- The indexed stage charges the ordinal and every captured query word. -/
@[fun_prop] theorem indexedInterpolationWord_polyTime (stage : Fin 8)
    {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → SumContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input sumEncoding) :
    ComputableInPolyTime (fun a => indexedInterpolationWord stage (ordinal a) (context a)) input encBits := by
  have hquery := hc.fst'.prod (hi.prod hc.snd')
  exact (interpolationTerm_polyTime stage hquery).of_enc_eq (fun a => by
    rw [indexedInterpolationWord_eq])

private theorem interpolationCallback_polyTime (stage : Fin 8) :
    ComputableInPolyTime (fun p : SumContext × List Bool => indexedInterpolationWord stage p.2 p.1)
      (encPair sumEncoding encBits) encBits :=
  indexedInterpolationWord_polyTime stage (ComputableInPolyTime.snd sumEncoding encBits)
    (ComputableInPolyTime.fst sumEncoding encBits)

/-- Sample scans charge all five original query-word producers. -/
@[fun_prop] theorem interpolationWord_polyTime (stage : Fin 8)
    {Input : Type} {input : Input ↪ List Bool} {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits) (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits) (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => interpolationWord stage (source a) (code₀ a) (code₁ a) (out a) (action a))
      input encBits := by
  have hcontext := (hs.prod (hc₀.prod hc₁)).prod (ho.prod ha)
  exact binarySignedFiniteSum_polyTime (interpolationCallback_polyTime stage) 41 hcontext

private theorem minimumR_polyTime {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => minimumR (context a)) input encBits := by
  exact ComputableInPolyTime.bitsAppend (weightOffset_polyTime 8 hc)
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp (cornerR_polyTime hc))
        (ComputableInPolyTime.const 4)))

private theorem minimumOffset_polyTime (corner : Fin 4) (flag : Fin 2) (n : ℕ)
    {Input : Type} {input : Input ↪ List Bool} {context : Input → QueryContext}
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => minimumOffset corner flag n (context a)) input encBits :=
  ComputableInPolyTime.bitsAppend (minimumR_polyTime hc)
    (ComputableInPolyTime.const (List.replicate (4 * corner.val + 2 * flag.val + n) false))

private theorem colorR_polyTime (corner : Fin 4) (flag : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {context : Input → QueryContext}
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => colorR corner flag (context a)) input encBits := by
  have hbase := ComputableInPolyTime.bitsAppend (weightOffset_polyTime 8 hc)
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp (cornerR_polyTime hc))
        (ComputableInPolyTime.const corner.val)))
  have harity := arityR_polyTime hc
  have htail : ComputableInPolyTime (fun a : Input => if flag.val = 0 then arityR (context a)
      else arityR (context a) ++ arityR (context a) ++ circuitUnaryPrefix (context a).1.2.1)
      input encBits := by
    by_cases hf : flag.val = 0
    · simpa only [hf, ↓reduceIte] using harity
    · simpa only [hf, ↓reduceIte] using ComputableInPolyTime.bitsAppend
        (ComputableInPolyTime.bitsAppend harity harity) (circuitUnaryPrefix_polyTime hc.fst'.snd'.fst')
  have h := ComputableInPolyTime.bitsAppend hbase htail
  exact h.of_enc_eq (fun a => by dsimp only [colorR, Function.comp_apply])

private theorem lastColorR_polyTime (corner : Fin 4) (flag : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {context : Input → QueryContext}
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => lastColorR corner flag (context a)) input encBits := by
  have hcode : ComputableInPolyTime (fun a : Input => if flag.val = 0 then (context a).1.2.1
      else (context a).1.2.2) input encBits := by
    by_cases hf : flag.val = 0
    · simpa only [hf, ↓reduceIte] using hc.fst'.snd'.fst'
    · simpa only [hf, ↓reduceIte] using hc.fst'.snd'.snd'
  have hprefix := circuitUnaryPrefix_polyTime hcode
  have htail := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hprefix
  have h := ComputableInPolyTime.bitsAppend (colorR_polyTime corner flag hc) htail
  exact h.of_enc_eq (fun a => by dsimp only [lastColorR, Function.comp_apply])

private theorem minimumSecondR_polyTime (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    {Input : Type} {input : Input ↪ List Bool} {context : Input → QueryContext}
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => minimumSecondR corner flag temporary (context a)) input encBits := by
  cases temporary
  · exact minimumOffset_polyTime corner flag 0 hc
  · exact lastColorR_polyTime corner flag hc

private theorem minimumTerm_polyTime (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    {Input : Type} {input : Input ↪ List Bool} {context : Input → QueryContext}
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => minimumTerm corner flag temporary (context a)) input encBits := by
  have hvalue := binarySignedAdd_polyTime
    (point_polyTime hc (weightOffset_polyTime ((![3, 5, 6, 7] : Fin 4 → ℕ) corner) hc) false)
    (point_polyTime hc (minimumSecondR_polyTime corner flag temporary hc) true)
  have houtput := ComputableInPolyTime.bitsAppend (startR_polyTime hc)
    (minimumOffset_polyTime corner flag (if temporary then 0 else 1) hc)
  have heq := (ComputableInPolyTime.length_bits_comp hc.snd'.snd'.fst').decide_eq'
    (ComputableInPolyTime.length_bits_comp houtput)
  exact (heq.ite hvalue (ComputableInPolyTime.const [])).of_enc_eq
    (fun a => by simp only [minimumTerm, decide_eq_true_eq])

/-- The indexed minimum charges its ordinal and all captured query words. -/
@[fun_prop] theorem indexedMinimumWord_polyTime (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → SumContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input sumEncoding) :
    ComputableInPolyTime (fun a => indexedMinimumWord corner flag temporary (ordinal a) (context a))
      input encBits := by
  have hquery := hc.fst'.prod (hi.prod hc.snd')
  exact (minimumTerm_polyTime corner flag temporary hquery).of_enc_eq
    (fun a => by rw [indexedMinimumWord_eq])

private theorem minimumCallback_polyTime (corner : Fin 4) (flag : Fin 2) (temporary : Bool) :
    ComputableInPolyTime
      (fun p : SumContext × List Bool => indexedMinimumWord corner flag temporary p.2 p.1)
      (encPair sumEncoding encBits) encBits :=
  indexedMinimumWord_polyTime corner flag temporary (ComputableInPolyTime.snd sumEncoding encBits)
    (ComputableInPolyTime.fst sumEncoding encBits)

/-- Weighted-minimum scans charge source, both code words and both query rulers. -/
@[fun_prop] theorem minimumWord_polyTime (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    {Input : Type} {input : Input ↪ List Bool} {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits) (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits) (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => minimumWord corner flag temporary
      (source a) (code₀ a) (code₁ a) (out a) (action a)) input encBits := by
  have hcontext := (hs.prod (hc₀.prod hc₁)).prod (ho.prod ha)
  exact binarySignedFiniteSum_polyTime (minimumCallback_polyTime corner flag temporary) 41 hcontext

/-- Enumerate the sixteen minimum gates in corner, flag, and temporary-output order. -/
def minimumQuery (index : Fin 16) (context : SumContext) : List Bool :=
  minimumWord ⟨index.val / 4, by omega⟩
    ⟨(index.val / 2) % 2, Nat.mod_lt _ (by decide)⟩ (decide (index.val % 2 = 0))
    context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2

private def queries : List (SumContext → List Bool) :=
  List.ofFn (fun stage : Fin 8 => fun context : SumContext => interpolationWord stage
    context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) ++ List.ofFn minimumQuery

/-- All fixed families retain their exact forty-one-sample scans and right-fold addition order. -/
def coefficientWord (source code₀ code₁ out action : List Bool) : List Bool :=
  let queries : List (SumContext → List Bool) :=
    List.ofFn (fun stage : Fin 8 => fun context : SumContext => interpolationWord stage
      context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) ++
    List.ofFn (fun index : Fin 16 => fun context : SumContext =>
      minimumWord ⟨index.val / 4, by omega⟩
        ⟨(index.val / 2) % 2, Nat.mod_lt _ (by decide)⟩ (decide (index.val % 2 = 0))
        context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2)
  binarySignedQuerySum queries ((source, (code₀, code₁)), (out, action))

private theorem coefficientWord_eq (source code₀ code₁ out action : List Bool) :
    coefficientWord source code₀ code₁ out action =
      binarySignedQuerySum queries ((source, (code₀, code₁)), (out, action)) := rfl

/-- The complete query certificate charges source, both code words, output and action. -/
@[fun_prop] theorem coefficientWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits) (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits) (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => coefficientWord (source a) (code₀ a) (code₁ a) (out a) (action a))
      input encBits := by
  have hroot : ComputableInPolyTime (fun context : SumContext => context) sumEncoding sumEncoding := .id'
  have hq : ∀ query ∈ queries, ComputableInPolyTime query sumEncoding encBits := by
    intro query hquery
    simp only [queries, List.mem_append, List.mem_ofFn] at hquery
    rcases hquery with ⟨stage, rfl⟩ | ⟨index, rfl⟩
    · exact interpolationWord_polyTime stage hroot.fst'.fst' hroot.fst'.snd'.fst'
        hroot.fst'.snd'.snd' hroot.snd'.fst' hroot.snd'.snd'
    · exact minimumWord_polyTime _ _ _ hroot.fst'.fst' hroot.fst'.snd'.fst'
        hroot.fst'.snd'.snd' hroot.snd'.fst' hroot.snd'.snd'
  have hcontext := (hs.prod (hc₀.prod hc₁)).prod (ho.prod ha)
  exact (binarySignedQuerySum_polyTime queries hq hcontext).of_enc_eq
    (fun a => by rw [coefficientWord_eq])

private theorem capacity_value (negative : Bool) (v : QueryContext) :
    binarySignedValue (capacity negative v) =
      if negative then -2 * ((dimR v).length : ℤ) else 2 * ((dimR v).length : ℤ) := by
  cases negative
  · change ((2 * ofBits (binaryLengthWord (dimR v)) : ℕ) : ℤ) = 2 * ((dimR v).length : ℤ)
    rw [binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]
  · change -((2 * ofBits (binaryLengthWord (dimR v)) : ℕ) : ℤ) = -2 * ((dimR v).length : ℤ)
    rw [binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]
    ring

private theorem startR_length (v : QueryContext) :
    (startR v).length = BrouwerNashLayout.globalCount (CircuitWords.first v.1.1).length +
      v.2.1.length * BrouwerNashLayout.sampleWidth (CircuitWords.first v.1.1).length
        (circuitUnaryPrefix v.1.2.1).length (circuitUnaryPrefix v.1.2.2).length := by
  simp only [startR, List.length_append, List.length_replicate,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length]

private theorem weightR_length (v : QueryContext) :
    (weightR v).length = BrouwerNashLayout.weightBase (CircuitWords.first v.1.1).length := by
  simp only [weightR, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, depthR, BrouwerNashHeaders.sourceDepthRuler, BrouwerNashLayout.weightBase]
  omega

private theorem remainderR_length (axis : Fin 2) (v : QueryContext) :
    (remainderR axis v).length = BrouwerNashLayout.remainder (CircuitWords.first v.1.1).length axis
      (CircuitWords.first v.1.1).length := by
  have hd : (depthR v).length = (CircuitWords.first v.1.1).length := rfl
  by_cases hz : (CircuitWords.first v.1.1).length = 0
  · simp only [remainderR, hd, hz, ↓reduceIte, List.length_replicate,
      BrouwerNashLayout.remainder, BrouwerNashLayout.jitter]
  · simp only [remainderR, hd, hz, ↓reduceIte, List.length_append,
      List.length_cons, List.length_nil, List.length_replicate, BrouwerNashLayout.remainder]
    have hb : 1 ≤ (CircuitWords.first v.1.1).length := by omega
    fin_cases axis <;> norm_num <;> omega

private theorem subtraction_coefficients {k : ℕ} (a z : Fin k) (C : ℤ) (r : Fin (k * 2)) :
    (GameTheory.Finite.BimatrixMinGate.subtractionGate C a z).coefficients r =
      (if r = finProdFinEquiv (a, 1) then C else 0) +
      (if r = finProdFinEquiv (z, 1) then -C else 0) := by
  rcases finProdFinEquiv.surjective r with ⟨⟨j, bit⟩, rfl⟩
  fin_cases bit <;> simp [GameTheory.Finite.BimatrixMinGate.subtractionGate,
    GameTheory.Finite.BimatrixMinGate.subtractionCoefficients,
    GameTheory.Finite.BimatrixArithmeticGate.gate,
    GameTheory.Finite.BimatrixArithmeticGate.coefficients, sub_eq_add_neg]
  split_ifs <;> rfl

private theorem complement_coefficients {k : ℕ} (a : Fin k) (r : Fin (k * 2)) :
    (GameTheory.Finite.BimatrixInterpolationGate.complementGate a).coefficients r =
      2 + (if r = finProdFinEquiv (a, 1) then -2 * (k : ℤ) else 0) := by
  rcases finProdFinEquiv.surjective r with ⟨⟨j, bit⟩, rfl⟩
  fin_cases bit <;> simp [GameTheory.Finite.BimatrixInterpolationGate.complementGate,
    GameTheory.Finite.BimatrixInterpolationGate.complementCoefficients,
    GameTheory.Finite.BimatrixArithmeticGate.gate,
    GameTheory.Finite.BimatrixArithmeticGate.coefficients, add_comm]
variable (source code₀ code₁ out action : List Bool)
local notation "b" => List.length (CircuitWords.first source)
local notation "ell₀" => List.length (circuitUnaryPrefix code₀)
local notation "ell₁" => List.length (circuitUnaryPrefix code₁)
local notation "k" => BrouwerNashLayout.dimension b ell₀ ell₁

private theorem point_index (input : QueryContext → List Bool) (negative : Bool)
    (t : Fin 41) (a : ℕ) (ha : a < BrouwerNashLayout.sampleWidth b ell₀ ell₁)
    (hlen : (input ((source, (code₀, code₁)), (List.replicate t.val false, (out, action)))).length = a)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (point input negative
      ((source, (code₀, code₁)), (List.replicate t.val false, (out, action)))) =
      if r = finProdFinEquiv (BrouwerNashProgram.sampleRef b ell₀ ell₁ t a, 1) then
        (if negative then -2 * (k : ℤ) else 2 * (k : ℤ)) else 0 := by
  let v : QueryContext := ((source, (code₀, code₁)), (List.replicate t.val false, (out, action)))
  have hs : (startR v).length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t := by
    rw [startR_length]
    simp only [v, List.length_replicate]
    rfl
  have habs : (startR v ++ input v).length =
      (BrouwerNashProgram.sampleRef b ell₀ ell₁ t a).val := by
    rw [List.length_append, hs, hlen]
    exact (BrouwerNashProgram.slot_val _ _ _ _
      (BrouwerNashLayout.sample_lt_dimension _ _ _ t a ha)).symm
  have he := binarySignedIndicator_index action (startR v ++ input v) (capacity negative v)
    r (BrouwerNashProgram.sampleRef b ell₀ ell₁ t a) hr habs
  change binarySignedValue (binarySignedIndicator ![action, startR v ++ input v,
    capacity negative v]) = _
  rw [he, capacity_value]
  have hd : (dimR v).length = k := by
    rw [dimR, BrouwerNashHeaders.dimensionRuler_length]
  rw [hd]

private theorem interpolationTerm_coefficients (t : Fin 41) (stage : Fin 8)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (interpolationTerm stage
      ((source, (code₀, code₁)), (List.replicate t.val false, (out, action)))) =
      if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.weightBase b + stage.val then
        (BrouwerNashProgram.interpolationGate b ell₀ ell₁ t stage.val).coefficients r
      else 0 := by
  let v : QueryContext := ((source, (code₀, code₁)), (List.replicate t.val false, (out, action)))
  have hs : (startR v).length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t := by
    rw [startR_length]
    simp only [v, List.length_replicate]
    rfl
  have hw : (weightR v).length = BrouwerNashLayout.weightBase b := weightR_length v
  have hrem (axis : Fin 2) :
      BrouwerNashLayout.remainder b axis b < BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
    fin_cases axis <;>
      simp only [BrouwerNashLayout.remainder, BrouwerNashLayout.jitter,
        BrouwerNashLayout.sampleWidth] <;>
      split_ifs <;> norm_num <;> omega
  have hweight (n : ℕ) (hn : n < 8) :
      BrouwerNashLayout.weightBase b + n < BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
    simp only [BrouwerNashLayout.weightBase, BrouwerNashLayout.sampleWidth]
    omega
  have hp (axis : Fin 2) (negative : Bool) := point_index source code₀ code₁ out action
    (remainderR axis) negative t (BrouwerNashLayout.remainder b axis b) (hrem axis)
    (remainderR_length axis v) r hr
  have hwp (n : ℕ) (hn : n < 8) (negative : Bool) := point_index source code₀ code₁ out action
    (weightOffset n) negative t (BrouwerNashLayout.weightBase b + n) (hweight n hn)
    (by rw [weightOffset, List.length_append, hw, List.length_replicate]) r hr
  change binarySignedValue (if out.length = (startR v ++ weightOffset stage.val v).length then _ else []) = _
  rw [select_value]
  have hguard : (startR v ++ weightOffset stage.val v).length =
      BrouwerNashLayout.sampleBase b ell₀ ell₁ t + BrouwerNashLayout.weightBase b + stage.val := by
    rw [List.length_append, hs, weightOffset, List.length_append, hw, List.length_replicate]
    omega
  rw [hguard]
  apply congrArg (fun z : ℤ => if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
    BrouwerNashLayout.weightBase b + stage.val then z else 0)
  fin_cases stage <;>
    simp only [firstR, secondR, ite_true, ite_false, Nat.reduceLT,
      binarySignedAdd_value, BrouwerNashProgram.interpolationGate,
      complement_coefficients, subtraction_coefficients]
  all_goals first
  | rw [hp 0 true]; rfl
  | rw [hp 1 true]; rfl
  | rw [hwp 0 (by omega) false, hwp 1 (by omega) true]; rfl
  | rw [hwp 0 (by omega) false, hwp 2 (by omega) true]; rfl
  | rw [hp 0 false, hp 1 true]; rfl
  | rw [hp 0 false, hwp 4 (by omega) true]; rfl
  | rw [hp 1 false, hp 0 true]; rfl

/-- Each fixed interpolation family selects precisely its allocated canonical coefficients. -/
theorem interpolationWord_value (stage : Fin 8) (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (interpolationWord stage source code₀ code₁ out action) =
      ∑ t : Fin 41, if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.weightBase b + stage.val then
        (BrouwerNashProgram.interpolationGate b ell₀ ell₁ t stage.val).coefficients r else 0 := by
  rw [interpolationWord, binarySignedFiniteSum_value, ← Fin.sum_univ_eq_sum_range]
  simp only [indexedInterpolationWord_eq]
  apply Finset.sum_congr rfl
  intro t _
  exact interpolationTerm_coefficients source code₀ code₁ out action t stage r hr

private theorem minimumR_length (v : QueryContext) :
    (minimumR v).length = BrouwerNashLayout.minimumBase (CircuitWords.first v.1.1).length
      (circuitUnaryPrefix v.1.2.1).length (circuitUnaryPrefix v.1.2.2).length := by
  simp only [minimumR, weightOffset, List.length_append, weightR_length, List.length_replicate,
    cornerR, BrouwerNashHeaders.cornerRuler_length, BrouwerNashLayout.minimumBase,
    BrouwerNashLayout.colorBase]
  omega

private theorem lastColorR_length (corner : Fin 4) (flag : Fin 2) (v : QueryContext) :
    (lastColorR corner flag v).length =
      BrouwerNashLayout.colorGate (CircuitWords.first v.1.1).length
        (circuitUnaryPrefix v.1.2.1).length (circuitUnaryPrefix v.1.2.2).length corner flag +
          ((if flag.val = 0 then circuitUnaryPrefix v.1.2.1 else circuitUnaryPrefix v.1.2.2).length - 1) := by
  fin_cases flag <;>
    simp only [lastColorR, colorR, List.length_append, weightOffset, weightR_length,
      List.length_replicate, List.length_tail, ite_true, ite_false, Nat.reduceEqDiff,
      cornerR, arityR, BrouwerNashHeaders.cornerRuler_length, BrouwerNashHeaders.arityRuler_length,
      BrouwerNashLayout.colorGate, BrouwerNashLayout.colorInput,
      BrouwerNashLayout.colorBase, BrouwerNashLayout.arity, BrouwerNashLayout.weightBase]
  all_goals ring

private theorem minimumTerm_coefficients (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (temporary : Bool) (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (minimumTerm corner flag temporary
      ((source, (code₀, code₁)), (List.replicate t.val false, (out, action)))) =
      if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
            (if temporary then 0 else 1) then
        (BrouwerNashProgram.minimumGate b ell₀ ell₁ t corner flag temporary).coefficients r
      else 0 := by
  let v : QueryContext := ((source, (code₀, code₁)), (List.replicate t.val false, (out, action)))
  let a := if temporary then BrouwerNashLayout.colorGate b ell₀ ell₁ corner flag +
    ((if flag.val = 0 then ell₀ else ell₁) - 1) else
      BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag
  have hs : (startR v).length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t := by
    rw [startR_length]
    simp only [v, List.length_replicate]
    rfl
  have hweight : BrouwerNashLayout.weight b corner <
      BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
    fin_cases corner <;> simp only [BrouwerNashLayout.weight, BrouwerNashLayout.weightBase,
      BrouwerNashLayout.sampleWidth] <;> norm_num <;> omega
  have ha : a < BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
    cases temporary <;> fin_cases corner <;> fin_cases flag <;>
      simp only [a, ite_true, ite_false, Nat.reduceEqDiff, BrouwerNashLayout.colorGate,
        BrouwerNashLayout.colorInput, BrouwerNashLayout.minimumTemporary,
        BrouwerNashLayout.minimumBase, BrouwerNashLayout.colorBase, BrouwerNashLayout.weightBase,
        BrouwerNashLayout.arity, BrouwerNashLayout.cornerWidth, BrouwerNashLayout.sampleWidth] <;>
      norm_num <;> omega
  have hfirst : (weightOffset ((![3, 5, 6, 7] : Fin 4 → ℕ) corner) v).length =
      BrouwerNashLayout.weight b corner := by
    rw [weightOffset, List.length_append, weightR_length, List.length_replicate]
    rfl
  have hsecond : (minimumSecondR corner flag temporary v).length = a := by
    cases temporary
    · simp only [minimumSecondR, Bool.false_eq_true, ite_false]
      rw [minimumOffset, List.length_append, minimumR_length,
        List.length_replicate]
      change BrouwerNashLayout.minimumBase b ell₀ ell₁ +
        (4 * corner.val + 2 * flag.val + 0) =
          BrouwerNashLayout.minimumBase b ell₀ ell₁ + 2 * (2 * corner.val + flag.val)
      omega
    · simp only [minimumSecondR, ite_true]
      rw [lastColorR_length]
      simp only [a, ite_true, v]
      fin_cases flag <;> rfl
  have hp := point_index source code₀ code₁ out action
    (weightOffset ((![3, 5, 6, 7] : Fin 4 → ℕ) corner)) false t
    (BrouwerNashLayout.weight b corner) hweight hfirst r hr
  have hz := point_index source code₀ code₁ out action (minimumSecondR corner flag temporary)
    true t a ha hsecond r hr
  change binarySignedValue (if out.length = (startR v ++ minimumOffset corner flag (if temporary then 0 else 1) v).length then _ else []) = _
  rw [select_value]
  have hguard : (startR v ++ minimumOffset corner flag (if temporary then 0 else 1) v).length =
      BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
        BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
          (if temporary then 0 else 1) := by
    rw [List.length_append, hs, minimumOffset, List.length_append, minimumR_length,
      List.length_replicate]
    change BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      (BrouwerNashLayout.minimumBase b ell₀ ell₁ +
        (4 * corner.val + 2 * flag.val + (if temporary then 0 else 1))) = _
    simp only [BrouwerNashLayout.minimumTemporary]
    omega
  rw [hguard]
  apply congrArg (fun z : ℤ => if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
    BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
      (if temporary then 0 else 1) then z else 0)
  rw [binarySignedAdd_value, hp, hz]
  cases temporary <;>
    simp only [BrouwerNashProgram.minimumGate, ite_true, ite_false, Bool.false_eq_true,
      subtraction_coefficients, a, neg_mul]

/-- Each weighted-minimum family selects its exact canonical signed subtraction coefficients. -/
theorem minimumWord_value (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (minimumWord corner flag temporary source code₀ code₁ out action) =
      ∑ t : Fin 41, if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
            (if temporary then 0 else 1) then
        (BrouwerNashProgram.minimumGate b ell₀ ell₁ t corner flag temporary).coefficients r
      else 0 := by
  rw [minimumWord, binarySignedFiniteSum_value, ← Fin.sum_univ_eq_sum_range]
  simp only [indexedMinimumWord_eq]
  apply Finset.sum_congr rfl
  intro t _
  exact minimumTerm_coefficients source code₀ code₁ out action t corner flag temporary r hr

private theorem sample_position_injective (offset : ℕ) :
    Function.Injective (fun t : Fin 41 => BrouwerNashLayout.sampleBase b ell₀ ell₁ t + offset) := by
  intro s t he
  apply Fin.ext
  apply Nat.mul_right_cancel (show 0 < BrouwerNashLayout.sampleWidth b ell₀ ell₁ by
    simp only [BrouwerNashLayout.sampleWidth]; omega)
  dsimp only [BrouwerNashLayout.sampleBase] at he
  omega

/-- A written interpolation output reads exactly its own canonical gate coefficient. -/
theorem interpolationWord_at (stage : Fin 8) (t : Fin 41) (r : Fin (k * 2))
    (hr : action.length = r.val)
    (hout : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.weightBase b + stage.val) :
    binarySignedValue (interpolationWord stage source code₀ code₁ out action) =
      (BrouwerNashProgram.interpolationGate b ell₀ ell₁ t stage.val).coefficients r := by
  rw [interpolationWord_value source code₀ code₁ out action stage r hr]
  have heq (s : Fin 41) : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ s +
      BrouwerNashLayout.weightBase b + stage.val ↔ s = t := by
    constructor
    · intro hs
      apply sample_position_injective source code₀ code₁
        (BrouwerNashLayout.weightBase b + stage.val)
      dsimp only
      omega
    · rintro rfl
      exact hout
  simp only [heq]
  simp

/-- Interpolation families contribute zero outside their allocated outputs. -/
theorem interpolationWord_zero (stage : Fin 8) (r : Fin (k * 2)) (hr : action.length = r.val)
    (hout : ∀ t : Fin 41, out.length ≠ BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.weightBase b + stage.val) :
    binarySignedValue (interpolationWord stage source code₀ code₁ out action) = 0 := by
  rw [interpolationWord_value source code₀ code₁ out action stage r hr]
  apply Finset.sum_eq_zero
  intro t _
  exact ite_eq_right (hout t)

/-- A weighted-minimum output reads exactly its own canonical gate coefficient. -/
theorem minimumWord_at (corner : Fin 4) (flag : Fin 2) (temporary : Bool) (t : Fin 41)
    (r : Fin (k * 2)) (hr : action.length = r.val)
    (hout : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
        (if temporary then 0 else 1)) :
    binarySignedValue (minimumWord corner flag temporary source code₀ code₁ out action) =
      (BrouwerNashProgram.minimumGate b ell₀ ell₁ t corner flag temporary).coefficients r := by
  rw [minimumWord_value source code₀ code₁ out action corner flag temporary r hr]
  have heq (s : Fin 41) : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ s +
      BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
        (if temporary then 0 else 1) ↔ s = t := by
    constructor
    · intro hs
      apply sample_position_injective source code₀ code₁
        (BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
          (if temporary then 0 else 1))
      dsimp only
      omega
    · rintro rfl
      exact hout
  simp only [heq]
  simp

/-- Weighted-minimum families contribute zero outside their allocated outputs. -/
theorem minimumWord_zero (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    (r : Fin (k * 2)) (hr : action.length = r.val)
    (hout : ∀ t : Fin 41, out.length ≠ BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
        (if temporary then 0 else 1)) :
    binarySignedValue (minimumWord corner flag temporary source code₀ code₁ out action) =
      0 := by
  rw [minimumWord_value source code₀ code₁ out action corner flag temporary r hr]
  apply Finset.sum_eq_zero
  intro t _
  exact ite_eq_right (hout t)

private theorem minimumQuery_position (index : Fin 16) :
    2 * (2 * (index.val / 4) + (index.val / 2) % 2) +
      (if decide (index.val % 2 = 0) then 0 else 1) = index.val := by
  by_cases hp : index.val % 2 = 0
  · simp only [hp, decide_true, ite_true, add_zero]
    omega
  · simp only [hp, decide_false, Bool.false_eq_true, ite_false]
    omega

/-- The fixed right fold preserves every signed coefficient without normalizing its representation. -/
theorem coefficientWord_value (source code₀ code₁ out action : List Bool) :
    binarySignedValue (coefficientWord source code₀ code₁ out action) =
      (∑ stage : Fin 8, binarySignedValue (interpolationWord stage source code₀ code₁ out action)) +
      ∑ index : Fin 16, binarySignedValue (minimumQuery index ((source, (code₀, code₁)), (out, action))) := by
  rw [coefficientWord_eq, binarySignedQuerySum_value]
  simp only [queries, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply]

private theorem minimumQuery_value (index : Fin 16) (r : Fin (k * 2))
    (hr : action.length = r.val) :
    binarySignedValue (minimumQuery index ((source, (code₀, code₁)), (out, action))) =
      ∑ t : Fin 41, if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.minimumBase b ell₀ ell₁ + index.val then
        (BrouwerNashProgram.minimumGate b ell₀ ell₁ t
          ⟨index.val / 4, by omega⟩ ⟨(index.val / 2) % 2, Nat.mod_lt _ (by decide)⟩
            (decide (index.val % 2 = 0))).coefficients r else 0 := by
  rw [minimumQuery, minimumWord_value source code₀ code₁ out action _ _ _ r hr]
  apply Finset.sum_congr rfl
  intro t _
  have he : BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.minimumTemporary b ell₀ ell₁
        ⟨index.val / 4, by omega⟩ ⟨(index.val / 2) % 2, Nat.mod_lt _ (by decide)⟩ +
          (if decide (index.val % 2 = 0) then 0 else 1) =
        BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.minimumBase b ell₀ ell₁ + index.val := by
    dsimp only [BrouwerNashLayout.minimumTemporary]
    have hp := minimumQuery_position index
    omega
  rw [he]

private theorem interpolation_local_lt (stage : Fin 8) :
    BrouwerNashLayout.weightBase b + stage.val < BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
  have hs := stage.isLt
  dsimp only [BrouwerNashLayout.weightBase, BrouwerNashLayout.sampleWidth]
  omega

private theorem minimum_local_lt (index : Fin 16) :
    BrouwerNashLayout.minimumBase b ell₀ ell₁ + index.val <
      BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
  have hs := index.isLt
  dsimp only [BrouwerNashLayout.minimumBase, BrouwerNashLayout.colorBase,
    BrouwerNashLayout.weightBase, BrouwerNashLayout.sampleWidth]
  omega

private theorem same_local (t t' : Fin 41) (i i' : ℕ)
    (hi : i < BrouwerNashLayout.sampleWidth b ell₀ ell₁)
    (hi' : i' < BrouwerNashLayout.sampleWidth b ell₀ ell₁)
    (ho : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t + i)
    (he : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t' + i') : i = i' :=
  (BrouwerNashQueryRegions.sampleOutput_injective b ell₀ ell₁ t t' i i'
    hi hi' (ho.symm.trans he)).2

/-- On an interpolation output, the combined fixed families emit its canonical coefficient. -/
theorem coefficientWord_interpolation_at (stage : Fin 8) (t : Fin 41) (r : Fin (k * 2))
    (hr : action.length = r.val)
    (ho : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      (BrouwerNashLayout.weightBase b + stage.val)) :
    binarySignedValue (coefficientWord source code₀ code₁ out action) =
      (BrouwerNashProgram.interpolationGate b ell₀ ell₁ t stage.val).coefficients r := by
  rw [coefficientWord_value]
  have hm (index : Fin 16) :
      binarySignedValue (minimumQuery index ((source, (code₀, code₁)), (out, action))) = 0 := by
    rw [minimumQuery_value source code₀ code₁ out action index r hr]
    apply Finset.sum_eq_zero
    intro t' _
    apply ite_eq_right
    intro he
    have hx := same_local source code₀ code₁ out t t' _ _
      (interpolation_local_lt source code₀ code₁ stage)
      (minimum_local_lt source code₀ code₁ index) ho (by omega)
    have hs := stage.isLt
    dsimp only [BrouwerNashLayout.minimumBase, BrouwerNashLayout.colorBase] at hx
    omega
  simp only [hm, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single stage]
  · apply interpolationWord_at source code₀ code₁ out action stage t r hr
    omega
  · intro stage' _ hne
    apply interpolationWord_zero source code₀ code₁ out action stage' r hr
    intro t' he
    have hx := same_local source code₀ code₁ out t t' _ _
      (interpolation_local_lt source code₀ code₁ stage)
      (interpolation_local_lt source code₀ code₁ stage') ho (by omega)
    exact hne (Fin.ext (by omega))
  · simp

private theorem minimumQuery_at (index : Fin 16) (t : Fin 41) (r : Fin (k * 2))
    (hr : action.length = r.val)
    (ho : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      (BrouwerNashLayout.minimumBase b ell₀ ell₁ + index.val)) :
    binarySignedValue (minimumQuery index ((source, (code₀, code₁)), (out, action))) =
      (BrouwerNashProgram.minimumGate b ell₀ ell₁ t
        ⟨index.val / 4, by omega⟩ ⟨(index.val / 2) % 2, Nat.mod_lt _ (by decide)⟩
          (decide (index.val % 2 = 0))).coefficients r := by
  rw [minimumQuery]
  apply minimumWord_at source code₀ code₁ out action _ _ _ t r hr
  dsimp only [BrouwerNashLayout.minimumTemporary]
  have hp := minimumQuery_position index
  omega

private theorem coefficientWord_minimumIndex_at (index : Fin 16) (t : Fin 41)
    (r : Fin (k * 2)) (hr : action.length = r.val)
    (ho : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      (BrouwerNashLayout.minimumBase b ell₀ ell₁ + index.val)) :
    binarySignedValue (coefficientWord source code₀ code₁ out action) =
      (BrouwerNashProgram.minimumGate b ell₀ ell₁ t
        ⟨index.val / 4, by omega⟩ ⟨(index.val / 2) % 2, Nat.mod_lt _ (by decide)⟩
          (decide (index.val % 2 = 0))).coefficients r := by
  rw [coefficientWord_value]
  have hz (stage : Fin 8) :
      binarySignedValue (interpolationWord stage source code₀ code₁ out action) = 0 := by
    apply interpolationWord_zero source code₀ code₁ out action stage r hr
    intro t' he
    have hx := same_local source code₀ code₁ out t t' _ _
      (minimum_local_lt source code₀ code₁ index)
      (interpolation_local_lt source code₀ code₁ stage) ho (by omega)
    have hs := stage.isLt
    dsimp only [BrouwerNashLayout.minimumBase, BrouwerNashLayout.colorBase] at hx
    omega
  simp only [hz, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single index]
  · exact minimumQuery_at source code₀ code₁ out action index t r hr ho
  · intro index' _ hne
    rw [minimumQuery_value source code₀ code₁ out action index' r hr]
    apply Finset.sum_eq_zero
    intro t' _
    apply ite_eq_right
    intro he
    have hx := same_local source code₀ code₁ out t t' _ _
      (minimum_local_lt source code₀ code₁ index)
      (minimum_local_lt source code₀ code₁ index') ho (by omega)
    exact hne (Fin.ext (by omega))
  · simp

/-- On a weighted-minimum output, the combined fixed families emit its canonical coefficient. -/
theorem coefficientWord_minimum_at (corner : Fin 4) (flag : Fin 2) (temporary : Bool)
    (t : Fin 41) (r : Fin (k * 2)) (hr : action.length = r.val)
    (ho : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      (BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
        (if temporary then 0 else 1))) :
    binarySignedValue (coefficientWord source code₀ code₁ out action) =
      (BrouwerNashProgram.minimumGate b ell₀ ell₁ t corner flag temporary).coefficients r := by
  have hc := corner.isLt
  have hf := flag.isLt
  let index : Fin 16 := ⟨4 * corner.val + 2 * flag.val + (if temporary then 0 else 1),
    by cases temporary <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega⟩
  have hd : index.val / 4 = corner.val := by
    dsimp only [index]
    cases temporary <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hflag : (index.val / 2) % 2 = flag.val := by
    dsimp only [index]
    cases temporary <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  have ht : decide (index.val % 2 = 0) = temporary := by
    dsimp only [index]
    cases temporary
    · apply decide_eq_false_iff_not.mpr
      change (4 * corner.val + 2 * flag.val + 1) % 2 ≠ 0
      omega
    · apply decide_eq_true_eq.mpr
      change (4 * corner.val + 2 * flag.val + 0) % 2 = 0
      omega
  have hout : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      (BrouwerNashLayout.minimumBase b ell₀ ell₁ + index.val) := by
    dsimp only [index]
    simp only [BrouwerNashLayout.minimumTemporary] at ho
    omega
  have hv := coefficientWord_minimumIndex_at source code₀ code₁ out action index t r hr hout
  have hec : (⟨index.val / 4, by omega⟩ : Fin 4) = corner := Fin.ext hd
  have hef : (⟨(index.val / 2) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = flag := Fin.ext hflag
  simpa only [hec, hef, ht] using hv

/-- Fixed families emit zero outside the interpolation and minimum intervals of every sample. -/
theorem coefficientWord_eq_zero_of_outside (r : Fin (k * 2)) (hr : action.length = r.val)
    (hno : ∀ t : Fin 41,
      ¬ (BrouwerNashLayout.sampleBase b ell₀ ell₁ t + BrouwerNashLayout.weightBase b ≤
        out.length ∧ out.length < BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.colorBase b) ∧
      ¬ (BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
        BrouwerNashLayout.minimumBase b ell₀ ell₁ ≤ out.length ∧
        out.length < BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.sampleWidth b ell₀ ell₁)) :
    binarySignedValue (coefficientWord source code₀ code₁ out action) = 0 := by
  rw [coefficientWord_value]
  have hz (stage : Fin 8) :
      binarySignedValue (interpolationWord stage source code₀ code₁ out action) = 0 := by
    apply interpolationWord_zero source code₀ code₁ out action stage r hr
    intro t he
    apply (hno t).1
    have hs := stage.isLt
    dsimp only [BrouwerNashLayout.colorBase]
    omega
  have hm (index : Fin 16) :
      binarySignedValue (minimumQuery index ((source, (code₀, code₁)), (out, action))) = 0 := by
    rw [minimumQuery_value source code₀ code₁ out action index r hr]
    apply Finset.sum_eq_zero
    intro t _
    apply ite_eq_right
    intro he
    apply (hno t).2
    have hx := minimum_local_lt source code₀ code₁ index
    omega
  simp only [hz, hm, Finset.sum_const_zero, add_zero]

end GameTheory.Complexity.Backend.BrouwerNashInterpolationQuery
