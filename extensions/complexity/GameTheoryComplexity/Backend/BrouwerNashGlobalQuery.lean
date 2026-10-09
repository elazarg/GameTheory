import GameTheoryComplexity.Backend.BrouwerNashAverageQuery
import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
import GameTheoryComplexity.Backend.BrouwerNashHeaders
import GameTheoryComplexity.Backend.BinaryIndexedLookup
import GameTheoryComplexity.Backend.BinarySignedIndicator
import GameTheoryComplexity.Backend.BinaryUnaryEncoding

/-! Polynomial-time coefficient queries for the shared affine feedback and scaling blocks.
Unary output scans use the source precision as their bounded clock. Signed addition retains
all contributions before the canonical fixed-width program writer serializes them. -/
namespace GameTheory.Complexity.Backend.BrouwerNashGlobalQuery
open _root_.Complexity _root_.Complexity.Cobham
open BrouwerNashCoefficientQuery

private def alphaPredecessor (r : List Bool) : List Bool :=
  caseBit₀ (lenEqFlag r []) [false, false] ([false, false, false] ++ r)

private theorem alphaPredecessor_cobham :
    Cobham fun v : Fin 1 → List Bool => alphaPredecessor (v 0) :=
  Cobham.iteFn (lenEqFlag_mem (.proj 0) (Cobham.const [])) (Cobham.const [false, false])
    (appendFn (Cobham.const [false, false, false]) (.proj 0))

private def alphaTest (v : Fin 6 → List Bool) : List Bool :=
  andBit (lenEqFlag (v 1) ([false, false, false, false] ++ v 0))
    (notBit (lenLeFlag (v 0) (BrouwerNashHeaders.precisionRuler ![v 3, v 4, v 5])))

private def alphaTerm (v : Fin 6 → List Bool) : List Bool :=
  binarySignedIndicator ![v 2, alphaPredecessor (v 0),
    false :: binaryLengthWord (BrouwerNashHeaders.dimensionRuler ![v 3, v 4, v 5])]

private theorem alphaTest_cobham : Cobham alphaTest :=
  Cobham.andFn (lenEqFlag_mem (.proj 1)
    (appendFn (Cobham.const [false, false, false, false]) (.proj 0)))
    (Cobham.notFn (lenLeFlag_mem
      (.proj 0)
      (Cobham.comp₃ BrouwerNashHeaders.precisionRuler_cobham (.proj 3) (.proj 4) (.proj 5))))

private theorem alphaTerm_cobham : Cobham alphaTerm := by
  have hd : Cobham fun v : Fin 6 → List Bool =>
      BrouwerNashHeaders.dimensionRuler ![v 3, v 4, v 5] :=
    Cobham.comp₃ BrouwerNashHeaders.dimensionRuler_cobham (.proj 3) (.proj 4) (.proj 5)
  have hn : Cobham fun v : Fin 6 → List Bool =>
      binaryLengthWord (BrouwerNashHeaders.dimensionRuler ![v 3, v 4, v 5]) :=
    (Cobham.comp binaryLengthWord_cobham fun _ : Fin 1 => hd).of_eq fun _ => rfl
  have hs : Cobham fun v : Fin 6 → List Bool =>
      false :: binaryLengthWord (BrouwerNashHeaders.dimensionRuler ![v 3, v 4, v 5]) :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => hn).of_eq fun _ => rfl
  have hp : Cobham fun v : Fin 6 → List Bool => alphaPredecessor (v 0) :=
    (Cobham.comp alphaPredecessor_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  exact (Cobham.comp₃ binarySignedIndicator_cobham (.proj 2) hp hs).of_eq fun _ => rfl

/-- Query the alpha-chain family using output, action, source and two circuit-code words. -/
def alphaWord (v : Fin 5 → List Bool) : List Bool :=
  binaryIndexedLookup alphaTest alphaTerm
    (BrouwerNashHeaders.precisionRuler ![v 2, v 3, v 4])
    (BrouwerNashHeaders.widthRuler ![v 2, v 3, v 4]) v

/-- The source-dependent family scan has an actual polynomial-time certificate. -/
theorem alphaWord_cobham : Cobham alphaWord := by
  have hp : Cobham fun v : Fin 5 → List Bool =>
      BrouwerNashHeaders.precisionRuler ![v 2, v 3, v 4] :=
    Cobham.comp₃ BrouwerNashHeaders.precisionRuler_cobham (.proj 2) (.proj 3) (.proj 4)
  have hw : Cobham fun v : Fin 5 → List Bool =>
      BrouwerNashHeaders.widthRuler ![v 2, v 3, v 4] :=
    Cobham.comp₃ BrouwerNashHeaders.widthRuler_cobham (.proj 2) (.proj 3) (.proj 4)
  have hg : ∀ i : Fin 7, Cobham fun v : Fin 5 → List Bool =>
      (Fin.cons (BrouwerNashHeaders.precisionRuler ![v 2, v 3, v 4])
        (Fin.cons (BrouwerNashHeaders.widthRuler ![v 2, v 3, v 4]) v) : Fin 7 → List Bool) i := by
    intro i
    exact Fin.cases hp (fun j => Fin.cases hw (fun a => .proj a) j) i
  exact (Cobham.comp (binaryIndexedLookup_cobham alphaTest_cobham alphaTerm_cobham) hg).of_eq
    fun _ => rfl

theorem alphaWord_mem_FPn : FPn alphaWord := cobham_iff_FPn.mp alphaWord_cobham


private def header (f : (Fin 3 → List Bool) → List Bool) (v : Fin 5 → List Bool) : List Bool :=
  f ![v 2, v 3, v 4]
private theorem header_cobham {f : (Fin 3 → List Bool) → List Bool} (hf : Cobham f) :
    Cobham (header f) := (Cobham.comp₃ hf (.proj 2) (.proj 3) (.proj 4)).of_eq fun _ => rfl

private def scalar (n : ℕ) (negative : Bool) (ruler : List Bool) : List Bool :=
  negative :: binaryLengthWord (smash ruler (List.replicate n true))
private theorem scalar_cobham (n : ℕ) (negative : Bool) :
    Cobham fun v : Fin 1 → List Bool => scalar n negative (v 0) :=
  (Cobham.comp (.bit negative) fun _ : Fin 1 => Cobham.comp binaryLengthWord_cobham
    fun _ : Fin 1 => Cobham.comp₂ Cobham.smash (.proj 0)
      (Cobham.const (List.replicate n true))).of_eq fun _ => rfl

private def point (input coefficient : (Fin 5 → List Bool) → List Bool)
    (v : Fin 5 → List Bool) : List Bool := binarySignedIndicator ![v 1, input v, coefficient v]
private theorem point_cobham {input coefficient : (Fin 5 → List Bool) → List Bool}
    (hi : Cobham input) (hc : Cobham coefficient) : Cobham (point input coefficient) :=
  (Cobham.comp₃ binarySignedIndicator_cobham (.proj 1) hi hc).of_eq fun _ => rfl

private def atOutput (position term : (Fin 5 → List Bool) → List Bool)
    (v : Fin 5 → List Bool) : List Bool := caseBit₀ (lenEqFlag (v 0) (position v)) (term v) []
private theorem atOutput_cobham {position term : (Fin 5 → List Bool) → List Bool}
    (hp : Cobham position) (ht : Cobham term) : Cobham (atOutput position term) :=
  (Cobham.iteFn (lenEqFlag_mem (.proj 0) hp) ht Cobham.empty).of_eq fun _ => rfl

private def precisionR (v : Fin 5 → List Bool) : List Bool :=
  header BrouwerNashHeaders.precisionRuler v
private theorem precisionR_cobham : Cobham precisionR :=
  header_cobham BrouwerNashHeaders.precisionRuler_cobham
private def dimensionR (v : Fin 5 → List Bool) : List Bool :=
  header BrouwerNashHeaders.dimensionRuler v
private theorem dimensionR_cobham : Cobham dimensionR :=
  header_cobham BrouwerNashHeaders.dimensionRuler_cobham
private def unitsR (v : Fin 5 → List Bool) : List Bool := header BrouwerNashHeaders.unitsRuler v
private theorem unitsR_cobham : Cobham unitsR := header_cobham BrouwerNashHeaders.unitsRuler_cobham

/-- Coefficients of the shared constant-one block. -/
def oneWord : (Fin 5 → List Bool) → List Bool :=
  atOutput (fun _ => [false, false]) (fun _ => [false, false, true])
theorem oneWord_cobham : Cobham oneWord := atOutput_cobham (Cobham.const _) (Cobham.const _)

/-- Coefficients of the positive third-scale feedback block. -/
def positiveWord : (Fin 5 → List Bool) → List Bool :=
  atOutput (fun v => precisionR v ++ List.replicate 4 false)
    (point (fun v => precisionR v ++ List.replicate 3 false) (fun v => scalar 82 false (unitsR v)))
theorem positiveWord_cobham : Cobham positiveWord := by
  have hi : Cobham fun v : Fin 5 → List Bool => precisionR v ++ List.replicate 3 false :=
    appendFn precisionR_cobham (Cobham.const (List.replicate 3 false))
  have hs : Cobham fun v : Fin 5 → List Bool => scalar 82 false (unitsR v) :=
    (Cobham.comp (scalar_cobham 82 false) fun _ : Fin 1 => unitsR_cobham).of_eq fun _ => rfl
  exact atOutput_cobham (appendFn precisionR_cobham (Cobham.const (List.replicate 4 false)))
    (point_cobham hi hs)

private def feedbackPosition (axis : Fin 2) (v : Fin 5 → List Bool) : List Bool :=
  smash (precisionR v) [true, true, true] ++ List.replicate (7 + 2 * axis.val) false
private theorem feedbackPosition_cobham (axis : Fin 2) : Cobham (feedbackPosition axis) :=
  appendFn (Cobham.comp₂ Cobham.smash precisionR_cobham (Cobham.const _)) (Cobham.const _)

/-- Coefficients of a cyclic coordinate's final doubling block. -/
def doubleWord (axis : Fin 2) : (Fin 5 → List Bool) → List Bool :=
  atOutput (fun _ => List.replicate axis.val false)
    (point (fun v => feedbackPosition axis v ++ [false]) (fun v => scalar 4 false (dimensionR v)))
theorem doubleWord_cobham (axis : Fin 2) : Cobham (doubleWord axis) := by
  have hi : Cobham fun v : Fin 5 → List Bool => feedbackPosition axis v ++ [false] :=
    appendFn (feedbackPosition_cobham axis) (Cobham.const [false])
  have hs : Cobham fun v : Fin 5 → List Bool => scalar 4 false (dimensionR v) :=
    (Cobham.comp (scalar_cobham 4 false) fun _ : Fin 1 => dimensionR_cobham).of_eq fun _ => rfl
  exact atOutput_cobham (Cobham.const (List.replicate axis.val false)) (point_cobham hi hs)

private theorem tail_cobham {f : (Fin 5 → List Bool) → List Bool} (hf : Cobham f) :
    Cobham fun v : Fin 6 → List Bool => f (Fin.tail v) :=
  (Cobham.comp hf fun i => .proj i.succ).of_eq fun _ => rfl

private def negativeBase (axis : Fin 2) (v : Fin 5 → List Bool) : List Bool :=
  precisionR v ++ List.replicate 7 false ++
    (if axis.val = 0 then [] else precisionR v)
private theorem negativeBase_cobham (axis : Fin 2) : Cobham (negativeBase axis) := by
  have haxis : Cobham fun v : Fin 5 → List Bool =>
      if axis.val = 0 then [] else precisionR v := by
    by_cases h : axis.val = 0
    · exact Cobham.empty.of_eq fun _ => by rw [ite_eq_left h]
    · exact precisionR_cobham.of_eq fun _ => by rw [ite_eq_right h]
  exact appendFn (appendFn precisionR_cobham (Cobham.const (List.replicate 7 false))) haxis

private def negativePredecessor (axis : Fin 2) (v : Fin 6 → List Bool) : List Bool :=
  caseBit₀ (lenEqFlag (v 0) [])
    (precisionR (Fin.tail v) ++ List.replicate (5 + axis.val) false)
    (negativeBase axis (Fin.tail v) ++ (v 0).tail)
private theorem negativePredecessor_cobham (axis : Fin 2) : Cobham (negativePredecessor axis) :=
  Cobham.iteFn (lenEqFlag_mem (.proj 0) Cobham.empty)
    (appendFn (tail_cobham precisionR_cobham) (Cobham.const (List.replicate (5 + axis.val) false)))
    (appendFn (tail_cobham (negativeBase_cobham axis)) (Cobham.tailFn (.proj 0)))

private def negativeTest (axis : Fin 2) (v : Fin 6 → List Bool) : List Bool :=
  andBit (lenEqFlag (v 1) (negativeBase axis (Fin.tail v) ++ v 0))
    (notBit (lenLeFlag (v 0) (precisionR (Fin.tail v))))
private theorem negativeTest_cobham (axis : Fin 2) : Cobham (negativeTest axis) :=
  Cobham.andFn (lenEqFlag_mem (.proj 1)
    (appendFn (tail_cobham (negativeBase_cobham axis)) (.proj 0)))
    (Cobham.notFn (lenLeFlag_mem (.proj 0) (tail_cobham precisionR_cobham)))

private def negativeTerm (axis : Fin 2) (v : Fin 6 → List Bool) : List Bool :=
  binarySignedIndicator ![v 2, negativePredecessor axis v,
    scalar 1 false (dimensionR (Fin.tail v))]
private theorem negativeTerm_cobham (axis : Fin 2) : Cobham (negativeTerm axis) := by
  have hs : Cobham fun v : Fin 6 → List Bool => scalar 1 false (dimensionR (Fin.tail v)) :=
    (Cobham.comp (scalar_cobham 1 false) fun _ : Fin 1 => tail_cobham dimensionR_cobham).of_eq
      fun _ => rfl
  exact (Cobham.comp₃ binarySignedIndicator_cobham (.proj 2)
    (negativePredecessor_cobham axis) hs).of_eq fun _ => rfl

private def scan (test term : (Fin 6 → List Bool) → List Bool)
    (v : Fin 5 → List Bool) : List Bool :=
  binaryIndexedLookup test term (precisionR v) (header BrouwerNashHeaders.widthRuler v) v
private theorem scan_cobham {test term : (Fin 6 → List Bool) → List Bool}
    (htest : Cobham test) (hterm : Cobham term) : Cobham (scan test term) := by
  have hw : Cobham (header BrouwerNashHeaders.widthRuler) :=
    header_cobham BrouwerNashHeaders.widthRuler_cobham
  have ha : ∀ i : Fin 7, Cobham fun v : Fin 5 → List Bool =>
      (Fin.cons (precisionR v) (Fin.cons (header BrouwerNashHeaders.widthRuler v) v) :
        Fin 7 → List Bool) i := by
    intro i
    exact Fin.cases precisionR_cobham (fun j => Fin.cases hw (fun a => .proj a) j) i
  exact (Cobham.comp (binaryIndexedLookup_cobham htest hterm) ha).of_eq fun _ => rfl

/-- All negative-component halving blocks for a selected coordinate. -/
def negativeWord (axis : Fin 2) : (Fin 5 → List Bool) → List Bool :=
  scan (negativeTest axis) (negativeTerm axis)
theorem negativeWord_cobham (axis : Fin 2) : Cobham (negativeWord axis) :=
  scan_cobham (negativeTest_cobham axis) (negativeTerm_cobham axis)

/-- Coefficients of the shared half-add stage of cyclic feedback. -/
def halfWord (axis : Fin 2) : (Fin 5 → List Bool) → List Bool :=
  atOutput (feedbackPosition axis) (fun v => binarySignedAdd
    (point (fun _ => List.replicate axis.val false) (fun w => scalar 1 false (dimensionR w)) v)
    (point (fun w => precisionR w ++ List.replicate 4 false)
      (fun w => scalar 1 false (dimensionR w)) v))
theorem halfWord_cobham (axis : Fin 2) : Cobham (halfWord axis) := by
  have hs : Cobham fun v : Fin 5 → List Bool => scalar 1 false (dimensionR v) :=
    (Cobham.comp (scalar_cobham 1 false) fun _ : Fin 1 => dimensionR_cobham).of_eq fun _ => rfl
  have hq := point_cobham (Cobham.const (List.replicate axis.val false)) hs
  have hp := point_cobham
    (appendFn precisionR_cobham (Cobham.const (List.replicate 4 false))) hs
  exact atOutput_cobham (feedbackPosition_cobham axis)
    ((Cobham.comp₂ binarySignedAdd_cobham hq hp).of_eq fun _ => rfl)

/-- Coefficients of the shared half-subtract stage of cyclic feedback. -/
def subtractWord (axis : Fin 2) : (Fin 5 → List Bool) → List Bool :=
  atOutput (fun v => feedbackPosition axis v ++ [false]) (fun v => binarySignedAdd
    (point (feedbackPosition axis) (fun w => scalar 2 false (dimensionR w)) v)
    (point (fun w => negativePredecessor axis (Fin.cons (precisionR w) w))
      (fun w => scalar 1 true (dimensionR w)) v))
theorem subtractWord_cobham (axis : Fin 2) : Cobham (subtractWord axis) := by
  have hpos : Cobham fun v : Fin 5 → List Bool => scalar 2 false (dimensionR v) :=
    (Cobham.comp (scalar_cobham 2 false) fun _ : Fin 1 => dimensionR_cobham).of_eq fun _ => rfl
  have hneg : Cobham fun v : Fin 5 → List Bool => scalar 1 true (dimensionR v) :=
    (Cobham.comp (scalar_cobham 1 true) fun _ : Fin 1 => dimensionR_cobham).of_eq fun _ => rfl
  have ha : ∀ i : Fin 6, Cobham fun v : Fin 5 → List Bool =>
      (Fin.cons (precisionR v) v : Fin 6 → List Bool) i := by
    intro i
    exact Fin.cases precisionR_cobham (fun j => .proj j) i
  have hi : Cobham fun v : Fin 5 → List Bool =>
      negativePredecessor axis (Fin.cons (precisionR v) v) :=
    (Cobham.comp (negativePredecessor_cobham axis) ha).of_eq fun _ => rfl
  exact atOutput_cobham
    (appendFn (feedbackPosition_cobham axis) (Cobham.const [false]))
    ((Cobham.comp₂ binarySignedAdd_cobham (point_cobham (feedbackPosition_cobham axis) hpos)
      (point_cobham hi hneg)).of_eq fun _ => rfl)

private theorem scalar_value (n : ℕ) (negative : Bool) (ruler : List Bool) :
    binarySignedValue (scalar n negative ruler) =
      if negative then -((n * ruler.length : ℕ) : ℤ) else ((n * ruler.length : ℕ) : ℤ) := by
  cases negative <;>
    simp only [scalar, binarySignedValue, binaryLengthWord_value, smash_length,
      List.length_replicate, List.headD_cons, List.tail_cons,
      Bool.false_eq_true, ite_false, ite_true] <;> simp only [Nat.cast_mul, Nat.mul_comm]

/-- Constant one contributes its affine offset to every row action. -/
theorem oneWord_value (out action source code₀ code₁ : List Bool) :
    binarySignedValue (oneWord ![out, action, source, code₀, code₁]) =
      if out.length = 2 then 2 else 0 := by
  change binarySignedValue (caseBit₀ (lenEqFlag out [false, false])
    [false, false, true] []) = _
  rw [select_value]
  rfl

private theorem precisionR_length (v : Fin 5 → List Bool) :
    (precisionR v).length = BrouwerNashLayout.precision (pairFst (v 2)).length :=
  BrouwerNashHeaders.precisionRuler_length ![v 2, v 3, v 4]
private theorem dimensionR_length (v : Fin 5 → List Bool) :
    (dimensionR v).length = BrouwerNashLayout.dimension (pairFst (v 2)).length
      (circuitUnaryPrefix (v 3)).length (circuitUnaryPrefix (v 4)).length :=
  BrouwerNashHeaders.dimensionRuler_length ![v 2, v 3, v 4]
private theorem unitsR_length (v : Fin 5 → List Bool) :
    (unitsR v).length = BrouwerNashLayout.units (pairFst (v 2)).length
      (circuitUnaryPrefix (v 3)).length (circuitUnaryPrefix (v 4)).length :=
  BrouwerNashHeaders.unitsRuler_length ![v 2, v 3, v 4]

/-- Positive scaling uses the exact integer coefficient of the canonical block. -/
theorem positiveWord_value (out action source code₀ code₁ : List Bool) :
    binarySignedValue (positiveWord ![out, action, source, code₀, code₁]) =
      if out.length = BrouwerNashLayout.positive (pairFst source).length then
        if action.length / 2 = BrouwerNashLayout.alpha
            (BrouwerNashLayout.precision (pairFst source).length) ∧ action.length % 2 = 1
        then 82 * (BrouwerNashLayout.units (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0
      else 0 := by
  change binarySignedValue (caseBit₀ (lenEqFlag out
    (precisionR ![out, action, source, code₀, code₁] ++ List.replicate 4 false))
    (binarySignedIndicator ![action,
      precisionR ![out, action, source, code₀, code₁] ++ List.replicate 3 false,
      scalar 82 false (unitsR ![out, action, source, code₀, code₁])]) []) = _
  rw [select_value, binarySignedIndicator_value, scalar_value]
  simp only [List.length_append, List.length_replicate, precisionR_length,
    unitsR_length, BrouwerNashLayout.positive, BrouwerNashLayout.alpha,
    BrouwerNashLayout.precision, Nat.cast_mul, Nat.cast_ofNat]
  norm_num
  simp only [Nat.add_comm]

private theorem lenEq_value (a b : List Bool) :
    lenEqFlag a b = [decide (a.length = b.length)] := by
  rcases lenEqFlag_flag a b with h | h
  · rw [h]
    simp [(lenEqFlag_eq_true_iff a b).mp h]
  · have hn : a.length ≠ b.length := by
      intro he
      have ht := (lenEqFlag_eq_true_iff a b).mpr he
      rw [h] at ht
      contradiction
    rw [h]
    simp [hn]

private theorem lenLe_value (a b : List Bool) :
    lenLeFlag a b = [decide (b.length ≤ a.length)] := by
  rcases lenLeFlag_flag a b with h | h
  · rw [h]
    simp [(lenLeFlag_eq_true_iff a b).mp h]
  · have hn : ¬b.length ≤ a.length := by
      intro he
      have ht := (lenLeFlag_eq_true_iff a b).mpr he
      rw [h] at ht
      contradiction
    rw [h]
    simp [hn]

private theorem alphaTest_value (ordinal : List Bool) (v : Fin 5 → List Bool) :
    alphaTest (Fin.cons ordinal v) =
      [decide ((v 0).length = 4 + ordinal.length ∧
        ordinal.length < (precisionR v).length)] := by
  change andBit (lenEqFlag (v 0) ([false, false, false, false] ++ ordinal))
    (notBit (lenLeFlag ordinal (precisionR v))) = _
  rw [lenEq_value, lenLe_value]
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd]
  have hle : ((precisionR v).length ≤ ordinal.length) ↔
      ¬ordinal.length < (precisionR v).length := by omega
  by_cases he : (v 0).length = 4 + ordinal.length <;>
    by_cases hl : ordinal.length < (precisionR v).length <;>
    simp [he, hle, hl, andBit, notBit, caseBit₀]

private theorem alphaPredecessor_length (r : List Bool) :
    (alphaPredecessor r).length = BrouwerNashLayout.alpha r.length := by
  rw [alphaPredecessor, lenEq_value]
  by_cases hz : r.length = 0
  · simp [hz, caseBit₀, BrouwerNashLayout.alpha, BrouwerNashLayout.one]
  · simp [hz, caseBit₀, BrouwerNashLayout.alpha]
    omega

/-- The bounded alpha scan decodes exactly the selected halving-chain coefficient. -/
theorem alphaWord_value (out action source code₀ code₁ : List Bool) :
    binarySignedValue (alphaWord ![out, action, source, code₀, code₁]) =
      if 4 ≤ out.length ∧ out.length <
          BrouwerNashLayout.precision (pairFst source).length + 4 then
        if action.length / 2 = BrouwerNashLayout.alpha (out.length - 4) ∧
            action.length % 2 = 1
        then (BrouwerNashLayout.dimension (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0
      else 0 := by
  let v : Fin 5 → List Bool := ![out, action, source, code₀, code₁]
  let k := (dimensionR v).length
  let z : ℤ := if action.length / 2 = BrouwerNashLayout.alpha (out.length - 4) ∧
      action.length % 2 = 1 then (k : ℤ) else 0
  have hz : z.natAbs ≤ 100 * k := by
    dsimp only [z]
    split_ifs <;> simp only [Int.natAbs_natCast, Int.natAbs_zero] <;> omega
  have ht : ∀ ordinal, alphaTest (Fin.cons ordinal v) =
      [decide (out.length = 4 + ordinal.length ∧ ordinal.length < (precisionR v).length)] :=
    fun ordinal => alphaTest_value ordinal v
  have hterm : ∀ ordinal,
      decide (out.length = 4 + ordinal.length ∧ ordinal.length < (precisionR v).length) = true →
      binarySignedValue (alphaTerm (Fin.cons ordinal v)) = z := by
    intro ordinal h
    have he := (of_decide_eq_true h).1
    have hi : ordinal.length = out.length - 4 := by omega
    change binarySignedValue (binarySignedIndicator ![action, alphaPredecessor ordinal,
      false :: binaryLengthWord (dimensionR v)]) = z
    rw [binarySignedIndicator_value, alphaPredecessor_length, hi]
    simp only [binarySignedValue, List.headD_cons, Bool.false_eq_true, ite_false,
      List.tail_cons, binaryLengthWord_value]
    rfl
  have hw : 0 < (BrouwerNashHeaders.widthRuler ![source, code₀, code₁]).length := by
    rw [BrouwerNashHeaders.widthRuler_length]
    omega
  have hc := binaryIndexedLookup_value alphaTest alphaTerm
    (BrouwerNashHeaders.widthRuler ![source, code₀, code₁]) v
    (fun i => decide (out.length = 4 + i ∧ i < (precisionR v).length)) z ht hterm hw
    (BrouwerNashHeaders.widthRuler_fits ![source, code₀, code₁] z hz)
    (precisionR v)
  change binarySignedValue (alphaWord v) = _
  rw [show alphaWord v = binaryIndexedLookup alphaTest alphaTerm (precisionR v)
    (BrouwerNashHeaders.widthRuler ![source, code₀, code₁]) v from rfl, hc]
  have he : (∃ i < (precisionR v).length,
      decide (out.length = 4 + i ∧ i < (precisionR v).length) = true) ↔
      4 ≤ out.length ∧ out.length < (precisionR v).length + 4 := by
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi, hout, _⟩
      omega
    · rintro ⟨hl, hu⟩
      refine ⟨out.length - 4, by omega, by omega, by omega⟩
  simp only [he]
  simp only [precisionR_length, z, k, dimensionR_length]
  rfl

private theorem negativeBase_length (axis : Fin 2) (v : Fin 5 → List Bool) :
    (negativeBase axis v).length =
      BrouwerNashLayout.precision (pairFst (v 2)).length + 7 +
        axis.val * BrouwerNashLayout.precision (pairFst (v 2)).length := by
  fin_cases axis <;> simp [negativeBase, precisionR_length]
  all_goals omega

private theorem negativePredecessor_length (axis : Fin 2) (ordinal : List Bool)
    (v : Fin 5 → List Bool) :
    (negativePredecessor axis (Fin.cons ordinal v)).length =
      BrouwerNashLayout.negative (pairFst (v 2)).length axis ordinal.length := by
  change (caseBit₀ (lenEqFlag ordinal [])
    (precisionR v ++ List.replicate (5 + axis.val) false)
    (negativeBase axis v ++ ordinal.tail)).length = _
  rw [lenEq_value]
  by_cases hz : ordinal.length = 0
  · simp [hz, caseBit₀, BrouwerNashLayout.negative, BrouwerNashLayout.average,
      precisionR_length]
    omega
  · simp [hz, caseBit₀, BrouwerNashLayout.negative, negativeBase_length]

private theorem negativeTest_value (axis : Fin 2) (ordinal : List Bool)
    (v : Fin 5 → List Bool) :
    negativeTest axis (Fin.cons ordinal v) =
      [decide ((v 0).length = (negativeBase axis v).length + ordinal.length ∧
        ordinal.length < (precisionR v).length)] := by
  change andBit (lenEqFlag (v 0) (negativeBase axis v ++ ordinal))
    (notBit (lenLeFlag ordinal (precisionR v))) = _
  rw [lenEq_value, lenLe_value]
  simp only [List.length_append]
  have hle : ((precisionR v).length ≤ ordinal.length) ↔
      ¬ordinal.length < (precisionR v).length := by omega
  by_cases he : (v 0).length = (negativeBase axis v).length + ordinal.length <;>
    by_cases hl : ordinal.length < (precisionR v).length <;>
    simp [he, hle, hl, andBit, notBit, caseBit₀]

/-- Each negative-feedback chain is a bounded scan of its exact canonical input indices. -/
theorem negativeWord_value (axis : Fin 2) (out action source code₀ code₁ : List Bool) :
    binarySignedValue (negativeWord axis ![out, action, source, code₀, code₁]) =
      let base := BrouwerNashLayout.precision (pairFst source).length + 7 +
        axis.val * BrouwerNashLayout.precision (pairFst source).length
      if base ≤ out.length ∧ out.length <
          base + BrouwerNashLayout.precision (pairFst source).length then
        if action.length / 2 = BrouwerNashLayout.negative (pairFst source).length axis
            (out.length - base) ∧ action.length % 2 = 1
        then (BrouwerNashLayout.dimension (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0
      else 0 := by
  let v : Fin 5 → List Bool := ![out, action, source, code₀, code₁]
  let base := (negativeBase axis v).length
  let k := (dimensionR v).length
  let z : ℤ := if action.length / 2 = BrouwerNashLayout.negative (pairFst source).length
      axis (out.length - base) ∧ action.length % 2 = 1 then (k : ℤ) else 0
  have hz : z.natAbs ≤ 100 * k := by
    dsimp only [z]
    split_ifs <;> simp only [Int.natAbs_natCast, Int.natAbs_zero] <;> omega
  have ht : ∀ ordinal, negativeTest axis (Fin.cons ordinal v) =
      [decide (out.length = base + ordinal.length ∧
        ordinal.length < (precisionR v).length)] :=
    fun ordinal => negativeTest_value axis ordinal v
  have hterm : ∀ ordinal,
      decide (out.length = base + ordinal.length ∧ ordinal.length < (precisionR v).length) =
        true → binarySignedValue (negativeTerm axis (Fin.cons ordinal v)) = z := by
    intro ordinal h
    have he := (of_decide_eq_true h).1
    have hi : ordinal.length = out.length - base := by omega
    change binarySignedValue (binarySignedIndicator ![action,
      negativePredecessor axis (Fin.cons ordinal v), scalar 1 false (dimensionR v)]) = z
    rw [binarySignedIndicator_value, negativePredecessor_length, hi, scalar_value]
    simp only [Bool.false_eq_true, ite_false, one_mul]
    rfl
  have hw : 0 < (BrouwerNashHeaders.widthRuler ![source, code₀, code₁]).length := by
    rw [BrouwerNashHeaders.widthRuler_length]
    omega
  have hc := binaryIndexedLookup_value (negativeTest axis) (negativeTerm axis)
    (BrouwerNashHeaders.widthRuler ![source, code₀, code₁]) v
    (fun i => decide (out.length = base + i ∧ i < (precisionR v).length)) z ht hterm hw
    (BrouwerNashHeaders.widthRuler_fits ![source, code₀, code₁] z hz) (precisionR v)
  change binarySignedValue (negativeWord axis v) = _
  rw [show negativeWord axis v = binaryIndexedLookup (negativeTest axis) (negativeTerm axis)
    (precisionR v) (BrouwerNashHeaders.widthRuler ![source, code₀, code₁]) v from rfl, hc]
  have he : (∃ i < (precisionR v).length,
      decide (out.length = base + i ∧ i < (precisionR v).length) = true) ↔
      base ≤ out.length ∧ out.length < base + (precisionR v).length := by
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi, hout, _⟩
      omega
    · rintro ⟨hl, hu⟩
      exact ⟨out.length - base, by omega, by omega, by omega⟩
  simp only [he]
  simp only [precisionR_length, z, k, dimensionR_length, base, negativeBase_length]
  rfl

private theorem feedbackPosition_length (axis : Fin 2) (v : Fin 5 → List Bool) :
    (feedbackPosition axis v).length =
      BrouwerNashLayout.feedbackHalf (pairFst (v 2)).length axis := by
  simp only [feedbackPosition, List.length_append, smash_length, List.length_cons,
    List.length_nil, Nat.reduceAdd, List.length_replicate, precisionR_length,
    BrouwerNashLayout.feedbackHalf]
  omega

/-- The coordinate block reads the final feedback subtraction at the exact doubling scale. -/
theorem doubleWord_value (axis : Fin 2) (out action source code₀ code₁ : List Bool) :
    binarySignedValue (doubleWord axis ![out, action, source, code₀, code₁]) =
      if out.length = axis.val then
        if action.length / 2 = BrouwerNashLayout.feedbackSub (pairFst source).length axis ∧
            action.length % 2 = 1
        then 4 * (BrouwerNashLayout.dimension (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0
      else 0 := by
  change binarySignedValue (caseBit₀ (lenEqFlag out (List.replicate axis.val false))
    (binarySignedIndicator ![action,
      feedbackPosition axis ![out, action, source, code₀, code₁] ++ [false],
      scalar 4 false (dimensionR ![out, action, source, code₀, code₁])]) []) = _
  rw [select_value, binarySignedIndicator_value, scalar_value]
  simp only [List.length_replicate, List.length_append, List.length_cons, List.length_nil,
    feedbackPosition_length, dimensionR_length, Bool.false_eq_true, ite_false,
    Nat.cast_mul, Nat.cast_ofNat, BrouwerNashLayout.feedbackSub]
  rfl

/-- Half addition retains both input contributions, even if references coincide. -/
theorem halfWord_value (axis : Fin 2) (out action source code₀ code₁ : List Bool) :
    binarySignedValue (halfWord axis ![out, action, source, code₀, code₁]) =
      if out.length = BrouwerNashLayout.feedbackHalf (pairFst source).length axis then
        (if action.length / 2 = axis.val ∧ action.length % 2 = 1
        then (BrouwerNashLayout.dimension (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0) +
        (if action.length / 2 = BrouwerNashLayout.positive (pairFst source).length ∧
            action.length % 2 = 1
        then (BrouwerNashLayout.dimension (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0)
      else 0 := by
  change binarySignedValue (caseBit₀
    (lenEqFlag out (feedbackPosition axis ![out, action, source, code₀, code₁]))
    (binarySignedAdd
      (binarySignedIndicator ![action, List.replicate axis.val false,
        scalar 1 false (dimensionR ![out, action, source, code₀, code₁])])
      (binarySignedIndicator ![action,
        precisionR ![out, action, source, code₀, code₁] ++ List.replicate 4 false,
        scalar 1 false (dimensionR ![out, action, source, code₀, code₁])])) []) = _
  rw [select_value, binarySignedAdd_value, binarySignedIndicator_value,
    binarySignedIndicator_value, scalar_value]
  simp only [List.length_replicate, List.length_append, precisionR_length,
    feedbackPosition_length, dimensionR_length, Bool.false_eq_true, ite_false, one_mul,
    BrouwerNashLayout.positive]
  rfl

/-- The final subtraction emits a negative signed input coefficient. -/
theorem subtractWord_value (axis : Fin 2) (out action source code₀ code₁ : List Bool) :
    binarySignedValue (subtractWord axis ![out, action, source, code₀, code₁]) =
      if out.length = BrouwerNashLayout.feedbackSub (pairFst source).length axis then
        (if action.length / 2 = BrouwerNashLayout.feedbackHalf (pairFst source).length axis ∧
            action.length % 2 = 1
        then 2 * (BrouwerNashLayout.dimension (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0) +
        (if action.length / 2 = BrouwerNashLayout.negative (pairFst source).length axis
            (BrouwerNashLayout.precision (pairFst source).length) ∧ action.length % 2 = 1
        then -(BrouwerNashLayout.dimension (pairFst source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0)
      else 0 := by
  let v : Fin 5 → List Bool := ![out, action, source, code₀, code₁]
  change binarySignedValue (caseBit₀ (lenEqFlag out (feedbackPosition axis v ++ [false]))
    (binarySignedAdd
      (binarySignedIndicator ![action, feedbackPosition axis v, scalar 2 false (dimensionR v)])
      (binarySignedIndicator ![action, negativePredecessor axis (Fin.cons (precisionR v) v),
        scalar 1 true (dimensionR v)])) []) = _
  rw [select_value, binarySignedAdd_value, binarySignedIndicator_value,
    binarySignedIndicator_value, scalar_value, scalar_value]
  simp only [List.length_append, List.length_cons, List.length_nil,
    feedbackPosition_length, dimensionR_length, Bool.false_eq_true, ite_false,
    ite_true, one_mul, negativePredecessor_length, precisionR_length,
    Nat.cast_mul, Nat.cast_ofNat, BrouwerNashLayout.feedbackSub]
  rfl

private def pairWords (term : Fin 2 → (Fin 5 → List Bool) → List Bool)
    (v : Fin 5 → List Bool) : List Bool := binarySignedAdd (term 0 v) (term 1 v)
private theorem pairWords_cobham {term : Fin 2 → (Fin 5 → List Bool) → List Bool}
    (ht : ∀ axis, Cobham (term axis)) : Cobham (pairWords term) :=
  (Cobham.comp₂ binarySignedAdd_cobham (ht 0) (ht 1)).of_eq fun _ => rfl

/-- All shared affine coefficient families, including the two color means. -/
def coefficientWord (v : Fin 5 → List Bool) : List Bool :=
  binarySignedAdd (alphaWord v) (binarySignedAdd (oneWord v)
    (binarySignedAdd (positiveWord v) (binarySignedAdd (pairWords doubleWord v)
      (binarySignedAdd (pairWords negativeWord v) (binarySignedAdd (pairWords halfWord v)
        (binarySignedAdd (pairWords subtractWord v)
          (BrouwerNashAverageQuery.coefficientWord v)))))))

/-- Every shared query is certified by an actual polynomial-time machine. -/
theorem coefficientWord_cobham : Cobham coefficientWord := by
  have hsum {f g : (Fin 5 → List Bool) → List Bool} (hf : Cobham f) (hg : Cobham g) :
      Cobham fun v => binarySignedAdd (f v) (g v) :=
    (Cobham.comp₂ binarySignedAdd_cobham hf hg).of_eq fun _ => rfl
  exact hsum alphaWord_cobham (hsum oneWord_cobham (hsum positiveWord_cobham
    (hsum (pairWords_cobham doubleWord_cobham) (hsum (pairWords_cobham negativeWord_cobham)
      (hsum (pairWords_cobham halfWord_cobham) (hsum (pairWords_cobham subtractWord_cobham)
        BrouwerNashAverageQuery.coefficientWord_cobham))))))

theorem coefficientWord_mem_FPn : FPn coefficientWord := cobham_iff_FPn.mp coefficientWord_cobham

/-- Signed addition exposes all family contributions without any intermediate capacity bound. -/
theorem coefficientWord_expansion (v : Fin 5 → List Bool) :
    binarySignedValue (coefficientWord v) = binarySignedValue (alphaWord v) +
      (binarySignedValue (oneWord v) + (binarySignedValue (positiveWord v) +
        ((binarySignedValue (doubleWord 0 v) + binarySignedValue (doubleWord 1 v)) +
          ((binarySignedValue (negativeWord 0 v) + binarySignedValue (negativeWord 1 v)) +
            ((binarySignedValue (halfWord 0 v) + binarySignedValue (halfWord 1 v)) +
              ((binarySignedValue (subtractWord 0 v) + binarySignedValue (subtractWord 1 v)) +
                binarySignedValue (BrouwerNashAverageQuery.coefficientWord v))))))) := by
  simp only [coefficientWord, pairWords, binarySignedAdd_value]

end GameTheory.Complexity.Backend.BrouwerNashGlobalQuery
