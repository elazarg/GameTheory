module

public import GameTheory.Math.FiniteLinearBitBound
public import GameTheoryComplexity.Backend.BinaryCertificateFold
public import GameTheory.Finite.BimatrixNashCertificate
public import GameTheory.Finite.BimatrixTable
public import GameTheoryComplexity.Backend.WordOperations

@[expose] public section

/-! A binary certificate verifier for the total signed-tally table decoder.
All iteration clocks are word lengths, dimensions, or tally lengths. -/
namespace GameTheory.Complexity.Backend
open GameTheory.Math (constrainedNashCertificateWidth)
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

private theorem reindexProducer {m n : ℕ} {f : (Fin m → List Bool) → List Bool}
    (hf : ComputableInPolyTime f (encPi encBits) encBits) (index : Fin m → Fin n) :
    ComputableInPolyTime (fun v : Fin n → List Bool => f (fun i => v (index i)))
      (encPi encBits) encBits := by
  apply hf.comp
  apply ComputableInPolyTime.pi
  intro i
  exact ComputableInPolyTime.pi_apply encBits (index i)

/-- Binary certificate field width determined solely by the table input length. -/
def certificateWidthWord (input : List Bool) : List Bool :=
  List.replicate (14 * input.length * input.length) true ++
    List.replicate (36 * input.length) true ++ List.replicate 23 true

/-- The dimension ruler is the table's initial run of true bits. -/
def certificateDimensionWord (input : List Bool) : List Bool := input.takeWhile id

/-- Read one fixed-width binary field, with total decoding of short certificates. -/
def certificateFieldWord (v : Fin 3 → List Bool) : List Bool :=
  ((v 2).drop ((v 0).length * (certificateWidthWord (v 1)).length)).take
    (certificateWidthWord (v 1)).length

/-- Read a row or column probability numerator indexed by a unary ruler. -/
def certificateWeightWord (rowWeights : Bool) (v : Fin 3 → List Bool) : List Bool :=
  certificateFieldWord ![List.replicate 4 true ++
    (if rowWeights then [] else certificateDimensionWord (v 1)) ++ v 0, v 1, v 2]

/-- The positive or negative tally of one decoded row-major payoff cell. -/
def matrixTallyWord (positive : Bool) (v : Fin 3 → List Bool) : List Bool :=
  let q := certificateDimensionWord (v 2)
  let w := q ++ [true, true]
  let offset := List.replicate (((v 0).length * q.length + (v 1).length) *
    (2 * w.length)) true
  (((v 2).drop (q.length + 1)).drop
    (offset.length + (if positive then 0 else w.length))).take w.length

/-- One weighted tally term uses binary addition once per true tally bit. -/
def matrixWeightedTerm (rowWeights positive : Bool) (v : Fin 4 → List Bool) : List Bool :=
  binaryTallySum (matrixTallyWord positive ![v 1, v 0, v 2])
    (certificateWeightWord rowWeights ![v 0, v 2, v 3])

/-- Sum one sign of a pure-action payoff numerator against the selected distribution. -/
def matrixScoreWord (rowWeights positive : Bool) (v : Fin 3 → List Bool) : List Bool :=
  binaryIndexedSum (matrixWeightedTerm rowWeights positive)
    (certificateDimensionWord (v 1)) v

/-- Sum all weights of one certificate distribution. -/
def certificateWeightSumWord (rowWeights : Bool) (v : Fin 2 → List Bool) : List Bool :=
  binaryIndexedSum (certificateWeightWord rowWeights)
    (certificateDimensionWord (v 0)) v

/-- Binary equality is independent of zero padding. -/
def certificateEqualWord (x y : List Bool) : List Bool :=
  andFlag (binaryCertificateLE ![x, y]) (binaryCertificateLE ![y, x])

/-- Check one pure-action inequality and equality on positive support. -/
def matrixActionCheck (columnPlayer : Bool) (v : Fin 3 → List Bool) : List Bool :=
  let pos := matrixScoreWord columnPlayer true v
  let neg := matrixScoreWord columnPlayer false v
  let utility := certificateFieldWord ![List.replicate (if columnPlayer then 3 else 2) true,
    v 1, v 2]
  let bound := binaryCertificateAdd ![neg, utility]
  let support := certificateWeightWord (!columnPlayer) v
  andFlag (binaryCertificateLE ![pos, bound])
    (orFlag (certificateEqualWord support []) (certificateEqualWord pos bound))

/-- Accumulate action-check flags over a dimension clock. -/
def certificateAllStep {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (v : Fin (p + 2) → List Bool) : List Bool :=
  andFlag (v 1) (term (Fin.cons (v 0) (Fin.tail (Fin.tail v))))

/-- Conjunction of terms indexed by the clock's successive suffix rulers. -/
def certificateAll {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) : List Bool :=
  WordFold.suffixFold
    (fun (params : Fin p → List Bool) suffix state (_bit : Bool) =>
      andFlag state (term (Fin.cons suffix params)))
    params [true] clock

/-- Check all pure-action constraints for one player. -/
def matrixAllChecks (columnPlayer : Bool) (v : Fin 2 → List Bool) : List Bool :=
  certificateAll (matrixActionCheck columnPlayer) (certificateDimensionWord (v 0)) v

/-- Check exact certificate length, normalization, payoff thresholds, and Nash deviations. -/
def binaryCertificateVerifier (v : Fin 2 → List Bool) : List Bool :=
  let q := certificateDimensionWord (v 0)
  let width := certificateWidthWord (v 0)
  let field := fun i => certificateFieldWord ![List.replicate i true, v 0, v 1]
  andFlag [decide ((v 1).length =
    (q.length + q.length + 4) * width.length)]
    (andFlag (notFlag (certificateEqualWord (field 0) []))
    (andFlag (notFlag (certificateEqualWord (field 1) []))
    (andFlag (certificateEqualWord (certificateWeightSumWord true v) (field 0))
    (andFlag (certificateEqualWord (certificateWeightSumWord false v) (field 1))
    (andFlag (binaryCertificateLE ![field 1, field 2])
    (andFlag (binaryCertificateLE ![field 0, field 3])
    (andFlag (matrixAllChecks false v) (matrixAllChecks true v))))))))

/-- The width word has the prescribed quadratic length. -/
theorem certificateWidthWord_length (input : List Bool) :
    (certificateWidthWord input).length = constrainedNashCertificateWidth input.length := by
  simp only [certificateWidthWord, constrainedNashCertificateWidth, List.length_append,
    List.length_replicate, pow_two]
  ring

/-- The dimension word has exactly the total decoder's dimension. -/
theorem certificateDimensionWord_length (input : List Bool) :
    (certificateDimensionWord input).length =
      GameTheory.Finite.BimatrixTable.decodeDimension input := rfl

private theorem verifierInput_polyTime :
    ComputableInPolyTime (fun x : List Bool => x) encBits encBits :=
  ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.encode encBits)

/-- The quadratic width ruler is polynomial-time. -/
@[fun_prop] theorem certificateWidthWord_polyTime :
    ComputableInPolyTime certificateWidthWord encBits encBits := by
  have hlength := ComputableInPolyTime.length_bits_comp verifierInput_polyTime
  have hsquare := ComputableInPolyTime.unary_mul' hlength hlength
  have hfirst := (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.unary_mul' (.const 14) hsquare)
  have hfirst' : ComputableInPolyTime
      (fun x : List Bool => List.replicate (14 * x.length * x.length) true)
      encBits encBits := by
    simpa only [Function.comp_def, Nat.mul_assoc] using hfirst
  have hsecond := (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.unary_mul' (.const 36) hlength)
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend hfirst' hsecond)
    (.const (List.replicate 23 true))

private def dimensionStep (_context : List Bool) (_suffix state : List Bool) (bit : Bool) :
    List Bool := if bit then true :: state else []

private theorem dimensionFold_eq (context word : List Bool) :
    WordFold.suffixFold dimensionStep context [] word = word.takeWhile id := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    rw [WordFold.suffixFold_cons]
    cases bit <;> simp [dimensionStep, ih]

/-- Leading unary headers are extracted by a bounded scan of the input word. -/
@[fun_prop] theorem certificateDimensionWord_polyTime :
    ComputableInPolyTime certificateDimensionWord encBits encBits := by
  have hstep : ComputableInPolyTime
      (fun p : ((List Bool × (List Bool × List Bool)) × Bool) =>
        dimensionStep p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair encBits (encPair encBits encBits)) encBool) encBits := by
    simp only [dimensionStep]
    fun_prop (config := { maxSteps := 32 })
  have hscan := WordFold.suffixFold_polyTime verifierInput_polyTime verifierInput_polyTime
    (.const []) hstep verifierInput_polyTime.polyBounded_length
    (fun input suffix hpre => by
      rw [dimensionFold_eq]
      exact ((List.takeWhile_sublist _).length_le).trans hpre.length_le)
  have heq : (fun input : List Bool => WordFold.suffixFold dimensionStep input [] input) =
      certificateDimensionWord := by
    funext input
    simp only [certificateDimensionWord, dimensionFold_eq]
  rw [heq] at hscan
  exact hscan

/-- Field addressing multiplies unary lengths, never binary numeric values. -/
@[fun_prop] theorem certificateFieldWord_polyTime :
    ComputableInPolyTime certificateFieldWord (encPi encBits) encBits := by
  have hindex : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hinput : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hcertificate : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 2)
      (encPi encBits) encBits := .pi_apply encBits 2
  have hwidth := certificateWidthWord_polyTime.comp hinput
  have hwidthLength := ComputableInPolyTime.length_bits_comp hwidth
  have hoffset := ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.length_bits_comp hindex) hwidthLength
  exact (hcertificate.bitsDropWithInput hoffset).bitsTakeWithInput hwidthLength

/-- Every field is bounded by its input-determined width even for malformed certificates. -/
theorem certificateFieldWord_length_le (v : Fin 3 → List Bool) :
    (certificateFieldWord v).length ≤ (certificateWidthWord (v 1)).length := by
  exact List.length_take_le _ _

@[fun_prop] theorem certificateWeightWord_polyTime (rowWeights : Bool) :
    ComputableInPolyTime (certificateWeightWord rowWeights) (encPi encBits) encBits := by
  have hdim := certificateDimensionWord_polyTime.comp
    (ComputableInPolyTime.pi_apply encBits (1 : Fin 3))
  have hbase : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => if rowWeights then [] else certificateDimensionWord (v 1))
      (encPi encBits) encBits := by
    cases rowWeights with
    | false => simpa [Function.comp_def] using hdim
    | true => exact .const []
  have hindex := ComputableInPolyTime.bitsAppend (.const (List.replicate 4 true))
    (ComputableInPolyTime.bitsAppend hbase (.pi_apply encBits 0))
  have hargs : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => ![List.replicate 4 true ++
        (if rowWeights then [] else certificateDimensionWord (v 1)) ++ v 0, v 1, v 2])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hindex
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
  exact certificateFieldWord_polyTime.comp hargs

/-- Weight fields obey the fixed binary width bound. -/
theorem certificateWeightWord_length_le (rowWeights : Bool) (v : Fin 3 → List Bool) :
    (certificateWeightWord rowWeights v).length ≤ (certificateWidthWord (v 1)).length :=
  certificateFieldWord_length_le _

@[fun_prop] theorem matrixTallyWord_polyTime (positive : Bool) :
    ComputableInPolyTime (matrixTallyWord positive) (encPi encBits) encBits := by
  let q : (Fin 3 → List Bool) → List Bool := fun v => certificateDimensionWord (v 2)
  let w : (Fin 3 → List Bool) → List Bool := fun v => q v ++ [true, true]
  have hq := certificateDimensionWord_polyTime.comp
    (ComputableInPolyTime.pi_apply encBits (2 : Fin 3))
  have hw : ComputableInPolyTime w (encPi encBits) encBits :=
    ComputableInPolyTime.bitsAppend hq (.const [true, true])
  have hqlen := ComputableInPolyTime.length_bits_comp hq
  have hwlen := ComputableInPolyTime.length_bits_comp hw
  have hrowlen : ComputableInPolyTime (fun v : Fin 3 → List Bool => (v 0).length)
      (encPi encBits) encUnary :=
    ComputableInPolyTime.length_bits_comp (.pi_apply encBits (0 : Fin 3))
  have hcolumnlen : ComputableInPolyTime (fun v : Fin 3 → List Bool => (v 1).length)
      (encPi encBits) encUnary :=
    ComputableInPolyTime.length_bits_comp (.pi_apply encBits (1 : Fin 3))
  have haddress := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul' hrowlen hqlen) hcolumnlen
  have hstride := ComputableInPolyTime.unary_mul' (.const 2) hwlen
  have hoffset := ComputableInPolyTime.unary_mul' haddress hstride
  have hdrop₁ := ComputableInPolyTime.unary_add' hqlen (.const 1)
  have hsign : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => if positive then 0 else (w v).length)
      (encPi encBits) encUnary := by
    cases positive with
    | false => simpa [w, Function.comp_def] using hwlen
    | true => exact .const 0
  have hdrop₂ := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.length_bits_comp hoffset) hsign
  have hword : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 2)
      (encPi encBits) encBits := .pi_apply encBits (2 : Fin 3)
  have hdrop := (hword.bitsDropWithInput hdrop₁).bitsDropWithInput hdrop₂
  have htake := hdrop.bitsTakeWithInput hwlen
  unfold matrixTallyWord
  simpa [q, w, Function.comp_def, List.length_replicate,
    List.length_append, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake

/-- Short and malformed cells remain bounded by the tally width. -/
theorem matrixTallyWord_length_le (positive : Bool) (v : Fin 3 → List Bool) :
    (matrixTallyWord positive v).length ≤ (certificateDimensionWord (v 2)).length + 2 := by
  have hw : (certificateDimensionWord (v 2) ++ [true, true]).length =
      (certificateDimensionWord (v 2)).length + 2 := by simp
  rw [← hw]
  exact List.length_take_le _ _

/-- Binary tally weighting preserves actual machine certificates. -/
@[fun_prop] theorem matrixWeightedTerm_polyTime (rowWeights positive : Bool) :
    ComputableInPolyTime (matrixWeightedTerm rowWeights positive) (encPi encBits) encBits := by
  have htally := reindexProducer (matrixTallyWord_polyTime positive) (![1, 0, 2] : Fin 3 → Fin 4)
  have hvalue := reindexProducer (certificateWeightWord_polyTime rowWeights)
    (![0, 2, 3] : Fin 3 → Fin 4)
  exact binaryTallySum_polyTime htally hvalue

/-- Weighted terms have polynomial binary width irrespective of field values. -/
theorem matrixWeightedTerm_length_le (rowWeights positive : Bool) (v : Fin 4 → List Bool) :
    (matrixWeightedTerm rowWeights positive v).length ≤
      (certificateWidthWord (v 2)).length + (certificateDimensionWord (v 2)).length + 2 := by
  have ht := binaryTallySum_length_le
    (matrixTallyWord positive ![v 1, v 0, v 2])
    (certificateWeightWord rowWeights ![v 0, v 2, v 3])
  have hw := certificateWeightWord_length_le rowWeights ![v 0, v 2, v 3]
  have hm := matrixTallyWord_length_le positive ![v 1, v 0, v 2]
  change (matrixWeightedTerm rowWeights positive v).length ≤ _ at ht
  change (certificateWeightWord rowWeights ![v 0, v 2, v 3]).length ≤
    (certificateWidthWord (v 2)).length at hw
  change (matrixTallyWord positive ![v 1, v 0, v 2]).length ≤
    (certificateDimensionWord (v 2)).length + 2 at hm
  omega

/- Pure-action payoff sums are computed by a genuine polynomial-time machine. -/
@[fun_prop] theorem matrixScoreWord_polyTime (rowWeights positive : Bool) :
    ComputableInPolyTime (matrixScoreWord rowWeights positive) (encPi encBits) encBits := by
  let width : (Fin 3 → List Bool) → List Bool := fun params =>
    certificateWidthWord (params 1) ++ certificateDimensionWord (params 1) ++ [true, true]
  have hwidthWord := certificateWidthWord_polyTime.comp
    (ComputableInPolyTime.pi_apply encBits (1 : Fin 3))
  have hdimensionWord := certificateDimensionWord_polyTime.comp
    (ComputableInPolyTime.pi_apply encBits (1 : Fin 3))
  have hwidth := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend hwidthWord hdimensionWord) (.const [true, true])
  have hparams : ComputableInPolyTime (fun v : Fin 3 → List Bool => v)
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    exact ComputableInPolyTime.pi_apply encBits i
  have hclock := certificateDimensionWord_polyTime.comp
    (ComputableInPolyTime.pi_apply encBits (1 : Fin 3))
  have hbound (suffix : List Bool) (params : Fin 3 → List Bool) :
      (matrixWeightedTerm rowWeights positive (Fin.cons suffix params)).length ≤
        (width params).length := by
    have h := matrixWeightedTerm_length_le rowWeights positive (Fin.cons suffix params)
    have hi : (Fin.cons suffix params : Fin 4 → List Bool) 2 = params 1 := rfl
    rw [hi] at h
    simpa [width, List.length_append, Nat.add_assoc] using h
  change ComputableInPolyTime
    (fun x : Fin 3 → List Bool => binaryIndexedSum (matrixWeightedTerm rowWeights positive)
      (certificateDimensionWord (x 1)) x) (encPi encBits) encBits
  exact
    (binaryIndexedSum_polyTime (p := 3) (Input := Fin 3 → List Bool) (input := encPi encBits)
      (term := matrixWeightedTerm rowWeights positive) (width := width)
      (clock := fun v : Fin 3 → List Bool => certificateDimensionWord (v 1))
      (params := fun v : Fin 3 → List Bool => v)
      (matrixWeightedTerm_polyTime rowWeights positive) hwidth hbound hclock hparams)

/- Simplex numerator sums scan the dimension, rather than denominator values. -/
@[fun_prop] theorem certificateWeightSumWord_polyTime (rowWeights : Bool) :
    ComputableInPolyTime (certificateWeightSumWord rowWeights) (encPi encBits) encBits := by
  let width : (Fin 2 → List Bool) → List Bool := fun params => certificateWidthWord (params 0)
  have hwidth0 := certificateWidthWord_polyTime.comp
    (ComputableInPolyTime.pi_apply encBits (0 : Fin 2))
  have hwidth : ComputableInPolyTime width (encPi encBits) encBits := by
    simpa [width, Function.comp_def] using hwidth0
  have hparams : ComputableInPolyTime (fun v : Fin 2 → List Bool => v)
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    exact ComputableInPolyTime.pi_apply encBits i
  have hclock := certificateDimensionWord_polyTime.comp
    (ComputableInPolyTime.pi_apply encBits (0 : Fin 2))
  have hbound (suffix : List Bool) (params : Fin 2 → List Bool) :
      (certificateWeightWord rowWeights (Fin.cons suffix params)).length ≤ (width params).length := by
    exact certificateWeightWord_length_le rowWeights (Fin.cons suffix params)
  change ComputableInPolyTime
    (fun x : Fin 2 → List Bool => binaryIndexedSum (certificateWeightWord rowWeights)
      (certificateDimensionWord (x 0)) x) (encPi encBits) encBits
  simpa [certificateWeightSumWord, width] using
    (binaryIndexedSum_polyTime (p := 2) (Input := Fin 2 → List Bool) (input := encPi encBits)
      (term := certificateWeightWord rowWeights) (width := width)
      (clock := fun v : Fin 2 → List Bool => certificateDimensionWord (v 0))
      (params := fun v : Fin 2 → List Bool => v)
    (certificateWeightWord_polyTime rowWeights) hwidth hbound hclock hparams)

@[fun_prop] theorem certificateEqualWord_polyTime :
    ComputableInPolyTime (fun v : Fin 2 → List Bool =>
      certificateEqualWord (v 0) (v 1)) (encPi encBits) encBits := by
  have hxy : ComputableInPolyTime (fun v : Fin 2 → List Bool =>
      binaryCertificateLE ![v 0, v 1]) (encPi encBits) encBits := by
    exact binaryCertificateLE_polyTime.comp (by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact .pi_apply encBits 0
      · exact .pi_apply encBits 1)
  have hyx := reindexProducer binaryCertificateLE_polyTime (![1, 0] : Fin 2 → Fin 2)
  have htable : ComputableInPolyTime
      (fun v : Fin 2 → List Bool =>
        (binaryCertificateLE ![v 0, v 1], binaryCertificateLE ![v 1, v 0]))
      (encPi encBits) (encPair encBits encBits) :=
    ComputableInPolyTime.pair hxy hyx
  exact andFlag_polyTime.comp htable

/- Support-sensitive pure-action checks use binary comparisons on exact weighted sums. -/
@[fun_prop] theorem matrixActionCheck_polyTime (columnPlayer : Bool) :
    ComputableInPolyTime (matrixActionCheck columnPlayer) (encPi encBits) encBits := by
  have hpos := matrixScoreWord_polyTime columnPlayer true
  have hneg := matrixScoreWord_polyTime columnPlayer false
  have hutilityTable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        ![List.replicate (if columnPlayer then 3 else 2) true, v 1, v 2])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .const (List.replicate (if columnPlayer then 3 else 2) true)
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
  have hutility := certificateFieldWord_polyTime.comp hutilityTable
  have hsumTable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => ![matrixScoreWord columnPlayer false v,
        certificateFieldWord ![List.replicate (if columnPlayer then 3 else 2) true, v 1, v 2]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hneg
    · exact hutility
  have hbound := binaryCertificateAdd_polyTime.comp hsumTable
  have hleTable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => ![matrixScoreWord columnPlayer true v,
        binaryCertificateAdd ![matrixScoreWord columnPlayer false v,
          certificateFieldWord ![List.replicate (if columnPlayer then 3 else 2) true, v 1, v 2]]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hpos
    · exact hbound
  have hle := binaryCertificateLE_polyTime.comp hleTable
  have hsupport := certificateWeightWord_polyTime (!columnPlayer)
  have hsupportEmpty : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => ![certificateWeightWord (!columnPlayer) v, []])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hsupport
    · exact .const []
  have heqEmpty := certificateEqualWord_polyTime.comp hsupportEmpty
  have heqTable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => ![matrixScoreWord columnPlayer true v,
        binaryCertificateAdd ![matrixScoreWord columnPlayer false v,
          certificateFieldWord ![List.replicate (if columnPlayer then 3 else 2) true, v 1, v 2]]])
      (encPi encBits) (encPi encBits) := hleTable
  have heqScore := certificateEqualWord_polyTime.comp heqTable
  have horTable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        (certificateEqualWord (certificateWeightWord (!columnPlayer) v) [],
          certificateEqualWord (matrixScoreWord columnPlayer true v)
            (binaryCertificateAdd ![matrixScoreWord columnPlayer false v,
              certificateFieldWord ![List.replicate (if columnPlayer then 3 else 2) true, v 1, v 2]])))
      (encPi encBits) (encPair encBits encBits) :=
    ComputableInPolyTime.pair heqEmpty heqScore
  have hor := orFlag_polyTime.comp horTable
  have hfinalTable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        (binaryCertificateLE ![matrixScoreWord columnPlayer true v,
          binaryCertificateAdd ![matrixScoreWord columnPlayer false v,
            certificateFieldWord ![List.replicate (if columnPlayer then 3 else 2) true, v 1, v 2]]],
          orFlag (certificateEqualWord (certificateWeightWord (!columnPlayer) v) [])
            (certificateEqualWord (matrixScoreWord columnPlayer true v)
              (binaryCertificateAdd ![matrixScoreWord columnPlayer false v,
                certificateFieldWord ![List.replicate (if columnPlayer then 3 else 2) true, v 1, v 2]]))))
      (encPi encBits) (encPair encBits encBits) :=
    ComputableInPolyTime.pair hle hor
  unfold matrixActionCheck
  exact andFlag_polyTime.comp hfinalTable

private theorem andFlag_length (x y : List Bool) : (andFlag x y).length = 1 := by
  simp [WordOperations.andFlag]

private theorem certificateAll_length {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool) (clock : List Bool)
    (params : Fin p → List Bool) :
    (certificateAll term clock params).length = 1 := by
  cases clock with
  | nil => rfl
  | cons b clock =>
    rw [certificateAll, WordFold.suffixFold_cons]
    exact andFlag_length _ _

private theorem certificateAllStep_polyTime {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool}
    (hterm : ComputableInPolyTime term (encPi encBits) encBits) :
    ComputableInPolyTime
      (fun z : ((Fin p → List Bool) × (List Bool × List Bool)) × Bool =>
        andFlag z.1.2.2 (term (Fin.cons z.1.2.1 z.1.1)))
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool) encBits := by
  let paramsEncoding : (Fin p → List Bool) ↪ List Bool := encPi encBits
  let termParamsEncoding : (Fin (p + 1) → List Bool) ↪ List Bool := encPi encBits
  let stateEncoding := encPair paramsEncoding (encPair encBits encBits)
  have houter := ComputableInPolyTime.fst stateEncoding encBool
  have hparams := ComputableInPolyTime.fst paramsEncoding
    (encPair encBits encBits)
  have hpair := ComputableInPolyTime.snd paramsEncoding
    (encPair encBits encBits)
  have hsuffix := (ComputableInPolyTime.fst encBits encBits).comp hpair
  have hacc := (ComputableInPolyTime.snd encBits encBits).comp hpair
  have htable : ComputableInPolyTime
      (fun z : (Fin p → List Bool) × (List Bool × List Bool) => Fin.cons z.2.1 z.1)
      stateEncoding termParamsEncoding := by
    apply ComputableInPolyTime.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hsuffix
    · exact (ComputableInPolyTime.pi_apply encBits j).comp hparams
  have hterm' := hterm.comp htable
  have hargs : ComputableInPolyTime
      (fun z : (Fin p → List Bool) × (List Bool × List Bool) =>
        (z.2.2, term (Fin.cons z.2.1 z.1))) stateEncoding (encPair encBits encBits) :=
    ComputableInPolyTime.pair hacc hterm'
  exact (andFlag_polyTime.comp hargs).comp houter

/-- Dimension-bounded conjunction preserves native polynomial-time certificates. -/
@[fun_prop] theorem certificateAll_polyTime {p : ℕ} {Input : Type}
    {input : Input ↪ List Bool}
    {term : (Fin (p + 1) → List Bool) → List Bool}
    {clock : Input → List Bool} {params : Input → Fin p → List Bool}
    (hterm : ComputableInPolyTime term (encPi encBits) encBits)
    (hclock : ComputableInPolyTime clock input encBits)
    (hparams : ComputableInPolyTime params input (encPi encBits)) :
    ComputableInPolyTime
      (fun x => certificateAll term (clock x) (params x)) input encBits := by
  exact WordFold.suffixFold_polyTime hparams hclock (.const [true])
    (certificateAllStep_polyTime hterm) (PolyBounded.const 1)
    (fun x suffix _ => by
      exact Nat.le_of_eq (certificateAll_length term suffix (params x)))

/- All deviation constraints are checked with a dimension-sized iteration clock. -/
@[fun_prop] theorem matrixAllChecks_polyTime (columnPlayer : Bool) :
    ComputableInPolyTime (matrixAllChecks columnPlayer) (encPi encBits) encBits := by
  have hclock := certificateDimensionWord_polyTime.comp
    (ComputableInPolyTime.pi_apply encBits (0 : Fin 2))
  have hclock' : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => certificateDimensionWord (v 0))
      (encPi encBits) encBits := by
    simpa [Function.comp_def] using hclock
  have hparams : ComputableInPolyTime (fun v : Fin 2 → List Bool => v)
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    exact ComputableInPolyTime.pi_apply encBits i
  have hchecks :=
    (certificateAll_polyTime (p := 2) (Input := Fin 2 → List Bool) (input := encPi encBits)
      (term := matrixActionCheck columnPlayer)
      (clock := fun v : Fin 2 → List Bool => certificateDimensionWord (v 0))
      (params := fun v : Fin 2 → List Bool => v)
      (matrixActionCheck_polyTime columnPlayer) hclock' hparams)
  change ComputableInPolyTime
    (fun v : Fin 2 → List Bool =>
      certificateAll (matrixActionCheck columnPlayer) (certificateDimensionWord (v 0)) v)
    (encPi encBits) encBits
  exact hchecks

/- The entire fixed-format Nash certificate verifier has a native machine certificate. -/
theorem binaryCertificateVerifier_polyTime :
    ComputableInPolyTime binaryCertificateVerifier (encPi encBits) encBits := by
  have hfield (i : ℕ) : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => certificateFieldWord ![List.replicate i true, v 0, v 1])
      (encPi encBits) encBits := by
    have htable : ComputableInPolyTime
        (fun v : Fin 2 → List Bool => ![List.replicate i true, v 0, v 1])
        (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro j
      fin_cases j
      · exact .const (List.replicate i true)
      · exact .pi_apply encBits 0
      · exact .pi_apply encBits 1
    exact certificateFieldWord_polyTime.comp htable
  have hf0 := hfield 0
  have hf1 := hfield 1
  have hf2 := hfield 2
  have hf3 := hfield 3
  have hq := certificateDimensionWord_polyTime.comp (.pi_apply encBits (0 : Fin 2))
  have hwidth := certificateWidthWord_polyTime.comp (.pi_apply encBits (0 : Fin 2))
  have hqlen := ComputableInPolyTime.length_bits_comp hq
  have hwlen := ComputableInPolyTime.length_bits_comp hwidth
  have hcertlen := ComputableInPolyTime.length_bits_comp (.pi_apply encBits (1 : Fin 2))
  have hdouble := ComputableInPolyTime.unary_add' hqlen hqlen
  have hheader := ComputableInPolyTime.unary_add' hdouble (.const 4)
  have htotal := ComputableInPolyTime.unary_mul' hheader hwlen
  have heq' := ComputableInPolyTime.of_tidy
      ((ComputableTidilyInPolyTime.decide_eq encUnary).comp (hcertlen.tidy.prod htotal.tidy))
  have heq : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => decide ((v 1).length =
        ((certificateDimensionWord (v 0)).length + (certificateDimensionWord (v 0)).length + 4) *
          (certificateWidthWord (v 0)).length))
      (encPi encBits) encBool := by
    simpa [Function.comp_def] using heq'
  have hlengthFlag := ComputableInPolyTime.bitsCons heq (.const [])
  have heqEmpty0Table : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![certificateFieldWord ![List.replicate 0 true, v 0, v 1], []])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro j
    fin_cases j
    · exact hf0
    · exact .const []
  have heqEmpty1Table : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![certificateFieldWord ![List.replicate 1 true, v 0, v 1], []])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro j
    fin_cases j
    · exact hf1
    · exact .const []
  have hnot0 := notFlag_polyTime.comp (certificateEqualWord_polyTime.comp heqEmpty0Table)
  have hnot1 := notFlag_polyTime.comp (certificateEqualWord_polyTime.comp heqEmpty1Table)
  have hsumTrue := certificateWeightSumWord_polyTime true
  have hsumFalse := certificateWeightSumWord_polyTime false
  have heqTrueTable : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![certificateWeightSumWord true v,
        certificateFieldWord ![List.replicate 0 true, v 0, v 1]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro j
    fin_cases j
    · exact hsumTrue
    · exact hf0
  have heqFalseTable : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![certificateWeightSumWord false v,
        certificateFieldWord ![List.replicate 1 true, v 0, v 1]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro j
    fin_cases j
    · exact hsumFalse
    · exact hf1
  have heqTrue := certificateEqualWord_polyTime.comp heqTrueTable
  have heqFalse := certificateEqualWord_polyTime.comp heqFalseTable
  have hleTopTable : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![
        certificateFieldWord ![List.replicate 1 true, v 0, v 1],
        certificateFieldWord ![List.replicate 2 true, v 0, v 1]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro j
    fin_cases j
    · exact hf1
    · exact hf2
  have hleBottomTable : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![
        certificateFieldWord ![List.replicate 0 true, v 0, v 1],
        certificateFieldWord ![List.replicate 3 true, v 0, v 1]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro j
    fin_cases j
    · exact hf0
    · exact hf3
  have hleTop := binaryCertificateLE_polyTime.comp hleTopTable
  have hleBottom := binaryCertificateLE_polyTime.comp hleBottomTable
  have hallFalse := matrixAllChecks_polyTime false
  have hallTrue := matrixAllChecks_polyTime true
  have andC {f g : (Fin 2 → List Bool) → List Bool}
      (hf : ComputableInPolyTime f (encPi encBits) encBits)
      (hg : ComputableInPolyTime g (encPi encBits) encBits) :
      ComputableInPolyTime (fun v => andFlag (f v) (g v)) (encPi encBits) encBits :=
    andFlag_polyTime.comp (hf.prod hg)
  have hlast := andC hallFalse hallTrue
  have h7 := andC hleBottom hlast
  have h6 := andC hleTop h7
  have h5 := andC heqFalse h6
  have h4 := andC heqTrue h5
  have h3 := andC hnot1 h4
  have h2 := andC hnot0 h3
  have h1 := andC hlengthFlag h2
  apply ComputableInPolyTime.of_tidy
  apply h1.tidy.of_enc_eq
  intro v
  rfl

/-- Every verifier output is exactly one Boolean flag. -/
theorem binaryCertificateVerifier_flag (v : Fin 2 → List Bool) :
    binaryCertificateVerifier v = [true] ∨ binaryCertificateVerifier v = [false] := by
  have hf (x y : List Bool) : andFlag x y = [true] ∨ andFlag x y = [false] := by
    cases x with
    | nil => exact Or.inr rfl
    | cons b x => cases b with
      | false => exact Or.inr rfl
      | true => cases y with
        | nil => exact Or.inr rfl
        | cons c y => cases c with
          | false => exact Or.inr rfl
          | true => exact Or.inl rfl
  exact hf _ _

end GameTheory.Complexity.Backend
