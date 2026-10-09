import GameTheory.Math.FiniteLinearBitBound
import GameTheoryComplexity.Backend.BinaryCertificateFold
import GameTheory.Finite.BimatrixNashCertificate
import GameTheory.Finite.BimatrixTable

/-! A binary certificate verifier for the total signed-tally table decoder.
All iteration clocks are word lengths, dimensions, or tally lengths. -/
namespace GameTheory.Complexity.Backend
open GameTheory.Math (constrainedNashCertificateWidth)
open _root_.Complexity _root_.Complexity.Cobham

/-- Binary certificate field width determined solely by the table input length. -/
def certificateWidthWord (input : List Bool) : List Bool :=
  smash (List.replicate 14 true) (smash input input) ++
    smash (List.replicate 36 true) input ++ List.replicate 23 true

/-- The dimension ruler is the table's initial run of true bits. -/
def certificateDimensionWord (input : List Bool) : List Bool := input.takeWhile id

/-- Read one fixed-width binary field, with total decoding of short certificates. -/
def certificateFieldWord (v : Fin 3 → List Bool) : List Bool :=
  ((v 2).drop ((v 0).length * (certificateWidthWord (v 1)).length)).take
    (certificateWidthWord (v 1)).length

/-- Read a row or column probability numerator indexed by a unary ruler. -/
def certificateWeightWord (rowWeights : Bool) (v : Fin 3 → List Bool) : List Bool :=
  certificateFieldWord ![List.replicate 4 true ++
    (bif rowWeights then [] else certificateDimensionWord (v 1)) ++ v 0, v 1, v 2]

/-- The positive or negative tally of one decoded row-major payoff cell. -/
def matrixTallyWord (positive : Bool) (v : Fin 3 → List Bool) : List Bool :=
  let q := certificateDimensionWord (v 2)
  let w := q ++ [true, true]
  let offset := smash (smash (v 0) q ++ v 1) (w ++ w)
  (((v 2).drop (q.length + 1)).drop
    (offset.length + (bif positive then 0 else w.length))).take w.length

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
  andBit (binaryCertificateLE ![x, y]) (binaryCertificateLE ![y, x])

/-- Check one pure-action inequality and equality on positive support. -/
def matrixActionCheck (columnPlayer : Bool) (v : Fin 3 → List Bool) : List Bool :=
  let pos := matrixScoreWord columnPlayer true v
  let neg := matrixScoreWord columnPlayer false v
  let utility := certificateFieldWord ![List.replicate (bif columnPlayer then 3 else 2) true,
    v 1, v 2]
  let bound := binaryCertificateAdd ![neg, utility]
  let support := certificateWeightWord (!columnPlayer) v
  andBit (binaryCertificateLE ![pos, bound])
    (orBit (certificateEqualWord support []) (certificateEqualWord pos bound))

/-- Accumulate action-check flags over a dimension clock. -/
def certificateAllStep {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (v : Fin (p + 2) → List Bool) : List Bool :=
  andBit (v 1) (term (Fin.cons (v 0) (Fin.tail (Fin.tail v))))

/-- Conjunction of terms indexed by the clock's successive suffix rulers. -/
def certificateAll {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) : List Bool :=
  recNotation (fun _ => [true]) (certificateAllStep term) (certificateAllStep term) clock params

/-- Check all pure-action constraints for one player. -/
def matrixAllChecks (columnPlayer : Bool) (v : Fin 2 → List Bool) : List Bool :=
  certificateAll (matrixActionCheck columnPlayer) (certificateDimensionWord (v 0)) v

/-- Check exact certificate length, normalization, payoff thresholds, and Nash deviations. -/
def binaryCertificateVerifier (v : Fin 2 → List Bool) : List Bool :=
  let q := certificateDimensionWord (v 0)
  let width := certificateWidthWord (v 0)
  let field := fun i => certificateFieldWord ![List.replicate i true, v 0, v 1]
  andBit (lenEqFlag (v 1) (smash (q ++ q ++ List.replicate 4 true) width))
    (andBit (notBit (certificateEqualWord (field 0) []))
    (andBit (notBit (certificateEqualWord (field 1) []))
    (andBit (certificateEqualWord (certificateWeightSumWord true v) (field 0))
    (andBit (certificateEqualWord (certificateWeightSumWord false v) (field 1))
    (andBit (binaryCertificateLE ![field 1, field 2])
    (andBit (binaryCertificateLE ![field 0, field 3])
    (andBit (matrixAllChecks false v) (matrixAllChecks true v))))))))

/-- The width word has the prescribed quadratic length. -/
theorem certificateWidthWord_length (input : List Bool) :
    (certificateWidthWord input).length = constrainedNashCertificateWidth input.length := by
  simp only [certificateWidthWord, constrainedNashCertificateWidth, List.length_append,
    smash_length,
    List.length_replicate, pow_two]

/-- The dimension word has exactly the total decoder's dimension. -/
theorem certificateDimensionWord_length (input : List Bool) :
    (certificateDimensionWord input).length =
      GameTheory.Finite.BimatrixTable.decodeDimension input := rfl

/-- The quadratic width ruler is polynomial-time. -/
theorem certificateWidthWord_cobham : Cobham fun v : Fin 1 → List Bool =>
    certificateWidthWord (v 0) :=
  Cobham.appendFn (Cobham.appendFn
    (Cobham.comp₂ Cobham.smash (Cobham.const (List.replicate 14 true))
      (Cobham.comp₂ Cobham.smash (.proj 0) (.proj 0)))
    (Cobham.comp₂ Cobham.smash (Cobham.const (List.replicate 36 true)) (.proj 0)))
    (Cobham.const (List.replicate 23 true))

/-- Leading unary headers are extracted by a bounded scan of the input word. -/
theorem certificateDimensionWord_cobham : Cobham fun v : Fin 1 → List Bool =>
    certificateDimensionWord (v 0) := by
  have hr : ∀ x (v : Fin 0 → List Bool),
      recNotation (fun _ => []) (fun _ : Fin 2 → List Bool => [])
        (fun w : Fin 2 → List Bool => true :: w 1) x v = x.takeWhile id := by
    intro x v
    induction x with
    | nil => rfl
    | cons b x ih => cases b <;> simp [ih]
  have hs : Cobham fun w : Fin 2 → List Bool => true :: w 1 :=
    (Cobham.comp (.bit true) fun _ => .proj 1).of_eq fun _ => rfl
  exact (Cobham.boundedRec Cobham.empty Cobham.empty hs (.proj 0) (fun x v => by
    rw [hr]
    exact (List.takeWhile_sublist _).length_le)).of_eq fun v => hr _ _

/-- Field addressing multiplies unary lengths, never binary numeric values. -/
theorem certificateFieldWord_cobham : Cobham certificateFieldWord := by
  have hw : Cobham fun v : Fin 3 → List Bool => certificateWidthWord (v 1) :=
    Cobham.comp certificateWidthWord_cobham fun _ => .proj 1
  exact (Cobham.takeFn hw (Cobham.dropFn
    (Cobham.comp₂ Cobham.smash (.proj 0) hw) (.proj 2))).of_eq fun v => by
      simp only [smash_length]
      rfl

/-- Every field is bounded by its input-determined width even for malformed certificates. -/
theorem certificateFieldWord_length_le (v : Fin 3 → List Bool) :
    (certificateFieldWord v).length ≤ (certificateWidthWord (v 1)).length := by
  exact List.length_take_le _ _

/-- Weight addressing is a fixed offset plus a dimension and index ruler. -/
theorem certificateWeightWord_cobham (rowWeights : Bool) :
    Cobham (certificateWeightWord rowWeights) := by
  have hq : Cobham fun v : Fin 3 → List Bool => certificateDimensionWord (v 1) :=
    Cobham.comp certificateDimensionWord_cobham fun _ => .proj 1
  apply Cobham.comp₃ certificateFieldWord_cobham
    (Cobham.appendFn (Cobham.appendFn (Cobham.const (List.replicate 4 true)) ?_) (.proj 0))
    (.proj 1) (.proj 2)
  cases rowWeights
  · exact hq
  · exact Cobham.empty

/-- Weight fields obey the fixed binary width bound. -/
theorem certificateWeightWord_length_le (rowWeights : Bool) (v : Fin 3 → List Bool) :
    (certificateWeightWord rowWeights v).length ≤ (certificateWidthWord (v 1)).length :=
  certificateFieldWord_length_le _

/-- Reading a signed tally cell is polynomial-time in the explicit table word. -/
theorem matrixTallyWord_cobham (positive : Bool) : Cobham (matrixTallyWord positive) := by
  have hq : Cobham fun v : Fin 3 → List Bool => certificateDimensionWord (v 2) :=
    Cobham.comp certificateDimensionWord_cobham fun _ => .proj 2
  have hw : Cobham fun v : Fin 3 → List Bool => certificateDimensionWord (v 2) ++ [true, true] :=
    Cobham.appendFn hq (Cobham.const [true, true])
  have ho := Cobham.comp₂ Cobham.smash
    (Cobham.appendFn (Cobham.comp₂ Cobham.smash (.proj 0) hq) (.proj 1))
    (Cobham.appendFn hw hw)
  have hp : Cobham fun v : Fin 3 → List Bool =>
      bif positive then [] else certificateDimensionWord (v 2) ++ [true, true] := by
    cases positive
    · exact hw
    · exact Cobham.empty
  have hb := Cobham.dropFn (Cobham.appendFn hq (Cobham.const [true])) (.proj 2)
  exact (Cobham.takeFn hw (Cobham.dropFn (Cobham.appendFn ho hp) hb)).of_eq fun v => by
    cases positive <;> simp [matrixTallyWord, List.length_append]

/-- Short and malformed cells remain bounded by the tally width. -/
theorem matrixTallyWord_length_le (positive : Bool) (v : Fin 3 → List Bool) :
    (matrixTallyWord positive v).length ≤ (certificateDimensionWord (v 2)).length + 2 := by
  have hw : (certificateDimensionWord (v 2) ++ [true, true]).length =
      (certificateDimensionWord (v 2)).length + 2 := by simp
  rw [← hw]
  exact List.length_take_le _ _

/-- Binary tally weighting preserves actual machine certificates. -/
theorem matrixWeightedTerm_cobham (rowWeights positive : Bool) :
    Cobham (matrixWeightedTerm rowWeights positive) := by
  apply Cobham.comp₂ binaryTallySum_cobham
  · exact Cobham.comp₃ (matrixTallyWord_cobham positive) (.proj 1) (.proj 0) (.proj 2)
  · exact Cobham.comp₃ (certificateWeightWord_cobham rowWeights) (.proj 0) (.proj 2) (.proj 3)

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

/-- Pure-action payoff sums are computed by a genuine polynomial-time machine. -/
theorem matrixScoreWord_cobham (rowWeights positive : Bool) :
    Cobham (matrixScoreWord rowWeights positive) := by
  let width := fun v : Fin 3 → List Bool =>
    certificateWidthWord (v 1) ++ certificateDimensionWord (v 1) ++ [true, true]
  have hw : Cobham width := Cobham.appendFn (Cobham.appendFn
    (Cobham.comp certificateWidthWord_cobham fun _ => .proj 1)
    (Cobham.comp certificateDimensionWord_cobham fun _ => .proj 1))
    (Cobham.const [true, true])
  have hf := binaryIndexedSum_cobham (matrixWeightedTerm_cobham rowWeights positive) hw
    (fun r v => by
      have h := matrixWeightedTerm_length_le rowWeights positive (Fin.cons r v)
      change (matrixWeightedTerm rowWeights positive (Fin.cons r v)).length ≤
        (certificateWidthWord (v 1)).length + (certificateDimensionWord (v 1)).length + 2 at h
      simpa only [width, List.length_append, List.length_cons, List.length_nil] using h)
  have hg : ∀ i : Fin 4, Cobham fun v : Fin 3 → List Bool =>
      (Fin.cons (certificateDimensionWord (v 1)) v : Fin 4 → List Bool) i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Cobham.comp certificateDimensionWord_cobham fun _ => .proj 1
    · exact Cobham.proj j
  exact (Cobham.comp hf hg).of_eq fun _ => rfl

/-- Simplex numerator sums scan the dimension, rather than denominator values. -/
theorem certificateWeightSumWord_cobham (rowWeights : Bool) :
    Cobham (certificateWeightSumWord rowWeights) := by
  have hw : Cobham fun v : Fin 2 → List Bool => certificateWidthWord (v 0) :=
    Cobham.comp certificateWidthWord_cobham fun _ => .proj 0
  have hf := binaryIndexedSum_cobham (certificateWeightWord_cobham rowWeights) hw
    (fun r v => certificateWeightWord_length_le rowWeights (Fin.cons r v))
  have hg : ∀ i : Fin 3, Cobham fun v : Fin 2 → List Bool =>
      (Fin.cons (certificateDimensionWord (v 0)) v : Fin 3 → List Bool) i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Cobham.comp certificateDimensionWord_cobham fun _ => .proj 0
    · exact Cobham.proj j
  exact (Cobham.comp hf hg).of_eq fun _ => rfl

private theorem certificateEqualWord_cobham : Cobham fun v : Fin 2 → List Bool =>
    certificateEqualWord (v 0) (v 1) :=
  Cobham.andFn binaryCertificateLE_cobham
    (Cobham.comp₂ binaryCertificateLE_cobham (.proj 1) (.proj 0))

/-- Support-sensitive pure-action checks use binary comparisons on exact weighted sums. -/
theorem matrixActionCheck_cobham (columnPlayer : Bool) :
    Cobham (matrixActionCheck columnPlayer) := by
  have hp := matrixScoreWord_cobham columnPlayer true
  have hn := matrixScoreWord_cobham columnPlayer false
  have hu := Cobham.comp₃ certificateFieldWord_cobham
    (Cobham.const (List.replicate (bif columnPlayer then 3 else 2) true))
    (Cobham.proj (1 : Fin 3)) (Cobham.proj 2)
  have hb := Cobham.comp₂ binaryCertificateAdd_cobham hn hu
  exact Cobham.andFn (Cobham.comp₂ binaryCertificateLE_cobham hp hb)
    (Cobham.orFn
      (Cobham.comp₂ certificateEqualWord_cobham
        (certificateWeightWord_cobham (!columnPlayer)) Cobham.empty)
      (Cobham.comp₂ certificateEqualWord_cobham hp hb))

private theorem andBit_length (x y : List Bool) : (andBit x y).length = 1 := by
  cases x with
  | nil => rfl
  | cons b x => cases b with
    | false => rfl
    | true => cases y with
      | nil => rfl
      | cons c y => cases c <;> rfl

private theorem certificateAll_length {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool) (clock : List Bool)
    (params : Fin p → List Bool) :
    (certificateAll term clock params).length = 1 := by
  cases clock with
  | nil => rfl
  | cons b clock => simp only [certificateAll, recNotation_cons, Bool.cond_self,
      certificateAllStep, andBit_length]

/-- Dimension-bounded conjunction preserves real polynomial-time certificates. -/
theorem certificateAll_cobham {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool} (ht : Cobham term) :
    Cobham fun v : Fin (p + 1) → List Bool => certificateAll term (v 0) (Fin.tail v) := by
  have hs : Cobham (certificateAllStep term) := by
    apply Cobham.andFn (.proj 1)
    apply Cobham.comp ht
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Cobham.proj 0
    · exact Cobham.proj j.succ.succ
  exact (Cobham.boundedRec (Cobham.const [true]) hs hs (Cobham.const [true])
    (fun r v => (certificateAll_length term r v).le)).of_eq fun _ => rfl

/-- All deviation constraints are checked with a dimension-sized iteration clock. -/
theorem matrixAllChecks_cobham (columnPlayer : Bool) : Cobham (matrixAllChecks columnPlayer) := by
  have hf := certificateAll_cobham (matrixActionCheck_cobham columnPlayer)
  have hg : ∀ i : Fin 3, Cobham fun v : Fin 2 → List Bool =>
      (Fin.cons (certificateDimensionWord (v 0)) v : Fin 3 → List Bool) i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Cobham.comp certificateDimensionWord_cobham fun _ => .proj 0
    · exact Cobham.proj j
  exact (Cobham.comp hf hg).of_eq fun _ => rfl

/-- The entire fixed-format Nash certificate verifier is polynomial-time. -/
theorem binaryCertificateVerifier_cobham : Cobham binaryCertificateVerifier := by
  have hq : Cobham fun v : Fin 2 → List Bool => certificateDimensionWord (v 0) :=
    Cobham.comp certificateDimensionWord_cobham fun _ => .proj 0
  have hw : Cobham fun v : Fin 2 → List Bool => certificateWidthWord (v 0) :=
    Cobham.comp certificateWidthWord_cobham fun _ => .proj 0
  have hfield (i : ℕ) : Cobham fun v : Fin 2 → List Bool =>
      certificateFieldWord ![List.replicate i true, v 0, v 1] :=
    Cobham.comp₃ certificateFieldWord_cobham (Cobham.const (List.replicate i true))
      (.proj 0) (.proj 1)
  have heq {x y : (Fin 2 → List Bool) → List Bool} (hx : Cobham x) (hy : Cobham y) :=
    Cobham.comp₂ certificateEqualWord_cobham hx hy
  exact Cobham.andFn
    (lenEqFlag_mem (.proj 1) (Cobham.comp₂ Cobham.smash
      (Cobham.appendFn (Cobham.appendFn hq hq) (Cobham.const (List.replicate 4 true))) hw))
    (Cobham.andFn (Cobham.notFn (heq (hfield 0) Cobham.empty))
    (Cobham.andFn (Cobham.notFn (heq (hfield 1) Cobham.empty))
    (Cobham.andFn (heq (certificateWeightSumWord_cobham true) (hfield 0))
    (Cobham.andFn (heq (certificateWeightSumWord_cobham false) (hfield 1))
    (Cobham.andFn (Cobham.comp₂ binaryCertificateLE_cobham (hfield 1) (hfield 2))
    (Cobham.andFn (Cobham.comp₂ binaryCertificateLE_cobham (hfield 0) (hfield 3))
    (Cobham.andFn (matrixAllChecks_cobham false) (matrixAllChecks_cobham true))))))))

/-- The verifier certificate is for a real deterministic machine on binary words. -/
theorem binaryCertificateVerifier_mem_FPn : FPn binaryCertificateVerifier :=
  cobham_iff_FPn.mp binaryCertificateVerifier_cobham

/-- Every verifier output is exactly one Boolean flag. -/
theorem binaryCertificateVerifier_flag (v : Fin 2 → List Bool) :
    binaryCertificateVerifier v = [true] ∨ binaryCertificateVerifier v = [false] := by
  have hf (x y : List Bool) : andBit x y = [true] ∨ andBit x y = [false] := by
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
