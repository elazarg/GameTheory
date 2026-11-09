module

public import GameTheoryComplexity.Backend.BinarySignedMatrixMachine
public import GameTheoryComplexity.Backend.BinaryBirdWidth
public import GameTheoryComplexity.Backend.WordOperations
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

@[expose] public section

/-! Fixed-width, materialized Bird determinant machines.

Dimension and field widths are unary length rulers. Diagonal and product sums
normalize every stored accumulator; rows and complete stages are materialized
as packed fixed-width tables.
-/

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations
open scoped BigOperators

/-- Arguments: row-index ruler, column-index ruler, dimension ruler, width ruler, packed matrix. -/
def binaryBirdField (v : Fin 5 → List Bool) : List Bool :=
  binarySignedRowField ![List.replicate ((v 0).length * (v 2).length) true ++ v 1, v 3, v 4]

@[fun_prop] theorem binaryBirdField_polyTime :
    ComputableInPolyTime binaryBirdField (encPi encBits) encBits := by
  have hrow : ComputableInPolyTime (fun v : Fin 5 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hcol : ComputableInPolyTime (fun v : Fin 5 → List Bool => v 2)
      (encPi encBits) encBits := .pi_apply encBits 2
  have hrowLength := ComputableInPolyTime.length_bits_comp hrow
  have hcolLength := ComputableInPolyTime.length_bits_comp hcol
  have hspacer := (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.unary_mul' hrowLength hcolLength)
  have hfirst := ComputableInPolyTime.bitsAppend hspacer
    (ComputableInPolyTime.pi_apply encBits 1)
  have hargs : ComputableInPolyTime
      (fun v : Fin 5 → List Bool =>
        ![List.replicate ((v 0).length * (v 2).length) true ++ v 1, v 3, v 4])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hfirst
    · exact ComputableInPolyTime.pi_apply encBits 3
    · exact ComputableInPolyTime.pi_apply encBits 4
  exact binarySignedRowField_polyTime.comp hargs

private def binaryBirdDiagTerm (v : Fin 5 → List Bool) : List Bool :=
  if (v 0).length ≤ (v 4).length then []
  else binaryBirdField ![v 0, v 0, v 2, v 1, v 3]

private theorem binaryBirdDiagTerm_polyTime :
    ComputableInPolyTime binaryBirdDiagTerm (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 5 → List Bool => ![v 0, v 0, v 2, v 1, v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 3
  have hfield := binaryBirdField_polyTime.comp hargs
  have hleftWord : ComputableInPolyTime (fun v : Fin 5 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hrightWord : ComputableInPolyTime (fun v : Fin 5 → List Bool => v 4)
      (encPi encBits) encBits := .pi_apply encBits 4
  have hleft := ComputableInPolyTime.length_bits_comp hleftWord
  have hright := ComputableInPolyTime.length_bits_comp hrightWord
  have hcondition := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.unary_le' hleft.tidy hright.tidy)
  exact .of_tidy (.ite_decide hcondition.tidy (.const []) hfield.tidy)

/-- Arguments: dimension, width, previous matrix, row-index ruler. -/
def binaryBirdDiagSum (v : Fin 4 → List Bool) : List Bool :=
  binarySignedSum binaryBirdDiagTerm (v 0) (v 1) ![v 1, v 0, v 2, v 3]

@[fun_prop] theorem binaryBirdDiagSum_polyTime :
    ComputableInPolyTime binaryBirdDiagSum (encPi encBits) encBits := by
  have hsum := binarySignedSum_polyTime (p := 4) (term := binaryBirdDiagTerm) binaryBirdDiagTerm_polyTime
  have hargs : ComputableInPolyTime
      (fun v : Fin 4 → List Bool => ![v 0, v 1, v 1, v 0, v 2, v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
  have hsum' := hsum.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply hsum'.tidy.of_enc_eq
  intro v
  change binaryBirdDiagSum v = binarySignedSum binaryBirdDiagTerm (v 0) (v 1)
    (Fin.tail (Fin.tail (![v 0, v 1, v 1, v 0, v 2, v 3] : Fin 6 → List Bool)))
  unfold binaryBirdDiagSum
  apply congrArg (binarySignedSum binaryBirdDiagTerm (v 0) (v 1))
  funext i
  fin_cases i <;> rfl

private def binaryBirdCrossTerm (v : Fin 7 → List Bool) : List Bool :=
  if (v 0).length ≤ (v 5).length then []
  else binarySignedMul (binaryBirdField ![v 5, v 0, v 2, v 1, v 4])
      (binaryBirdField ![v 0, v 6, v 2, v 1, v 3])

private theorem binaryBirdCrossTerm_polyTime :
    ComputableInPolyTime binaryBirdCrossTerm (encPi encBits) encBits := by
  have hargs₁ : ComputableInPolyTime
      (fun v : Fin 7 → List Bool => ![v 5, v 0, v 2, v 1, v 4])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i <;> first | exact .pi_apply encBits 5 | exact .pi_apply encBits 0 |
      exact .pi_apply encBits 2 | exact .pi_apply encBits 1 | exact .pi_apply encBits 4
  have hargs₂ : ComputableInPolyTime
      (fun v : Fin 7 → List Bool => ![v 0, v 6, v 2, v 1, v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i <;> first | exact .pi_apply encBits 0 | exact .pi_apply encBits 6 |
      exact .pi_apply encBits 2 | exact .pi_apply encBits 1 | exact .pi_apply encBits 3
  have hleft := binaryBirdField_polyTime.comp hargs₁
  have hright := binaryBirdField_polyTime.comp hargs₂
  have hmul := binarySignedMul_polyTime hleft hright
  have hword₀ : ComputableInPolyTime (fun v : Fin 7 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hword₅ : ComputableInPolyTime (fun v : Fin 7 → List Bool => v 5)
      (encPi encBits) encBits := .pi_apply encBits 5
  have hlength₀ := ComputableInPolyTime.length_bits_comp hword₀
  have hlength₅ := ComputableInPolyTime.length_bits_comp hword₅
  have hcondition := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.unary_le' hlength₀.tidy hlength₅.tidy)
  exact .of_tidy (.ite_decide hcondition.tidy (.const []) hmul.tidy)

/-- Arguments: dimension, width, original matrix, previous matrix, row and column rulers. -/
def binaryBirdCrossSum (v : Fin 6 → List Bool) : List Bool :=
  binarySignedSum binaryBirdCrossTerm (v 0) (v 1) ![v 1, v 0, v 2, v 3, v 4, v 5]

@[fun_prop] theorem binaryBirdCrossSum_polyTime :
    ComputableInPolyTime binaryBirdCrossSum (encPi encBits) encBits := by
  have hsum := binarySignedSum_polyTime (p := 6) (term := binaryBirdCrossTerm) binaryBirdCrossTerm_polyTime
  have hargs : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => ![v 0, v 1, v 1, v 0, v 2, v 3, v 4, v 5])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 4
    · exact .pi_apply encBits 5
  have hsum' := hsum.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply hsum'.tidy.of_enc_eq
  intro v
  change binaryBirdCrossSum v = binarySignedSum binaryBirdCrossTerm (v 0) (v 1)
    (Fin.tail (Fin.tail (![v 0, v 1, v 1, v 0, v 2, v 3, v 4, v 5] : Fin 8 → List Bool)))
  unfold binaryBirdCrossSum
  apply congrArg (binarySignedSum binaryBirdCrossTerm (v 0) (v 1))
  funext i
  fin_cases i <;> rfl

/-- One fixed-width division-free Bird entry. -/
def binaryBirdEntry (v : Fin 6 → List Bool) : List Bool :=
  binarySignedFixedAdd (v 1)
    (binarySignedFixedMul (v 1)
      (binarySignedNeg (binaryBirdDiagSum ![v 0, v 1, v 3, v 4]))
      (binaryBirdField ![v 4, v 5, v 0, v 1, v 2]))
    (binaryBirdCrossSum v)

@[simp] theorem binaryBirdEntry_length (v : Fin 6 → List Bool) :
    (binaryBirdEntry v).length = (v 1).length := binarySignedFixedAdd_length _ _ _

@[fun_prop] theorem binaryBirdEntry_polyTime :
    ComputableInPolyTime binaryBirdEntry (encPi encBits) encBits := by
  have hdiagArgs : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => ![v 0, v 1, v 3, v 4])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 4
  have hfieldArgs : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => ![v 4, v 5, v 0, v 1, v 2])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 4
    · exact .pi_apply encBits 5
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
  have hwidth : ComputableInPolyTime (fun v : Fin 6 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hdiag := binaryBirdDiagSum_polyTime.comp hdiagArgs
  have hfield := binaryBirdField_polyTime.comp hfieldArgs
  have hneg := binarySignedNeg_polyTime hdiag
  have hmul := binarySignedFixedMul_polyTime hwidth hneg hfield
  exact binarySignedFixedAdd_polyTime hwidth hmul binaryBirdCrossSum_polyTime

private def binaryBirdRowTerm (v : Fin 6 → List Bool) : List Bool :=
  binaryBirdEntry ![v 1, v 2, v 3, v 4, v 5, v 0]

private theorem binaryBirdRowTerm_polyTime :
    ComputableInPolyTime binaryBirdRowTerm (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => ![v 1, v 2, v 3, v 4, v 5, v 0])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 4
    · exact .pi_apply encBits 5
    · exact .pi_apply encBits 0
  exact binaryBirdEntry_polyTime.comp hargs

/-- Materialize one row; arguments are dimension, width, original and previous matrices, row ruler. -/
def binaryBirdRow (v : Fin 5 → List Bool) : List Bool :=
  binarySignedTable binaryBirdRowTerm (v 0) (v 1) ![v 0, v 1, v 2, v 3, v 4]

@[simp] theorem binaryBirdRow_length (v : Fin 5 → List Bool) :
    (binaryBirdRow v).length = (v 0).length * (v 1).length := binarySignedTable_length _ _ _ _

@[fun_prop] theorem binaryBirdRow_polyTime :
    ComputableInPolyTime binaryBirdRow (encPi encBits) encBits := by
  have htable := binarySignedTable_polyTime (p := 5) (term := binaryBirdRowTerm) binaryBirdRowTerm_polyTime
  have hargs : ComputableInPolyTime
      (fun v : Fin 5 → List Bool => ![v 0, v 1, v 0, v 1, v 2, v 3, v 4])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 4
  have htable' := htable.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply htable'.tidy.of_enc_eq
  intro v
  change binaryBirdRow v = binarySignedTable binaryBirdRowTerm (v 0) (v 1)
    (Fin.tail (Fin.tail (![v 0, v 1, v 0, v 1, v 2, v 3, v 4] : Fin 7 → List Bool)))
  unfold binaryBirdRow
  apply congrArg (binarySignedTable binaryBirdRowTerm (v 0) (v 1))
  funext i
  fin_cases i <;> rfl

private def binaryBirdStageTerm (v : Fin 5 → List Bool) : List Bool :=
  binaryBirdRow ![v 1, v 2, v 3, v 4, v 0]

private theorem binaryBirdStageTerm_polyTime :
    ComputableInPolyTime binaryBirdStageTerm (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 5 → List Bool => ![v 1, v 2, v 3, v 4, v 0])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 4
    · exact .pi_apply encBits 0
  exact binaryBirdRow_polyTime.comp hargs

/-- Materialize a complete Bird stage; arguments are dimension, width, original and previous matrices. -/
def binaryBirdStage (v : Fin 4 → List Bool) : List Bool :=
  binarySignedTable binaryBirdStageTerm (v 0)
    (List.replicate ((v 0).length * (v 1).length) true) ![v 0, v 1, v 2, v 3]

@[simp] theorem binaryBirdStage_length (v : Fin 4 → List Bool) :
    (binaryBirdStage v).length = (v 0).length * (v 0).length * (v 1).length := by
  rw [binaryBirdStage, binarySignedTable_length]
  simp [Nat.mul_assoc]

@[fun_prop] theorem binaryBirdStage_polyTime :
    ComputableInPolyTime binaryBirdStage (encPi encBits) encBits := by
  have htable := binarySignedTable_polyTime (p := 4) (term := binaryBirdStageTerm) binaryBirdStageTerm_polyTime
  have hdim : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hwidth : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hspacer := (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.length_bits_comp hdim)
      (ComputableInPolyTime.length_bits_comp hwidth))
  have hargs : ComputableInPolyTime
      (fun v : Fin 4 → List Bool =>
        ![v 0, List.replicate ((v 0).length * (v 1).length) true, v 0, v 1, v 2, v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hdim
    · exact hspacer
    · exact hdim
    · exact hwidth
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
  have htable' := htable.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply htable'.tidy.of_enc_eq
  intro v
  change binaryBirdStage v = binarySignedTable binaryBirdStageTerm (v 0)
    (List.replicate ((v 0).length * (v 1).length) true)
    (Fin.tail (Fin.tail (![v 0, List.replicate ((v 0).length * (v 1).length) true,
      v 0, v 1, v 2, v 3] : Fin 6 → List Bool)))
  unfold binaryBirdStage
  apply congrArg (binarySignedTable binaryBirdStageTerm (v 0)
    (List.replicate ((v 0).length * (v 1).length) true))
  funext i
  fin_cases i <;> rfl

/-- Iterate materialized stages; the stored matrix size depends only on dimension and width. -/
def binaryBirdStages (clock dim width A : List Bool) : List Bool :=
  let context : Fin 3 → List Bool := ![dim, width, A]
  let initial := (A ++ List.replicate (dim.length * dim.length * width.length) false).take
    (dim.length * dim.length * width.length)
  WordFold.suffixFold
    (fun (context : Fin 3 → List Bool) (_suffix state : List Bool) (_bit : Bool) =>
      binaryBirdStage ![context 0, context 1, context 2, state])
    context initial clock

@[simp] theorem binaryBirdStages_length (clock dim width A : List Bool) :
    (binaryBirdStages clock dim width A).length = dim.length * dim.length * width.length := by
  cases clock with
  | nil => simp [binaryBirdStages]
  | cons b r =>
    simp only [binaryBirdStages, WordFold.suffixFold_cons, binaryBirdStage_length]
    simp [Nat.mul_assoc]

private theorem binaryBirdStages_step_polyTime :
    ComputableInPolyTime
      (fun p : ((Fin 3 → List Bool) × (List Bool × List Bool)) × Bool =>
        binaryBirdStage ![p.1.1 0, p.1.1 1, p.1.1 2, p.1.2.2])
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool) encBits := by
  have houter : ComputableInPolyTime
      (fun p : ((Fin 3 → List Bool) × (List Bool × List Bool)) × Bool => p.1)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool)
      (encPair (encPi encBits) (encPair encBits encBits)) :=
    .fst (encPair (encPi encBits) (encPair encBits encBits)) encBool
  have hcontext : ComputableInPolyTime
      (fun p : ((Fin 3 → List Bool) × (List Bool × List Bool)) × Bool => p.1.1)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool)
      (encPi encBits) :=
    (ComputableInPolyTime.fst (encPi encBits) (encPair encBits encBits)).comp houter
  have hstate : ComputableInPolyTime
      (fun p : ((Fin 3 → List Bool) × (List Bool × List Bool)) × Bool => p.1.2.2)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool) encBits :=
    (ComputableInPolyTime.snd encBits encBits).comp
      ((ComputableInPolyTime.snd (encPi encBits) (encPair encBits encBits)).comp houter)
  have hargs : ComputableInPolyTime
      (fun p : ((Fin 3 → List Bool) × (List Bool × List Bool)) × Bool =>
        ![p.1.1 0, p.1.1 1, p.1.1 2, p.1.2.2])
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool)
      (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact (ComputableInPolyTime.pi_apply encBits (0 : Fin 3)).comp hcontext
    · exact (ComputableInPolyTime.pi_apply encBits (1 : Fin 3)).comp hcontext
    · exact (ComputableInPolyTime.pi_apply encBits (2 : Fin 3)).comp hcontext
    · exact hstate
  exact binaryBirdStage_polyTime.comp hargs

@[fun_prop] theorem binaryBirdStages_polyTime :
    ComputableInPolyTime
      (fun v : Fin 4 → List Bool => binaryBirdStages (v 0) (v 1) (v 2) (v 3))
      (encPi encBits) encBits := by
  let context : (Fin 4 → List Bool) → Fin 3 → List Bool := fun v => ![v 1, v 2, v 3]
  let word : (Fin 4 → List Bool) → List Bool := fun v => v 0
  let initial : (Fin 4 → List Bool) → List Bool := fun v =>
    (v 3 ++ List.replicate ((v 1).length * (v 1).length * (v 2).length) false).take
      ((v 1).length * (v 1).length * (v 2).length)
  let step : (Fin 3 → List Bool) → List Bool → List Bool → Bool → List Bool :=
    fun c _suffix state _bit => binaryBirdStage ![c 0, c 1, c 2, state]
  have hcontext : ComputableInPolyTime context (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
  have hword : ComputableInPolyTime word (encPi encBits) encBits := .pi_apply encBits 0
  have hdim : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hwidth : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 2)
      (encPi encBits) encBits := .pi_apply encBits 2
  have hinitial : ComputableInPolyTime initial (encPi encBits) encBits := by
    have hdimLength := ComputableInPolyTime.length_bits_comp hdim
    have hwidthLength := ComputableInPolyTime.length_bits_comp hwidth
    have hsize := ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.unary_mul' hdimLength hdimLength) hwidthLength
    have hpad := ComputableInPolyTime.bitsAppend (ComputableInPolyTime.pi_apply encBits (3 : Fin 4))
      ((ComputableInPolyTime.bitsReplicate false).comp hsize)
    simpa only [initial, Function.comp_def] using hpad.bitsTakeWithInput hsize
  have hstep : ComputableInPolyTime
      (fun p : ((Fin 3 → List Bool) × (List Bool × List Bool)) × Bool =>
        step p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool) encBits :=
    binaryBirdStages_step_polyTime
  have hbound : PolyBounded (fun v : Fin 4 → List Bool => (encPi encBits v).length)
      (fun v => (v 1).length * (v 1).length * (v 2).length) :=
    (hdim.polyBounded_length.mul hdim.polyBounded_length).mul hwidth.polyBounded_length
  have hstates : ∀ v suffix, suffix <:+ word v →
      (WordFold.suffixFold step (context v) (initial v) suffix).length ≤
        (v 1).length * (v 1).length * (v 2).length := by
    intro v suffix _
    have hlen := binaryBirdStages_length suffix (v 1) (v 2) (v 3)
    simpa [binaryBirdStages, context, initial, step] using hlen.le
  exact WordFold.suffixFold_polyTime hcontext hword hinitial hstep hbound hstates

/-- A two-bit signed word for `(-1)` raised to the clock length. -/
def binaryBirdSign (clock : List Bool) : List Bool :=
  WordFold.suffixFold
    (fun (_ : Fin 0 → List Bool) (_suffix state : List Bool) (_bit : Bool) =>
      notFlag state ++ [true])
    ![] [false, true] clock

@[simp] theorem binaryBirdSign_length (clock : List Bool) : (binaryBirdSign clock).length = 2 := by
  cases clock with
  | nil => rfl
  | cons b r =>
    simp [binaryBirdSign, WordFold.suffixFold_cons, notFlag]

private theorem binaryBirdSign_tail (clock : List Bool) : (binaryBirdSign clock).tail = [true] := by
  cases clock with
  | nil => rfl
  | cons b r =>
    simp [binaryBirdSign, WordFold.suffixFold_cons, notFlag]

theorem binaryBirdSign_value (clock : List Bool) :
    binarySignedValue (binaryBirdSign clock) = (-1 : ℤ) ^ clock.length := by
  induction clock with
  | nil => rfl
  | cons b r ih =>
    simp only [binaryBirdSign, WordFold.suffixFold_cons]
    change binarySignedValue (notFlag (binaryBirdSign r) ++ [true]) = (-1 : ℤ) ^ (b :: r).length
    have he : notFlag (binaryBirdSign r) ++ [true] = binarySignedNeg (binaryBirdSign r) := by
      rw [binarySignedNeg, binaryBirdSign_tail]
      simp [WordOperations.notFlag]
    rw [he, binarySignedNeg_value, ih, List.length_cons, pow_succ]
    ring

@[fun_prop] theorem binaryBirdSign_polyTime :
    ComputableInPolyTime binaryBirdSign encBits encBits := by
  let context : List Bool → Fin 0 → List Bool := fun _ => ![]
  let initial : List Bool → List Bool := fun _ => [false, true]
  let step : (Fin 0 → List Bool) → List Bool → List Bool → Bool → List Bool :=
    fun _ _ state _ => notFlag state ++ [true]
  have hcontext : ComputableInPolyTime context encBits (encPi encBits) := .const ![]
  have hinitial : ComputableInPolyTime initial encBits encBits := .const [false, true]
  have houter : ComputableInPolyTime
      (fun p : ((Fin 0 → List Bool) × (List Bool × List Bool)) × Bool => p.1)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool)
      (encPair (encPi encBits) (encPair encBits encBits)) :=
    .fst (encPair (encPi encBits) (encPair encBits encBits)) encBool
  have hstate : ComputableInPolyTime
      (fun p : ((Fin 0 → List Bool) × (List Bool × List Bool)) × Bool => p.1.2.2)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool) encBits :=
    (ComputableInPolyTime.snd encBits encBits).comp
      ((ComputableInPolyTime.snd (encPi encBits) (encPair encBits encBits)).comp houter)
  have hstep : ComputableInPolyTime
      (fun p : ((Fin 0 → List Bool) × (List Bool × List Bool)) × Bool =>
        step p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool) encBits :=
    (notFlag_polyTime.comp hstate).bitsAppend (ComputableInPolyTime.const [true])
  exact WordFold.suffixFold_polyTime hcontext (ComputableInPolyTime.id' (encIn := encBits))
    hinitial hstep (PolyBounded.const 2)
    (fun _clock suffix _ => by
      simpa only [context, initial, step, binaryBirdSign] using (binaryBirdSign_length suffix).le)

/-- Fixed-width division-free determinant computation; arguments are dimension, width, packed matrix. -/
def binaryBirdDeterminant (v : Fin 3 → List Bool) : List Bool :=
  if (v 0).isEmpty then binarySignedFixed (v 1) [false, true]
  else binarySignedFixedMul (v 1) (binaryBirdSign (v 0).tail)
      (binaryBirdField ![[], [], v 0, v 1, binaryBirdStages (v 0).tail (v 0) (v 1) (v 2)])

@[simp] theorem binaryBirdDeterminant_length (v : Fin 3 → List Bool) :
    (binaryBirdDeterminant v).length = (v 1).length := by
  unfold binaryBirdDeterminant
  cases h : v 0 with
  | nil => simp
  | cons b r => simp

@[fun_prop] theorem binaryBirdDeterminant_polyTime :
    ComputableInPolyTime binaryBirdDeterminant (encPi encBits) encBits := by
  have hdim : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hwidth : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hmatrix : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 2)
      (encPi encBits) encBits := .pi_apply encBits 2
  have htail := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hdim
  have hstageArgs : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => ![(v 0).tail, v 0, v 1, v 2])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact htail
    · exact hdim
    · exact hwidth
    · exact hmatrix
  have hstages := binaryBirdStages_polyTime.comp hstageArgs
  have hfieldArgs : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        ![[], [], v 0, v 1, binaryBirdStages (v 0).tail (v 0) (v 1) (v 2)])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .const []
    · exact .const []
    · exact hdim
    · exact hwidth
    · exact hstages
  have hfield := binaryBirdField_polyTime.comp hfieldArgs
  have hsign := binaryBirdSign_polyTime.comp htail
  have hmul := binarySignedFixedMul_polyTime hwidth hsign hfield
  have hunit := binarySignedFixed_polyTime hwidth (ComputableInPolyTime.const [false, true])
  have hempty := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.bitsIsEmpty.comp hdim.tidy)
  exact hempty.ite hunit hmul

theorem binaryBirdField_value (v : Fin 5 → List Bool) :
    binarySignedValue (binaryBirdField v) =
      binarySignedRowValue (v 3) (v 4) ((v 0).length * (v 2).length + (v 1).length) := by
  change binarySignedValue (((v 4).drop
    ((List.replicate ((v 0).length * (v 2).length) true ++ v 1).length * (v 3).length)).take
      (v 3).length) = _
  simp only [List.length_append, List.length_replicate]
  rfl

private theorem binaryBirdDiagTerm_value (v : Fin 5 → List Bool) :
    binarySignedValue (binaryBirdDiagTerm v) =
      if (v 4).length < (v 0).length then
        binarySignedRowValue (v 1) (v 3) ((v 0).length * (v 2).length + (v 0).length) else 0 := by
  by_cases hk : (v 4).length < (v 0).length
  · simp [binaryBirdDiagTerm, not_le_of_gt hk, binaryBirdField_value]
  · have hle : (v 0).length ≤ (v 4).length := by omega
    simp [binaryBirdDiagTerm, hle, binarySignedValue, hk, Turing.MultiTapeTM.ofBits]

theorem binaryBirdDiagSum_value (v : Fin 4 → List Bool) (hr : 0 < (v 1).length)
    (hbound : ∀ t ≤ (v 0).length,
      (∑ k ∈ Finset.range t, if (v 3).length < k then
        binarySignedRowValue (v 1) (v 2) (k * (v 0).length + k) else 0).natAbs <
          2 ^ ((v 1).length - 1)) :
    binarySignedValue (binaryBirdDiagSum v) =
      ∑ k ∈ Finset.range (v 0).length, if (v 3).length < k then
        binarySignedRowValue (v 1) (v 2) (k * (v 0).length + k) else 0 := by
  apply binarySignedSum_value _ _ _ _ _ hr _ hbound
  intro r
  exact binaryBirdDiagTerm_value _
private theorem binaryBirdCrossTerm_value (v : Fin 7 → List Bool) :
    binarySignedValue (binaryBirdCrossTerm v) =
      if (v 5).length < (v 0).length then
        binarySignedRowValue (v 1) (v 4) ((v 5).length * (v 2).length + (v 0).length) *
        binarySignedRowValue (v 1) (v 3) ((v 0).length * (v 2).length + (v 6).length) else 0 := by
  by_cases hk : (v 5).length < (v 0).length
  · simp only [binaryBirdCrossTerm, not_le_of_gt hk, ↓reduceIte,
      binarySignedMul_value, binaryBirdField_value, hk]
    rfl
  · have hle : (v 0).length ≤ (v 5).length := by omega
    simp [binaryBirdCrossTerm, hle, binarySignedValue, hk, Turing.MultiTapeTM.ofBits]

theorem binaryBirdCrossSum_value (v : Fin 6 → List Bool) (hr : 0 < (v 1).length)
    (hbound : ∀ t ≤ (v 0).length,
      (∑ k ∈ Finset.range t, if (v 4).length < k then
        binarySignedRowValue (v 1) (v 3) ((v 4).length * (v 0).length + k) *
        binarySignedRowValue (v 1) (v 2) (k * (v 0).length + (v 5).length) else 0).natAbs <
          2 ^ ((v 1).length - 1)) :
    binarySignedValue (binaryBirdCrossSum v) =
      ∑ k ∈ Finset.range (v 0).length, if (v 4).length < k then
        binarySignedRowValue (v 1) (v 3) ((v 4).length * (v 0).length + k) *
        binarySignedRowValue (v 1) (v 2) (k * (v 0).length + (v 5).length) else 0 := by
  apply binarySignedSum_value _ _ _ _ _ hr _ hbound
  intro r
  exact binaryBirdCrossTerm_value _
theorem binaryBirdEntry_value (v : Fin 6 → List Bool) (D P : ℤ)
    (hr : 0 < (v 1).length)
    (hD : binarySignedValue (binaryBirdDiagSum ![v 0, v 1, v 3, v 4]) = D)
    (hP : binarySignedValue (binaryBirdCrossSum v) = P)
    (hmul : (-D * binarySignedRowValue (v 1) (v 2)
      ((v 4).length * (v 0).length + (v 5).length)).natAbs < 2 ^ ((v 1).length - 1))
    (hadd : (-D * binarySignedRowValue (v 1) (v 2)
      ((v 4).length * (v 0).length + (v 5).length) + P).natAbs < 2 ^ ((v 1).length - 1)) :
    binarySignedValue (binaryBirdEntry v) =
      -D * binarySignedRowValue (v 1) (v 2)
        ((v 4).length * (v 0).length + (v 5).length) + P := by
  have hF : binarySignedValue (binaryBirdField ![v 4, v 5, v 0, v 1, v 2]) =
      binarySignedRowValue (v 1) (v 2) ((v 4).length * (v 0).length + (v 5).length) :=
    binaryBirdField_value _
  have hM : binarySignedValue (binarySignedFixedMul (v 1)
      (binarySignedNeg (binaryBirdDiagSum ![v 0, v 1, v 3, v 4]))
      (binaryBirdField ![v 4, v 5, v 0, v 1, v 2])) =
      -D * binarySignedRowValue (v 1) (v 2)
        ((v 4).length * (v 0).length + (v 5).length) := by
    rw [binarySignedFixedMul_value _ _ _ hr]
    · rw [binarySignedNeg_value, hD, hF]
    · simpa only [binarySignedNeg_value, hD, hF] using hmul
  unfold binaryBirdEntry
  rw [binarySignedFixedAdd_value _ _ _ hr]
  · rw [hM, hP]
  · simpa only [hM, hP] using hadd
theorem binaryBirdRow_field (v : Fin 5 → List Bool) (j : ℕ) (hj : j < (v 0).length) :
    ((binaryBirdRow v).drop (j * (v 1).length)).take (v 1).length =
      binaryBirdEntry ![v 0, v 1, v 2, v 3, v 4, (v 0).drop ((v 0).length - j)] := by
  rw [binaryBirdRow, binarySignedTable_field _ _ _ _ j hj]
  change binarySignedFixed (v 1) (binaryBirdEntry _) = _
  exact binarySignedFixed_eq_of_length _ _ (binaryBirdEntry_length _)

theorem binaryBirdStage_row (v : Fin 4 → List Bool) (i : ℕ) (hi : i < (v 0).length) :
    ((binaryBirdStage v).drop (i * ((v 0).length * (v 1).length))).take
      ((v 0).length * (v 1).length) =
      binaryBirdRow ![v 0, v 1, v 2, v 3, (v 0).drop ((v 0).length - i)] := by
  have h := binarySignedTable_field binaryBirdStageTerm (v 0)
    (List.replicate ((v 0).length * (v 1).length) true)
    ![v 0, v 1, v 2, v 3] i hi
  change _ = binarySignedFixed (List.replicate ((v 0).length * (v 1).length) true)
    (binaryBirdRow _) at h
  rw [binarySignedFixed_eq_of_length] at h
  · let packed : Fin 5 → List Bool :=
      Fin.cons ((v 0).drop ((v 0).length - i)) ![v 0, v 1, v 2, v 3]
    have hrow : binaryBirdRow ![packed 1, packed 2, packed 3, packed 4, packed 0] =
        binaryBirdRow ![v 0, v 1, v 2, v 3, (v 0).drop ((v 0).length - i)] := by
      apply congrArg binaryBirdRow
      funext j
      fin_cases j <;> rfl
    simpa only [binaryBirdStage, List.length_replicate] using h.trans hrow
  · rw [binaryBirdRow_length, List.length_replicate]
    rfl

theorem binaryBirdStage_field (v : Fin 4 → List Bool) (i j : ℕ)
    (hi : i < (v 0).length) (hj : j < (v 0).length) :
    ((binaryBirdStage v).drop ((i * (v 0).length + j) * (v 1).length)).take (v 1).length =
      binaryBirdEntry ![v 0, v 1, v 2, v 3,
        (v 0).drop ((v 0).length - i), (v 0).drop ((v 0).length - j)] := by
  have h := congrArg (fun x : List Bool => (x.drop (j * (v 1).length)).take (v 1).length)
    (binaryBirdStage_row v i hi)
  rw [List.drop_take, List.drop_drop, List.take_take] at h
  have hm : (v 1).length ≤ (v 0).length * (v 1).length - j * (v 1).length := by
    have hb := Nat.mul_le_mul_right (v 1).length (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at hb
    omega
  rw [Nat.min_eq_left hm, ← Nat.mul_assoc, ← Nat.add_mul] at h
  exact h.trans (binaryBirdRow_field ![v 0, v 1, v 2, v 3, (v 0).drop ((v 0).length - i)] j hj)
@[simp] theorem binaryBirdStages_nil (dim width A : List Bool) :
    binaryBirdStages [] dim width A =
      (A ++ List.replicate (dim.length * dim.length * width.length) false).take
        (dim.length * dim.length * width.length) := rfl

@[simp] theorem binaryBirdStages_cons (b : Bool) (r dim width A : List Bool) :
    binaryBirdStages (b :: r) dim width A =
      binaryBirdStage ![dim, width, A, binaryBirdStages r dim width A] := by
  simp only [binaryBirdStages, WordFold.suffixFold_cons]
  rfl
end GameTheory.Complexity.Backend
