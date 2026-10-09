import GameTheoryComplexity.Backend.GeneralBimatrixDictionary
import GameTheoryComplexity.Backend.BinaryDictionaryFeasibility
import GameTheoryComplexity.Backend.BimatrixNodeWord
import GameTheoryComplexity.Backend.GeneralBimatrixVerifierMachine
import GameTheoryComplexity.Backend.GeneralBimatrixVerifierCorrectness

/-! Arithmetic and syntactic validation of complementary path words.
The same reconstructed integer dictionary drives feasibility and later pivots. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- Decode the two masks and recover the entering variable's canonical position. -/
def generalBimatrixNodeData (v : Fin 2 → List Bool) : Fin 3 → List Bool :=
  let dim := generalBimatrixDimensionWord (v 0)
  ![v 0, bimatrixNodeBasicWord ![dim, v 1],
    (binarySubsetNth ![bimatrixNodeEnteringWord ![dim, v 1], []]).tail]

theorem generalBimatrixNodeData_cobham (i : Fin 3) :
    Cobham fun v : Fin 2 → List Bool => generalBimatrixNodeData v i := by
  have hd : Cobham fun v : Fin 2 → List Bool => generalBimatrixDimensionWord (v 0) :=
    (Cobham.comp generalBimatrixDimensionWord_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  fin_cases i
  · exact .proj 0
  · exact (Cobham.comp₂ bimatrixNodeBasicWord_cobham hd (.proj 1)).of_eq fun _ => rfl
  · have he : Cobham fun v : Fin 2 → List Bool =>
        bimatrixNodeEnteringWord ![generalBimatrixDimensionWord (v 0), v 1] :=
      Cobham.comp₂ bimatrixNodeEnteringWord_cobham hd (.proj 1)
    exact (Cobham.tailFn (Cobham.comp₂ binarySubsetNth_cobham he Cobham.empty)).of_eq fun _ => rfl

/-- Compute invertibility and strict lexicographic positivity from the stored integer fields. -/
def generalBimatrixNodeFeasibleFlag (v : Fin 2 → List Bool) : List Bool :=
  let data := generalBimatrixNodeData v
  andBit (binarySignedNonzero (generalBimatrixDictionaryDeterminant data))
    (binaryDictionaryPositive ![generalBimatrixDictionaryDimension data,
      true :: generalBimatrixDictionaryDimension data, generalBimatrixDictionaryWidth data,
      generalBimatrixDictionaryCoefficients data])

theorem generalBimatrixNodeFeasibleFlag_cobham : Cobham generalBimatrixNodeFeasibleFlag := by
  have hd := Cobham.comp generalBimatrixDictionaryDimension_cobham generalBimatrixNodeData_cobham
  have hw := Cobham.comp generalBimatrixDictionaryWidth_cobham generalBimatrixNodeData_cobham
  have hc := Cobham.comp generalBimatrixDictionaryCoefficients_cobham generalBimatrixNodeData_cobham
  have ht := Cobham.comp generalBimatrixDictionaryDeterminant_cobham generalBimatrixNodeData_cobham
  have hp : Cobham fun v : Fin 2 → List Bool => binaryDictionaryPositive
      ![generalBimatrixDictionaryDimension (generalBimatrixNodeData v),
        true :: generalBimatrixDictionaryDimension (generalBimatrixNodeData v),
        generalBimatrixDictionaryWidth (generalBimatrixNodeData v),
        generalBimatrixDictionaryCoefficients (generalBimatrixNodeData v)] := by
    apply Cobham.comp binaryDictionaryPositive_cobham
    intro i
    fin_cases i
    · exact hd
    · exact Cobham.comp (.bit true) fun _ : Fin 1 => hd
    · exact hw
    · exact hc
  exact (Cobham.andFn (Cobham.comp binarySignedNonzero_cobham fun _ : Fin 1 => ht) hp).of_eq
    fun _ => rfl

/-- Only a well-formed game and a genuine feasible path port pass validation. -/
def generalBimatrixNodeValidFlag (v : Fin 2 → List Bool) : List Bool :=
  andBit (generalInstanceFlag (v 0))
    (andBit (bimatrixNodeSyntaxFlag ![generalBimatrixDimensionWord (v 0), v 1])
      (generalBimatrixNodeFeasibleFlag v))

theorem generalBimatrixNodeValidFlag_cobham : Cobham generalBimatrixNodeValidFlag := by
  have hi := Cobham.comp generalInstanceFlag_cobham fun _ : Fin 1 => (.proj 0 : Cobham
    fun v : Fin 2 → List Bool => v 0)
  have hd := Cobham.comp generalBimatrixDimensionWord_cobham fun _ : Fin 1 => (.proj 0 : Cobham
    fun v : Fin 2 → List Bool => v 0)
  exact Cobham.andFn hi (Cobham.andFn
    (Cobham.comp₂ bimatrixNodeSyntaxFlag_cobham hd (.proj 1)) generalBimatrixNodeFeasibleFlag_cobham)

theorem generalBimatrixNodeValidFlag_mem_FPn : FPn generalBimatrixNodeValidFlag :=
  cobham_iff_FPn.mp generalBimatrixNodeValidFlag_cobham

set_option backward.isDefEq.respectTransparency false in
/-- Exact decoded determinant and coefficient fields identify the integer feasibility check. -/
theorem generalBimatrixNodeFeasibleFlag_iff (v : Fin 2 → List Bool)
    (M : Matrix (Fin (generalBimatrixDictionaryDimension (generalBimatrixNodeData v)).length)
      (Fin (generalBimatrixDictionaryDimension (generalBimatrixNodeData v)).length) ℤ)
    (hd : binarySignedValue (generalBimatrixDictionaryDeterminant (generalBimatrixNodeData v)) =
      GameTheory.Math.IntegerCramerComputation.determinant M)
    (hc : ∀ i j, binarySignedMatrixValue
      (true :: generalBimatrixDictionaryDimension (generalBimatrixNodeData v))
      (generalBimatrixDictionaryWidth (generalBimatrixNodeData v))
      (generalBimatrixDictionaryCoefficients (generalBimatrixNodeData v)) i.val j.val =
      GameTheory.Math.IntegerDictionaryComputation.coefficients M (fun _ => 1) i j) :
    generalBimatrixNodeFeasibleFlag v = [true] ↔
      GameTheory.Math.IntegerFeasible M := by
  have andTrue (a b : Bool) : andBit [a] [b] = [true] ↔ a = true ∧ b = true := by
    cases a <;> cases b <;> decide
  rw [generalBimatrixNodeFeasibleFlag, binarySignedNonzero_value, binaryDictionaryPositive_value,
    andTrue]
  simp only [decide_eq_true_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, hd]
  unfold GameTheory.Math.IntegerFeasible
  constructor
  · rintro ⟨hdet, hrows⟩
    refine ⟨hdet, fun i => ?_⟩
    have h := hrows i.val i.isLt
    have he : (fun j => binarySignedMatrixValue
        (true :: generalBimatrixDictionaryDimension (generalBimatrixNodeData v))
        (generalBimatrixDictionaryWidth (generalBimatrixNodeData v))
        (generalBimatrixDictionaryCoefficients (generalBimatrixNodeData v)) i.val j.val) =
        GameTheory.Math.IntegerDictionaryComputation.coefficients M (fun _ => 1) i :=
      funext (hc i)
    change GameTheory.Math.FiniteLexicographicCompare.lexLT
      (fun _ : Fin ((generalBimatrixDictionaryDimension (generalBimatrixNodeData v)).length + 1) => (0 : ℤ))
      (fun j => binarySignedMatrixValue
        (true :: generalBimatrixDictionaryDimension (generalBimatrixNodeData v))
        (generalBimatrixDictionaryWidth (generalBimatrixNodeData v))
        (generalBimatrixDictionaryCoefficients (generalBimatrixNodeData v)) i.val j.val) = true at h
    rw [he] at h
    exact h
  · rintro ⟨hdet, hrows⟩
    refine ⟨hdet, fun i hi => ?_⟩
    have he : (fun j => binarySignedMatrixValue
        (true :: generalBimatrixDictionaryDimension (generalBimatrixNodeData v))
        (generalBimatrixDictionaryWidth (generalBimatrixNodeData v))
        (generalBimatrixDictionaryCoefficients (generalBimatrixNodeData v)) i j.val) =
        GameTheory.Math.IntegerDictionaryComputation.coefficients M (fun _ => 1) ⟨i, hi⟩ :=
      funext (hc ⟨i, hi⟩)
    change GameTheory.Math.FiniteLexicographicCompare.lexLT
      (fun _ : Fin ((generalBimatrixDictionaryDimension (generalBimatrixNodeData v)).length + 1) => (0 : ℤ))
      (fun j => binarySignedMatrixValue
        (true :: generalBimatrixDictionaryDimension (generalBimatrixNodeData v))
        (generalBimatrixDictionaryWidth (generalBimatrixNodeData v))
        (generalBimatrixDictionaryCoefficients (generalBimatrixNodeData v)) i j.val) = true
    rw [he]
    exact hrows ⟨i, hi⟩

/-- The controller receives the exact basis membership of a canonical port. -/
theorem generalBimatrixNodeData_basis {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    (input : List Bool) (hk : (generalBimatrixDimensionWord input).length = m + n)
    {d : Fin (m + n)} (port : GameTheory.Finite.BimatrixPathPort A B d) :
    generalBimatrixNodeData ![input, GameTheory.Finite.BimatrixPathBinaryCodec.encode port] 1 =
      GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord port.node.basis.basic := by
  change bimatrixNodeBasicWord ![generalBimatrixDimensionWord input,
    GameTheory.Finite.BimatrixPathBinaryCodec.encode port] = _
  rw [bimatrixNodeBasicWord_membership _ _ hk,
    GameTheory.Finite.BimatrixPathBinaryCodec.basic_encode]

/-- One-hot lookup supplies the canonical entering position to the arithmetic controller. -/
theorem generalBimatrixNodeData_entering {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    (input : List Bool) (hk : (generalBimatrixDimensionWord input).length = m + n)
    {d : Fin (m + n)} (hd : d.val = 0) (port : GameTheory.Finite.BimatrixPathPort A B d) :
    (generalBimatrixNodeData ![input, GameTheory.Finite.BimatrixPathBinaryCodec.encode port] 2).length =
      (GameTheory.Finite.BimatrixPathBinaryCodec.index port.entering).val := by
  open GameTheory.Finite.BimatrixPathBinaryCodec in
  have he : bimatrixNodeEnteringWord ![generalBimatrixDimensionWord input, encode port] =
      membershipWord {port.entering} := by
    rw [bimatrixNodeEnteringWord_membership _ _ hk d hd, enteringSet_encode]
  open GameTheory.Finite.BimatrixPathBinaryCodec in
  have hs : binarySubsetNthPosition ![membershipWord {port.entering}, []] =
      some (index port.entering).val := by
    apply (binarySubsetNth_value _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · simpa only [membershipWord, List.length_ofFn, Matrix.cons_val_zero] using
        (index port.entering).isLt
    · simp [membershipWord, (index port.entering).isLt]
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, List.length_nil,
        membershipWord_prefix_count]
      simp
  change (binarySubsetNth ![bimatrixNodeEnteringWord ![generalBimatrixDimensionWord input,
    GameTheory.Finite.BimatrixPathBinaryCodec.encode port], []]).tail.length = _
  rw [he]
  change (if (binarySubsetNth _).headD false then some (binarySubsetNth _).tail.length
    else none) = some _ at hs
  split at hs
  · exact Option.some.inj hs
  · contradiction

end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

private theorem nodeData_eq (input node : List Bool) :
    generalBimatrixNodeData ![input, node] =
      ![input, membershipWord (basic (m := generalRowCount input) (n := generalColCount input) node),
        generalBimatrixNodeData ![input, node] 2] := by
  funext i
  fin_cases i
  · rfl
  · exact bimatrixNodeBasicWord_membership _ _ (generalBimatrixDimensionWord_length input)
  · rfl

theorem generalBimatrixNodeFeasibleFlag_candidate_iff (input node : List Bool)
    (hs : (basic (m := generalRowCount input) (n := generalColCount input) node).card =
      generalRowCount input + generalColCount input) :
    generalBimatrixNodeFeasibleFlag ![input, node] = [true] ↔
      GameTheory.Math.IntegerFeasible (generalBimatrixCandidateMatrix input (basic node) hs) := by
  let s := basic (m := generalRowCount input) (n := generalColCount input) node
  let e := generalBimatrixNodeData ![input, node] 2
  let d := generalBimatrixDimensionWord input
  let W := generalBimatrixDictionaryWidth ![input, membershipWord s, e]
  let P := generalBimatrixDictionaryMatrix ![input, membershipWord s, e]
  let C := generalBimatrixDictionaryCoefficients ![input, membershipWord s, e]
  let M := binaryBirdMatrix d W P
  obtain ⟨hw, hl, hb⟩ := generalBimatrixDictionaryCandidateMatrix_hypotheses input s hs e
  have hd : binarySignedValue (generalBimatrixDictionaryDeterminant
      (generalBimatrixNodeData ![input, node])) = GameTheory.Math.IntegerCramerComputation.determinant M := by
    rw [nodeData_eq]
    exact (binaryBirdDeterminant_value d W P (generalCoefficientBits input + 2) hw hl hb).trans
      (GameTheory.Math.IntegerCramerComputation.determinant_eq M).symm
  have hc : ∀ i j, binarySignedMatrixValue
      (true :: generalBimatrixDictionaryDimension (generalBimatrixNodeData ![input, node]))
      (generalBimatrixDictionaryWidth (generalBimatrixNodeData ![input, node]))
      (generalBimatrixDictionaryCoefficients (generalBimatrixNodeData ![input, node])) i.val j.val =
      GameTheory.Math.IntegerDictionaryComputation.coefficients M (fun _ => 1) i j := by
    intro i j
    rw [nodeData_eq]
    change binarySignedMatrixValue (true :: d) W C i.val j.val = _
    rw [binarySignedMatrixValue_eq_flat _ _ _ _ _ j.isLt]
    exact binaryDictionaryCoefficients_value d W P (generalCoefficientBits input + 2) hw hl hb i j
  have hiff := generalBimatrixNodeFeasibleFlag_iff ![input, node] M hd hc
  have hm : (fun i j : Fin (generalRowCount input + generalColCount input) =>
      binarySignedRowValue W P (i.val * (generalRowCount input + generalColCount input) + j.val)) =
      generalBimatrixCandidateMatrix input s hs := by
    funext i j
    exact generalBimatrixDictionaryCandidateMatrix_integer input s hs e i j
  have he : GameTheory.Math.IntegerFeasible M ↔ GameTheory.Math.IntegerFeasible (generalBimatrixCandidateMatrix input s hs) := by
    unfold M binaryBirdMatrix
    generalize hdim : d.length = size
    have hsize : size = generalRowCount input + generalColCount input := hdim.symm.trans (generalBimatrixDimensionWord_length input)
    clear hdim
    subst size
    rw [hm]
  exact hiff.trans he
end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

/-- Ports of the positive game obtained by shifting the serialized integer payoffs. -/
abbrev GeneralBimatrixShiftedPort (input : List Bool)
    (d : Fin (generalRowCount input + generalColCount input)) :=
  BimatrixPathPort
    (fun i j => decodeGeneralPayoff false input i.val j.val +
      ((2 : ℤ) ^ generalCoefficientBits input + 1))
    (fun i j => decodeGeneralPayoff true input i.val j.val +
      ((2 : ℤ) ^ generalCoefficientBits input + 1)) d

/-- The path controller omits label zero. Valid instances have a nonempty label set. -/
def generalBimatrixDistinguishedLabel (input : List Bool) (hi : GeneralInstanceValid input) :
    Fin (generalRowCount input + generalColCount input) :=
  ⟨0, by have h := hi.1; omega⟩

@[simp] theorem generalBimatrixDistinguishedLabel_val (input : List Bool)
    (hi : GeneralInstanceValid input) : (generalBimatrixDistinguishedLabel input hi).val = 0 := rfl

private theorem nodeValid_flags_iff (input node : List Bool) :
    generalBimatrixNodeValidFlag ![input, node] = [true] ↔
      GeneralInstanceValid input ∧
      bimatrixNodeSyntaxFlag ![generalBimatrixDimensionWord input, node] = [true] ∧
      generalBimatrixNodeFeasibleFlag ![input, node] = [true] := by
  have hs : bimatrixNodeSyntaxFlag ![generalBimatrixDimensionWord input, node] = [true] ∨
      bimatrixNodeSyntaxFlag ![generalBimatrixDimensionWord input, node] = [false] := by
    rw [bimatrixNodeSyntaxFlag_value]
    simp only [List.cons.injEq, and_true]
    exact Bool.eq_false_or_eq_true _
  have hi : generalInstanceFlag input = [true] ∨ generalInstanceFlag input = [false] := by
    exact andBit_flag _ _
  have hf : generalBimatrixNodeFeasibleFlag ![input, node] = [true] ∨
      generalBimatrixNodeFeasibleFlag ![input, node] = [false] := by
    exact andBit_flag _ _
  unfold generalBimatrixNodeValidFlag
  change andBit (generalInstanceFlag input)
    (andBit (bimatrixNodeSyntaxFlag ![generalBimatrixDimensionWord input, node])
      (generalBimatrixNodeFeasibleFlag ![input, node])) = [true] ↔ _
  rw [andBit_eq_true_iff hi (andBit_flag _ _),
    andBit_eq_true_iff hs hf, generalInstanceFlag_eq_true_iff]
end GameTheory.Complexity.Backend



namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

theorem generalBimatrixNodeValidFlag_encode (input : List Bool)
    (hi : GeneralInstanceValid input)
    {d : Fin (generalRowCount input + generalColCount input)} (hd : d.val = 0)
    (port : GeneralBimatrixShiftedPort input d) :
    generalBimatrixNodeValidFlag ![input, encode port] = [true] := by
  apply (nodeValid_flags_iff input (encode port)).mpr
  refine ⟨hi, ?_, ?_⟩
  · apply (bimatrixNodeSyntaxFlag_codec _ _ (generalBimatrixDimensionWord_length input) d hd).mpr
    simp only [encode_length, basic_encode, enteringSet_encode, Finset.card_singleton]
    exact ⟨trivial, port.node.basis.cardinality, trivial, port.node.coverage, by
      intro v hv
      have hv' : v = port.entering := Finset.mem_singleton.mp hv
      subst v
      exact port.permitted⟩
  · have hs : (basic (m := generalRowCount input) (n := generalColCount input) (encode port)).card =
        generalRowCount input + generalColCount input := by
      rw [basic_encode]
      exact port.node.basis.cardinality
    apply (generalBimatrixNodeFeasibleFlag_candidate_iff input (encode port) hs).mpr
    have hh := integerFeasible_basis port.node.basis
    unfold generalBimatrixCandidateMatrix
    generalize hb : basic (encode port) = s at hs ⊢
    have he : s = port.node.basis.basic := hb.symm.trans (basic_encode port)
    clear hb
    subst s
    exact hh

/-- The machine accepts exactly canonical ports of the shifted game at omitted label zero. -/
theorem generalBimatrixNodeValidFlag_iff (input node : List Bool) :
    generalBimatrixNodeValidFlag ![input, node] = [true] ↔
      GeneralInstanceValid input ∧
      ∃ (d : Fin (generalRowCount input + generalColCount input))
        (port : GeneralBimatrixShiftedPort input d),
        d.val = 0 ∧ decode _ _ d node = some port := by
  constructor
  · intro hv
    obtain ⟨hi, hsyntax, hfeasible⟩ := (nodeValid_flags_iff input node).mp hv
    let d := generalBimatrixDistinguishedLabel input hi
    obtain ⟨hw, hs, he, hc, hp⟩ :=
      (bimatrixNodeSyntaxFlag_codec _ _ (generalBimatrixDimensionWord_length input) d rfl).mp hsyntax
    have hf := (generalBimatrixNodeFeasibleFlag_candidate_iff input node hs).mp hfeasible
    obtain ⟨port, hport⟩ := exists_decode_of_checks d node hw hs he hf hc hp
    exact ⟨hi, d, port, rfl, hport⟩
  · rintro ⟨hi, d, port, hd, hdecode⟩
    rw [← encode_of_decode_eq_some hdecode]
    exact generalBimatrixNodeValidFlag_encode input hi hd port
end GameTheory.Complexity.Backend


namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

theorem generalBimatrixNodeValidFlag_flag (input node : List Bool) :
    generalBimatrixNodeValidFlag ![input, node] = [true] ∨
      generalBimatrixNodeValidFlag ![input, node] = [false] :=
  andBit_flag _ _

/-- At the distinguished label, machine validation is precisely successful decoding. -/
theorem generalBimatrixNodeValidFlag_iff_decode (input node : List Bool)
    (hi : GeneralInstanceValid input)
    (d : Fin (generalRowCount input + generalColCount input)) (hd : d.val = 0) :
    generalBimatrixNodeValidFlag ![input, node] = [true] ↔
      ∃ port : GeneralBimatrixShiftedPort input d, decode _ _ d node = some port := by
  rw [generalBimatrixNodeValidFlag_iff]
  constructor
  · rintro ⟨_, e, port, he, hdecode⟩
    have hed : e = d := Fin.ext (he.trans hd.symm)
    subst e
    exact ⟨port, hdecode⟩
  · rintro ⟨port, hdecode⟩
    exact ⟨hi, d, port, hd, hdecode⟩

/-- A failed canonical decoder yields the machine's false flag. -/
theorem generalBimatrixNodeValidFlag_eq_false_of_decode_none (input node : List Bool)
    (hi : GeneralInstanceValid input)
    (d : Fin (generalRowCount input + generalColCount input)) (hd : d.val = 0)
    (hdecode : decode
      (fun i j => decodeGeneralPayoff false input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1))
      (fun i j => decodeGeneralPayoff true input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1)) d node = none) :
    generalBimatrixNodeValidFlag ![input, node] = [false] := by
  rcases generalBimatrixNodeValidFlag_flag input node with hv | hv
  · obtain ⟨port, hp⟩ := (generalBimatrixNodeValidFlag_iff_decode input node hi d hd).mp hv
    rw [hdecode] at hp
    contradiction
  · exact hv
end GameTheory.Complexity.Backend
