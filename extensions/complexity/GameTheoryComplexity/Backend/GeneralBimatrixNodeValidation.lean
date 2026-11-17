module

public import GameTheoryComplexity.Backend.GeneralBimatrixDictionary
public import GameTheoryComplexity.Backend.BinaryDictionaryFeasibility
public import GameTheoryComplexity.Backend.BimatrixNodeWord
public import GameTheoryComplexity.Backend.GeneralBimatrixVerifierMachine
public import GameTheoryComplexity.Backend.GeneralBimatrixVerifierCorrectness
public import GameTheoryComplexity.Backend.WordOperations

@[expose] public section

/-! Arithmetic and syntactic validation of complementary path words.
The same reconstructed integer dictionary drives feasibility and later pivots. -/

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

private theorem andFlag_flag (left right : List Bool) :
    andFlag left right = [true] ∨ andFlag left right = [false] := by
  cases left.headD false <;> cases right.headD false <;> simp [andFlag]

private theorem andFlag_eq_true_of_flags (left right : List Bool)
    (hl : left = [true] ∨ left = [false]) (hr : right = [true] ∨ right = [false]) :
    andFlag left right = [true] ↔ left = [true] ∧ right = [true] := by
  rcases hl with rfl | rfl <;> rcases hr with rfl | rfl <;> decide

/-- Decode the two masks and recover the entering variable's canonical position. -/
def generalBimatrixNodeData (v : Fin 2 → List Bool) : Fin 3 → List Bool :=
  let dim := generalBimatrixDimensionWord (v 0)
  ![v 0, bimatrixNodeBasicWord ![dim, v 1],
    (binarySubsetNth ![bimatrixNodeEnteringWord ![dim, v 1], []]).tail]

/-- Compute invertibility and strict lexicographic positivity from the stored integer fields. -/
def generalBimatrixNodeFeasibleFlag (v : Fin 2 → List Bool) : List Bool :=
  let data := generalBimatrixNodeData v
  andFlag (binarySignedNonzero (generalBimatrixDictionaryDeterminant data))
    (binaryDictionaryPositive ![generalBimatrixDictionaryDimension data,
      true :: generalBimatrixDictionaryDimension data, generalBimatrixDictionaryWidth data,
      generalBimatrixDictionaryCoefficients data])

/-- Only a well-formed game and a genuine feasible path port pass validation. -/
def generalBimatrixNodeValidFlag (v : Fin 2 → List Bool) : List Bool :=
  andFlag (generalInstanceFlag (v 0))
    (andFlag (bimatrixNodeSyntaxFlag ![generalBimatrixDimensionWord (v 0), v 1])
      (generalBimatrixNodeFeasibleFlag v))

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
  have andTrue (a b : Bool) : andFlag [a] [b] = [true] ↔ a = true ∧ b = true := by
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
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations
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
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations
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
    exact andFlag_flag _ _
  have hf : generalBimatrixNodeFeasibleFlag ![input, node] = [true] ∨
      generalBimatrixNodeFeasibleFlag ![input, node] = [false] := by
    exact andFlag_flag _ _
  unfold generalBimatrixNodeValidFlag
  change andFlag (generalInstanceFlag input)
    (andFlag (bimatrixNodeSyntaxFlag ![generalBimatrixDimensionWord input, node])
      (generalBimatrixNodeFeasibleFlag ![input, node])) = [true] ↔ _
  rw [andFlag_eq_true_of_flags _ _ hi (andFlag_flag _ _),
    andFlag_eq_true_of_flags _ _ hs hf, generalInstanceFlag_eq_true_iff]
end GameTheory.Complexity.Backend



namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations
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
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

theorem generalBimatrixNodeValidFlag_flag (input node : List Bool) :
    generalBimatrixNodeValidFlag ![input, node] = [true] ∨
      generalBimatrixNodeValidFlag ![input, node] = [false] :=
  andFlag_flag _ _

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

@[fun_prop] theorem generalBimatrixNodeData_polyTime :
    ComputableInPolyTime generalBimatrixNodeData (encPi encBits) (encPi encBits) := by
  have hinput : ComputableInPolyTime (fun v : Fin 2 → List Bool => ![v 0])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact .pi_apply encBits (0 : Fin 2)
  have hdim0 := generalBimatrixDimensionWord_polyTime.comp hinput
  have hdim : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => generalBimatrixDimensionWord (v 0))
      (encPi encBits) encBits := by
    apply ComputableInPolyTime.of_tidy
    apply hdim0.tidy.of_enc_eq
    intro v
    rfl
  have hnodeArgs : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![generalBimatrixDimensionWord (v 0), v 1])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hdim
    · exact .pi_apply encBits 1
  have hbasic := bimatrixNodeBasicWord_polyTime.comp hnodeArgs
  have hentering := bimatrixNodeEnteringWord_polyTime.comp hnodeArgs
  have hselectArgs : ComputableInPolyTime
      (fun v : Fin 2 → List Bool =>
        ![bimatrixNodeEnteringWord ![generalBimatrixDimensionWord (v 0), v 1], []])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hentering
    · exact .const []
  have hselected := binarySubsetNth_polyTime.comp hselectArgs
  have htail := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hselected
  have hvalues : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![v 0,
        bimatrixNodeBasicWord ![generalBimatrixDimensionWord (v 0), v 1],
        (binarySubsetNth ![bimatrixNodeEnteringWord ![generalBimatrixDimensionWord (v 0), v 1], []]).tail])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact hbasic
    · exact htail
  apply ComputableInPolyTime.of_tidy
  apply hvalues.tidy.of_enc_eq (g := generalBimatrixNodeData)
  intro v
  rfl

@[fun_prop] theorem generalBimatrixNodeFeasibleFlag_polyTime :
    ComputableInPolyTime generalBimatrixNodeFeasibleFlag (encPi encBits) encBits := by
  have hd := generalBimatrixDictionaryDimension_polyTime.comp generalBimatrixNodeData_polyTime
  have hw := generalBimatrixDictionaryWidth_polyTime.comp generalBimatrixNodeData_polyTime
  have hc := generalBimatrixDictionaryCoefficients_polyTime.comp generalBimatrixNodeData_polyTime
  have ht := generalBimatrixDictionaryDeterminant_polyTime.comp generalBimatrixNodeData_polyTime
  have hcount := ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true) hd
  have hargs : ComputableInPolyTime
      (fun v : Fin 2 → List Bool =>
        ![generalBimatrixDictionaryDimension (generalBimatrixNodeData v),
          true :: generalBimatrixDictionaryDimension (generalBimatrixNodeData v),
          generalBimatrixDictionaryWidth (generalBimatrixNodeData v),
          generalBimatrixDictionaryCoefficients (generalBimatrixNodeData v)])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hd
    · exact hcount
    · exact hw
    · exact hc
  have hp := binaryDictionaryPositive_polyTime.comp hargs
  have hnonzero := binarySignedNonzero_polyTime.comp ht
  have h := andFlag_polyTime.comp (hnonzero.prod hp)
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq (g := generalBimatrixNodeFeasibleFlag)
  intro v
  rfl

@[fun_prop] theorem generalBimatrixNodeValidFlag_polyTime :
    ComputableInPolyTime generalBimatrixNodeValidFlag (encPi encBits) encBits := by
  have hinput : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hi := generalInstanceFlag_polyTime.comp hinput
  have hinputArgs : ComputableInPolyTime (fun v : Fin 2 → List Bool => ![v 0])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact hinput
  have hdim0 := generalBimatrixDimensionWord_polyTime.comp hinputArgs
  have hdim : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => generalBimatrixDimensionWord (v 0))
      (encPi encBits) encBits := by
    apply ComputableInPolyTime.of_tidy
    apply hdim0.tidy.of_enc_eq
    intro v
    rfl
  have hnodeArgs : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![generalBimatrixDimensionWord (v 0), v 1])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hdim
    · exact .pi_apply encBits 1
  have hs := bimatrixNodeSyntaxFlag_polyTime.comp hnodeArgs
  have hinner := andFlag_polyTime.comp (hs.prod generalBimatrixNodeFeasibleFlag_polyTime)
  have h := andFlag_polyTime.comp (hi.prod hinner)
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq (g := generalBimatrixNodeValidFlag)
  intro v
  rfl

end GameTheory.Complexity.Backend
