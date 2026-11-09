module

public import GameTheoryComplexity.Backend.BrouwerNashSampleKind
public import GameTheoryComplexity.Backend.BrouwerNashProgram

@[expose] public section

/-! Exact comparator flags for the non-color regions of the canonical Brouwer feedback program. -/
namespace GameTheory.Complexity.Backend.BrouwerNashKindCorrectness
open Cslib.Circuits
open GameTheory.Finite BrouwerNashLayout BrouwerNashProgram

private theorem guardedRaw_kind {k : ℕ} (raw : CircuitFormat.signature.Op × List ℕ)
    (h : Program.IsCodeFrom CircuitFormat.signature k 0 [raw]) :
    (guardedRaw raw : BimatrixGateProgram.Gate k).kind = .comparator := by
  rw [guardedRaw, dite_eq_left h]
  rfl

/-- All four increment stages are comparators, including the shared initial carry. -/
theorem incrementGate_kind (b ell₀ ell₁ : ℕ) (t : Fin 41) (axis : Fin 2)
    (j : ℕ) (stage : Fin 4) :
    (incrementGate b ell₀ ell₁ t axis j stage).kind = .comparator := by
  have hcarry : (if j = 0 then one else
      (sampleRef b ell₀ ell₁ t (increment b axis (j - 1) 3)).val) < dimension b ell₀ ell₁ := by
    split_ifs
    · exact one_lt_dimension b ell₀ ell₁
    · exact (sampleRef b ell₀ ell₁ t (increment b axis (j - 1) 3)).isLt
  have href (op : CircuitFormat.signature.Op) (i j : ℕ)
      (hi : i < dimension b ell₀ ell₁) (hj : j < dimension b ell₀ ell₁) :
      Program.IsCodeFrom CircuitFormat.signature (dimension b ell₀ ell₁) 0 [(op, [i, j])] := by
    refine ⟨⟨rfl, ?_⟩, trivial⟩
    intro ref h
    rcases List.mem_cons.mp h with rfl | h
    · exact hi
    · have he := List.mem_singleton.mp h
      subst ref
      exact hj
  fin_cases stage <;>
    unfold incrementGate <;>
    apply guardedRaw_kind <;>
    apply href <;>
    first | exact Fin.isLt _ | exact hcarry

/-- The non-color sample flag is false on shared wires and unused padding. -/
theorem sampleKind_zero (out source code₀ code₁ : List Bool)
    (ho : out.length < globalCount (CircuitWords.first source).length ∨
      globalCount (CircuitWords.first source).length + 41 * sampleWidth (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length ≤ out.length) :
    BrouwerNashSampleKind.kindWord (source) (code₀) (code₁) (out) = [false] := by
  rw [BrouwerNashSampleKind.kindWord_value]
  have hn : ¬∃ t : Fin 41, BrouwerNashSampleKind.sampleFlag source code₀ code₁ (List.replicate t.val false) out = [true] := by
    rintro ⟨t, ht⟩
    change BrouwerNashSampleKind.sampleFlag (source) (code₀) (code₁) (List.replicate t.val false) (out) = [true] at ht
    rw [BrouwerNashSampleKind.sampleFlag_value] at ht
    have hp := of_decide_eq_true (List.cons.inj ht).1
    simp only [List.length_replicate] at hp
    have hw : 2 + 12 * (CircuitWords.first source).length ≤
        sampleWidth (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
      unfold sampleWidth
      omega
    have hm := Nat.mul_le_mul_right
      (sampleWidth (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length)
      (show t.val + 1 ≤ 41 from Nat.succ_le_of_lt t.isLt)
    simp only [Nat.add_mul, one_mul] at hm
    rcases ho with hbefore | hafter <;> omega
  simp only [hn, decide_false]

/-- Every interpolation stage uses the canonical affine kind. -/
theorem interpolationGate_kind (b ell₀ ell₁ : ℕ) (t : Fin 41) (stage : ℕ) :
    (interpolationGate b ell₀ ell₁ t stage).kind = .affine := by
  unfold interpolationGate
  split <;> rfl

/-- Both weighted-minimum stages use the canonical affine kind. -/
theorem minimumGate_kind (b ell₀ ell₁ : ℕ) (t : Fin 41)
    (corner : Fin 4) (flag : Fin 2) (temporary : Bool) :
    (minimumGate b ell₀ ell₁ t corner flag temporary).kind = .affine := by
  unfold minimumGate
  split_ifs <;> rfl

/-- Outside the color region, only digit extraction and ripple stages are comparators. -/
theorem sampleGate_kind (b : ℕ) (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ)) (t : Fin 41) (i : ℕ)
    (hno : i < colorBase b ∨ minimumBase b raw₀.length raw₁.length ≤ i) :
    (sampleGate b raw₀ raw₁ t i).kind =
      if (2 ≤ i ∧ i < 2 + 4 * b ∧ i % 2 ≠ 1) ∨
          (2 + 4 * b ≤ i ∧ i < 2 + 12 * b) then .comparator else .affine := by
  let pred : Prop := (2 ≤ i ∧ i < 2 + 4 * b ∧ i % 2 ≠ 1) ∨
    (2 + 4 * b ≤ i ∧ i < 2 + 12 * b)
  change (sampleGate b raw₀ raw₁ t i).kind = if pred then .comparator else .affine
  unfold sampleGate
  by_cases h2 : i < 2
  · have hpred : ¬pred := by dsimp only [pred]; omega
    rw [dite_eq_left h2, ite_eq_right hpred]
    rfl
  rw [dite_eq_right h2]
  by_cases he : i < 2 + 4 * b
  · rw [ite_eq_left he]
    have hp : ((i - 2) % (2 * b)) % 2 = (i - 2) % 2 :=
      Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right 2 b)
    have hmod : (i - 2) % 2 = i % 2 := by omega
    simp only [hp, hmod]
    by_cases hparity : i % 2 = 0
    · have hpred : pred := by dsimp only [pred]; omega
      rw [ite_eq_left hparity, ite_eq_left hpred]
      rfl
    · have hpred : ¬pred := by dsimp only [pred]; omega
      rw [ite_eq_right hparity, ite_eq_right hpred]
      rfl
  rw [ite_eq_right he]
  by_cases hi : i < weightBase b
  · have hpred : pred := by dsimp only [pred]; simp only [weightBase] at hi; omega
    rw [ite_eq_left hi, incrementGate_kind, ite_eq_left hpred]
  rw [ite_eq_right hi]
  have hpred : ¬pred := by dsimp only [pred]; simp only [weightBase] at hi; omega
  rw [ite_eq_right hpred]
  by_cases hc : i < colorBase b
  · rw [ite_eq_left hc, interpolationGate_kind]
  rw [ite_eq_right hc]
  have hm : ¬ i < minimumBase b raw₀.length raw₁.length := by omega
  rw [ite_eq_right hm, minimumGate_kind]

/-- The actual non-color flag agrees with every non-color sample's canonical gate kind. -/
theorem sampleKind_at_sample (out source code₀ code₁ : List Bool)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ)) (t : Fin 41) (i : ℕ)
    (h₀ : (circuitUnaryPrefix code₀).length = raw₀.length)
    (h₁ : (circuitUnaryPrefix code₁).length = raw₁.length)
    (hi : i < sampleWidth (CircuitWords.first source).length raw₀.length raw₁.length)
    (ho : out.length = sampleBase (CircuitWords.first source).length raw₀.length raw₁.length t + i)
    (hno : i < colorBase (CircuitWords.first source).length ∨
      minimumBase (CircuitWords.first source).length raw₀.length raw₁.length ≤ i) :
    BrouwerNashSampleKind.kindWord (source) (code₀) (code₁) (out) =
      [decide ((sampleGate (CircuitWords.first source).length raw₀ raw₁ t i).kind = .comparator)] := by
  have hicode : i < sampleWidth (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    simpa only [h₀, h₁] using hi
  have hocode : out.length = sampleBase (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t + i := by
    simpa only [h₀, h₁] using ho
  rw [BrouwerNashSampleKind.kindWord_at_sample _ _ _ _ t i hicode hocode,
    BrouwerNashSampleKind.sampleFlag_value, h₀, h₁, sampleGate_kind _ _ _ _ _ hno]
  simp only [List.length_replicate, ho, sampleBase, Nat.add_sub_cancel_left]
  congr 2
  let pred : Prop := (2 ≤ i ∧ i < 2 + 4 * (CircuitWords.first source).length ∧ i % 2 ≠ 1) ∨
    (2 + 4 * (CircuitWords.first source).length ≤ i ∧ i < 2 + 12 * (CircuitWords.first source).length)
  apply propext
  change _ ↔ ((if pred then BimatrixGateProgram.GateKind.comparator else .affine) = .comparator)
  by_cases hp : pred
  · rw [ite_eq_left hp]
    constructor
    · intro _
      rfl
    · intro _
      dsimp only [pred] at hp
      omega
  · rw [ite_eq_right hp]
    constructor
    · intro hx
      exfalso
      dsimp only [pred] at hp
      omega
    · intro hx
      cases hx

/-- Interpolation, color and minimum outputs cannot select an extraction/increment flag. -/
theorem sampleKind_false_of_weightBase (out source code₀ code₁ : List Bool)
    (t : Fin 41) (i : ℕ)
    (hi : i < sampleWidth (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length)
    (ho : out.length = sampleBase (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t + i)
    (hafter : weightBase (CircuitWords.first source).length ≤ i) :
    BrouwerNashSampleKind.kindWord (source) (code₀) (code₁) (out) = [false] := by
  rw [BrouwerNashSampleKind.kindWord_at_sample _ _ _ _ t i hi ho,
    BrouwerNashSampleKind.sampleFlag_value]
  simp only [List.length_replicate, ho, sampleBase, Nat.add_sub_cancel_left]
  congr 1
  apply decide_eq_false_iff_not.mpr
  simp only [weightBase] at hafter
  omega

end GameTheory.Complexity.Backend.BrouwerNashKindCorrectness
