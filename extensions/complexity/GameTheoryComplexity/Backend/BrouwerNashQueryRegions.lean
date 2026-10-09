import GameTheoryComplexity.Backend.BrouwerNashProgram

/-! Exact decompositions of the contiguous regions in the canonical gate allocation. -/
namespace GameTheory.Complexity.Backend.BrouwerNashQueryRegions
open _root_.Complexity.CircuitCode

/-- The interpolation region contains precisely its eight affine stages. -/
theorem exists_interpolationStage (b i : ℕ)
    (hlo : BrouwerNashLayout.weightBase b ≤ i) (hhi : i < BrouwerNashLayout.colorBase b) :
    ∃ stage : Fin 8, i = BrouwerNashLayout.weightBase b + stage.val := by
  refine ⟨⟨i - BrouwerNashLayout.weightBase b, ?_⟩, ?_⟩
  · dsimp only [BrouwerNashLayout.colorBase] at hhi
    omega
  · change i = BrouwerNashLayout.weightBase b + (i - BrouwerNashLayout.weightBase b)
    omega

/-- Every interpolation output retains the existing factory's exact gate. -/
theorem sampleGate_interpolation_of_interval (b i : ℕ)
    (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (hlo : BrouwerNashLayout.weightBase b ≤ i) (hhi : i < BrouwerNashLayout.colorBase b) :
    ∃ stage : Fin 8, i = BrouwerNashLayout.weightBase b + stage.val ∧
      BrouwerNashProgram.sampleGate b raw₀ raw₁ t i =
        BrouwerNashProgram.interpolationGate b raw₀.length raw₁.length t stage.val := by
  obtain ⟨stage, hi⟩ := exists_interpolationStage b i hlo hhi
  refine ⟨stage, hi, ?_⟩
  rw [hi]
  exact BrouwerNashProgram.sampleGate_interpolation b raw₀ raw₁ t stage

/-- The minimum region contains one temporary and one final output per corner and color flag. -/
theorem exists_minimumSlot (b ell₀ ell₁ i : ℕ)
    (hlo : BrouwerNashLayout.minimumBase b ell₀ ell₁ ≤ i)
    (hhi : i < BrouwerNashLayout.sampleWidth b ell₀ ell₁) :
    ∃ (corner : Fin 4) (flag : Fin 2) (temporary : Bool),
      i = BrouwerNashLayout.minimumTemporary b ell₀ ell₁ corner flag +
        (if temporary then 0 else 1) := by
  let offset := i - BrouwerNashLayout.minimumBase b ell₀ ell₁
  have hoff : offset < 16 := by
    dsimp [offset, BrouwerNashLayout.minimumBase, BrouwerNashLayout.colorBase,
      BrouwerNashLayout.weightBase, BrouwerNashLayout.sampleWidth] at *
    omega
  refine ⟨⟨offset / 4, by omega⟩,
    ⟨(offset / 2) % 2, Nat.mod_lt _ (by omega)⟩, decide (offset % 2 = 0), ?_⟩
  dsimp only [BrouwerNashLayout.minimumTemporary]
  by_cases hp : offset % 2 = 0
  · simp only [hp, decide_true, ite_true, add_zero]
    dsimp only [offset] at *
    omega
  · simp only [hp, decide_false, Bool.false_eq_true, ite_false]
    dsimp only [offset] at *
    omega

/-- Every minimum output retains the existing two-subtraction factory's exact gate. -/
theorem sampleGate_minimum_of_interval (b i : ℕ)
    (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (hlo : BrouwerNashLayout.minimumBase b raw₀.length raw₁.length ≤ i)
    (hhi : i < BrouwerNashLayout.sampleWidth b raw₀.length raw₁.length) :
    ∃ (corner : Fin 4) (flag : Fin 2) (temporary : Bool),
      i = BrouwerNashLayout.minimumTemporary b raw₀.length raw₁.length corner flag +
        (if temporary then 0 else 1) ∧
      BrouwerNashProgram.sampleGate b raw₀ raw₁ t i =
        BrouwerNashProgram.minimumGate b raw₀.length raw₁.length t corner flag temporary := by
  obtain ⟨corner, flag, temporary, hi⟩ := exists_minimumSlot b raw₀.length raw₁.length i hlo hhi
  refine ⟨corner, flag, temporary, hi, ?_⟩
  rw [hi]
  exact BrouwerNashProgram.sampleGate_minimum b raw₀ raw₁ t corner flag temporary

/-- Two bounded local outputs can name the same absolute wire only in the same sample. -/
theorem sampleOutput_injective (b ell₀ ell₁ : ℕ) (t t' : Fin 41) (i i' : ℕ)
    (hi : i < BrouwerNashLayout.sampleWidth b ell₀ ell₁)
    (hi' : i' < BrouwerNashLayout.sampleWidth b ell₀ ell₁)
    (he : BrouwerNashLayout.sampleBase b ell₀ ell₁ t + i =
      BrouwerNashLayout.sampleBase b ell₀ ell₁ t' + i') : t = t' ∧ i = i' := by
  let w := BrouwerNashLayout.sampleWidth b ell₀ ell₁
  have ht : t = t' := by
    apply Fin.ext
    dsimp only [BrouwerNashLayout.sampleBase] at he
    change _ + t.val * w + i = _ + t'.val * w + i' at he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm := Nat.mul_le_mul_right w (show t.val + 1 ≤ t'.val by omega)
      rw [Nat.add_mul, one_mul] at hm
      omega
    · have hm := Nat.mul_le_mul_right w (show t'.val + 1 ≤ t.val by omega)
      rw [Nat.add_mul, one_mul] at hm
      omega
  subst t'
  exact ⟨rfl, by omega⟩

/-- A bounded sample output lies in no other sample's half-open interval. -/
theorem sampleOutput_interval_unique (b ell₀ ell₁ out i : ℕ) (t t' : Fin 41)
    (hi : i < BrouwerNashLayout.sampleWidth b ell₀ ell₁)
    (ho : out = BrouwerNashLayout.sampleBase b ell₀ ell₁ t + i)
    (hin : BrouwerNashLayout.sampleBase b ell₀ ell₁ t' ≤ out ∧
      out < BrouwerNashLayout.sampleBase b ell₀ ell₁ t' +
        BrouwerNashLayout.sampleWidth b ell₀ ell₁) : t = t' := by
  have hi' : out - BrouwerNashLayout.sampleBase b ell₀ ell₁ t' <
      BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by omega
  apply (sampleOutput_injective b ell₀ ell₁ t t' i
    (out - BrouwerNashLayout.sampleBase b ell₀ ell₁ t') hi hi' ?_).1
  omega
end GameTheory.Complexity.Backend.BrouwerNashQueryRegions
