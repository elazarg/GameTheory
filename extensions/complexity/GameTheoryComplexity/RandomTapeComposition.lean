import GameTheoryComplexity.RandomTape
import GameTheory.Math.Probability.UniformProjection

/-! Ignoring unused fair random bits preserves the full verdict law. -/

noncomputable section

namespace GameTheory.Complexity

open GameTheory.Math.Probability

/-- A suffix of a uniform fair tape is itself a uniform fair tape. -/
theorem randomTapeLaw_suffix (s t : ℕ) (verdict : (Fin s → Bool) → Bool) :
    randomTapeLaw (s + t)
      (fun choices => verdict (fun i => choices ⟨i.val + t, by omega⟩)) =
      randomTapeLaw s verdict := by
  change (PMF.uniformOfFintype (Fin (s + t) → Bool)).map
    (verdict ∘ (fun choices => fun i : Fin s => choices ⟨i.val + t, by omega⟩)) = _
  rw [← PMF.map_comp, uniformOfFintype_map_fin_suffix]
  rfl

/-- A prefix of a uniform fair tape is itself a uniform fair tape. -/
theorem randomTapeLaw_prefix (s t : ℕ) (verdict : (Fin s → Bool) → Bool) :
    randomTapeLaw (s + t)
      (fun choices => verdict (fun i => choices ⟨i.val, by omega⟩)) =
      randomTapeLaw s verdict := by
  change (PMF.uniformOfFintype (Fin (s + t) → Bool)).map
    (verdict ∘ (fun choices => fun i : Fin s => choices ⟨i.val, by omega⟩)) = _
  rw [← PMF.map_comp, uniformOfFintype_map_fin_prefix]
  rfl

end GameTheory.Complexity
