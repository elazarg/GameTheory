import GameTheoryComplexity.Backend.SimplicialBrouwer

/-! PPAD-completeness for circuit-coded simplicial Brouwer search with rational
barycenter residuals. This is a discrete displacement problem; unrestricted
approximate fixed-point search for continuous maps is a separate formulation. -/

namespace GameTheory.Complexity

open _root_.Complexity Backend

/-- Succinct simplicial residual search belongs to standard PPAD. -/
theorem simplicialBrouwerRelation_mem_PPAD : simplicialBrouwerRelation ∈ PPAD :=
  PPAD.of_reduction simplicialBrouwerToSpernerReduction
    simplicialBrouwerRelation_mem_FNP spernerRelation_mem_PPAD

/-- Every PPAD search problem reduces to simplicial residual search. -/
theorem simplicialBrouwerRelation_PPADHard : PPADHard simplicialBrouwerRelation := by
  intro T hT
  obtain ⟨a⟩ := spernerRelation_PPADHard T hT
  exact ⟨a.trans spernerToSimplicialBrouwerReduction⟩

/-- Succinct barycenter displacement search is complete for standard PPAD. -/
theorem simplicialBrouwerRelation_PPADComplete : PPADComplete simplicialBrouwerRelation :=
  ⟨simplicialBrouwerRelation_mem_PPAD, simplicialBrouwerRelation_PPADHard⟩

/-- The residual relation has short, efficiently verified answers on every input. -/
theorem simplicialBrouwerRelation_mem_TFNP : simplicialBrouwerRelation ∈ TFNP :=
  PPAD.mem_TFNP simplicialBrouwerRelation_mem_PPAD

/-- Boundary correction supplies a residual answer for every serialized input. -/
theorem simplicialBrouwerRelation_total (input : List Bool) :
    ∃ word, simplicialBrouwerRelation input word :=
  simplicialBrouwerRelation_mem_TFNP.2 input

end GameTheory.Complexity
