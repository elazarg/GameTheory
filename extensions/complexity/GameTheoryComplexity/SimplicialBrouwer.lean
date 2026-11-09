module

public import GameTheoryComplexity.Backend.SimplicialBrouwer

@[expose] public section

/-! PPAD-completeness for circuit-coded simplicial Brouwer search with rational
barycenter residuals. This is a discrete displacement problem; unrestricted
approximate fixed-point search for continuous maps is a separate formulation. -/

namespace GameTheory.Complexity

open Turing.MultiTapeTM Cslib.Complexity Backend

/-- Succinct simplicial residual search belongs to standard PPAD. -/
theorem simplicialBrouwerRelation_mem_PPAD : simplicialBrouwerRelation ∈ PPAD encBits :=
  simplicialBrouwerToSpernerReduction.mem_PPAD
    simplicialBrouwerRelation_mem_FNP spernerRelation_mem_PPAD

/-- Every PPAD search problem reduces to simplicial residual search. -/
theorem simplicialBrouwerRelation_PPADHard :
    SearchHard @PPAD encBits simplicialBrouwerRelation := by
  intro α enc R hR
  exact (spernerRelation_PPADHard enc R hR).trans spernerToSimplicialBrouwerReduction

/-- Succinct barycenter displacement search is complete for standard PPAD. -/
theorem simplicialBrouwerRelation_PPADComplete : SearchComplete @PPAD encBits simplicialBrouwerRelation :=
  ⟨simplicialBrouwerRelation_mem_PPAD, simplicialBrouwerRelation_PPADHard⟩

/-- The residual relation has short, efficiently verified answers on every input. -/
theorem simplicialBrouwerRelation_mem_TFNP : simplicialBrouwerRelation ∈ TFNP encBits :=
  PPAD_subset_TFNP simplicialBrouwerRelation_mem_PPAD

/-- Boundary correction supplies a residual answer for every serialized input. -/
theorem simplicialBrouwerRelation_total (input : List Bool) :
    ∃ word, simplicialBrouwerRelation input word :=
  simplicialBrouwerRelation_mem_TFNP.2 input

end GameTheory.Complexity
