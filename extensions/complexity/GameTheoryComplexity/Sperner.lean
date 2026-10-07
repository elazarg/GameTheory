import GameTheoryComplexity.Backend.SpernerReduction
import GameTheoryComplexity.Backend.SpernerVerifier
import GameTheoryComplexity.PPAD

/-! Succinct square-grid Sperner search belongs to PPAD. Canonical boundary
colors enforce totality for every serialized color-circuit input. This is
membership through End-of-Line, without a reverse hardness reduction. -/

namespace GameTheory.Complexity

open _root_.Complexity Backend

/-- Succinct Sperner search has an independent FNP verifier and a certified
polynomial search reduction to the standard PPAD reference problem. -/
theorem spernerRelation_mem_PPAD : spernerRelation ∈ PPAD := by
  obtain ⟨a⟩ := exists_spernerToEndOfLineReduction
  exact PPAD.of_reduction a spernerRelation_mem_FNP endOfLineRelation_mem_PPAD

/-- Every succinct Sperner instance has a polynomially bounded, efficiently verified answer. -/
theorem spernerRelation_mem_TFNP : spernerRelation ∈ TFNP :=
  PPAD.mem_TFNP spernerRelation_mem_PPAD

/-- Totality covers arbitrary serialized inputs, with no coloring promise to check. -/
theorem spernerRelation_total (input : List Bool) : ∃ word, spernerRelation input word :=
  spernerRelation_mem_TFNP.2 input

end GameTheory.Complexity
