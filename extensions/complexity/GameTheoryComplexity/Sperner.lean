import GameTheoryComplexity.Backend.SpernerReduction
import GameTheoryComplexity.Backend.SpernerVerifier
import GameTheoryComplexity.Backend.EndOfLineSpernerReduction
import GameTheoryComplexity.PPAD

/-! Succinct square-grid Sperner search is PPAD-complete. Canonical boundary
colors enforce totality for arbitrary serialized inputs. Uniformly compiled
routed color circuits give the reverse reduction, preserving every answer. -/

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

/-- Every PPAD search problem reduces to succinct square-grid Sperner through
actual polynomial-time circuit generation and source-aware answer decoding. -/
theorem spernerRelation_PPADHard : PPADHard spernerRelation := by
  obtain ⟨b⟩ := exists_endOfLineToSpernerReduction
  intro T hT
  obtain ⟨a⟩ := endOfLineRelation_PPADHard T hT
  exact ⟨a.trans b⟩

/-- Succinct square-grid Sperner is complete for standard PPAD. -/
theorem spernerRelation_PPADComplete : PPADComplete spernerRelation :=
  ⟨spernerRelation_mem_PPAD, spernerRelation_PPADHard⟩

end GameTheory.Complexity
