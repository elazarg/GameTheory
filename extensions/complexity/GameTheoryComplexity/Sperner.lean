module

public import GameTheoryComplexity.Backend.SpernerReduction
public import GameTheoryComplexity.Backend.SpernerVerifier
public import GameTheoryComplexity.Backend.EndOfLineSpernerReduction
public import GameTheoryComplexity.PPAD

@[expose] public section

/-! Succinct square-grid Sperner search is PPAD-complete. Canonical boundary
colors enforce totality for arbitrary serialized inputs. Uniformly compiled
routed color circuits give the reverse reduction, preserving every answer. -/

namespace GameTheory.Complexity

open Turing.MultiTapeTM Cslib.Complexity Backend

/-- Succinct Sperner search has an independent FNP verifier and a certified
polynomial search reduction to the standard PPAD reference problem. -/
theorem spernerRelation_mem_PPAD : spernerRelation ∈ PPAD encBits := by
  exact exists_spernerToEndOfLineReduction.mem_PPAD spernerRelation_mem_FNP
    endOfLineRelation_mem_PPAD

/-- Every succinct Sperner instance has a polynomially bounded, efficiently verified answer. -/
theorem spernerRelation_mem_TFNP : spernerRelation ∈ TFNP encBits :=
  PPAD_subset_TFNP spernerRelation_mem_PPAD

/-- Totality covers arbitrary serialized inputs, with no coloring promise to check. -/
theorem spernerRelation_total (input : List Bool) : ∃ word, spernerRelation input word :=
  spernerRelation_mem_TFNP.2 input

/-- Every PPAD search problem reduces to succinct square-grid Sperner through
actual polynomial-time circuit generation and source-aware answer decoding. -/
theorem spernerRelation_PPADHard : SearchHard @PPAD encBits spernerRelation := by
  intro α enc R hR
  exact (endOfLineRelation_PPADHard enc R hR).trans exists_endOfLineToSpernerReduction

/-- Succinct square-grid Sperner is complete for standard PPAD. -/
theorem spernerRelation_PPADComplete : SearchComplete @PPAD encBits spernerRelation :=
  ⟨spernerRelation_mem_PPAD, spernerRelation_PPADHard⟩

end GameTheory.Complexity
