module

public import GameTheoryComplexity.Backend.SATReduction

@[expose] public section

/-! Satisfiable, contradictory, empty-formula and malformed-source controls for
the explicit payoff-table reduction. -/

namespace GameTheory.Complexity.Tests.SATReduction

open Cslib.Logic.PL
open GameTheory.Complexity.Backend
open GameTheory.Finite.BimatrixTable

def separated : CNF ℕ := [[(0, true)], [(1, false)]]

def contradictory : CNF ℕ := [[(0, true)], [(0, false)]]

theorem separated_table_has_high_payoff_nash :
    satTableReduction (SATWords.encodeFormula separated) ∈ unitPayoffLanguage := by
  apply (sat_mem_iff_reduction_mem _).mp
  exact (mem_satWordLanguage_encodeFormula _).mpr ⟨fun i => decide (i = 0), by decide⟩

theorem contradictory_table_has_no_high_payoff_nash :
    satTableReduction (SATWords.encodeFormula contradictory) ∉ unitPayoffLanguage := by
  rw [← sat_mem_iff_reduction_mem, mem_satWordLanguage_encodeFormula]
  rintro ⟨assignment, h⟩
  simp [contradictory, CNF.eval, Clause.eval, Literal.eval] at h

theorem malformed_table_has_no_high_payoff_nash :
    satTableReduction [true] ∉ unitPayoffLanguage := by
  rw [← sat_mem_iff_reduction_mem]
  rintro ⟨formula, h, _⟩
  have hn : SATWords.decodeFormula? [true] = none := by decide
  rw [hn] at h
  cases h

theorem empty_formula_table_has_high_payoff_nash :
    satTableReduction [] ∈ unitPayoffLanguage := by
  apply (sat_mem_iff_reduction_mem _).mp
  exact ⟨[], rfl, ⟨fun _ => false, rfl⟩⟩

theorem empty_clause_table_has_no_high_payoff_nash :
    satTableReduction (SATWords.encodeFormula ([[]] : CNF ℕ)) ∉ unitPayoffLanguage := by
  rw [← sat_mem_iff_reduction_mem, mem_satWordLanguage_encodeFormula]
  rintro ⟨assignment, h⟩
  simp [CNF.eval, Clause.eval] at h

example : (satTableEncode []).length = 356 := by
  rw [satTableEncode_eq, satTableReduction_length]
  rfl

private theorem empty_cell (i j : ℕ) (hi : i < 5) (hj : j < 5) :
    decodedPayoff (satTableEncode []) i j = satTablePayoff [] i j := by
  rw [satTableEncode_eq, satTableReduction]
  exact decode_encoded_table _ _ (fun i _ j _ => satTablePayoff_bound [] i j) i j hi hj

example : decodedPayoff (satTableEncode []) 0 0 = 1 := by
  rw [empty_cell 0 0 (by decide) (by decide)]
  rfl
example : decodedPayoff (satTableEncode []) 0 1 = -2 := by
  rw [empty_cell 0 1 (by decide) (by decide)]
  rfl
example : decodedPayoff (satTableEncode []) 4 4 = 0 := by
  rw [empty_cell 4 4 (by decide) (by decide)]
  rfl

end GameTheory.Complexity.Tests.SATReduction
