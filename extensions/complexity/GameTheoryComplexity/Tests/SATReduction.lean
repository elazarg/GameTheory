import GameTheoryComplexity.Backend.SATReduction

/-! Satisfiable, contradictory, empty-formula and malformed-source controls for
the explicit payoff-table reduction. -/

namespace GameTheory.Complexity.Tests.SATReduction

open _root_.Complexity
open GameTheory.Complexity.Backend
open GameTheory.Finite.BimatrixTable

private theorem encoded_mem_iff (φ : SAT.CNF) : φ.encode ∈ SAT.language ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨ψ, h, hψ⟩
    have heq := congrArg SAT.CNF.decode? h
    rw [SAT.CNF.decode?_encode, SAT.CNF.decode?_encode] at heq
    exact (Option.some.inj heq).symm ▸ hψ
  · exact fun h => ⟨φ, rfl, h⟩

def separated : SAT.CNF :=
  [[{sign := true, var := 0}], [{sign := false, var := 1}]]

def contradictory : SAT.CNF :=
  [[{sign := true, var := 0}], [{sign := false, var := 0}]]

theorem separated_table_has_high_payoff_nash :
    satTableReduction separated.encode ∈ unitPayoffLanguage := by
  apply (sat_mem_iff_reduction_mem _).mp
  exact (encoded_mem_iff _).mpr (by decide)

theorem contradictory_table_has_no_high_payoff_nash :
    satTableReduction contradictory.encode ∉ unitPayoffLanguage := by
  rw [← sat_mem_iff_reduction_mem, encoded_mem_iff]
  decide

theorem malformed_table_has_no_high_payoff_nash :
    satTableReduction [true] ∉ unitPayoffLanguage := by
  rw [← sat_mem_iff_reduction_mem]
  rintro ⟨φ, h, _⟩
  have hd := congrArg SAT.CNF.decode? h
  rw [SAT.CNF.decode?_encode] at hd
  have hn : SAT.CNF.decode? [true] = none := by decide
  rw [hn] at hd
  contradiction

theorem empty_formula_table_has_high_payoff_nash :
    satTableReduction [] ∈ unitPayoffLanguage := by
  apply (sat_mem_iff_reduction_mem _).mp
  exact ⟨[], rfl, by decide⟩

theorem empty_clause_table_has_no_high_payoff_nash :
    satTableReduction (SAT.CNF.encode [[]]) ∉ unitPayoffLanguage := by
  rw [← sat_mem_iff_reduction_mem, encoded_mem_iff]
  decide

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
