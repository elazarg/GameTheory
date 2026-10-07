import GameTheoryComplexity.Backend.SATReductionSemantic
import GameTheoryComplexity.Backend.SATTablePayoffCorrectness
import Complexitylib.SAT.CookLevin.Assembly
import Complexitylib.Classes.P.NormalForm

/-! NP-hardness of payoff-constrained mixed Nash equilibrium existence for
explicit symmetric integer payoff tables. The SAT reduction has a fixed
polynomial-time deterministic machine, an exact whole-word serializer proof,
and a membership equivalence against canonical decoded game semantics.
-/

namespace GameTheory.Complexity.Backend

open _root_.Complexity
open GameTheory.Finite.BimatrixTable

/-- The semantic dense-table serializer is computed by a polynomial-time machine. -/
theorem satTableReduction_mem_FP : satTableReduction ∈ FP := by
  have h : satTableReduction = satTableEncode :=
    funext fun input => (satTableEncode_eq input).symm
  rw [h]
  exact satTableEncode_mem_FP

/-- One fixed deterministic machine and polynomial work for every SAT input. -/
theorem exists_satTableReduction_machine :
    ∃ (k : ℕ) (machine : TM k) (bound : Polynomial ℕ),
      machine.ComputesInTime satTableReduction bound.eval :=
  mem_FP_iff_computesInTime_polynomial.mp satTableReduction_mem_FP

/-- SAT polynomial-time many-one reduces to explicit payoff-constrained Nash existence. -/
theorem sat_reduces_unitPayoffLanguage :
    SAT.language ≤ₚ unitPayoffLanguage :=
  ⟨satTableReduction, satTableReduction_mem_FP, sat_mem_iff_reduction_mem⟩

/-- Payoff-one mixed Nash existence in explicit symmetric integer tables is NP-hard. -/
theorem unitPayoffLanguage_NPHard : NPHard unitPayoffLanguage :=
  SAT.NPHard_language.of_reduction sat_reduces_unitPayoffLanguage

/-- A polynomial-time decision algorithm for the constrained-equilibrium language
would collapse deterministic and nondeterministic polynomial time. -/
theorem P_eq_NP_of_unitPayoffLanguage_mem_P (h : unitPayoffLanguage ∈ P) : P = NP :=
  unitPayoffLanguage_NPHard.P_eq_NP_of_mem_P h

end GameTheory.Complexity.Backend
