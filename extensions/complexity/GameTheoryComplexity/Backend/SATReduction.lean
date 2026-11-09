module

public import GameTheoryComplexity.Backend.SATWordsMachine
public import GameTheoryComplexity.Backend.SATReductionSemantic
public import GameTheoryComplexity.Backend.SATTablePayoffCorrectness
public import Complexity.Logics.Propositional.CNF.PolyTime
public import Complexity.Computability.Complexity.CookLevin.Completeness

@[expose] public section

/-! Native NP-hardness of payoff-constrained mixed Nash equilibrium existence
for explicit symmetric integer payoff tables. Native CNF compaction computes
unary indices before the public SAT byte serializer runs, preserving
satisfiability while charging the full representation conversion. The complete
table serializer has a native machine certificate and an exact whole-word proof
against canonical decoded game semantics.
-/

namespace GameTheory.Complexity.Backend

open Cslib Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM
open GameTheory.Finite.BimatrixTable

/-- The semantic dense-table serializer is computed by one native polynomial-time machine. -/
@[fun_prop] theorem satTableReduction_polyTime :
    ComputableInPolyTime satTableReduction encBits encBits := by
  have h : satTableReduction = satTableEncode :=
    funext fun input => (satTableEncode_eq input).symm
  rw [h]
  exact satTableEncode_polyTime

/-- One binary machine with finitely many states and fixed polynomial clocks works
for every raw SAT word, computing the complete explicit table. -/
theorem exists_satTableReduction_machine :
    ∃ (tapes : ℕ) (State : Type) (_ : Finite State)
      (machine : Turing.MultiTapeTM tapes Bool State)
      (timeCoefficient timeDegree spaceCoefficient spaceDegree : ℕ),
      machine.ComputesFunInTimeAndSpace encBits encBits satTableReduction
        (fun input => timeCoefficient * (input.length + 1) ^ timeDegree)
        (fun input => spaceCoefficient * (input.length + 1) ^ spaceDegree) := by
  obtain ⟨time, space, htime, hspace, tapes, State, hfinite, machine, hmachine⟩ :=
    satTableReduction_polyTime
  obtain ⟨timeCoefficient, timeDegree, htime⟩ := polynomiallyBounded_iff_le.mp htime
  obtain ⟨spaceCoefficient, spaceDegree, hspace⟩ := polynomiallyBounded_iff_le.mp hspace
  exact ⟨tapes, State, hfinite, machine, timeCoefficient, timeDegree, spaceCoefficient, spaceDegree,
    hmachine.mono (fun input => htime input.length) (fun input => hspace input.length)⟩

/-- Convert a native CNF instance to the public unary byte format after compacting
its variable names in order of first occurrence. -/
def satWordOfCNF (formula : CNF ℕ) : List Bool :=
  SATWords.encodeFormula formula.compact

/-- Native compaction already emits unary-encoded indices; literal and formula
serialization then charge every output bit and separator. -/
@[fun_prop] theorem satWordOfCNF_polyTime :
    ComputableInPolyTime satWordOfCNF encCNF encBits :=
  SATWords.encodeFormula_polyTime.comp (CNF.isPolyTime_compact encNat)

/-- Compacting variable names and serializing preserve native satisfiability exactly. -/
theorem satWordOfCNF_mem_iff (formula : CNF ℕ) :
    satWordOfCNF formula ∈ satWordLanguage ↔ formula ∈ SAT := by
  simp only [satWordOfCNF, mem_satWordLanguage_encodeFormula, CNF.satisfiable_compact, mem_SAT]

/-- Binary-indexed native SAT reduces to the concrete unary SAT-word language. -/
theorem sat_reduces_satWordLanguage :
    PolyTimeReducible encCNF encBits SAT satWordLanguage :=
  ⟨satWordOfCNF, satWordOfCNF_polyTime, fun formula => (satWordOfCNF_mem_iff formula).symm⟩

/-- Concrete SAT words reduce to decoded explicit payoff-constrained Nash existence. -/
theorem satWordLanguage_reduces_unitPayoffLanguage :
    PolyTimeReducible encBits encBits satWordLanguage unitPayoffLanguage :=
  ⟨satTableReduction, satTableReduction_polyTime, sat_mem_iff_reduction_mem⟩

/-- Native typed SAT reduces to the canonical language of explicit integer payoff tables. -/
theorem sat_reduces_unitPayoffLanguage :
    PolyTimeReducible encCNF encBits SAT unitPayoffLanguage :=
  sat_reduces_satWordLanguage.trans satWordLanguage_reduces_unitPayoffLanguage

/-- The concrete unary SAT-word language is NP-hard under native polynomial-time reductions. -/
theorem satWordLanguage_NPHard : NPHard encBits satWordLanguage :=
  CookLevin.SAT_npHard.trans sat_reduces_satWordLanguage

/-- Payoff-one mixed Nash existence in explicit symmetric integer tables is NP-hard. -/
theorem unitPayoffLanguage_NPHard : NPHard encBits unitPayoffLanguage :=
  CookLevin.SAT_npHard.trans sat_reduces_unitPayoffLanguage

/-- A polynomial-time decider for constrained equilibria collapses P and NP for
every native encoding of problem instances. -/
theorem P_eq_NP_of_unitPayoffLanguage_mem_P (h : unitPayoffLanguage ∈ P encBits)
    {Input : Type} (inputEncoding : Input ↪ List Bool) :
    P inputEncoding = NP inputEncoding :=
  P_subset_NP.antisymm fun problem hproblem =>
    (unitPayoffLanguage_NPHard inputEncoding problem hproblem).mem_P h

end GameTheory.Complexity.Backend
