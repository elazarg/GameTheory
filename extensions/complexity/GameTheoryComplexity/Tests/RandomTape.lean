module

public import GameTheoryComplexity.SampleTest
public import GameTheoryComplexity.Backend.Complexitylib
public import Complexity.Computability.Probabilistic.Sampling

@[expose] public section

/-! A native fair-coin program exercises exact laws, machine certification and the
limitations of bounded fair randomness.
-/

noncomputable section

namespace GameTheory.Complexity.Tests

open Cslib Cslib.Probability Turing.MultiTapeTM
open GameTheory.Complexity.Backend

/-- One sampled fair bit is the verdict, independently of the input. -/
def coinProgram : List Bool → ProbComp Bool := fun _ => ProbComp.uniform Bool

theorem coinProgram_isPPT : IsPPTOn encBits encBool coinProgram :=
  isPPTOn_uniform_bool encBits

example : booleanProgramTest coinProgram 0 ∈ GameTheory.Complexity.booleanMachineTests :=
  ⟨coinProgram, coinProgram_isPPT, 0, rfl⟩

/-- The native machine-certified consumer accepts with probability exactly one half. -/
theorem coinProgram_probability (input : List Bool) :
    (ProbComp.eval (coinProgram input) true).toReal = 1 / 2 := by
  norm_num [coinProgram, ProbComp.eval_uniform]

/-- Every certified program, including this fair coin, obeys the finite-tape restriction. -/
example (program : List Bool → ProbComp Bool)
    (efficient : IsPPTOn encBits encBool program) (input : List Bool) :
    (ProbComp.eval (program input) true).toReal ≠ 1 / 3 :=
  program_acceptProb_ne_one_third program efficient input

/-- Saved-coin replay admits any additional independent padding, uniformly over
the input; its complete verdict law stays unchanged. -/
theorem coinProgram_padded_randomTapeLaw :
    ∃ (coefficient degree : ℕ) (evaluate : List Bool → List Bool → Bool),
      ∀ input padding, ProbComp.eval (coinProgram input) =
        randomTapeLaw (coefficient * (input.length + 1) ^ degree + padding)
          (fun choices => evaluate input (List.ofFn choices)) := by
  obtain ⟨coefficient, degree, evaluate, _, _, hlaw⟩ :=
    coinProgram_isPPT.exists_total_seeded_evaluator
  refine ⟨coefficient, degree, evaluate, fun input padding => ?_⟩
  exact (hlaw input _ (Nat.le_add_right _ _)).trans
    (uniformList_map_eq_randomTapeLaw _ _)

end GameTheory.Complexity.Tests
