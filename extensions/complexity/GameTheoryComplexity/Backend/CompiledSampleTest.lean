module

public import GameTheoryComplexity.Backend.Serializer
public import Complexity.Computability.Probabilistic.PPT.Composition

@[expose] public section

/-! A single finite fair-coin machine implements serialization and testing.
Its security clock is uniform over all sample tuples, preserves the complete
verdict law and reaches a halted configuration on every supported execution.
-/

noncomputable section

namespace GameTheory.Complexity.Backend

open Cslib Cslib.Probability Turing.MultiTapeTM

/-- Certified serialization and a native PPT test have one intrinsically halting
finite realization. Its raw-word polynomial clock works on every word, with the
specified program law on encoded pairs. Its security clock is independent of
the samples, and the machine is fixed before the sample degree is chosen. -/
theorem exists_composed_booleanMachine (program : List Bool → ProbComp Bool)
    (efficient : IsPPTOn encBits encBool program) :
    ∃ (tapes : ℕ) (State : Type) (_ : Finite State)
      (machine : Turing.MultiTapePTM tapes Bool State) (coefficient degree : ℕ),
      (∀ word, ∀ final ∈ (ProbComp.eval (machine.runClosedConfigFrom
        (coefficient * (word.length + 1) ^ degree) (machine.initialConfig word))).support,
        final.tapes.state = none) ∧
      (∀ input : List Bool × List Bool,
        (ProbComp.eval (program (serializeBoolean input))).map encBool =
          ProbComp.eval (machine.runClosed
            (coefficient * ((encPair encBits encBits input).length + 1) ^ degree)
            (encPair encBits encBits input))) ∧
      ∀ sampleDegree : ℕ, ∃ bound : Polynomial ℕ,
        ∀ (κ : ℕ) (draws : Fin ((κ + 1) ^ sampleDegree) → Bool),
          (∀ final ∈ (ProbComp.eval (machine.runClosedConfigFrom (bound.eval κ)
            (machine.initialConfig (encPair encBits encBits
              (booleanTuple sampleDegree κ draws))))).support,
            final.tapes.state = none) ∧
          ProbComp.eval (machine.runClosed (bound.eval κ)
            (encPair encBits encBits (booleanTuple sampleDegree κ draws))) =
              ((booleanProgramTest program sampleDegree).accept κ draws).map encBool := by
  have hcomposed := efficient.preprocess serializeBoolean_polyTime
  obtain ⟨tapes, State, hfinite, machine, coefficient, degree, hlaw, hhalt⟩ :=
    hcomposed.exists_halting_machine
  refine ⟨tapes, State, hfinite, machine, coefficient, degree, hhalt, hlaw,
    fun sampleDegree => ?_⟩
  let bound : Polynomial ℕ := Polynomial.C coefficient *
    (Polynomial.C 4 * (Polynomial.X + Polynomial.C 1) ^ (sampleDegree + 1) +
      Polynomial.C 1) ^ degree
  refine ⟨bound, fun κ draws => ?_⟩
  let input := encPair encBits encBits (booleanTuple sampleDegree κ draws)
  have hle : coefficient * (input.length + 1) ^ degree ≤ bound.eval κ := by
    have hlength : input.length ≤ 4 * (κ + 1) ^ (sampleDegree + 1) :=
      booleanTuple_encode_length_bound sampleDegree κ draws
    have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hlength 1) degree
    simpa only [bound, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X] using Nat.mul_le_mul_left coefficient hpow
  have hconfig := machine.eval_runClosedConfigFrom_eq_of_halted
    (machine.initialConfig input) hle (hhalt input)
  constructor
  · intro final hfinal
    rw [hconfig] at hfinal
    exact hhalt input final hfinal
  · refine (machine.eval_runClosed_eq_of_halted input hle (hhalt input)).trans ?_
    simpa only [serializeBoolean_booleanTuple, booleanProgramTest] using
      (hlaw (booleanTuple sampleDegree κ draws)).symm

end GameTheory.Complexity.Backend
