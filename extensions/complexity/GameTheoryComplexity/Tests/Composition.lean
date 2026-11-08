module

public import GameTheoryComplexity.Backend.CompiledSampleTest
public import GameTheoryComplexity.Tests.RandomTape

@[expose] public section

/-! Actual compiled machines cover a fair verdict, immediate rejection and a
payload-sensitive deterministic result after canonical serialization.
-/

noncomputable section

namespace GameTheory.Complexity.Tests

open Cslib Cslib.Probability Turing.MultiTapeTM
open GameTheory.Complexity.Backend

/-- The compiled serializer and fair test have exactly the uniform Boolean law. -/
theorem composed_coin_law :
    ∃ (tapes : ℕ) (State : Type) (_ : Finite State)
      (machine : Turing.MultiTapePTM tapes Bool State) (bound : Polynomial ℕ),
      ∀ (κ : ℕ) (draws : Fin ((κ + 1) ^ 2) → Bool),
        (∀ final ∈ (ProbComp.eval (machine.runClosedConfigFrom (bound.eval κ)
          (machine.initialConfig (encPair encBits encBits (booleanTuple 2 κ draws))))).support,
          final.tapes.state = none) ∧
        ProbComp.eval (machine.runClosed (bound.eval κ)
          (encPair encBits encBits (booleanTuple 2 κ draws))) =
            (ProbComp.eval (ProbComp.uniform Bool)).map encBool := by
  obtain ⟨tapes, State, hfinite, machine, _, _, _, _, hdegrees⟩ :=
    exists_composed_booleanMachine coinProgram coinProgram_isPPT
  obtain ⟨bound, hcert⟩ := hdegrees 2
  refine ⟨tapes, State, hfinite, machine, bound, fun κ draws => ?_⟩
  simpa only [booleanProgramTest, coinProgram] using hcert κ draws

/-- Immediate deterministic rejection is a native PPT program. -/
def stoppedProgram : List Bool → ProbComp Bool := fun _ => pure false

theorem stoppedProgram_isPPT : IsPPTOn encBits encBool stoppedProgram :=
  (ComputableInPolyTime.const false).isPPTOn

/-- The composed realization handles a test that rejects without sampling a coin. -/
theorem composed_immediate_rejection :
    ∃ (tapes : ℕ) (State : Type) (_ : Finite State)
      (machine : Turing.MultiTapePTM tapes Bool State) (bound : Polynomial ℕ),
      ∀ (κ : ℕ) (draws : Fin ((κ + 1) ^ 0) → Bool),
        (∀ final ∈ (ProbComp.eval (machine.runClosedConfigFrom (bound.eval κ)
          (machine.initialConfig (encPair encBits encBits (booleanTuple 0 κ draws))))).support,
          final.tapes.state = none) ∧
        ProbComp.eval (machine.runClosed (bound.eval κ)
          (encPair encBits encBits (booleanTuple 0 κ draws))) = PMF.pure [false] := by
  obtain ⟨tapes, State, hfinite, machine, _, _, _, _, hdegrees⟩ :=
    exists_composed_booleanMachine stoppedProgram stoppedProgram_isPPT
  obtain ⟨bound, hcert⟩ := hdegrees 0
  refine ⟨tapes, State, hfinite, machine, bound, fun κ draws => ?_⟩
  simpa only [booleanProgramTest, stoppedProgram, ProbComp.eval_pure, PMF.pure_map,
    encBool_apply] using hcert κ draws

/-- Read the first sample following a unary parameter of length one and its delimiter. -/
def payloadProgram (input : List Bool) : ProbComp Bool := pure (input.getD 2 false)

theorem payloadProgram_isPPT : IsPPTOn encBits encBool payloadProgram :=
  (ComputableInPolyTime.bitsGetDWithInput ComputableInPolyTime.id'
    (ComputableInPolyTime.const 2) false).isPPTOn

/-- Both payload values remain observable after actual serialization and native
machine execution; a constant serializer would fail this control. -/
theorem composed_payload_reader :
    ∃ (tapes : ℕ) (State : Type) (_ : Finite State)
      (machine : Turing.MultiTapePTM tapes Bool State) (bound : Polynomial ℕ),
      ∀ bit : Bool,
        (∀ final ∈ (ProbComp.eval (machine.runClosedConfigFrom (bound.eval 1)
          (machine.initialConfig (encPair encBits encBits
            (booleanTuple 0 1 (fun _ => bit)))))).support,
          final.tapes.state = none) ∧
        ProbComp.eval (machine.runClosed (bound.eval 1)
          (encPair encBits encBits (booleanTuple 0 1 (fun _ => bit)))) = PMF.pure [bit] := by
  obtain ⟨tapes, State, hfinite, machine, _, _, _, _, hdegrees⟩ :=
    exists_composed_booleanMachine payloadProgram payloadProgram_isPPT
  obtain ⟨bound, hcert⟩ := hdegrees 0
  refine ⟨tapes, State, hfinite, machine, bound, fun bit => ?_⟩
  simpa [booleanProgramTest, payloadProgram, booleanInput, List.ofFn_succ] using
    hcert 1 (fun _ => bit)

end GameTheory.Complexity.Tests
