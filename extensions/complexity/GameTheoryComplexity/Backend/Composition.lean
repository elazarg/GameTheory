import GameTheoryComplexity.Backend.Complexitylib
import GameTheoryComplexity.Backend.ClockPadding
import GameTheoryComplexity.RandomTapeComposition
import Complexitylib.Models.TuringMachine.Composition.Nondeterministic.Trace
import Complexitylib.Classes.P.Defs

/-! Deterministic serialization and randomized testing form one uniform machine.
The deterministic prefix consumes unused fair bits; dropping those bits and padding
halted executions preserve the entire Boolean acceptance law exactly.
-/

noncomputable section

namespace GameTheory.Complexity.Backend

open _root_.Complexity

/-- A machine starting halted rejects independently of its input and clock. -/
theorem machineLaw_start_halted {n : ℕ} (machine : NTM n)
    (halted : machine.qstart = machine.qhalt) (input : List Bool) (steps : ℕ) :
    machineLaw machine input steps = PMF.pure false := by
  have hfun : machineVerdict machine input steps = fun _ => false := by
    funext choices
    unfold machineVerdict
    rw [machine.trace_halted steps choices (show machine.halted (machine.initCfg input) from halted)]
    simp [Tape.init]
  simp only [machineLaw, randomTapeLaw, hfun]
  exact PMF.map_const _ _

/-- A composed trace has exactly the original acceptance law after its deterministic
prefix, with a clock bounded by the preprocessing and test execution budgets. -/
theorem composition_machineLaw {nf ng : ℕ} (preprocessor : TM nf) (machine : NTM ng)
    {f : List Bool → List Bool} {preprocessTime : ℕ → ℕ}
    (computes : preprocessor.ComputesInTime f preprocessTime) (clock : PolynomialClock machine)
    (nontrivial : machine.qstart ≠ machine.qhalt) (input : List Bool) :
    ∃ steps : ℕ,
      steps ≤ 4 * preprocessTime input.length + 11 + clock.steps (f input).length ∧
      (∀ choices : Fin steps → Bool,
        (NTM.compositionNTM preprocessor machine).halted
          ((NTM.compositionNTM preprocessor machine).trace steps choices
            ((NTM.compositionNTM preprocessor machine).initCfg input))) ∧
      machineLaw (NTM.compositionNTM preprocessor machine) input steps =
        machineLaw machine (f input) (clock.steps (f input).length) := by
  obtain ⟨boundary, prefixSteps, hprefix, _, hrun⟩ :=
    NTM.compositionNTM_trace_run preprocessor machine computes input nontrivial
  let run := clock.steps (f input).length + 1
  have hhaltRun : ∀ choices : Fin run → Bool,
      machine.halted (machine.trace run choices (machine.initCfg (f input))) :=
    (clock.halts.mono (fun _ => Nat.le_succ _)) (f input)
  refine ⟨run + prefixSteps, by dsimp [run]; omega, ?_, ?_⟩
  · intro choices
    rw [hrun (clock.steps (f input).length) choices]
    exact (NTM.placedCfg_halted_iff preprocessor machine boundary.work boundary.input _).mpr
      (hhaltRun _)
  · have hfun : machineVerdict (NTM.compositionNTM preprocessor machine) input (run + prefixSteps) =
        fun choices => machineVerdict machine (f input) run
          (fun i => choices ⟨i.val + prefixSteps, by omega⟩) := by
      funext choices
      unfold machineVerdict
      rw [hrun (clock.steps (f input).length) choices]
      simp only [NTM.placedCfg_halted_iff, NTM.placedCfg_output]
      rfl
    change randomTapeLaw (run + prefixSteps) _ = _
    rw [hfun, randomTapeLaw_suffix]
    exact machineLaw_of_le_of_halts machine (f input) (Nat.le_succ _) (clock.halts (f input))

/-- Polynomial-time preprocessing before a clocked randomized machine has one
global polynomial clock on all raw inputs and preserves acceptance exactly. -/
theorem composition_polynomial_certificate {nf ng : ℕ} (preprocessor : TM nf)
    (machine : NTM ng) {f : List Bool → List Bool} {preprocessTime : ℕ → ℕ}
    (computes : preprocessor.ComputesInTime f preprocessTime)
    {degree : ℕ} (polynomial : preprocessTime =O (· ^ degree))
    (clock : PolynomialClock machine) (nontrivial : machine.qstart ≠ machine.qhalt) :
    ∃ bound : Polynomial ℕ,
      (NTM.compositionNTM preprocessor machine).AllPathsHaltIn bound.eval ∧
      ∀ input, machineLaw (NTM.compositionNTM preprocessor machine) input (bound.eval input.length) =
        machineLaw machine (f input) (clock.steps (f input).length) := by
  obtain ⟨p, hp⟩ := polynomial.pow_polynomial_bound
  let bound : Polynomial ℕ :=
    Polynomial.C 4 * p + Polynomial.C 11 +
      Polynomial.C clock.constant * (p + Polynomial.C 1) ^ clock.degree
  have hbudget (input : List Bool) :
      4 * preprocessTime input.length + 11 + clock.steps (f input).length ≤ bound.eval input.length := by
    have hlen := computes.output_length_le input
    have hpre := hp input.length
    have hclock := clock.bound (f input).length
    have hpow := Nat.pow_le_pow_left (by omega : (f input).length + 1 ≤ p.eval input.length + 1)
      clock.degree
    have hmul := Nat.mul_le_mul_left clock.constant hpow
    simp only [bound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow]
    omega
  refine ⟨bound, ?_, ?_⟩
  · intro input
    obtain ⟨steps, hsteps, hhalt, _⟩ := composition_machineLaw preprocessor machine computes clock nontrivial input
    exact machine_halts_of_le (NTM.compositionNTM preprocessor machine) input
      (hsteps.trans (hbudget input)) hhalt
  · intro input
    obtain ⟨steps, hsteps, hhalt, hlaw⟩ := composition_machineLaw preprocessor machine computes clock nontrivial input
    exact (machineLaw_of_le_of_halts (NTM.compositionNTM preprocessor machine) input
      (hsteps.trans (hbudget input)) hhalt).trans hlaw

/-- A polynomial-time deterministic preprocessor and a certified randomized test
have one uniform polynomial-time implementation on every raw input. -/
theorem exists_preprocessing_machine {f : List Bool → List Bool} (polynomial : f ∈ FP)
    {ng : ℕ} (machine : NTM ng) (clock : PolynomialClock machine) :
    ∃ (n : ℕ) (composite : NTM n) (bound : Polynomial ℕ),
      composite.IsPPT ∧ composite.AllPathsHaltIn bound.eval ∧
      ∀ input, machineLaw composite input (bound.eval input.length) =
        machineLaw machine (f input) (clock.steps (f input).length) := by
  by_cases trivial : machine.qstart = machine.qhalt
  · have hhalt : machine.AllPathsHaltIn (fun _ => 0) := by
      intro input choices
      simpa [NTM.trace] using trivial
    refine ⟨ng, machine, 0, ⟨fun _ => 0, 0, hhalt, BigO.const_le_pow 0 0⟩, ?_, ?_⟩
    · simpa using hhalt
    · intro input
      rw [machineLaw_start_halted machine trivial, machineLaw_start_halted machine trivial]
  · obtain ⟨degree, nf, preprocessor, preprocessTime, computes, hbig⟩ := polynomial
    obtain ⟨p, hhalt, hlaw⟩ :=
      composition_polynomial_certificate preprocessor machine computes hbig clock trivial
    exact ⟨TM.compositionTapeCount nf ng, NTM.compositionNTM preprocessor machine, p,
      ⟨p.eval, p.natDegree, hhalt, BigO.of_polynomial_bound p (fun _ => le_rfl)⟩, hhalt, hlaw⟩

end GameTheory.Complexity.Backend
