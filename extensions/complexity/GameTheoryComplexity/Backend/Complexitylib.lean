import GameTheoryComplexity.RandomTape
import GameTheory.Math.Probability.Indistinguishability
import Complexitylib.Classes.Randomized

/-! Clocked machine execution supplies acceptance laws for sample tests.
The canonical Boolean input serialization has a polynomial length bound.
An arbitrary encoder is deliberately not identified with efficient preprocessing.
-/

noncomputable section

namespace GameTheory.Complexity.Backend

open _root_.Complexity GameTheory.Math.Probability
open scoped _root_.Complexity

/-- A machine verdict is positive precisely when the halted output cell is one. -/
def machineVerdict {n : ℕ} (machine : NTM n) (input : List Bool) (steps : ℕ)
    (tape : Fin steps → Bool) : Bool :=
  decide ((machine.trace steps tape (machine.initCfg input)).state = machine.qhalt ∧
    (machine.trace steps tape (machine.initCfg input)).output.cells 1 = Γ.one)

/-- Run a machine against a uniform, bounded fair random tape. Nonhalting paths reject. -/
def machineLaw {n : ℕ} (machine : NTM n) (input : List Bool) (steps : ℕ) : PMF Bool :=
  randomTapeLaw steps (machineVerdict machine input steps)

/-- The probability-law semantics agrees exactly with the upstream path-count semantics. -/
theorem machineLaw_acceptProb {n : ℕ} (machine : NTM n) (input : List Bool) (steps : ℕ) :
    (machineLaw machine input steps true).toReal =
      (machine.acceptProb input steps : ℝ) := by
  rw [machineLaw, randomTapeLaw_true]
  simp [machineVerdict, NTM.acceptProb, NTM.acceptCount]

/-- A chosen all-path clock, with both asymptotic and explicit polynomial bounds.
The explicit bound also controls execution on inputs encoded from a security parameter. -/
structure PolynomialClock {n : ℕ} (machine : NTM n) where
  /-- The chosen execution clock as a function of encoded input length. -/
  steps : ℕ → ℕ
  halts : machine.AllPathsHaltIn steps
  /-- The degree of the polynomial clock bound. -/
  degree : ℕ
  asymptotic : steps =O (· ^ degree)
  /-- The coefficient of the everywhere-valid shifted polynomial bound. -/
  constant : ℕ
  bound : ∀ len, steps len ≤ constant * (len + 1) ^ degree

/-- This is one fixed uniform machine, with no parameter-indexed advice family. -/
theorem PolynomialClock.isPPT {n : ℕ} {machine : NTM n} (clock : PolynomialClock machine) :
    machine.IsPPT :=
  ⟨clock.steps, clock.degree, clock.halts, clock.asymptotic⟩

/-- Serialize a unary security parameter, a delimiter, and a prescribed Boolean sample tuple. -/
def booleanInput (sampleDegree κ : ℕ) (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    List Bool :=
  List.replicate κ true ++ [false] ++ List.ofFn draws

theorem booleanInput_length (sampleDegree κ : ℕ)
    (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    (booleanInput sampleDegree κ draws).length = κ + 1 + (κ + 1) ^ sampleDegree := by
  simp [booleanInput, Nat.add_assoc]
  omega

/-- Canonical sample serialization grows polynomially in the unary parameter. -/
theorem booleanInput_length_bound (sampleDegree κ : ℕ)
    (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    (booleanInput sampleDegree κ draws).length ≤ 2 * (κ + 1) ^ (sampleDegree + 1) := by
  rw [booleanInput_length, pow_succ]
  have hpow : 1 ≤ (κ + 1) ^ sampleDegree := one_le_pow₀ (by omega)
  nlinarith

/-- A canonical sample test obtained by unary serialization and a certified machine clock.
The machine execution is certified; no machine-level cost theorem for serialization is asserted. -/
def booleanMachineTest {n : ℕ} (machine : NTM n) (clock : PolynomialClock machine)
    (sampleDegree : ℕ) : SampleTest Bool where
  samples κ := (κ + 1) ^ sampleDegree
  accept κ draws :=
    let input := booleanInput sampleDegree κ draws
    machineLaw machine input (clock.steps input.length)

theorem booleanMachineTest_accept {n : ℕ} (machine : NTM n) (clock : PolynomialClock machine)
    (sampleDegree κ : ℕ) (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    ((booleanMachineTest machine clock sampleDegree).accept κ draws true).toReal =
      (machine.acceptProb (booleanInput sampleDegree κ draws)
        (clock.steps (booleanInput sampleDegree κ draws).length) : ℝ) :=
  machineLaw_acceptProb _ _ _

/-- The selected execution clock has a polynomial bound in the security parameter,
uniformly over every Boolean sample tuple. -/
theorem booleanMachineTest_steps_bound {n : ℕ} (machine : NTM n)
    (clock : PolynomialClock machine) (sampleDegree κ : ℕ)
    (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    clock.steps (booleanInput sampleDegree κ draws).length ≤
      clock.constant * 3 ^ clock.degree *
        (κ + 1) ^ ((sampleDegree + 1) * clock.degree) := by
  have hlen := booleanInput_length_bound sampleDegree κ draws
  have hpow : 1 ≤ (κ + 1) ^ (sampleDegree + 1) := one_le_pow₀ (by omega)
  have hlen' : (booleanInput sampleDegree κ draws).length + 1 ≤
      3 * (κ + 1) ^ (sampleDegree + 1) := by omega
  calc
    _ ≤ clock.constant * ((booleanInput sampleDegree κ draws).length + 1) ^ clock.degree :=
      clock.bound _
    _ ≤ clock.constant * (3 * (κ + 1) ^ (sampleDegree + 1)) ^ clock.degree :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen' clock.degree)
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]

/-- The class of canonically encoded, clocked machine tests. Membership certifies
execution and input length, without silently permitting arbitrary oracle encoders. -/
def booleanMachineTests : Set (SampleTest Bool) :=
  {test | ∃ (n : ℕ) (machine : NTM n) (clock : PolynomialClock machine) (degree : ℕ),
    test = booleanMachineTest machine clock degree}

/-- Canonical machine tests also satisfy the existing polynomial sample-count restriction. -/
theorem booleanMachineTests_subset_polySampleTests :
    booleanMachineTests ⊆ polySampleTests Bool := by
  rintro test ⟨n, machine, clock, degree, rfl⟩
  refine ⟨degree + 1, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 ^ degree)] with κ hκ
  change (κ + 1) ^ degree ≤ κ ^ (degree + 1)
  have hpositive : 1 ≤ κ := (one_le_pow₀ (by omega : 1 ≤ (2 : ℕ))).trans hκ
  calc
    (κ + 1) ^ degree ≤ (2 * κ) ^ degree := Nat.pow_le_pow_left (by omega) degree
    _ = 2 ^ degree * κ ^ degree := mul_pow _ _ _
    _ ≤ κ * κ ^ degree := Nat.mul_le_mul_right _ hκ
    _ = κ ^ (degree + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Statistical indistinguishability for all polynomial-sample tests implies
indistinguishability for the canonically encoded machine tests. -/
theorem indistinguishableBy_booleanMachineTests_of_polySampleTests {X X' : ℕ → PMF Bool}
    (h : IndistinguishableBy (polySampleTests Bool) X X') :
    IndistinguishableBy booleanMachineTests X X' :=
  h.mono booleanMachineTests_subset_polySampleTests

/-- Computationally restricted indistinguishability uses the existing test-class interface. -/
theorem indistinguishableBy_booleanMachineTest {X X' : ℕ → PMF Bool}
    (h : IndistinguishableBy booleanMachineTests X X') {n : ℕ} (machine : NTM n)
    (clock : PolynomialClock machine) (degree : ℕ) :
    GameTheory.Math.Negligible fun κ =>
      (booleanMachineTest machine clock degree).acceptProb X κ -
        (booleanMachineTest machine clock degree).acceptProb X' κ :=
  h _ ⟨n, machine, clock, degree, rfl⟩

end GameTheory.Complexity.Backend
