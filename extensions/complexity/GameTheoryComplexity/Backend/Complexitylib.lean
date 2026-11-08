module

public import GameTheoryComplexity.RandomTape
public import GameTheory.Math.Probability.Indistinguishability
public import Complexity.Computability.Probabilistic.CoinTape
public import Complexity.Computability.Probabilistic.PPT.Clock

@[expose] public section

/-! Certified probabilistic programs supply the laws of computational sample tests.
The native certificate realizes every encoded input with one finite fair-coin
machine and a strict polynomial clock. Canonical serialization bounds the encoded
input length in the unary security parameter.
-/

noncomputable section

namespace GameTheory.Complexity.Backend

open Cslib Cslib.Probability Turing.MultiTapeTM GameTheory.Math.Probability

/-- Native uniform word sampling agrees with the canonical finite random-tape law. -/
theorem uniformList_map_eq_randomTapeLaw (steps : ℕ) (verdict : List Bool → Bool) :
    (Cslib.BitString.uniformList steps).map verdict =
      randomTapeLaw steps (fun choices => verdict (List.ofFn choices)) := by
  classical
  ext result
  rw [Cslib.BitString.uniformList_map_apply, randomTapeLaw,
    uniformOfFintype_map_apply]
  simp

/-- A certified program has one efficient deterministic evaluator on saved fair
coins. The evaluator and polynomial budget are fixed before choosing its input. -/
theorem exists_program_randomTapeLaw (program : List Bool → ProbComp Bool)
    (efficient : IsPPTOn encBits encBool program) :
    ∃ (coefficient degree : ℕ) (evaluate : List Bool → List Bool → Bool),
      ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
        (encPair encBits encBits) encBool ∧
      ∀ input, ProbComp.eval (program input) =
        randomTapeLaw (coefficient * (input.length + 1) ^ degree)
          (fun choices => evaluate input (List.ofFn choices)) := by
  obtain ⟨coefficient, degree, evaluate, hefficient, hlaw⟩ :=
    efficient.exists_seeded_evaluator
  exact ⟨coefficient, degree, evaluate, hefficient, fun input =>
    (hlaw input).trans (uniformList_map_eq_randomTapeLaw _ _)⟩

/-- Strict fair-coin polynomial time cannot realize an exact acceptance third. -/
theorem program_acceptProb_ne_one_third (program : List Bool → ProbComp Bool)
    (efficient : IsPPTOn encBits encBool program) (input : List Bool) :
    (ProbComp.eval (program input) true).toReal ≠ 1 / 3 := by
  obtain ⟨coefficient, degree, evaluate, _, hlaw⟩ :=
    exists_program_randomTapeLaw program efficient
  rw [hlaw input]
  exact randomTapeLaw_ne_one_third _ _

/-- Serialize a unary security parameter, a delimiter, and a Boolean sample tuple. -/
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

/-- Interpret a Boolean probabilistic program on the canonical serialized samples.
Efficiency is required by membership in the computational test class. -/
def booleanProgramTest (program : List Bool → ProbComp Bool) (sampleDegree : ℕ) :
    SampleTest Bool where
  samples κ := (κ + 1) ^ sampleDegree
  accept κ draws := ProbComp.eval (program (booleanInput sampleDegree κ draws))

theorem booleanProgramTest_accept (program : List Bool → ProbComp Bool)
    (sampleDegree κ : ℕ) (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    (booleanProgramTest program sampleDegree).accept κ draws =
      ProbComp.eval (program (booleanInput sampleDegree κ draws)) := rfl

/-- Computational tests have a native uniform strict polynomial-time machine
certificate, rather than merely a polynomial number of sample requests. -/
def booleanMachineTests : Set (SampleTest Bool) :=
  {test | ∃ program : List Bool → ProbComp Bool,
    IsPPTOn encBits encBool program ∧
      ∃ degree : ℕ, test = booleanProgramTest program degree}

/-- Every certified computational test sees polynomially many samples. -/
theorem booleanMachineTests_subset_polySampleTests :
    booleanMachineTests ⊆ polySampleTests Bool := by
  rintro test ⟨program, _, degree, rfl⟩
  refine ⟨degree + 1, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 ^ degree)] with κ hκ
  change (κ + 1) ^ degree ≤ κ ^ (degree + 1)
  have hpositive : 1 ≤ κ := (one_le_pow₀ (by omega : 1 ≤ (2 : ℕ))).trans hκ
  calc
    (κ + 1) ^ degree ≤ (2 * κ) ^ degree := Nat.pow_le_pow_left (by omega) degree
    _ = 2 ^ degree * κ ^ degree := mul_pow _ _ _
    _ ≤ κ * κ ^ degree := Nat.mul_le_mul_right _ hκ
    _ = κ ^ (degree + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Statistical indistinguishability for all polynomial-sample tests includes the
canonically encoded computational tests. -/
theorem indistinguishableBy_booleanMachineTests_of_polySampleTests {X X' : ℕ → PMF Bool}
    (h : IndistinguishableBy (polySampleTests Bool) X X') :
    IndistinguishableBy booleanMachineTests X X' :=
  h.mono booleanMachineTests_subset_polySampleTests

/-- Computationally restricted indistinguishability retains the canonical
sample-test and signed negligible-advantage semantics. -/
theorem indistinguishableBy_booleanProgramTest {X X' : ℕ → PMF Bool}
    (h : IndistinguishableBy booleanMachineTests X X')
    (program : List Bool → ProbComp Bool) (efficient : IsPPTOn encBits encBool program)
    (degree : ℕ) :
    GameTheory.Math.Negligible fun κ =>
      (booleanProgramTest program degree).acceptProb X κ -
        (booleanProgramTest program degree).acceptProb X' κ :=
  h _ ⟨program, efficient, degree, rfl⟩

end GameTheory.Complexity.Backend
