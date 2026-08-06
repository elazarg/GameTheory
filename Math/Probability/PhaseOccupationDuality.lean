/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearProgramming.StrongDuality
import Math.Probability.SwitchedPotentialCalculus

/-!
# Phase-occupation duality for finite periodic systems

This module develops the finite-dimensional duality between cyclic occupation
measures and phase-indexed bias inequalities. A phase occupation is a
nonnegative normalized mass on phase-state-action triples whose state marginal
is preserved after advancing the phase and applying the scheduled transition
kernel.

The semantic and coordinate flow laws are equivalent. Feasible occupations
have uniform phase mass, and every feasible bias bounds the average reward of
every feasible occupation. The semantic objects are compiled exactly to a
finite standard-form linear program; primal and dual solutions are decoded
back into an optimal occupation and an optimal phase bias with a common value.

The strong-duality conclusion is conditional only on nonemptiness of the
phase-occupation set. This module supplies a concrete one-state witness but
does not prove nonemptiness for arbitrary finite kernels and action types.
That existence boundary is deliberately kept separate from the duality
compiler.
-/

noncomputable section

open scoped BigOperators

namespace Math
namespace Probability
namespace PhaseOccupationDuality

open Math Probability

variable {S A K : Type*} [Fintype S] [Fintype A] {P : ℕ} [NeZero P]

/-- A period is represented by a finite cyclic phase type. -/
abbrev Phase (P : ℕ) := ZMod P

/-- Real occupation mass on phase-state-action triples. -/
abbrev PhaseOccupation (P : ℕ) (S A : Type*) := Phase P → S → A → ℝ

/-- Sum a phase-state-action quantity over all its finite coordinates. -/
def phaseSum (f : Phase P → S → A → ℝ) : ℝ :=
  ∑ phase, ∑ state, ∑ action, f phase state action

theorem phaseSum_mono {f g : Phase P → S → A → ℝ}
    (h : ∀ phase state action, f phase state action ≤ g phase state action) :
    phaseSum f ≤ phaseSum g := by
  unfold phaseSum
  apply Finset.sum_le_sum
  intro phase _
  apply Finset.sum_le_sum
  intro state _
  apply Finset.sum_le_sum
  intro action _
  exact h phase state action

theorem phaseSum_add (f g : Phase P → S → A → ℝ) :
    phaseSum (fun phase state action => f phase state action + g phase state action) =
      phaseSum f + phaseSum g := by
  simp [phaseSum, Finset.sum_add_distrib]

theorem phaseSum_sub (f g : Phase P → S → A → ℝ) :
    phaseSum (fun phase state action => f phase state action - g phase state action) =
      phaseSum f - phaseSum g := by
  simp [phaseSum, Finset.sum_sub_distrib]

theorem phaseSum_mul_right (f : Phase P → S → A → ℝ) (c : ℝ) :
    phaseSum (fun phase state action => f phase state action * c) = phaseSum f * c := by
  simp [phaseSum, Finset.sum_mul]

/-- The phase-shifted invariant-flow identity, in test-function form.

For finite `S`, testing this equality with the coordinate indicators recovers
the usual pointwise equations
`sum_a μ (p+1) s a = sum_{x,a} μ p x a * K(p,x,a)(s)`.
The test-function presentation is more convenient for the bias pairing. -/
def HasPhaseShiftFlow (kernel : K → S → A → PMF S) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) : Prop :=
  ∀ potential : Phase P → S → ℝ,
    phaseSum (fun phase state action =>
      occupation phase state action *
        expect (kernel (word phase) state action) (potential (phase + 1))) =
      phaseSum (fun phase state action =>
        occupation phase state action * potential phase state)

/-- The coordinate form of cyclic occupation flow.  Mass at `(phase + 1,
state)` is precisely the transition image of the mass used at `phase`. -/
def HasPointwisePhaseShiftFlow (kernel : K → S → A → PMF S) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) : Prop :=
  ∀ phase state,
    (∑ action, occupation (phase + 1) state action) =
      ∑ source, ∑ action,
        occupation phase source action * ((kernel (word phase) source action) state).toReal

private def phaseStateIndicator (targetPhase : Phase P) (targetState : S) :
    Phase P → S → ℝ := by
  classical
  exact fun phase state => if phase = targetPhase then if state = targetState then 1 else 0 else 0

/-- Testing a cyclic flow against the phase-state coordinate indicator recovers
the corresponding pointwise flow equation. -/
theorem hasPointwisePhaseShiftFlow_of_hasPhaseShiftFlow
    {kernel : K → S → A → PMF S} {word : Phase P → K}
    {occupation : PhaseOccupation P S A}
    (hflow : HasPhaseShiftFlow kernel word occupation) :
    HasPointwisePhaseShiftFlow kernel word occupation := by
  classical
  intro phase target
  have tested := hflow (phaseStateIndicator (P := P) (phase + 1) target)
  simp only [phaseSum, phaseStateIndicator, expect_eq_sum] at tested
  simpa [add_right_cancel_iff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq'] using tested.symm

private theorem sum_phase_succ_eq (f : Phase P → ℝ) :
    (∑ phase, f (phase + 1)) = ∑ phase, f phase := by
  classical
  exact Fintype.sum_equiv (Equiv.addRight (1 : Phase P)) _ _ (by intro phase; rfl)

private theorem phaseSum_transition_expect_eq
    (kernel : K → S → A → PMF S) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) (potential : Phase P → S → ℝ) :
    phaseSum (fun phase source action =>
      occupation phase source action *
        expect (kernel (word phase) source action) (potential (phase + 1))) =
      ∑ phase, ∑ target,
        (∑ source, ∑ action,
          occupation phase source action * ((kernel (word phase) source action) target).toReal) *
            potential (phase + 1) target := by
  classical
  simp only [phaseSum, expect_eq_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro phase _
  calc
    (∑ source, ∑ action, ∑ target,
        occupation phase source action *
          (((kernel (word phase) source action) target).toReal * potential (phase + 1) target)) =
      ∑ source, ∑ target, ∑ action,
        occupation phase source action *
          (((kernel (word phase) source action) target).toReal * potential (phase + 1) target) := by
        apply Finset.sum_congr rfl
        intro source _
        exact Finset.sum_comm
    _ = ∑ target, ∑ source, ∑ action,
        occupation phase source action *
          (((kernel (word phase) source action) target).toReal * potential (phase + 1) target) := by
        exact Finset.sum_comm
    _ = ∑ target,
        (∑ source, ∑ action,
          occupation phase source action * ((kernel (word phase) source action) target).toReal) *
            potential (phase + 1) target := by
        apply Finset.sum_congr rfl
        intro target _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro source _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro action _
        ring

/-- The ordinary coordinate equations imply the all-test-functions cyclic
flow identity. -/
theorem hasPhaseShiftFlow_of_hasPointwisePhaseShiftFlow
    {kernel : K → S → A → PMF S} {word : Phase P → K}
    {occupation : PhaseOccupation P S A}
    (hflow : HasPointwisePhaseShiftFlow kernel word occupation) :
    HasPhaseShiftFlow kernel word occupation := by
  intro potential
  rw [phaseSum_transition_expect_eq]
  calc
    (∑ phase, ∑ target,
        (∑ source, ∑ action,
          occupation phase source action * ((kernel (word phase) source action) target).toReal) *
            potential (phase + 1) target) =
      ∑ phase, ∑ target, (∑ action, occupation (phase + 1) target action) *
        potential (phase + 1) target := by
        apply Finset.sum_congr rfl
        intro phase _
        apply Finset.sum_congr rfl
        intro target _
        rw [hflow phase target]
    _ = ∑ target, ∑ phase, (∑ action, occupation (phase + 1) target action) *
        potential (phase + 1) target := by
        exact Finset.sum_comm
    _ = ∑ target, ∑ phase, (∑ action, occupation phase target action) *
        potential phase target := by
        apply Finset.sum_congr rfl
        intro target _
        exact sum_phase_succ_eq fun phase =>
          (∑ action, occupation phase target action) * potential phase target
    _ = ∑ phase, ∑ target, (∑ action, occupation phase target action) *
        potential phase target := by
        exact Finset.sum_comm
    _ = phaseSum (fun phase state action =>
        occupation phase state action * potential phase state) := by
        simp only [phaseSum]
        apply Finset.sum_congr rfl
        intro phase _
        apply Finset.sum_congr rfl
        intro state _
        rw [Finset.sum_mul]

/-- The pointwise and test-function presentations of finite cyclic flow are
equivalent. -/
theorem hasPointwisePhaseShiftFlow_iff_hasPhaseShiftFlow
    (kernel : K → S → A → PMF S) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) :
    HasPointwisePhaseShiftFlow kernel word occupation ↔
      HasPhaseShiftFlow kernel word occupation := by
  constructor
  · exact hasPhaseShiftFlow_of_hasPointwisePhaseShiftFlow
  · exact hasPointwisePhaseShiftFlow_of_hasPhaseShiftFlow

/-- A finite, normalized phase occupation satisfying the cyclic flow law. -/
structure IsPhaseOccupation (kernel : K → S → A → PMF S) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) : Prop where
  nonnegative : ∀ phase state action, 0 ≤ occupation phase state action
  normalized : phaseSum occupation = 1
  flow : HasPhaseShiftFlow kernel word occupation

/-- Total occupation mass carried by a phase. -/
def phaseMass (occupation : PhaseOccupation P S A) (phase : Phase P) : ℝ :=
  ∑ state, ∑ action, occupation phase state action

theorem phaseMass_succ_eq (kernel : K → S → A → PMF S) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) (hoccupation : IsPhaseOccupation kernel word occupation)
    (phase : Phase P) : phaseMass occupation (phase + 1) = phaseMass occupation phase := by
  classical
  have hflow := hoccupation.flow (fun q _ => if q = phase + 1 then 1 else 0)
  simp [phaseSum, Math.Probability.expect_const] at hflow
  change (∑ state, ∑ action, occupation (phase + 1) state action) =
    ∑ state, ∑ action, occupation phase state action
  exact hflow.symm

theorem phaseMass_eq (kernel : K → S → A → PMF S) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) (hoccupation : IsPhaseOccupation kernel word occupation)
    (phase : Phase P) : phaseMass occupation phase = phaseMass occupation 0 := by
  have hnat : ∀ n : ℕ, phaseMass occupation (n : Phase P) = phaseMass occupation 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.cast_succ, phaseMass_succ_eq kernel word occupation hoccupation]
        exact ih
  rw [← phase.natCast_zmod_val]
  exact hnat phase.val

/-- Every phase receives the same mass, namely the reciprocal period. -/
theorem phaseMass_eq_inv_period (kernel : K → S → A → PMF S) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) (hoccupation : IsPhaseOccupation kernel word occupation)
    (phase : Phase P) : phaseMass occupation phase = 1 / (P : ℝ) := by
  have hconstant : ∀ q : Phase P, phaseMass occupation q = phaseMass occupation 0 :=
    phaseMass_eq kernel word occupation hoccupation
  have htotal : (P : ℝ) * phaseMass occupation 0 = 1 := by
    have hsum : (∑ q : Phase P, phaseMass occupation q) = 1 := by
      simpa only [phaseSum, phaseMass] using hoccupation.normalized
    rw [show (∑ q : Phase P, phaseMass occupation q) =
        ∑ _q : Phase P, phaseMass occupation 0 by
      apply Finset.sum_congr rfl
      intro q _
      exact hconstant q] at hsum
    simpa [ZMod.card, mul_comm] using hsum
  rw [hconstant phase]
  apply (eq_div_iff (by exact_mod_cast (NeZero.ne P))).2
  linarith

/-! ### A nonvacuity witness -/

namespace OneStateExample

/-- The unique one-state, one-action transition system. -/
def kernel (_ : Unit) (_ : Unit) (_ : Unit) : PMF Unit := PMF.pure ()

/-- Its one-phase schedule. -/
def word : Phase 1 → Unit := fun _ => ()

/-- Unit occupation mass on the sole phase-state-action triple. -/
def occupation : PhaseOccupation 1 Unit Unit := fun _ _ _ => 1

theorem pointwiseFlow : HasPointwisePhaseShiftFlow kernel word occupation := by
  intro phase state
  simp [occupation, kernel]

/-- The phase-occupation polytope is nonempty, even with its concrete
pointwise flow constraints. -/
theorem feasible : IsPhaseOccupation kernel word occupation := by
  refine ⟨?_, ?_, hasPhaseShiftFlow_of_hasPointwisePhaseShiftFlow pointwiseFlow⟩
  · intro phase state action
    norm_num [occupation]
  · simp [phaseSum, occupation]

end OneStateExample

/-- The phase-average reward carried by an occupation. -/
def phaseAverageReward (reward : K → S → A → ℝ) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) : ℝ :=
  phaseSum fun phase state action =>
    occupation phase state action * reward (word phase) state action

/-- The expected next-phase bias under an occupation. -/
def phasePotentialAdvance (kernel : K → S → A → PMF S) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) (potential : Phase P → S → ℝ) : ℝ :=
  phaseSum fun phase state action =>
    occupation phase state action *
      expect (kernel (word phase) state action) (potential (phase + 1))

/-- The current-phase bias under an occupation. -/
def phasePotentialValue (occupation : PhaseOccupation P S A)
    (potential : Phase P → S → ℝ) : ℝ :=
  phaseSum fun phase state action => occupation phase state action * potential phase state

/-- A phase-indexed bias with uniform per-stage slack `g`.

This is exactly `Math.Probability.HasPhaseSlack`, restated here so that the
occupation/bias LP has no dependence on a policy or a marginal-law path. -/
def HasPhaseBias (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ)
    (word : Phase P → K) (potential : Phase P → S → ℝ) (g : ℝ) : Prop :=
  ∀ phase state action,
    reward (word phase) state action +
        expect (kernel (word phase) state action) (potential (phase + 1)) -
      potential phase state ≤ g

omit [Fintype S] [Fintype A] [NeZero P] in
theorem hasPhaseBias_iff_hasPhaseSlack
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ)
    (word : Phase P → K) (potential : Phase P → S → ℝ) (g : ℝ) :
    HasPhaseBias kernel reward word potential g ↔
      HasPhaseSlack kernel reward word potential g := Iff.rfl

/-- A feasible phase occupation has zero net potential drift. -/
theorem phasePotentialAdvance_eq_phasePotentialValue
    {kernel : K → S → A → PMF S} {word : Phase P → K}
    {occupation : PhaseOccupation P S A} (flow : HasPhaseShiftFlow kernel word occupation)
    (potential : Phase P → S → ℝ) :
    phasePotentialAdvance kernel word occupation potential =
      phasePotentialValue occupation potential := flow potential

private theorem phaseSum_weightedSlack_eq
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ)
    (word : Phase P → K) (occupation : PhaseOccupation P S A)
    (potential : Phase P → S → ℝ) :
    phaseSum (fun phase state action => occupation phase state action *
      (reward (word phase) state action +
        expect (kernel (word phase) state action) (potential (phase + 1)) -
          potential phase state)) =
      phaseAverageReward reward word occupation +
        (phasePotentialAdvance kernel word occupation potential -
          phasePotentialValue occupation potential) := by
  rw [show (fun phase state action => occupation phase state action *
      (reward (word phase) state action +
        expect (kernel (word phase) state action) (potential (phase + 1)) -
          potential phase state)) =
      (fun phase state action =>
        occupation phase state action * reward (word phase) state action +
          (occupation phase state action *
            expect (kernel (word phase) state action) (potential (phase + 1)) -
            occupation phase state action * potential phase state)) by
        funext phase state action
        ring]
  rw [phaseSum_add, phaseSum_sub]
  rfl

/-- **Weak phase-occupation/bias duality.**

The conclusion is the phase-augmented average-reward LP weak-duality
inequality.  It is independent of any policy: occupation feasibility already
records the state-action frequencies, and the bias inequality is pointwise in
the action. -/
theorem phaseAverageReward_le_bias
    {kernel : K → S → A → PMF S} {reward : K → S → A → ℝ}
    {word : Phase P → K} {occupation : PhaseOccupation P S A}
    {potential : Phase P → S → ℝ} {g : ℝ}
    (hoccupation : IsPhaseOccupation kernel word occupation)
    (hbias : HasPhaseBias kernel reward word potential g) :
    phaseAverageReward reward word occupation ≤ g := by
  have hpoint : ∀ phase state action,
      occupation phase state action *
        (reward (word phase) state action +
          expect (kernel (word phase) state action) (potential (phase + 1)) -
            potential phase state) ≤ occupation phase state action * g := by
    intro phase state action
    exact mul_le_mul_of_nonneg_left (hbias phase state action)
      (hoccupation.nonnegative phase state action)
  have hsum := phaseSum_mono hpoint
  rw [phaseSum_weightedSlack_eq] at hsum
  rw [phasePotentialAdvance_eq_phasePotentialValue hoccupation.flow potential] at hsum
  have hmass : phaseSum (fun phase state action => occupation phase state action * g) = g := by
    rw [phaseSum_mul_right, hoccupation.normalized]
    ring
  rw [hmass] at hsum
  linarith

/-- The weak-duality theorem in the exact `HasPhaseSlack` vocabulary used by
`SwitchedPotentialCalculus`. -/
theorem phaseAverageReward_le_phaseSlack
    {kernel : K → S → A → PMF S} {reward : K → S → A → ℝ}
    {word : Phase P → K} {occupation : PhaseOccupation P S A}
    {potential : Phase P → S → ℝ} {g : ℝ}
    (hoccupation : IsPhaseOccupation kernel word occupation)
    (hslack : HasPhaseSlack kernel reward word potential g) :
    phaseAverageReward reward word occupation ≤ g :=
  phaseAverageReward_le_bias hoccupation hslack

/-! ### Standard-form matrix compiler

The semantic occupation variables are compiled to the finite standard-form
LP used by `Math.LinearProgramming.StrongDuality`.  Every equality receives a
positive and a negative row; nonnegativity is the built-in primal cone. -/

/-- Columns of the occupation LP, i.e. phase-state-action coordinates. -/
abbrev OccupationColumn (P : ℕ) (S A : Type*) := Phase P × S × A

/-- Paired flow and normalization rows of the occupation LP.  The left side
is `(sign, phase, state)`; the right side is the normalization sign. -/
abbrev OccupationRow (P : ℕ) (S : Type*) := (Bool × Phase P × S) ⊕ Bool

private noncomputable def flowCoefficient (kernel : K → S → A → PMF S) (word : Phase P → K)
    (phase : Phase P) (state : S) (column : OccupationColumn P S A) : ℝ := by
  classical
  exact (if column.1 = phase + 1 ∧ column.2.1 = state then 1 else 0) -
    (if column.1 = phase then ((kernel (word phase) column.2.1 column.2.2) state).toReal else 0)

/-- Matrix `A` for `A x ≥ b`: two signs of every flow equality and of
normalization. -/
noncomputable def occupationA (kernel : K → S → A → PMF S) (word : Phase P → K) :
    OccupationRow P S → OccupationColumn P S A → ℝ
  | .inl (true, phase, state), column => flowCoefficient kernel word phase state column
  | .inl (false, phase, state), column => -flowCoefficient kernel word phase state column
  | .inr true, _ => 1
  | .inr false, _ => -1

def occupationB : OccupationRow P S → ℝ
  | .inl _ => 0
  | .inr true => 1
  | .inr false => -1

/-- The primal minimizes negative average reward. -/
def occupationC (reward : K → S → A → ℝ) (word : Phase P → K) :
    OccupationColumn P S A → ℝ :=
  fun column => -reward (word column.1) column.2.1 column.2.2

/-- Repackage a curried semantic occupation as the LP column vector. -/
def occupationVector (occupation : PhaseOccupation P S A) : OccupationColumn P S A → ℝ :=
  fun column => occupation column.1 column.2.1 column.2.2

/-- Decode an LP column vector back into its curried semantic occupation. -/
def occupationOfVector (x : OccupationColumn P S A → ℝ) : PhaseOccupation P S A :=
  fun phase state action => x (phase, state, action)

omit [Fintype S] [Fintype A] [NeZero P] in
@[simp] theorem occupationVector_ofVector (x : OccupationColumn P S A → ℝ) :
    occupationVector (occupationOfVector x) = x := by
  funext column
  rcases column with ⟨phase, state, action⟩
  rfl

omit [Fintype S] [Fintype A] [NeZero P] in
@[simp] theorem occupationOfVector_vector (occupation : PhaseOccupation P S A) :
    occupationOfVector (occupationVector occupation) = occupation := by
  funext phase state action
  rfl

private theorem compiled_flow_rowEval
    (kernel : K → S → A → PMF S) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) (phase : Phase P) (state : S) :
    Math.LinearProgramming.rowEval (occupationA kernel word) (occupationVector occupation)
      (.inl (true, phase, state)) =
        (∑ action, occupation (phase + 1) state action) -
          ∑ source, ∑ action,
            occupation phase source action *
              ((kernel (word phase) source action) state).toReal := by
  classical
  simp only [Math.LinearProgramming.rowEval, occupationA, occupationVector, flowCoefficient]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  simp_rw [sub_mul]
  simp_rw [Finset.sum_sub_distrib]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hdelta (p : Phase P) (s : S) (f : Phase P → S → ℝ) :
      (∑ q, ∑ t, if q = p ∧ t = s then f q t else 0) = f p s := by
    calc
      (∑ q, ∑ t, if q = p ∧ t = s then f q t else 0) =
          ∑ q, if q = p then f q s else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases hq : q = p <;> simp [hq]
      _ = f p s := by simp
  rw [hdelta]
  congr 1
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro action _
  ring

private theorem compiled_neg_flow_rowEval
    (kernel : K → S → A → PMF S) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) (phase : Phase P) (state : S) :
    Math.LinearProgramming.rowEval (occupationA kernel word) (occupationVector occupation)
      (.inl (false, phase, state)) =
      -Math.LinearProgramming.rowEval (occupationA kernel word) (occupationVector occupation)
        (.inl (true, phase, state)) := by
  classical
  unfold Math.LinearProgramming.rowEval occupationA
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro column _
  simp [flowCoefficient]
  ring

private theorem compiled_normalization_rowEval
    (kernel : K → S → A → PMF S) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) (positive : Bool) :
    Math.LinearProgramming.rowEval (occupationA kernel word) (occupationVector occupation)
      (.inr positive) = if positive then phaseSum occupation else -phaseSum occupation := by
  classical
  cases positive <;>
    simp [Math.LinearProgramming.rowEval, occupationA, occupationVector, phaseSum,
      Fintype.sum_prod_type, Finset.sum_neg_distrib]

/-- Every semantic phase occupation is feasible for the compiled standard-form
primal. Together with the row-decoding argument below, this is one direction
of the exact semantic/compiler equivalence. -/
theorem minPrimalFeasible_of_isPhaseOccupation
    (kernel : K → S → A → PMF S) (word : Phase P → K)
    (occupation : PhaseOccupation P S A)
    (hoccupation : IsPhaseOccupation kernel word occupation) :
    Math.LinearProgramming.MinPrimalFeasible (occupationA kernel word) occupationB
      (occupationVector occupation) := by
  constructor
  · intro column
    exact hoccupation.nonnegative _ _ _
  · intro row
    cases row with
    | inl row =>
        rcases row with ⟨positive, phase, state⟩
        cases positive
        · rw [occupationB, compiled_neg_flow_rowEval, compiled_flow_rowEval]
          rw [hasPointwisePhaseShiftFlow_of_hasPhaseShiftFlow hoccupation.flow phase state]
          norm_num
        · rw [occupationB, compiled_flow_rowEval]
          rw [hasPointwisePhaseShiftFlow_of_hasPhaseShiftFlow hoccupation.flow phase state]
          norm_num
    | inr positive =>
        cases positive
        · rw [occupationB, compiled_normalization_rowEval]
          rw [hoccupation.normalized]
          norm_num
        · rw [occupationB, compiled_normalization_rowEval]
          rw [hoccupation.normalized]
          norm_num

/-- The compiler is exact: standard-form primal feasibility is precisely
nonnegative normalized cyclic occupation flow. -/
theorem minPrimalFeasible_iff_isPhaseOccupation
    (kernel : K → S → A → PMF S) (word : Phase P → K)
    (x : OccupationColumn P S A → ℝ) :
    Math.LinearProgramming.MinPrimalFeasible (occupationA kernel word) occupationB x ↔
      IsPhaseOccupation kernel word (occupationOfVector x) := by
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · intro phase state action
      simpa [occupationOfVector] using hx.1 (phase, state, action)
    · have hpos := hx.2 (.inr true)
      have hneg := hx.2 (.inr false)
      rw [← occupationVector_ofVector x] at hpos hneg
      simp only [occupationB] at hpos hneg
      rw [compiled_normalization_rowEval] at hpos hneg
      change 1 ≤ phaseSum (occupationOfVector x) at hpos
      change -1 ≤ -phaseSum (occupationOfVector x) at hneg
      linarith
    · apply hasPhaseShiftFlow_of_hasPointwisePhaseShiftFlow
      intro phase state
      have hpos := hx.2 (.inl (true, phase, state))
      have hneg := hx.2 (.inl (false, phase, state))
      rw [← occupationVector_ofVector x] at hpos hneg
      simp only [occupationB] at hpos hneg
      rw [compiled_flow_rowEval] at hpos
      rw [compiled_neg_flow_rowEval, compiled_flow_rowEval] at hneg
      linarith
  · intro hoccupation
    simpa using minPrimalFeasible_of_isPhaseOccupation kernel word
      (occupationOfVector x) hoccupation

theorem compiled_objective_eq_neg_phaseAverageReward
    (reward : K → S → A → ℝ) (word : Phase P → K)
    (occupation : PhaseOccupation P S A) :
    Math.LinearProgramming.minPrimalValue (occupationC reward word)
      (occupationVector occupation) = -phaseAverageReward reward word occupation := by
  classical
  simp only [Math.LinearProgramming.minPrimalValue, Math.LinearProgramming.dot,
    occupationC, occupationVector, phaseAverageReward, phaseSum]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro phase _
  apply Finset.sum_congr rfl
  intro state _
  apply Finset.sum_congr rfl
  intro action _
  ring

/-- A finite, data-only absolute bound for the compiled objective. -/
def compiledObjectiveAbsBound (reward : K → S → A → ℝ) (word : Phase P → K) : ℝ :=
  ∑ column : OccupationColumn P S A, |occupationC reward word column|

private theorem occupationC_ge_neg_compiledObjectiveAbsBound
    (reward : K → S → A → ℝ) (word : Phase P → K)
    (column : OccupationColumn P S A) :
    -compiledObjectiveAbsBound reward word ≤ occupationC reward word column := by
  unfold compiledObjectiveAbsBound
  calc
    -(∑ other : OccupationColumn P S A, |occupationC reward word other|) ≤
        -|occupationC reward word column| := by
      exact neg_le_neg (Finset.single_le_sum
        (fun other _ => abs_nonneg (occupationC reward word other)) (Finset.mem_univ _))
    _ ≤ occupationC reward word column := neg_abs_le _

private theorem compiled_vector_mass_eq_one
    (kernel : K → S → A → PMF S) (word : Phase P → K)
    (x : OccupationColumn P S A → ℝ)
    (hx : Math.LinearProgramming.MinPrimalFeasible (occupationA kernel word) occupationB x) :
    (∑ column, x column) = 1 := by
  have hnormal := (minPrimalFeasible_iff_isPhaseOccupation kernel word x).mp hx |>.normalized
  change (∑ phase, ∑ state, ∑ action, x (phase, state, action)) = 1 at hnormal
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  exact hnormal

/-- The compiled minimization is automatically bounded below whenever its
constraints are feasible; no reward boundedness assumption is needed in the
finite setting. -/
theorem compiled_objective_lower_bound
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (word : Phase P → K)
    (x : OccupationColumn P S A → ℝ)
    (hx : Math.LinearProgramming.MinPrimalFeasible (occupationA kernel word) occupationB x) :
    -compiledObjectiveAbsBound reward word ≤
      Math.LinearProgramming.minPrimalValue (occupationC reward word) x := by
  have hmass := compiled_vector_mass_eq_one kernel word x hx
  calc
    -compiledObjectiveAbsBound reward word =
        -compiledObjectiveAbsBound reward word * (∑ column, x column) := by rw [hmass]; ring
    _ = ∑ column, -compiledObjectiveAbsBound reward word * x column := by
      rw [Finset.mul_sum]
    _ ≤ ∑ column, occupationC reward word column * x column := by
      apply Finset.sum_le_sum
      intro column _
      exact mul_le_mul_of_nonneg_right
        (occupationC_ge_neg_compiledObjectiveAbsBound reward word column) (hx.1 column)
    _ = Math.LinearProgramming.minPrimalValue (occupationC reward word) x := rfl

/-- The direct standard-form strong-duality consequence for the compiled
occupation matrix. The exact primal-feasibility equivalence above supplies
the semantic bridge; this theorem packages LP-level attainment and equality. -/
theorem compiled_lp_attains_and_has_dual
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (word : Phase P → K)
    (hfeasible : ∃ x, Math.LinearProgramming.MinPrimalFeasible
      (occupationA kernel word) occupationB x)
    (hbounded : ∃ lower : ℝ, ∀ x,
      Math.LinearProgramming.MinPrimalFeasible (occupationA kernel word) occupationB x →
        lower ≤ Math.LinearProgramming.minPrimalValue (occupationC reward word) x) :
    ∃ x y,
      Math.LinearProgramming.MinPrimalFeasible (occupationA kernel word) occupationB x ∧
      Math.LinearProgramming.MaxDualFeasible (occupationA kernel word) (occupationC reward word) y ∧
      (∀ z, Math.LinearProgramming.MinPrimalFeasible (occupationA kernel word) occupationB z →
        Math.LinearProgramming.minPrimalValue (occupationC reward word) x ≤
          Math.LinearProgramming.minPrimalValue (occupationC reward word) z) ∧
      Math.LinearProgramming.maxDualValue occupationB y =
        Math.LinearProgramming.minPrimalValue (occupationC reward word) x := by
  obtain ⟨x, hx, hopt⟩ :=
    Math.LinearProgramming.exists_minPrimalOptimal_of_feasible_of_bounded hfeasible hbounded
  obtain ⟨y, hy, hvalue⟩ := Math.LinearProgramming.lp_strong_duality hx hopt
  exact ⟨x, y, hx, hy, hopt, hvalue⟩

/-- In finite phase problems the lower-bound premise of strong duality is
automatic. -/
theorem compiled_lp_attains_and_has_dual_of_feasible
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (word : Phase P → K)
    (hfeasible : ∃ x, Math.LinearProgramming.MinPrimalFeasible
      (occupationA kernel word) occupationB x) :
    ∃ x y,
      Math.LinearProgramming.MinPrimalFeasible (occupationA kernel word) occupationB x ∧
      Math.LinearProgramming.MaxDualFeasible (occupationA kernel word) (occupationC reward word) y ∧
      (∀ z, Math.LinearProgramming.MinPrimalFeasible (occupationA kernel word) occupationB z →
        Math.LinearProgramming.minPrimalValue (occupationC reward word) x ≤
          Math.LinearProgramming.minPrimalValue (occupationC reward word) z) ∧
      Math.LinearProgramming.maxDualValue occupationB y =
        Math.LinearProgramming.minPrimalValue (occupationC reward word) x :=
  compiled_lp_attains_and_has_dual kernel reward word hfeasible
    ⟨-compiledObjectiveAbsBound reward word,
      fun x hx => compiled_objective_lower_bound kernel reward word x hx⟩

/-- Difference of the paired flow-row multipliers. -/
def dualFlow (y : OccupationRow P S → ℝ) (phase : Phase P) (state : S) : ℝ :=
  y (.inl (true, phase, state)) - y (.inl (false, phase, state))

/-- Difference of the paired normalization-row multipliers. -/
def dualNormalization (y : OccupationRow P S → ℝ) : ℝ :=
  y (.inr true) - y (.inr false)

/-- The phase bias read from a standard-form dual multiplier. -/
def dualPotential (y : OccupationRow P S → ℝ) (phase : Phase P) (state : S) : ℝ :=
  -dualFlow y (phase - 1) state

/-- The average slack read from a standard-form dual multiplier. -/
def dualSlack (y : OccupationRow P S → ℝ) : ℝ := -dualNormalization y

omit [Fintype A] in
private theorem compiled_dual_column_eval
    (kernel : K → S → A → PMF S) (word : Phase P → K)
    (y : OccupationRow P S → ℝ) (column : OccupationColumn P S A) :
    Math.LinearProgramming.colEval (occupationA kernel word) y column =
      dualFlow y (column.1 - 1) column.2.1 -
        ∑ target, dualFlow y column.1 target *
          ((kernel (word column.1) column.2.1 column.2.2) target).toReal +
        dualNormalization y := by
  classical
  unfold Math.LinearProgramming.colEval occupationA dualFlow dualNormalization
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Fintype.sum_bool]
  simp only [flowCoefficient, mul_neg, Finset.sum_neg_distrib, Fintype.univ_bool,
    Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, mul_one, Finset.sum_singleton]
  have hdelta (f : Phase P → S → ℝ) :
      (∑ phase, ∑ state,
        f phase state *
          (if column.1 = phase + 1 ∧ column.2.1 = state then 1 else 0)) =
        f (column.1 - 1) column.2.1 := by
    calc
      (∑ phase, ∑ state,
          f phase state *
            (if column.1 = phase + 1 ∧ column.2.1 = state then 1 else 0)) =
          ∑ phase, if phase = column.1 - 1 then f phase column.2.1 else 0 := by
        apply Finset.sum_congr rfl
        intro phase _
        by_cases hphase : phase = column.1 - 1
        · subst phase
          simp
        · have hne : column.1 ≠ phase + 1 := by
            intro h
            apply hphase
            calc
              phase = phase + 1 - 1 := by simp
              _ = column.1 - 1 := by rw [h]
          simp [hphase, hne]
      _ = f (column.1 - 1) column.2.1 := by simp
  have hkernel (f : Phase P → S → ℝ) :
      (∑ phase, ∑ state,
        f phase state *
          (if column.1 = phase then
            ((kernel (word phase) column.2.1 column.2.2) state).toReal else 0)) =
        ∑ state, f column.1 state *
          ((kernel (word column.1) column.2.1 column.2.2) state).toReal := by
    calc
      (∑ phase, ∑ state,
          f phase state *
            (if column.1 = phase then
              ((kernel (word phase) column.2.1 column.2.2) state).toReal else 0)) =
          ∑ phase, if phase = column.1 then
            ∑ state, f phase state *
              ((kernel (word phase) column.2.1 column.2.2) state).toReal else 0 := by
        apply Finset.sum_congr rfl
        intro phase _
        by_cases hphase : column.1 = phase
        · subst phase
          simp
        · have hphase' : phase ≠ column.1 := Ne.symm hphase
          simp [hphase, hphase']
      _ = ∑ state, f column.1 state *
          ((kernel (word column.1) column.2.1 column.2.2) state).toReal := by simp
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hdelta, hkernel, hkernel, hdelta]
  simp_rw [sub_mul]
  simp_rw [Finset.sum_sub_distrib]
  ring

omit [Fintype A] in
/-- Every feasible standard-form dual multiplier decodes to a semantic phase
bias certificate.  Paired equality rows are read by subtraction. -/
theorem hasPhaseBias_of_maxDualFeasible
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (word : Phase P → K)
    (y : OccupationRow P S → ℝ)
    (hy : Math.LinearProgramming.MaxDualFeasible (occupationA kernel word)
      (occupationC reward word) y) :
    HasPhaseBias kernel reward word (dualPotential y) (dualSlack y) := by
  intro phase state action
  have hcolumn := hy.2 (phase, state, action)
  rw [compiled_dual_column_eval] at hcolumn
  change dualFlow y (phase - 1) state -
      ∑ target, dualFlow y phase target *
        ((kernel (word phase) state action) target).toReal + dualNormalization y ≤
      -reward (word phase) state action at hcolumn
  unfold dualPotential dualSlack
  rw [Math.Probability.expect_eq_sum]
  simp only [add_sub_cancel_right]
  have hsum :
      (∑ target, ((kernel (word phase) state action) target).toReal *
        -dualFlow y phase target) =
        -(∑ target, dualFlow y phase target *
          ((kernel (word phase) state action) target).toReal) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro target _
    ring
  rw [hsum]
  linarith

private theorem compiled_dual_value_eq_dualNormalization
    (y : OccupationRow P S → ℝ) :
    Math.LinearProgramming.maxDualValue occupationB y = dualNormalization y := by
  classical
  unfold Math.LinearProgramming.maxDualValue Math.LinearProgramming.dot dualNormalization
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Fintype.sum_bool]
  simp [occupationB, sub_eq_add_neg]

/-- **Semantic strong duality, conditional only on occupation nonemptiness.**

The finite compiler supplies an optimal occupation and a decoded optimal
phase-bias slack.  The final universal clauses state that their common value
is respectively the maximum semantic occupation reward and the minimum
semantic bias bound. -/
theorem exists_optimal_phaseOccupation_and_phaseBias_of_feasible
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (word : Phase P → K)
    (hfeasible : ∃ occupation : PhaseOccupation P S A,
      IsPhaseOccupation kernel word occupation) :
    ∃ occupation potential g,
      IsPhaseOccupation kernel word occupation ∧
      HasPhaseBias kernel reward word potential g ∧
      phaseAverageReward reward word occupation = g ∧
      (∀ other, IsPhaseOccupation kernel word other →
        phaseAverageReward reward word other ≤ phaseAverageReward reward word occupation) ∧
      (∀ potential' g', HasPhaseBias kernel reward word potential' g' → g ≤ g') := by
  obtain ⟨seed, hseed⟩ := hfeasible
  obtain ⟨x, y, hx, hy, hopt, hvalue⟩ :=
    compiled_lp_attains_and_has_dual_of_feasible kernel reward word
      ⟨occupationVector seed, minPrimalFeasible_of_isPhaseOccupation kernel word seed hseed⟩
  let occupation := occupationOfVector x
  let potential := dualPotential y
  let g := dualSlack y
  have hoccupation : IsPhaseOccupation kernel word occupation :=
    (minPrimalFeasible_iff_isPhaseOccupation kernel word x).mp hx
  have hbias : HasPhaseBias kernel reward word potential g :=
    hasPhaseBias_of_maxDualFeasible kernel reward word y hy
  have hprimal : Math.LinearProgramming.minPrimalValue (occupationC reward word) x =
      -phaseAverageReward reward word occupation := by
    rw [← occupationVector_ofVector x]
    exact compiled_objective_eq_neg_phaseAverageReward reward word occupation
  have hdual : Math.LinearProgramming.maxDualValue occupationB y = -g := by
    rw [compiled_dual_value_eq_dualNormalization]
    simp [g, dualSlack]
  have hvalue' : phaseAverageReward reward word occupation = g := by
    rw [hprimal] at hvalue
    rw [hdual] at hvalue
    linarith
  refine ⟨occupation, potential, g, hoccupation, hbias, hvalue', ?_, ?_⟩
  · intro other hother
    have hotherPrimal := minPrimalFeasible_of_isPhaseOccupation kernel word other hother
    have hle := hopt (occupationVector other) hotherPrimal
    rw [hprimal, compiled_objective_eq_neg_phaseAverageReward] at hle
    linarith
  · intro potential' g' hbias'
    rw [← hvalue']
    exact phaseAverageReward_le_bias hoccupation hbias'

end PhaseOccupationDuality
end Probability
end Math

/-! ## Axiom audit -/

#print axioms
  Math.Probability.PhaseOccupationDuality.hasPointwisePhaseShiftFlow_iff_hasPhaseShiftFlow
#print axioms Math.Probability.PhaseOccupationDuality.phaseAverageReward_le_phaseSlack
#print axioms Math.Probability.PhaseOccupationDuality.minPrimalFeasible_of_isPhaseOccupation
#print axioms Math.Probability.PhaseOccupationDuality.compiled_lp_attains_and_has_dual
