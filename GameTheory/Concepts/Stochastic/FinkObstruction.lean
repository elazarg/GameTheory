/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.FinkSelectionCounterexample

/-!
# Dual obstructions to the supported Fink tangent system

This file makes the branch point after the discounted tangent hierarchy
explicit.  Either the supported tangent target has a harmonic preimage, or a
linear functional annihilates every harmonic adjustment while detecting the
target.  The latter object is the input that an obstruction-to-phase
constructor must turn into a public test, punishment, descent, or sublinear
charge.

The selection-resistant tangent example instantiates the obstruction branch.
Its forced rare-action rate shows that changing the discounted equilibrium
selection cannot move the example back to the feasible branch.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type}

/-- A finite-dimensional dual witness that the supported Fink tangent target
does not lie in the range of the harmonic-adjustment operator. -/
structure FinkSupportTangentDualObstruction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) where
  functional : Module.Dual ℝ G.FinkSupportTangentEquationVector
  operator_eq_zero : ∀ A : G.State → Payoff ι,
    functional (G.finkSupportTangentOperator z A) = 0
  target_ne_zero :
    functional (G.finkSupportTangentTarget z H K) ≠ 0

/-- A scale-fixed dual obstruction.  Normalizing the detected target to one
removes the irrelevant sign and magnitude ambiguity from the functional. -/
structure NormalizedFinkSupportTangentDualObstruction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) where
  functional : Module.Dual ℝ G.FinkSupportTangentEquationVector
  operator_eq_zero : ∀ A : G.State → Payoff ι,
    functional (G.finkSupportTangentOperator z A) = 0
  target_eq_one :
    functional (G.finkSupportTangentTarget z H K) = 1

/-- Embed one player's scalar state potential into the payoff-vector space. -/
noncomputable def finkPlayerPotential
    (G : StochasticGame ι) [DecidableEq ι]
    (who : ι) (w : G.State → ℝ) :
    G.State → Payoff ι :=
  fun s => Pi.single who (w s)

@[simp] theorem finkPlayerPotential_apply_self
    (G : StochasticGame ι) [DecidableEq ι]
    (who : ι) (w : G.State → ℝ) (s : G.State) :
    G.finkPlayerPotential who w s who = w s := by
  simp [finkPlayerPotential]

@[simp] theorem finkPlayerPotential_apply_of_ne
    (G : StochasticGame ι) [DecidableEq ι]
    (who other : ι) (w : G.State → ℝ) (s : G.State)
    (hother : other ≠ who) :
    G.finkPlayerPotential who w s other = 0 := by
  simp [finkPlayerPotential, hother]

/-- Unit vector in one residual-equation coordinate. -/
noncomputable def finkSupportResidualBasis
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s : G.State) (who : ι) :
    G.FinkSupportTangentEquationVector := by
  classical
  exact (Pi.single s (Pi.single who 1), 0)

/-- Unit vector in one supported-action equation coordinate. -/
noncomputable def finkSupportActionBasis
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s : G.State) (who : ι) (d : G.Act who) :
    G.FinkSupportTangentEquationVector := by
  classical
  exact (0, Pi.single s (Pi.single who (Pi.single d 1)))

/-- Every supported-tangent equation vector is the finite sum of its
residual and action coordinates against the corresponding unit vectors. -/
theorem finkSupportTangentEquationVector_eq_sum_basis
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (x : G.FinkSupportTangentEquationVector) :
    x =
      (∑ s, ∑ who, x.1 s who • G.finkSupportResidualBasis s who) +
      ∑ s, ∑ who, ∑ d,
        x.2 s who d • G.finkSupportActionBasis s who d := by
  classical
  apply Prod.ext
  · funext s who
    simp [finkSupportResidualBasis, finkSupportActionBasis, Prod.fst_sum,
      Pi.single_apply]
  · funext s who d
    suffices h :
        x.2 s who d =
          ∑ other, ∑ e,
            x.2 s other e *
              (Pi.single other (Pi.single e (1 : ℝ)) :
                (who : ι) → G.Act who → ℝ) who d by
      simpa [finkSupportResidualBasis, finkSupportActionBasis, Prod.snd_sum,
        Pi.single_apply] using h
    rw [Fintype.sum_eq_single who]
    · simp [Pi.single_apply]
    · intro other hother
      simp [hother]

/-- Coordinate expansion of a linear functional on the supported tangent
equation space. -/
theorem finkSupportTangentDual_apply_eq_sum
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (ℓ : Module.Dual ℝ G.FinkSupportTangentEquationVector)
    (x : G.FinkSupportTangentEquationVector) :
    ℓ x =
      (∑ s, ∑ who,
        x.1 s who * ℓ (G.finkSupportResidualBasis s who)) +
      ∑ s, ∑ who, ∑ d,
        x.2 s who d * ℓ (G.finkSupportActionBasis s who d) := by
  classical
  conv_lhs =>
    rw [G.finkSupportTangentEquationVector_eq_sum_basis x]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]

@[simp] theorem finkContinuationResidualVector_playerPotential_self
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (who : ι)
    (w : G.State → ℝ) (s : G.State) :
    G.finkContinuationResidualVector (G.finkPlayerPotential who w) z s who =
      expect (G.finkStateKernel z s) w - w s := by
  unfold finkContinuationResidualVector finkContinuationResidual
    finkContinuationEU
  rw [← G.expect_finkStateKernel_eq]
  simp

@[simp] theorem finkContinuationResidualVector_playerPotential_of_ne
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (who other : ι)
    (w : G.State → ℝ) (s : G.State) (hother : other ≠ who) :
    G.finkContinuationResidualVector (G.finkPlayerPotential who w)
      z s other = 0 := by
  unfold finkContinuationResidualVector finkContinuationResidual
    finkContinuationEU
  simp [hother]

@[simp] theorem finkContinuationGain_playerPotential_self
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (who : ι)
    (w : G.State → ℝ) (s : G.State) (d : G.Act who) :
    G.finkContinuationGain (G.finkPlayerPotential who w) z s who d =
      expect (G.finkPureDeviationStateKernel z s who d) w -
        expect (G.finkStateKernel z s) w := by
  rw [G.finkContinuationGain_eq_expect_stateKernels]
  simp

@[simp] theorem finkContinuationGain_playerPotential_of_ne
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (who other : ι)
    (w : G.State → ℝ) (s : G.State) (d : G.Act other)
    (hother : other ≠ who) :
    G.finkContinuationGain (G.finkPlayerPotential who w)
      z s other d = 0 := by
  rw [G.finkContinuationGain_eq_expect_stateKernels]
  simp [hother]

/-- A concrete signed flow certificate for tangent obstruction.

`residualWeight` prices the harmonicity equations and `actionWeight` prices
the supported-action equations.  `operator_balance` says the resulting
signed flow annihilates every potential adjustment; `target_balance`
normalizes the detected tangent imbalance to one. -/
structure NormalizedFinkSupportTangentObstructionFlow
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) where
  residualWeight : G.State → ι → ℝ
  actionWeight : G.State → ∀ who : ι, G.Act who → ℝ
  operator_balance : ∀ A : G.State → Payoff ι,
    (∑ s, ∑ who,
      residualWeight s who *
        G.finkContinuationResidualVector A z s who) +
      ∑ s, ∑ who, ∑ d,
        actionWeight s who d *
          (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain A z s who d else 0) = 0
  target_balance :
    ∑ s, ∑ who, ∑ d,
      actionWeight s who d *
        (if G.finkProfile z s who d ≠ 0 then
          G.finkStageGain z s who d +
            G.finkContinuationGain (H - K) z s who d else 0) = 1

/-- Playerwise weak conservation law carried by an obstruction flow.  For
every scalar state potential, the weighted baseline residuals and supported
pure-deviation kernel differences cancel. -/
theorem NormalizedFinkSupportTangentObstructionFlow.player_transition_balance
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (who : ι) (w : G.State → ℝ) :
    (∑ s, F.residualWeight s who *
      (expect (G.finkStateKernel z s) w - w s)) +
      ∑ s, ∑ d,
        F.actionWeight s who d *
          (if G.finkProfile z s who d ≠ 0 then
            expect (G.finkPureDeviationStateKernel z s who d) w -
              expect (G.finkStateKernel z s) w else 0) = 0 := by
  classical
  have h := F.operator_balance (G.finkPlayerPotential who w)
  have hres (s : G.State) :
      (∑ other, F.residualWeight s other *
        G.finkContinuationResidualVector
          (G.finkPlayerPotential who w) z s other) =
        F.residualWeight s who *
          G.finkContinuationResidualVector
            (G.finkPlayerPotential who w) z s who := by
    rw [Fintype.sum_eq_single who]
    intro other hother
    simp [hother]
  have hact (s : G.State) :
      (∑ other, ∑ d,
        F.actionWeight s other d *
          (if G.finkProfile z s other d ≠ 0 then
            G.finkContinuationGain
              (G.finkPlayerPotential who w) z s other d else 0)) =
        ∑ d, F.actionWeight s who d *
          (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain
              (G.finkPlayerPotential who w) z s who d else 0) := by
    rw [Fintype.sum_eq_single who]
    intro other hother
    simp [hother]
  simp_rw [hres, hact] at h
  simpa using h

/-- Coordinate form of the weak conservation law.  At every player and
destination state, the weighted baseline inflow-minus-source mass and the
supported pure-deviation transition differences cancel. -/
theorem
    NormalizedFinkSupportTangentObstructionFlow.player_state_transition_balance
    (G : StochasticGame ι)
    [Fintype G.State] [DecidableEq G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (who : ι) (t : G.State) :
    (∑ s, F.residualWeight s who *
      ((G.finkStateKernel z s t).toReal - if s = t then 1 else 0)) +
      ∑ s, ∑ d,
        F.actionWeight s who d *
          (if G.finkProfile z s who d ≠ 0 then
            (G.finkPureDeviationStateKernel z s who d t).toReal -
              (G.finkStateKernel z s t).toReal else 0) = 0 := by
  classical
  simpa [Math.Probability.expect_pi_single, Pi.single_apply] using
    NormalizedFinkSupportTangentObstructionFlow.player_transition_balance
      G z H K F who (Pi.single t 1)

/-- A normalized obstruction flow has a supported action at which its weight
and tangent target are positively aligned.  This is the sign information
forced by target normalization without any positivity assumption on the dual
functional itself. -/
theorem
    NormalizedFinkSupportTangentObstructionFlow.exists_positive_target_coordinate
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K) :
    ∃ s, ∃ who, ∃ d : G.Act who,
      G.finkProfile z s who d ≠ 0 ∧
        0 < F.actionWeight s who d *
          (G.finkStageGain z s who d +
            G.finkContinuationGain (H - K) z s who d) := by
  classical
  by_contra hpositive
  push Not at hpositive
  have hnonpos :
      (∑ s, ∑ who, ∑ d,
        F.actionWeight s who d *
          (if G.finkProfile z s who d ≠ 0 then
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d else 0)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro s hs
    apply Finset.sum_nonpos
    intro who hwho
    apply Finset.sum_nonpos
    intro d hd
    by_cases hsupp : G.finkProfile z s who d ≠ 0
    · simpa [hsupp] using hpositive s who d hsupp
    · simp [hsupp]
  have hpos :
      0 <
        ∑ s, ∑ who, ∑ d,
          F.actionWeight s who d *
            (if G.finkProfile z s who d ≠ 0 then
              G.finkStageGain z s who d +
                G.finkContinuationGain (H - K) z s who d else 0) := by
    rw [F.target_balance]
    norm_num
  exact (not_lt_of_ge hnonpos) hpos

namespace NormalizedFinkSupportTangentObstructionFlow

/-- Every normalized obstruction exposes one of two semantically distinct
response coordinates.  A transition-visible coordinate changes the
next-state kernel.  At a transition-invisible coordinate all continuation
gains vanish, so positive alignment is carried entirely by the stage gain and
must be handled by a payoff charge or punishment response. -/
theorem exists_positive_transition_coordinate_or_positive_stage_coordinate
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K) :
    (∃ s, ∃ who, ∃ d : G.Act who,
      G.finkProfile z s who d ≠ 0 ∧
        G.finkPureDeviationStateKernel z s who d ≠
          G.finkStateKernel z s ∧
        0 < F.actionWeight s who d *
          (G.finkStageGain z s who d +
            G.finkContinuationGain (H - K) z s who d)) ∨
      ∃ s, ∃ who, ∃ d : G.Act who,
        G.finkProfile z s who d ≠ 0 ∧
          G.finkPureDeviationStateKernel z s who d =
            G.finkStateKernel z s ∧
          0 < F.actionWeight s who d * G.finkStageGain z s who d := by
  obtain ⟨s, who, d, hsupp, hpositive⟩ :=
    F.exists_positive_target_coordinate
  by_cases hkernel :
      G.finkPureDeviationStateKernel z s who d = G.finkStateKernel z s
  · right
    refine ⟨s, who, d, hsupp, hkernel, ?_⟩
    have hzero :=
      G.finkContinuationGain_eq_zero_of_pureDeviationStateKernel_eq
        (H - K) z s who d hkernel
    rw [hzero, add_zero] at hpositive
    exact hpositive
  · left
    exact ⟨s, who, d, hsupp, hkernel, hpositive⟩

end NormalizedFinkSupportTangentObstructionFlow

/-- A normalized obstruction flow must charge at least one supported action
whose tangent target is nonzero.  Thus the coordinate certificate contains a
concrete location at which any obstruction response has to act. -/
theorem NormalizedFinkSupportTangentObstructionFlow.exists_active_target_coordinate
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K) :
    ∃ s, ∃ who, ∃ d : G.Act who,
      G.finkProfile z s who d ≠ 0 ∧
        F.actionWeight s who d ≠ 0 ∧
          G.finkStageGain z s who d +
            G.finkContinuationGain (H - K) z s who d ≠ 0 := by
  obtain ⟨s, who, d, hsupp, hpositive⟩ :=
    F.exists_positive_target_coordinate
  obtain ⟨hweight, htarget⟩ := mul_ne_zero_iff.mp (ne_of_gt hpositive)
  exact ⟨s, who, d, hsupp, hweight, htarget⟩

/-- Extract the explicit signed obstruction flow from a normalized dual
functional. -/
def NormalizedFinkSupportTangentDualObstruction.toObstructionFlow
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (O : G.NormalizedFinkSupportTangentDualObstruction z H K) :
    G.NormalizedFinkSupportTangentObstructionFlow z H K where
  residualWeight := fun s who =>
    O.functional (G.finkSupportResidualBasis s who)
  actionWeight := fun s who d =>
    O.functional (G.finkSupportActionBasis s who d)
  operator_balance := by
    intro A
    have h := G.finkSupportTangentDual_apply_eq_sum O.functional
      (G.finkSupportTangentOperator z A)
    rw [O.operator_eq_zero A] at h
    simpa [finkSupportTangentOperator, mul_comm] using h.symm
  target_balance := by
    have h := G.finkSupportTangentDual_apply_eq_sum O.functional
      (G.finkSupportTangentTarget z H K)
    rw [O.target_eq_one] at h
    simpa [finkSupportTangentTarget, mul_comm] using h.symm

/-- Forget the normalization while retaining the obstruction. -/
def NormalizedFinkSupportTangentDualObstruction.toDualObstruction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (O : G.NormalizedFinkSupportTangentDualObstruction z H K) :
    G.FinkSupportTangentDualObstruction z H K where
  functional := O.functional
  operator_eq_zero := O.operator_eq_zero
  target_ne_zero := by rw [O.target_eq_one]; norm_num

/-- Every nonzero dual obstruction has a canonical target-one scaling. -/
def FinkSupportTangentDualObstruction.normalize
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (O : G.FinkSupportTangentDualObstruction z H K) :
    G.NormalizedFinkSupportTangentDualObstruction z H K where
  functional :=
    (O.functional (G.finkSupportTangentTarget z H K))⁻¹ • O.functional
  operator_eq_zero := by
    intro A
    simp only [LinearMap.smul_apply, smul_eq_mul, O.operator_eq_zero, mul_zero]
  target_eq_one := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ O.target_ne_zero

/-- A dual obstruction rules out every supported harmonic adjustment. -/
theorem FinkSupportTangentDualObstruction.not_exists_harmonicAdjustment
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (O : G.FinkSupportTangentDualObstruction z H K) :
    ¬ ∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d := by
  rintro ⟨A, hA⟩
  have htarget :
      G.finkSupportTangentTarget z H K =
        G.finkSupportTangentOperator z A :=
    (G.finkSupportTangentOperator_eq_target_iff z H K A).2 hA |>.symm
  apply O.target_ne_zero
  rw [htarget]
  exact O.operator_eq_zero A

/-- Exact finite-dimensional branch point for the supported tangent system.
The obstruction branch carries data rather than only the negation of
feasibility. -/
theorem exists_harmonicAdjustment_or_dualObstruction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) :
    (∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d) ∨
      Nonempty (G.FinkSupportTangentDualObstruction z H K) := by
  classical
  by_cases hA : ∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d
  · exact Or.inl hA
  · right
    have hdual : ¬ ∀ ℓ : Module.Dual ℝ G.FinkSupportTangentEquationVector,
        (∀ A : G.State → Payoff ι,
          ℓ (G.finkSupportTangentOperator z A) = 0) →
        ℓ (G.finkSupportTangentTarget z H K) = 0 := by
      intro h
      exact hA ((G.exists_finkSupportHarmonicAdjustment_iff_forall_dual
        z H K).2 h)
    push Not at hdual
    obtain ⟨ℓ, hoperator, htarget⟩ := hdual
    exact ⟨{
      functional := ℓ
      operator_eq_zero := hoperator
      target_ne_zero := htarget
    }⟩

/-- Scale-fixed form of the tangent branch point.  This is the form intended
for quantitative obstruction responses. -/
theorem exists_harmonicAdjustment_or_normalizedDualObstruction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) :
    (∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d) ∨
      Nonempty
        (G.NormalizedFinkSupportTangentDualObstruction z H K) := by
  rcases G.exists_harmonicAdjustment_or_dualObstruction z H K with
    hA | hO
  · exact Or.inl hA
  · obtain ⟨O⟩ := hO
    exact Or.inr ⟨O.normalize⟩

/-- Coordinate form of the tangent branch point.  The infeasible branch
exposes finite signed residual and action weights, together with an active
supported target coordinate. -/
theorem exists_harmonicAdjustment_or_normalizedObstructionFlow
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) :
    (∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d) ∨
      Nonempty
        (G.NormalizedFinkSupportTangentObstructionFlow z H K) := by
  rcases G.exists_harmonicAdjustment_or_normalizedDualObstruction z H K with
    hA | hO
  · exact Or.inl hA
  · obtain ⟨O⟩ := hO
    exact Or.inr ⟨O.toObstructionFlow⟩

namespace FinkSelectionCounterexample
namespace Base

/-- The limiting Fink point from the tangent example, read in the
selection-resistant game.  The compact domain depends only on states and
actions, which are shared by the two games. -/
abbrev selectionLimitPoint : game.finkDomain 1 :=
  FinkTangentCounterexample.limitPoint

lemma selection_limit_live_playerOne_actionA_support :
    game.finkProfile selectionLimitPoint .live false false ≠ 0 := by
  change FinkTangentCounterexample.game.finkProfile
    FinkTangentCounterexample.limitPoint .live false false ≠ 0
  exact FinkTangentCounterexample.limit_live_playerOne_actionA_support

lemma selection_finkContinuationGain_limit_live_playerOne
    (A : CState → Payoff Player) (d : Bool) :
    game.finkContinuationGain A selectionLimitPoint .live false d = 0 := by
  change FinkTangentCounterexample.game.finkContinuationGain A
    FinkTangentCounterexample.limitPoint .live false d = 0
  exact FinkTangentCounterexample.finkContinuationGain_limit_live_playerOne A d

lemma selection_finkStageGain_limit_live_playerOne_actionA :
    game.finkStageGain selectionLimitPoint .live false false = -1 := by
  change FinkTangentCounterexample.game.finkStageGain
    FinkTangentCounterexample.limitPoint .live false false = -1
  exact FinkTangentCounterexample.finkStageGain_limit_live_playerOne_actionA

/-- Coordinate dual obstruction for the selection-resistant example. -/
def selectionTangentDualObstruction :
    game.FinkSupportTangentDualObstruction selectionLimitPoint
      (0 : CState → Payoff Player) 0 := by
  let ℓ := game.finkSupportActionCoordinateDual .live false false
  have h := game.finkSupportActionCoordinateDual_is_obstruction
    selectionLimitPoint (0 : CState → Payoff Player) 0 .live false false
    selection_limit_live_playerOne_actionA_support
    (fun A => selection_finkContinuationGain_limit_live_playerOne A false)
    (by
      rw [selection_finkStageGain_limit_live_playerOne_actionA]
      have hzero : game.finkContinuationGain
          ((0 : CState → Payoff Player) - 0) selectionLimitPoint
            .live false false = 0 := by
        simpa using selection_finkContinuationGain_limit_live_playerOne
          (0 : CState → Payoff Player) false
      rw [hzero]
      norm_num)
  exact {
    functional := ℓ
    operator_eq_zero := h.1
    target_ne_zero := h.2
  }

/-- Selection-resistant acceptance test for the obstruction branch.  The
same example forces the reciprocal-bias rare-action rate at every discounted
Bellman equilibrium and supplies a dual witness at its limiting tangent
system. -/
theorem selection_resistant_tangent_dualObstruction :
    Nonempty (game.FinkSupportTangentDualObstruction selectionLimitPoint
      (0 : CState → Payoff Player) 0) :=
  ⟨selectionTangentDualObstruction⟩

/-- Scale-fixed obstruction carried by the selection-resistant example. -/
theorem selection_resistant_tangent_normalizedDualObstruction :
    Nonempty
      (game.NormalizedFinkSupportTangentDualObstruction selectionLimitPoint
        (0 : CState → Payoff Player) 0) :=
  ⟨selectionTangentDualObstruction.normalize⟩

/-- Coordinate signed-flow form of the selection-resistant obstruction. -/
theorem selection_resistant_tangent_normalizedObstructionFlow :
    Nonempty
      (game.NormalizedFinkSupportTangentObstructionFlow selectionLimitPoint
        (0 : CState → Payoff Player) 0) :=
  ⟨selectionTangentDualObstruction.normalize.toObstructionFlow⟩

/-- The active selection-resistant target coordinate has value `-1`. -/
lemma selection_tangentTarget_live_playerOne_actionA :
    game.finkStageGain selectionLimitPoint .live false false +
      game.finkContinuationGain
        ((0 : CState → Payoff Player) - 0)
        selectionLimitPoint .live false false = -1 := by
  rw [selection_finkStageGain_limit_live_playerOne_actionA]
  have hzero : game.finkContinuationGain
      ((0 : CState → Payoff Player) - 0) selectionLimitPoint
        .live false false = 0 := by
    simpa using selection_finkContinuationGain_limit_live_playerOne
      (0 : CState → Payoff Player) false
  rw [hzero]
  norm_num

/-- At the active obstruction coordinate, the unilateral pure-deviation state
kernel is exactly the baseline state kernel.  The obstruction is therefore
payoff-facing rather than detectable from transition frequencies. -/
lemma selection_pureDeviationStateKernel_live_playerOne_actionA_eq :
    game.finkPureDeviationStateKernel
        selectionLimitPoint .live false false =
      game.finkStateKernel selectionLimitPoint .live := by
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro t
  have hgain := selection_finkContinuationGain_limit_live_playerOne
    (game.finkPlayerPotential false (Pi.single t 1)) false
  rw [game.finkContinuationGain_playerPotential_self] at hgain
  have hexpect :
      expect
          (game.finkPureDeviationStateKernel
            selectionLimitPoint .live false false)
          (Pi.single t 1) =
        expect (game.finkStateKernel selectionLimitPoint .live)
          (Pi.single t 1) :=
    sub_eq_zero.mp hgain
  simpa [Math.Probability.expect_pi_single] using hexpect

/-- Normalization reverses the coordinate witness in the
selection-resistant example: its active action weight is negative. -/
lemma selection_normalizedObstructionFlow_actionWeight_live_playerOne_actionA :
    selectionTangentDualObstruction.normalize.toObstructionFlow.actionWeight
      .live false false = -1 := by
  have htarget : selectionTangentDualObstruction.functional
      (game.finkSupportTangentTarget selectionLimitPoint
        (0 : CState → Payoff Player) 0) = -1 := by
    change game.finkSupportActionCoordinateDual .live false false
      (game.finkSupportTangentTarget selectionLimitPoint
        (0 : CState → Payoff Player) 0) = -1
    rw [game.finkSupportActionCoordinateDual_target]
    rw [if_pos selection_limit_live_playerOne_actionA_support]
    exact selection_tangentTarget_live_playerOne_actionA
  change (selectionTangentDualObstruction.functional
      (game.finkSupportTangentTarget selectionLimitPoint
        (0 : CState → Payoff Player) 0))⁻¹ *
      selectionTangentDualObstruction.functional
        (game.finkSupportActionBasis .live false false) = -1
  rw [htarget]
  norm_num
  simp [selectionTangentDualObstruction, finkSupportActionCoordinateDual,
    finkSupportActionBasis]

/-- Raw action weights of a normalized dual obstruction cannot in general be
read as nonnegative occupation masses. -/
theorem selection_normalizedObstructionFlow_not_actionWeight_nonneg :
    ¬ ∀ s who (d : game.Act who),
      0 ≤
        selectionTangentDualObstruction.normalize.toObstructionFlow.actionWeight
          s who d := by
  intro hnonneg
  have h := hnonneg .live false false
  rw [selection_normalizedObstructionFlow_actionWeight_live_playerOne_actionA]
    at h
  norm_num at h

/-- The same negative weight is positively aligned with its negative tangent
target, so the sign-compatible coordinate theorem is sharp on the
selection-resistant example. -/
theorem selection_normalizedObstructionFlow_positive_live_playerOne_actionA :
    game.finkProfile selectionLimitPoint .live false false ≠ 0 ∧
      0 <
        selectionTangentDualObstruction.normalize.toObstructionFlow.actionWeight
          .live false false *
          (game.finkStageGain selectionLimitPoint .live false false +
            game.finkContinuationGain
              ((0 : CState → Payoff Player) - 0)
              selectionLimitPoint .live false false) := by
  constructor
  · exact selection_limit_live_playerOne_actionA_support
  · rw [
      selection_normalizedObstructionFlow_actionWeight_live_playerOne_actionA,
      selection_tangentTarget_live_playerOne_actionA]
    norm_num

/-- The selection-resistant acceptance example realizes the
transition-invisible stage-payoff branch of the generic response dichotomy. -/
theorem selection_normalizedObstructionFlow_positive_stage_coordinate :
    game.finkProfile selectionLimitPoint .live false false ≠ 0 ∧
      game.finkPureDeviationStateKernel
          selectionLimitPoint .live false false =
        game.finkStateKernel selectionLimitPoint .live ∧
      0 <
        selectionTangentDualObstruction.normalize.toObstructionFlow.actionWeight
          .live false false *
          game.finkStageGain selectionLimitPoint .live false false := by
  refine ⟨selection_limit_live_playerOne_actionA_support,
    selection_pureDeviationStateKernel_live_playerOne_actionA_eq, ?_⟩
  rw [
    selection_normalizedObstructionFlow_actionWeight_live_playerOne_actionA,
    selection_finkStageGain_limit_live_playerOne_actionA]
  norm_num

/-- The selection-resistant flow necessarily identifies a supported action
with nonzero tangent target and nonzero obstruction weight. -/
theorem selection_resistant_tangent_active_target_coordinate :
    ∃ s, ∃ who, ∃ d : game.Act who,
      game.finkProfile selectionLimitPoint s who d ≠ 0 ∧
        selectionTangentDualObstruction.normalize.toObstructionFlow.actionWeight
          s who d ≠ 0 ∧
          game.finkStageGain selectionLimitPoint s who d +
            game.finkContinuationGain
              ((0 : CState → Payoff Player) - 0)
              selectionLimitPoint s who d ≠ 0 :=
  selectionTangentDualObstruction.normalize.toObstructionFlow
    |>.exists_active_target_coordinate

/-- The obstruction data rules out supported harmonic adjustment in the
selection-resistant game. -/
theorem no_selection_finkSupportHarmonicAdjustment :
    ¬ ∃ A : CState → Payoff Player,
      game.finkContinuationResidualVector A selectionLimitPoint = 0 ∧
        ∀ s who (d : Bool),
          game.finkProfile selectionLimitPoint s who d ≠ 0 →
            game.finkContinuationGain A selectionLimitPoint s who d =
              game.finkStageGain selectionLimitPoint s who d +
                game.finkContinuationGain
                  ((0 : CState → Payoff Player) - 0)
                    selectionLimitPoint s who d :=
  selectionTangentDualObstruction.not_exists_harmonicAdjustment

end Base
end FinkSelectionCounterexample

end StochasticGame
end GameTheory
