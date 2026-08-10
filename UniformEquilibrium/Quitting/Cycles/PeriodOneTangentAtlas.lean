/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.MarkedAbsorptionCylinder
import UniformEquilibrium.Quitting.Cycles.PeriodicNormalizedSeam

/-!
# The period-one quitting tangent atlas

For one product root and one player, this file relates four exact masses:

* joint survival `C`;
* opponent-only survival `rho`;
* total absorption `A = 1 - C`;
* the player's singleton absorption mass `a`.

The division-free identities are `rho - C = a` and
`1 - rho = A - a`.  At positive absorption, if `mu = a / A`, these become
`rho - C = A * mu` and `1 - rho = A * (1 - mu)`.

Specializing the exact periodic evaluator to a repeated one-root word then
shows that the phase coefficient acts on the charge-normalized endpoint
tangent by `-C`, while the proper-mass refusal coefficient is the packet odds
`mu / (1 - mu)`.  The full-mass case `mu = 1` is kept separate: its opponent
survival is one, so the refusal normalization has zero denominator.

The odds coefficient matches the finite packet-defect algebra, but this file
makes no dynamic-tail occupation, provenance, packet-identification, or
one-stage realization claim.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Conditional singleton-owner share of a one-stage product root.  It is
totalized to zero when the root has zero absorption. -/
def quittingRootNormalizedSingletonMass
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootCoalitionMass root {who} /
    quittingRootAbsorptionMass root

/-- The singleton mass of `who` is its quit probability times the probability
that all its opponents continue. -/
theorem quittingRootCoalitionMass_singleton_eq_opponentContinue_mul_quit
    (root : ι → PMF Bool) (who : ι) :
    quittingRootCoalitionMass root {who} =
      quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) *
        (root who true).toReal := by
  have hcomplement : ({who} : Finset ι)ᶜ = Finset.univ.erase who := by
    ext player
    simp [and_comm]
  have hcontinue : ∀ player,
      1 - (root player true).toReal = (root player false).toReal := by
    intro player
    linarith [quittingRoot_continueProbability_add_quitProbability root player]
  have hforced :
      quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) =
        ∏ player ∈ Finset.univ.erase who,
          (root player false).toReal := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability,
      ← Finset.mul_prod_erase Finset.univ
        (fun player ↦
          (Function.update root who (PMF.pure false) player false).toReal)
        (Finset.mem_univ who)]
    have hpure : ((PMF.pure false) false).toReal = (1 : ℝ) := by simp
    rw [Function.update_self, hpure, one_mul]
    apply Finset.prod_congr rfl
    intro player hplayer
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hplayer)]
  unfold quittingRootCoalitionMass quittingRootQuitRates
    Math.PMFProduct.coalitionMass
  rw [hcomplement]
  simp only [Finset.prod_singleton, hcontinue, hforced]
  ring

/-! ## Division-free mass atlas -/

/-- The excess of opponent-only survival over joint survival is exactly the
mass of the event in which `who` is the unique quitter. -/
theorem quittingRootOpponentContinue_sub_continue_eq_singletonMass
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) -
        quittingStationaryContinueMass root =
      quittingRootCoalitionMass root {who} := by
  let rho := quittingStationaryContinueMass
    (Function.update root who (PMF.pure false))
  let ownContinue := (root who false).toReal
  let ownQuit := (root who true).toReal
  have hfactor : quittingStationaryContinueMass root = rho * ownContinue :=
    quittingStationaryContinueMass_eq_forcedContinue_mul_own root who
  have hprobability : ownContinue + ownQuit = 1 :=
    quittingRoot_continueProbability_add_quitProbability root who
  have hsingleton : quittingRootCoalitionMass root {who} = rho * ownQuit :=
    quittingRootCoalitionMass_singleton_eq_opponentContinue_mul_quit root who
  dsimp only [rho, ownContinue, ownQuit] at hfactor hprobability hsingleton ⊢
  rw [hfactor, hsingleton]
  calc
    quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) -
        quittingStationaryContinueMass
            (Function.update root who (PMF.pure false)) *
              (root who false).toReal =
        quittingStationaryContinueMass
            (Function.update root who (PMF.pure false)) *
              (1 - (root who false).toReal) := by ring
    _ = quittingStationaryContinueMass
            (Function.update root who (PMF.pure false)) *
          (root who true).toReal := by
      congr 1
      linarith

/-- Opponent absorption is total absorption with `who`'s singleton event
removed. -/
theorem one_sub_quittingRootOpponentContinue_eq_absorption_sub_singletonMass
    (root : ι → PMF Bool) (who : ι) :
    1 - quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) =
      quittingRootAbsorptionMass root -
        quittingRootCoalitionMass root {who} := by
  rw [quittingRootAbsorptionMass]
  have hsingleton :=
    quittingRootOpponentContinue_sub_continue_eq_singletonMass root who
  linarith

/-! ## Positive-absorption normalization -/

/-- On the positive-absorption branch, the singleton mass is total
absorption times its conditional owner share. -/
theorem quittingRootAbsorption_mul_normalizedSingletonMass
    (root : ι → PMF Bool) (who : ι)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    quittingRootAbsorptionMass root *
        quittingRootNormalizedSingletonMass root who =
      quittingRootCoalitionMass root {who} := by
  unfold quittingRootNormalizedSingletonMass
  exact mul_div_cancel₀ _ habsorption.ne'

/-- Normalized form of `rho - C = a`: the survival difference is total
absorption times the singleton-owner share. -/
theorem quittingRootOpponentContinue_sub_continue_eq_absorption_mul_share
    (root : ι → PMF Bool) (who : ι)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) -
        quittingStationaryContinueMass root =
      quittingRootAbsorptionMass root *
        quittingRootNormalizedSingletonMass root who := by
  rw [quittingRootOpponentContinue_sub_continue_eq_singletonMass,
    quittingRootAbsorption_mul_normalizedSingletonMass root who habsorption]

/-- Normalized form of `1 - rho = A - a`: the opponent absorption gap is
the non-owner share of total absorption. -/
theorem one_sub_quittingRootOpponentContinue_eq_absorption_mul_one_sub_share
    (root : ι → PMF Bool) (who : ι)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    1 - quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) =
      quittingRootAbsorptionMass root *
        (1 - quittingRootNormalizedSingletonMass root who) := by
  rw [one_sub_quittingRootOpponentContinue_eq_absorption_sub_singletonMass,
    ← quittingRootAbsorption_mul_normalizedSingletonMass root who habsorption]
  ring

/-- A normalized singleton-owner share is nonnegative. -/
theorem quittingRootNormalizedSingletonMass_nonneg
    (root : ι → PMF Bool) (who : ι) :
    0 ≤ quittingRootNormalizedSingletonMass root who := by
  exact div_nonneg
    (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {who})
    (by
      unfold quittingRootAbsorptionMass
      linarith [quittingStationaryContinueMass_le_one root])

/-- On the positive-absorption branch, a normalized singleton-owner share is
at most one. -/
theorem quittingRootNormalizedSingletonMass_le_one
    (root : ι → PMF Bool) (who : ι)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    quittingRootNormalizedSingletonMass root who ≤ 1 := by
  apply (div_le_one habsorption).2
  have hrho := quittingStationaryContinueMass_le_one
    (Function.update root who (PMF.pure false))
  have hsplit :=
    one_sub_quittingRootOpponentContinue_eq_absorption_sub_singletonMass
      root who
  linarith

/-! ## The full-mass boundary -/

/-- At positive total absorption, full singleton-owner mass is equivalent to
opponent-only survival one. -/
theorem quittingRootNormalizedSingletonMass_eq_one_iff_opponentContinue_eq_one
    (root : ι → PMF Bool) (who : ι)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    quittingRootNormalizedSingletonMass root who = 1 ↔
      quittingStationaryContinueMass
        (Function.update root who (PMF.pure false)) = 1 := by
  have hidentity :=
    one_sub_quittingRootOpponentContinue_eq_absorption_mul_one_sub_share
      root who habsorption
  constructor <;> intro h
  · rw [h] at hidentity
    linarith
  · rw [h] at hidentity
    have hzero : 1 - quittingRootNormalizedSingletonMass root who = 0 :=
      (mul_eq_zero.mp (by simpa using hidentity)).resolve_left
        habsorption.ne'
    linarith

/-- Full singleton-owner mass is precisely the isolated-player boundary:
every opponent continues surely. -/
theorem quittingRootOpponents_eq_pureContinue_of_normalizedSingletonMass_eq_one
    (root : ι → PMF Bool) (who : ι)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hfull : quittingRootNormalizedSingletonMass root who = 1) :
    ∀ other, other ≠ who → root other = PMF.pure false := by
  have hrho : quittingStationaryContinueMass
      (Function.update root who (PMF.pure false)) = 1 :=
    (quittingRootNormalizedSingletonMass_eq_one_iff_opponentContinue_eq_one
      root who habsorption).mp hfull
  intro other hother
  have hproduct : ∏ player : ι,
      ((Function.update root who (PMF.pure false)) player false).toReal = 1 := by
    rw [← quittingStationaryContinueMass_eq_prod_continueProbability]
    exact hrho
  have hfactor :
      ((Function.update root who (PMF.pure false)) other false).toReal = 1 :=
    eq_one_of_prod_eq_one_of_mem
      (fun _ _ ↦ ENNReal.toReal_nonneg)
      (fun player _ ↦ ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one
          (Function.update root who (PMF.pure false) player) false))
      hproduct (Finset.mem_univ other)
  rw [Function.update_of_ne hother] at hfactor
  exact eq_pure_false_of_continueProbability_eq_one hfactor

/-- Away from the full-mass boundary, opponent-only survival contracts. -/
theorem quittingRootOpponentContinue_lt_one_of_normalizedSingletonMass_lt_one
    (root : ι → PMF Bool) (who : ι)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hproper : quittingRootNormalizedSingletonMass root who < 1) :
    quittingStationaryContinueMass
        (Function.update root who (PMF.pure false)) < 1 := by
  have hidentity :=
    one_sub_quittingRootOpponentContinue_eq_absorption_mul_one_sub_share
      root who habsorption
  have hpositive : 0 < quittingRootAbsorptionMass root *
      (1 - quittingRootNormalizedSingletonMass root who) :=
    mul_pos habsorption (sub_pos.mpr hproper)
  linarith

/-! ## One-period survival clocks -/

/-- The stationary sequence obtained by repeating one product root. -/
def quittingPeriodOneRootSequence
    (root : ι → PMF Bool) : ℕ → ι → PMF Bool :=
  fun _ ↦ root

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingPeriodOneRootSequence_apply
    (root : ι → PMF Bool) (time : ℕ) :
    quittingPeriodOneRootSequence root time = root := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Repetition of one root is literally one-periodic. -/
theorem quittingPeriodOneRootSequence_periodic
    (root : ι → PMF Bool) (time : ℕ) :
    quittingPeriodOneRootSequence root (time + 1) =
      quittingPeriodOneRootSequence root time := rfl

omit [DecidableEq ι] in
/-- Joint survival through the one-root period is its stationary Continue
mass. -/
@[simp] theorem quittingJointSurvivalWeight_periodOne
    (root : ι → PMF Bool) :
    quittingJointSurvivalWeight (quittingPeriodOneRootSequence root) 0 1 =
      quittingStationaryContinueMass root := by
  rw [quittingJointSurvivalWeight_eq_prod]
  simp

/-- Opponent-only survival through the one-root period is the stationary
Continue mass after forcing the displayed player to Continue. -/
@[simp] theorem quittingOpponentSurvivalWeight_periodOne
    (root : ι → PMF Bool) (who : ι) :
    quittingOpponentSurvivalWeight
        (quittingPeriodOneRootSequence root) who 0 1 =
      quittingStationaryContinueMass
        (Function.update root who (PMF.pure false)) := by
  simp [quittingOpponentSurvivalWeight,
    quittingFixedOpponentsContinueMass]

/-! ## Exact slack-retaining tangent evaluator -/

/-- **Period-one phase atlas.**  For a positive-absorption root, the exact
phase seam is `-C` times the charge-normalized endpoint tangent, minus the
displayed finite phase slack.

The endpoint tangent is written using the existing exact semantic quantity
`restartDelivery - terminal`; no realization or limiting identification is
introduced. -/
theorem quittingPeriodOneBestPhaseStop_sub_restartDelivery_eq_tangent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward
      (quittingPeriodOneRootSequence root) who prescribed)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    quittingPeriodicWindowBestPhaseStop reward
          (quittingPeriodOneRootSequence root) who 1 -
        quittingWindowRestartDelivery reward
          (quittingPeriodOneRootSequence root) who 0 1 =
      -quittingStationaryContinueMass root *
          (quittingWindowRestartDelivery reward
              (quittingPeriodOneRootSequence root) who 0 1 -
            prescribed 1) -
        quittingPeriodicWindowPhaseSlack reward
          (quittingPeriodOneRootSequence root) who 1 (prescribed 0) := by
  let roots := quittingPeriodOneRootSequence root
  let C := quittingStationaryContinueMass root
  let A := quittingRootAbsorptionMass root
  let tangent := quittingWindowRestartDelivery reward roots who 0 1 -
    prescribed 1
  let drift := prescribed 0 - prescribed 1
  have hjoint : quittingJointSurvivalWeight roots 0 1 < 1 := by
    rw [show quittingJointSurvivalWeight roots 0 1 = C by simp [roots, C]]
    dsimp only [A, quittingRootAbsorptionMass] at habsorption
    dsimp only [C]
    linarith
  have hphase :=
    quittingPeriodicWindowBestPhaseStop_sub_restartDelivery_eq_normalizedSeam
      reward roots who prescribed hprescribed 1 hjoint
  have htangent :=
    quittingWindowAbsorption_mul_restartDelivery_sub_terminal
      reward roots who prescribed hprescribed 0 1 hjoint
  have hA : A = 1 - C := rfl
  have hAne : A ≠ 0 := habsorption.ne'
  have htangent' : A * tangent = drift := by
    simpa [roots, C, A, tangent, drift, quittingRootAbsorptionMass]
      using htangent
  have hcoefficient :
      -(C / (1 - C)) * drift = -C * tangent := by
    rw [← htangent', ← hA]
    field_simp [hAne]
  simpa [roots, C, tangent, drift, hcoefficient] using hphase

/-- **Period-one refusal atlas, proper-mass branch.**  When the singleton
share `mu` is strictly below one, the exact refusal seam is the packet-odds
coefficient `mu / (1 - mu)` times the same charge-normalized endpoint tangent,
minus the refusal slack divided by `A * (1 - mu)`.

The strict `mu < 1` premise is essential: it is exactly the positive
opponent-absorption denominator required by the existing periodic evaluator. -/
theorem quittingPeriodOneRefusalValue_sub_restartDelivery_eq_tangent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward
      (quittingPeriodOneRootSequence root) who prescribed)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hproper : quittingRootNormalizedSingletonMass root who < 1) :
    quittingPeriodicWindowRefusalValue reward
          (quittingPeriodOneRootSequence root) who -
        quittingWindowRestartDelivery reward
          (quittingPeriodOneRootSequence root) who 0 1 =
      (quittingRootNormalizedSingletonMass root who /
          (1 - quittingRootNormalizedSingletonMass root who)) *
          (quittingWindowRestartDelivery reward
              (quittingPeriodOneRootSequence root) who 0 1 -
            prescribed 1) -
        quittingPeriodicWindowRefusalSlack reward
            (quittingPeriodOneRootSequence root) who 1
              (prescribed 0) (prescribed 1) /
          (quittingRootAbsorptionMass root *
            (1 - quittingRootNormalizedSingletonMass root who)) := by
  let roots := quittingPeriodOneRootSequence root
  let C := quittingStationaryContinueMass root
  let rho := quittingStationaryContinueMass
    (Function.update root who (PMF.pure false))
  let A := quittingRootAbsorptionMass root
  let mu := quittingRootNormalizedSingletonMass root who
  let tangent := quittingWindowRestartDelivery reward roots who 0 1 -
    prescribed 1
  let drift := prescribed 0 - prescribed 1
  have hjoint : quittingJointSurvivalWeight roots 0 1 < 1 := by
    rw [show quittingJointSurvivalWeight roots 0 1 = C by simp [roots, C]]
    dsimp only [A, quittingRootAbsorptionMass] at habsorption
    dsimp only [C]
    linarith
  have hopponent : quittingOpponentSurvivalWeight roots who 0 1 < 1 := by
    rw [show quittingOpponentSurvivalWeight roots who 0 1 = rho by
      simp [roots, rho]]
    exact quittingRootOpponentContinue_lt_one_of_normalizedSingletonMass_lt_one
      root who habsorption hproper
  have hrefusal :=
    quittingPeriodicWindowRefusalValue_sub_restartDelivery_eq_normalizedSeam
      reward roots who prescribed hprescribed 1
        (quittingPeriodOneRootSequence_periodic root) hjoint hopponent
  have htangent :=
    quittingWindowAbsorption_mul_restartDelivery_sub_terminal
      reward roots who prescribed hprescribed 0 1 hjoint
  have hA : A = 1 - C := rfl
  have hAne : A ≠ 0 := habsorption.ne'
  have hmuNe : 1 - mu ≠ 0 := sub_ne_zero.mpr (ne_of_gt hproper)
  have htangent' : A * tangent = drift := by
    simpa [roots, C, A, tangent, drift, quittingRootAbsorptionMass]
      using htangent
  have hrhoC : rho - C = A * mu := by
    exact quittingRootOpponentContinue_sub_continue_eq_absorption_mul_share
      root who habsorption
  have hrhoGap : 1 - rho = A * (1 - mu) := by
    exact
      one_sub_quittingRootOpponentContinue_eq_absorption_mul_one_sub_share
        root who habsorption
  have hcoefficient :
      ((rho - C) / ((1 - rho) * (1 - C))) * drift =
        (mu / (1 - mu)) * tangent := by
    rw [hrhoC, hrhoGap, ← hA, ← htangent']
    field_simp [hAne, hmuNe]
  dsimp only [roots] at hrefusal
  simp only [quittingJointSurvivalWeight_periodOne,
    quittingOpponentSurvivalWeight_periodOne] at hrefusal
  change quittingPeriodicWindowRefusalValue reward roots who -
      quittingWindowRestartDelivery reward roots who 0 1 =
    ((rho - C) / ((1 - rho) * (1 - C))) * drift -
      quittingPeriodicWindowRefusalSlack reward roots who 1
          (prescribed 0) (prescribed 1) / (1 - rho) at hrefusal
  rw [hcoefficient, hrhoGap] at hrefusal
  exact hrefusal

/-- **Period-one refusal atlas, full-mass branch.**  Full singleton-owner
share forces opponent-only survival one, a zero refusal denominator, and a
literally isolated root at that player.  Consequently the normalized refusal
identity above is intentionally not asserted on this branch. -/
theorem quittingPeriodOne_fullSingletonMass_boundary
    (root : ι → PMF Bool) (who : ι)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hfull : quittingRootNormalizedSingletonMass root who = 1) :
    quittingOpponentSurvivalWeight
          (quittingPeriodOneRootSequence root) who 0 1 = 1 ∧
      1 - quittingOpponentSurvivalWeight
          (quittingPeriodOneRootSequence root) who 0 1 = 0 ∧
      ∀ other, other ≠ who → root other = PMF.pure false := by
  have hrho :=
    (quittingRootNormalizedSingletonMass_eq_one_iff_opponentContinue_eq_one
      root who habsorption).mp hfull
  refine ⟨?_, ?_,
    quittingRootOpponents_eq_pureContinue_of_normalizedSingletonMass_eq_one
      root who habsorption hfull⟩
  · simpa using hrho
  · simp [hrho]

end GameTheory
