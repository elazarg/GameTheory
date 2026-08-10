/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.EndpointBackwardStability
import UniformEquilibrium.Quitting.Cycles.ExactCycleStrata

/-!
# Global exactification of a cyclic quitting policy

An own-set reward shift `d i` adds `d i` to player `i`'s payoff whenever
`i` quits.  At one root with a fixed continuation this translates `i`'s
Quit-minus-Continue gap by exactly `d i`.  On a cycle the continuation is not
fixed: the common reward-table perturbation changes every phase value, and
those corrections feed around the cycle.

For a fixed cycle, let `a t i` be the change in player `i`'s phase value.  The
exact global equations are

```
a t i = q t * a (t+1) i + p t i * d i,
g' t i = g t i + d i - c t i * a (t+1) i,
```

where `q t` is joint all-Continue mass, `p t i` is `i`'s Quit probability,
and `c t i` is deleted opponent Continue mass.  The policy recurrence and the
root complementarity signs form a finite fixed-support linear feasibility
system.  The main iff theorem says that this system is neither a relaxation
nor a proxy: it is exactly global cyclic policy evaluation and exact endpoint
Nash for the shifted table.

For an absorbing cycle, the feedback recurrence is contractive around one
turn.  The final section supplies its canonical multiplier, proves uniqueness,
and eliminates every correction variable as `a t i = α t i * d i`.  Thus
own-set exactification separates player by player.  This is a finite
exactification interface; it does not assert that the system is feasible or
that own-set shifts exhaust general reward-table perturbations.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## One-stage identities with continuation feedback -/

/-- Changing the tail by `correction` translates the endpoint gap by minus
the deleted opponent-survival mass times the selected correction coordinate. -/
theorem quittingRootEndpointDifference_tail_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail correction : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootEndpointDifference reward
        (fun i ↦ tail i + correction i) root who =
      quittingRootEndpointDifference reward tail root who -
        quittingStationaryFixedOpponentsContinueMass root who * correction who := by
  have hquit := quittingRootSuccessorPayoff_sub_eq_continueMass_mul reward
    (fun i ↦ tail i + correction i) tail
    (Function.update root who (PMF.pure true)) who
  have hcontinue := quittingRootSuccessorPayoff_sub_eq_continueMass_mul reward
    (fun i ↦ tail i + correction i) tail
    (Function.update root who (PMF.pure false)) who
  change quittingRootQuitPayoff reward (fun i ↦ tail i + correction i) root who -
      quittingRootQuitPayoff reward tail root who = _ at hquit
  change quittingRootContinuePayoff reward (fun i ↦ tail i + correction i) root who -
      quittingRootContinuePayoff reward tail root who = _ at hcontinue
  rw [quittingStationaryContinueMass_update_pure_true_eq_zero] at hquit
  change quittingRootContinuePayoff reward
      (fun i ↦ tail i + correction i) root who -
        quittingRootContinuePayoff reward tail root who =
      quittingStationaryFixedOpponentsContinueMass root who *
        ((tail who + correction who) - tail who) at hcontinue
  unfold quittingRootEndpointDifference
  rw [show (tail who + correction who) - tail who = correction who by ring] at hcontinue
  linarith

/-- Under one common own-set table shift and a moving continuation, the
fixed-tail gap translation acquires the exact deleted-survival feedback term. -/
theorem quittingRootEndpointDifference_ownShiftReward_tail_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail correction : Payoff ι) (root : ι → PMF Bool)
    (d : ι → ℝ) (who : ι) :
    quittingRootEndpointDifference (ownShiftReward reward d)
        (fun i ↦ tail i + correction i) root who =
      quittingRootEndpointDifference reward tail root who + d who -
        quittingStationaryFixedOpponentsContinueMass root who * correction who := by
  rw [quittingRootEndpointDifference_tail_add,
    quittingRootEndpointDifference_ownShiftReward]

/-- At a fixed root, changing the common table and the tail changes the
prescribed successor coordinate by exactly the own quitting contribution plus
the joint-survival continuation correction. -/
theorem quittingRootSuccessorPayoff_ownShiftReward_tail_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail correction : Payoff ι) (root : ι → PMF Bool)
    (d : ι → ℝ) (who : ι) :
    quittingRootSuccessorPayoff (ownShiftReward reward d)
        (fun i ↦ tail i + correction i) root who =
      quittingRootSuccessorPayoff reward tail root who +
        (root who true).toReal * d who +
        quittingStationaryContinueMass root * correction who := by
  have htail := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    (ownShiftReward reward d) (fun i ↦ tail i + correction i) tail root who
  have hshift :
      quittingRootSuccessorPayoff (ownShiftReward reward d) tail root who =
        quittingRootSuccessorPayoff reward tail root who +
          (root who true).toReal * d who := by
    rw [quittingRootSuccessorPayoff_eq_endpointMix,
      quittingRootSuccessorPayoff_eq_endpointMix,
      quittingRootQuitPayoff_ownShiftReward,
      quittingRootContinuePayoff_ownShiftReward]
    ring
  rw [show (tail who + correction who) - tail who = correction who by ring] at htail
  linarith [hshift]

/-! ## The exact finite global system -/

/-- The affine value-feedback recurrence induced by an own-set table shift. -/
def SatisfiesOwnShiftFeedbackRecurrence
    (cycle : Fin K → ι → PMF Bool) (d : ι → ℝ)
    (correction : Fin K → Payoff ι) : Prop :=
  ∀ phase who,
    correction phase who =
      quittingStationaryContinueMass (cycle phase) *
          correction (finRotate K phase) who +
        ((cycle phase who) true).toReal * d who

/-- Exact cyclic policy recursion for the shifted table and corrected values. -/
def IsOwnShiftPolicyCorrection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (correction : Fin K → Payoff ι) : Prop :=
  ∀ phase,
    (fun who ↦ value phase who + correction phase who) =
      quittingRootSuccessorPayoff (ownShiftReward reward d)
        (fun who ↦ value (finRotate K phase) who +
          correction (finRotate K phase) who)
        (cycle phase)

/-- Policy-feedback consistency is exactly the finite cyclic affine
recurrence. -/
theorem isOwnShiftPolicyCorrection_iff_feedbackRecurrence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (correction : Fin K → Payoff ι)
    (hpolicy : ∀ phase, value phase = quittingRootSuccessorPayoff reward
      (value (finRotate K phase)) (cycle phase)) :
    IsOwnShiftPolicyCorrection reward cycle value d correction ↔
      SatisfiesOwnShiftFeedbackRecurrence cycle d correction := by
  constructor
  · intro h phase who
    have hnew := congrFun (h phase) who
    have hold := congrFun (hpolicy phase) who
    rw [quittingRootSuccessorPayoff_ownShiftReward_tail_add] at hnew
    linarith
  · intro h phase
    funext who
    have hold := congrFun (hpolicy phase) who
    rw [quittingRootSuccessorPayoff_ownShiftReward_tail_add]
    rw [h phase who, hold]
    ring

/-- The corrected endpoint gap, written entirely in the finite feedback
variables. -/
def ownShiftCorrectedGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (correction : Fin K → Payoff ι)
    (phase : Fin K) (who : ι) : ℝ :=
  quittingRootEndpointDifference reward (value (finRotate K phase))
      (cycle phase) who + d who -
    quittingStationaryFixedOpponentsContinueMass (cycle phase) who *
      correction (finRotate K phase) who

theorem ownShiftCorrectedGap_eq_endpointDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (correction : Fin K → Payoff ι)
    (phase : Fin K) (who : ι) :
    ownShiftCorrectedGap reward cycle value d correction phase who =
      quittingRootEndpointDifference (ownShiftReward reward d)
        (fun i ↦ value (finRotate K phase) i +
          correction (finRotate K phase) i)
        (cycle phase) who := by
  rw [quittingRootEndpointDifference_ownShiftReward_tail_add]
  rfl

/-- The complete finite feasibility predicate for globally exactifying one
supplied root/value cycle by a common own-set perturbation.  At a mixed
coordinate the two inequalities force equality; at a pure coordinate they
give the correct one-sided endpoint condition. -/
def OwnShiftExactificationSystem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (correction : Fin K → Payoff ι) : Prop :=
  SatisfiesOwnShiftFeedbackRecurrence cycle d correction ∧
    ∀ phase who,
      (cycle phase who false).toReal *
          ownShiftCorrectedGap reward cycle value d correction phase who ≤ 0 ∧
        0 ≤ (cycle phase who true).toReal *
          ownShiftCorrectedGap reward cycle value d correction phase who

/-- The finite recurrence and sign system is necessary and sufficient for
global cyclic policy evaluation and exact endpoint Nash under the own-set
shift. -/
theorem ownShiftExactificationSystem_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (correction : Fin K → Payoff ι)
    (hpolicy : ∀ phase, value phase = quittingRootSuccessorPayoff reward
      (value (finRotate K phase)) (cycle phase)) :
    OwnShiftExactificationSystem reward cycle value d correction ↔
      IsOwnShiftPolicyCorrection reward cycle value d correction ∧
        ∀ phase, IsεQuittingRootEndpointNash (ownShiftReward reward d)
          (fun who ↦ value (finRotate K phase) who +
            correction (finRotate K phase) who)
          0 (cycle phase) := by
  rw [isOwnShiftPolicyCorrection_iff_feedbackRecurrence
    reward cycle value d correction hpolicy]
  constructor
  · rintro ⟨hfeedback, hnash⟩
    refine ⟨hfeedback, fun phase who ↦ ?_⟩
    rw [← ownShiftCorrectedGap_eq_endpointDifference
      reward cycle value d correction phase who]
    simpa using hnash phase who
  · rintro ⟨hfeedback, hnash⟩
    refine ⟨hfeedback, fun phase who ↦ ?_⟩
    have h := hnash phase who
    rw [← ownShiftCorrectedGap_eq_endpointDifference
      reward cycle value d correction phase who] at h
    simpa using h

/-! ## Canonical feedback and correction elimination on absorbing cycles -/

/-- The actual change in the cyclic terminal value produced by an own-set
shift.  It supplies a canonical solution of the finite feedback recurrence. -/
def canonicalOwnShiftCycleCorrection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (d : ι → ℝ)
    (phase : Fin K) (who : ι) : ℝ :=
  quittingCyclicTerminalValue (ownShiftReward reward d) cycle phase who -
    quittingCyclicTerminalValue reward cycle phase who

/-- The canonical terminal-value correction satisfies the global feedback
recurrence for every cycle; absorption is not needed for existence. -/
theorem canonicalOwnShiftCycleCorrection_satisfiesFeedbackRecurrence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (d : ι → ℝ) :
    SatisfiesOwnShiftFeedbackRecurrence cycle d
      (canonicalOwnShiftCycleCorrection reward cycle d) := by
  intro phase who
  have hshift := congrFun
    (quittingCyclicTerminalValue_eq_rootSuccessorPayoff
      (ownShiftReward reward d) cycle phase) who
  have hbase := congrFun
    (quittingCyclicTerminalValue_eq_rootSuccessorPayoff reward cycle phase) who
  have htail :
      (fun i ↦ quittingCyclicTerminalValue reward cycle (finRotate K phase) i +
        canonicalOwnShiftCycleCorrection reward cycle d
          (finRotate K phase) i) =
        quittingCyclicTerminalValue (ownShiftReward reward d) cycle
          (finRotate K phase) := by
    funext i
    simp only [canonicalOwnShiftCycleCorrection]
    ring
  have hchange := quittingRootSuccessorPayoff_ownShiftReward_tail_add
    reward (quittingCyclicTerminalValue reward cycle (finRotate K phase))
      (canonicalOwnShiftCycleCorrection reward cycle d (finRotate K phase))
      (cycle phase) d who
  rw [htail] at hchange
  simp only [canonicalOwnShiftCycleCorrection]
  simp only [canonicalOwnShiftCycleCorrection] at hchange
  rw [hshift, hbase]
  linarith

omit [DecidableEq ι] in
/-- Around a jointly absorbing cycle, the feedback recurrence has at most one
solution for a fixed shift. -/
theorem eq_of_satisfiesOwnShiftFeedbackRecurrence_of_absorbing
    (cycle : Fin K → ι → PMF Bool) (d : ι → ℝ)
    (first second : Fin K → Payoff ι)
    (habsorb : (∏ phase : Fin K,
      quittingStationaryContinueMass (cycle phase)) < 1)
    (hfirst : SatisfiesOwnShiftFeedbackRecurrence cycle d first)
    (hsecond : SatisfiesOwnShiftFeedbackRecurrence cycle d second) :
    first = second := by
  funext phase who
  let coefficient : Fin K → ℝ := fun t ↦
    quittingStationaryContinueMass (cycle t)
  let error : Fin K → ℝ := fun t ↦ first t who - second t who
  have hcoefficient : ∀ t, 0 ≤ coefficient t := fun t ↦
    quittingStationaryContinueMass_nonneg (cycle t)
  have hstep : ∀ t,
      |error t| ≤ 0 + coefficient t * |error (finRotate K t)| := by
    intro t
    have h₁ := hfirst t who
    have h₂ := hsecond t who
    have heq : error t = coefficient t * error (finRotate K t) := by
      dsimp only [error, coefficient]
      linarith
    rw [heq, abs_mul, abs_of_nonneg (hcoefficient t), zero_add]
  have hbound := abs_cyclicValue_le_residualCharge_div_one_sub_prod
    coefficient (fun _ ↦ 0) error hcoefficient habsorb hstep phase
  have habs : |error phase| = 0 := by
    apply le_antisymm
    · simpa [quittingCyclicResidualCharge] using hbound
    · exact abs_nonneg _
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

/-- On an absorbing cycle, every feedback solution is the canonical change in
the actual cyclic terminal value. -/
theorem eq_canonicalOwnShiftCycleCorrection_of_feedback_of_absorbing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (d : ι → ℝ)
    (correction : Fin K → Payoff ι)
    (habsorb : (∏ phase : Fin K,
      quittingStationaryContinueMass (cycle phase)) < 1)
    (hcorrection : SatisfiesOwnShiftFeedbackRecurrence cycle d correction) :
    correction = canonicalOwnShiftCycleCorrection reward cycle d :=
  eq_of_satisfiesOwnShiftFeedbackRecurrence_of_absorbing cycle d
    correction (canonicalOwnShiftCycleCorrection reward cycle d) habsorb
      hcorrection
      (canonicalOwnShiftCycleCorrection_satisfiesFeedbackRecurrence reward cycle d)

/-- The unit own-set response multiplier.  On an absorbing cycle this is the
fraction of a unit own-set shift transmitted to the selected phase value. -/
def ownShiftCycleFeedbackMultiplier
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) : ℝ :=
  canonicalOwnShiftCycleCorrection (fun _ _ ↦ 0) cycle (fun _ ↦ 1) phase who

/-- The unit response multiplier satisfies its scalar cyclic recurrence. -/
theorem ownShiftCycleFeedbackMultiplier_eq
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) :
    ownShiftCycleFeedbackMultiplier cycle phase who =
      quittingStationaryContinueMass (cycle phase) *
          ownShiftCycleFeedbackMultiplier cycle (finRotate K phase) who +
        ((cycle phase who) true).toReal := by
  have h := canonicalOwnShiftCycleCorrection_satisfiesFeedbackRecurrence
    (fun _ _ ↦ 0) cycle (fun _ ↦ 1) phase who
  simpa [ownShiftCycleFeedbackMultiplier] using h

/-- The multiplier scaled by `d who` is itself a solution of the full
feedback recurrence for shift `d`. -/
theorem multiplier_mul_satisfiesOwnShiftFeedbackRecurrence
    (cycle : Fin K → ι → PMF Bool) (d : ι → ℝ) :
    SatisfiesOwnShiftFeedbackRecurrence cycle d
      (fun phase who ↦
        ownShiftCycleFeedbackMultiplier cycle phase who * d who) := by
  intro phase who
  change ownShiftCycleFeedbackMultiplier cycle phase who * d who =
    quittingStationaryContinueMass (cycle phase) *
        (ownShiftCycleFeedbackMultiplier cycle (finRotate K phase) who * d who) +
      ((cycle phase who) true).toReal * d who
  rw [ownShiftCycleFeedbackMultiplier_eq]
  ring

/-- **Correction elimination.**  On an absorbing cycle every global feedback
correction is coordinatewise the unit multiplier times the corresponding
own-set shift. -/
theorem correction_eq_multiplier_mul_of_feedback_of_absorbing
    (cycle : Fin K → ι → PMF Bool) (d : ι → ℝ)
    (correction : Fin K → Payoff ι)
    (habsorb : (∏ phase : Fin K,
      quittingStationaryContinueMass (cycle phase)) < 1)
    (hcorrection : SatisfiesOwnShiftFeedbackRecurrence cycle d correction) :
    correction = fun phase who ↦
      ownShiftCycleFeedbackMultiplier cycle phase who * d who :=
  eq_of_satisfiesOwnShiftFeedbackRecurrence_of_absorbing cycle d correction _
    habsorb hcorrection
      (multiplier_mul_satisfiesOwnShiftFeedbackRecurrence cycle d)

/-- The actual cyclic terminal-value response to an own-set shift is the
reward-independent multiplier of the fixed root cycle times that shift. -/
theorem canonicalOwnShiftCycleCorrection_eq_multiplier_mul_of_absorbing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (d : ι → ℝ)
    (habsorb : (∏ phase : Fin K,
      quittingStationaryContinueMass (cycle phase)) < 1) :
    canonicalOwnShiftCycleCorrection reward cycle d = fun phase who ↦
      ownShiftCycleFeedbackMultiplier cycle phase who * d who :=
  correction_eq_multiplier_mul_of_feedback_of_absorbing cycle d _ habsorb
    (canonicalOwnShiftCycleCorrection_satisfiesFeedbackRecurrence reward cycle d)

/-- The unit feedback multiplier is nonnegative on an absorbing cycle. -/
theorem ownShiftCycleFeedbackMultiplier_nonneg_of_absorbing
    (cycle : Fin K → ι → PMF Bool)
    (habsorb : (∏ phase : Fin K,
      quittingStationaryContinueMass (cycle phase)) < 1)
    (phase : Fin K) (who : ι) :
    0 ≤ ownShiftCycleFeedbackMultiplier cycle phase who := by
  let coefficient : Fin K → ℝ := fun t ↦
    quittingStationaryContinueMass (cycle t)
  let value : Fin K → ℝ := fun t ↦
    -ownShiftCycleFeedbackMultiplier cycle t who
  have hcoefficient : ∀ t, 0 ≤ coefficient t := fun t ↦
    quittingStationaryContinueMass_nonneg (cycle t)
  have hstep : ∀ t,
      value t ≤ 0 + coefficient t * value (finRotate K t) := by
    intro t
    have hmult := ownShiftCycleFeedbackMultiplier_eq cycle t who
    have hp : 0 ≤ ((cycle t who) true).toReal := ENNReal.toReal_nonneg
    dsimp only [value, coefficient]
    linarith
  have hbound := cyclicValue_le_residualCharge_div_one_sub_prod
    coefficient (fun _ ↦ 0) value hcoefficient habsorb hstep phase
  have hnonpos : value phase ≤ 0 := by
    simpa [quittingCyclicResidualCharge] using hbound
  dsimp only [value] at hnonpos
  linarith

/-- The unit feedback multiplier is at most one on an absorbing cycle. -/
theorem ownShiftCycleFeedbackMultiplier_le_one_of_absorbing
    (cycle : Fin K → ι → PMF Bool)
    (habsorb : (∏ phase : Fin K,
      quittingStationaryContinueMass (cycle phase)) < 1)
    (phase : Fin K) (who : ι) :
    ownShiftCycleFeedbackMultiplier cycle phase who ≤ 1 := by
  let coefficient : Fin K → ℝ := fun t ↦
    quittingStationaryContinueMass (cycle t)
  let value : Fin K → ℝ := fun t ↦
    ownShiftCycleFeedbackMultiplier cycle t who - 1
  have hcoefficient : ∀ t, 0 ≤ coefficient t := fun t ↦
    quittingStationaryContinueMass_nonneg (cycle t)
  have hstep : ∀ t,
      value t ≤ 0 + coefficient t * value (finRotate K t) := by
    intro t
    have hmult := ownShiftCycleFeedbackMultiplier_eq cycle t who
    have hcontinue :=
      quittingStationaryContinueMass_le_ownContinueProbability (cycle t) who
    have hsum := quittingRoot_continueProbability_add_quitProbability
      (cycle t) who
    dsimp only [value, coefficient]
    nlinarith
  have hbound := cyclicValue_le_residualCharge_div_one_sub_prod
    coefficient (fun _ ↦ 0) value hcoefficient habsorb hstep phase
  have hnonpos : value phase ≤ 0 := by
    simpa [quittingCyclicResidualCharge] using hbound
  exact sub_nonpos.mp hnonpos

/-- The scalar by which an own-set shift changes one phase endpoint gap after
the cyclic value has been recomputed. -/
def ownShiftCycleGapSlope
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) : ℝ :=
  1 - quittingStationaryFixedOpponentsContinueMass (cycle phase) who *
    ownShiftCycleFeedbackMultiplier cycle (finRotate K phase) who

/-- The complement of the current terminal-membership response is the
current own Continue mass times the gap slope after forcing that action.
This is the exact algebraic link between the cycle sensitivity singularity
and the full-owner singularity in normalized packet formulas. -/
theorem one_sub_ownShiftCycleFeedbackMultiplier_eq_continue_mul_gapSlope
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) :
    1 - ownShiftCycleFeedbackMultiplier cycle phase who =
      ((cycle phase who) false).toReal *
        ownShiftCycleGapSlope cycle phase who := by
  have hmass :=
    quittingStationaryContinueMass_eq_forcedContinue_mul_own
      (cycle phase) who
  change quittingStationaryContinueMass (cycle phase) =
    quittingStationaryFixedOpponentsContinueMass (cycle phase) who *
      ((cycle phase who) false).toReal at hmass
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (cycle phase) who
  rw [ownShiftCycleFeedbackMultiplier_eq, hmass]
  unfold ownShiftCycleGapSlope
  calc
    1 -
        (quittingStationaryFixedOpponentsContinueMass (cycle phase) who *
            ((cycle phase who) false).toReal *
              ownShiftCycleFeedbackMultiplier cycle
                (finRotate K phase) who +
          ((cycle phase who) true).toReal) =
      (((cycle phase who) false).toReal +
          ((cycle phase who) true).toReal) -
        (quittingStationaryFixedOpponentsContinueMass (cycle phase) who *
            ((cycle phase who) false).toReal *
              ownShiftCycleFeedbackMultiplier cycle
                (finRotate K phase) who +
          ((cycle phase who) true).toReal) := by rw [hsum]
    _ = ((cycle phase who) false).toReal *
        (1 - quittingStationaryFixedOpponentsContinueMass
          (cycle phase) who *
            ownShiftCycleFeedbackMultiplier cycle
              (finRotate K phase) who) := by ring

/-- On an absorbing cycle the recomputed gap slope is a probability-scale
coefficient in `[0,1]`. -/
theorem ownShiftCycleGapSlope_mem_unitInterval_of_absorbing
    (cycle : Fin K → ι → PMF Bool)
    (habsorb : (∏ phase : Fin K,
      quittingStationaryContinueMass (cycle phase)) < 1)
    (phase : Fin K) (who : ι) :
    ownShiftCycleGapSlope cycle phase who ∈ Set.Icc (0 : ℝ) 1 := by
  have hc0 : 0 ≤ quittingStationaryFixedOpponentsContinueMass
      (cycle phase) who := by
    exact quittingStationaryContinueMass_nonneg
      (Function.update (cycle phase) who (PMF.pure false))
  have hc1 : quittingStationaryFixedOpponentsContinueMass
      (cycle phase) who ≤ 1 := by
    exact quittingStationaryContinueMass_le_one
      (Function.update (cycle phase) who (PMF.pure false))
  have ha0 := ownShiftCycleFeedbackMultiplier_nonneg_of_absorbing
    cycle habsorb (finRotate K phase) who
  have ha1 := ownShiftCycleFeedbackMultiplier_le_one_of_absorbing
    cycle habsorb (finRotate K phase) who
  constructor <;> simp only [ownShiftCycleGapSlope] <;> nlinarith

/-- Endpoint gap after eliminating the cyclic correction variables. -/
def ownShiftReducedGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (phase : Fin K) (who : ι) : ℝ :=
  quittingRootEndpointDifference reward (value (finRotate K phase))
      (cycle phase) who +
    ownShiftCycleGapSlope cycle phase who * d who

/-- Once feedback is imposed on an absorbing cycle, the corrected gap is the
reduced one-scalar affine gap. -/
theorem ownShiftCorrectedGap_eq_reducedGap_of_feedback_of_absorbing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (correction : Fin K → Payoff ι)
    (habsorb : (∏ phase : Fin K,
      quittingStationaryContinueMass (cycle phase)) < 1)
    (hcorrection : SatisfiesOwnShiftFeedbackRecurrence cycle d correction)
    (phase : Fin K) (who : ι) :
    ownShiftCorrectedGap reward cycle value d correction phase who =
      ownShiftReducedGap reward cycle value d phase who := by
  rw [correction_eq_multiplier_mul_of_feedback_of_absorbing
    cycle d correction habsorb hcorrection]
  simp only [ownShiftCorrectedGap, ownShiftReducedGap, ownShiftCycleGapSlope]
  ring

/-- Playerwise sign feasibility after the cyclic correction variables have
been eliminated. -/
def OwnShiftReducedExactificationSystem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) : Prop :=
  ∀ phase who,
    (cycle phase who false).toReal *
        ownShiftReducedGap reward cycle value d phase who ≤ 0 ∧
      0 ≤ (cycle phase who true).toReal *
        ownShiftReducedGap reward cycle value d phase who

/-- The reduced affine gap for one player and one scalar own-set shift. -/
def ownShiftScalarGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (who : ι) (shift : ℝ) (phase : Fin K) : ℝ :=
  quittingRootEndpointDifference reward (value (finRotate K phase))
      (cycle phase) who +
    ownShiftCycleGapSlope cycle phase who * shift

/-- Feasibility of every phase sign for one player under one scalar shift. -/
def IsOwnShiftScalarExactificationAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (who : ι) (shift : ℝ) : Prop :=
  ∀ phase,
    (cycle phase who false).toReal *
        ownShiftScalarGap reward cycle value who shift phase ≤ 0 ∧
      0 ≤ (cycle phase who true).toReal *
        ownShiftScalarGap reward cycle value who shift phase

/-- The reduced global system is exactly the conjunction of the scalar
phase systems at the chosen player shifts. -/
theorem ownShiftReducedExactificationSystem_iff_scalar
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) :
    OwnShiftReducedExactificationSystem reward cycle value d ↔
      ∀ who, IsOwnShiftScalarExactificationAt reward cycle value who (d who) := by
  constructor
  · intro h who phase
    simpa [ownShiftReducedGap, ownShiftScalarGap] using h phase who
  · intro h phase who
    simpa [ownShiftReducedGap, ownShiftScalarGap] using h who phase

/-- Feasibility of the reduced system decomposes completely player by player:
one may select each scalar shift independently. -/
theorem exists_ownShiftReducedExactificationSystem_iff_forall_exists_scalar
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι) :
    (∃ d : ι → ℝ, OwnShiftReducedExactificationSystem reward cycle value d) ↔
      ∀ who, ∃ shift : ℝ,
        IsOwnShiftScalarExactificationAt reward cycle value who shift := by
  constructor
  · rintro ⟨d, hd⟩ who
    exact ⟨d who,
      (ownShiftReducedExactificationSystem_iff_scalar reward cycle value d).mp hd who⟩
  · intro h
    choose d hd using h
    exact ⟨d,
      (ownShiftReducedExactificationSystem_iff_scalar reward cycle value d).mpr hd⟩

/-- **Finite playerwise reduction.**  On an absorbing cycle, existence of any
global own-shift exactification correction is equivalent to the reduced sign
system in the `|ι|` shift variables alone. -/
theorem exists_ownShiftExactificationSystem_iff_reduced_of_absorbing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ)
    (habsorb : (∏ phase : Fin K,
      quittingStationaryContinueMass (cycle phase)) < 1) :
    (∃ correction : Fin K → Payoff ι,
      OwnShiftExactificationSystem reward cycle value d correction) ↔
      OwnShiftReducedExactificationSystem reward cycle value d := by
  constructor
  · rintro ⟨correction, hfeedback, hsign⟩ phase who
    rw [← ownShiftCorrectedGap_eq_reducedGap_of_feedback_of_absorbing
      reward cycle value d correction habsorb hfeedback phase who]
    exact hsign phase who
  · intro hsign
    let correction : Fin K → Payoff ι := fun phase who ↦
      ownShiftCycleFeedbackMultiplier cycle phase who * d who
    have hfeedback : SatisfiesOwnShiftFeedbackRecurrence cycle d correction :=
      multiplier_mul_satisfiesOwnShiftFeedbackRecurrence cycle d
    refine ⟨correction, hfeedback, fun phase who ↦ ?_⟩
    rw [ownShiftCorrectedGap_eq_reducedGap_of_feedback_of_absorbing
      reward cycle value d correction habsorb hfeedback phase who]
    exact hsign phase who

/-- The reduced fixed-root sign system together with punishment admissibility
for the shifted table.  This is the complete own-set slice of the solved-cycle
stratum. -/
def OwnShiftSolvedCycleExactificationSystem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) : Prop :=
  OwnShiftReducedExactificationSystem reward cycle value d ∧
    IsQuittingCyclePunishmentAdmissible (ownShiftReward reward d) cycle

/-- **Exact solved-stratum characterization in the own-set slice.**  For an
absorbing root cycle whose displayed values evaluate the original policy, the
reduced playerwise system plus shifted punishment admissibility is equivalent
to existence of corrected phase values making the same roots a solved exact
cycle for the shifted reward table. -/
theorem ownShiftSolvedCycleExactificationSystem_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ)
    (hpolicy : ∀ phase, value phase = quittingRootSuccessorPayoff reward
      (value (finRotate K phase)) (cycle phase))
    (habsorb : (∏ phase : Fin K,
      quittingStationaryContinueMass (cycle phase)) < 1) :
    OwnShiftSolvedCycleExactificationSystem reward cycle value d ↔
      ∃ shiftedValue : Fin K → Payoff ι,
        IsSolvedExactQuittingCycle (ownShiftReward reward d) cycle shiftedValue := by
  constructor
  · rintro ⟨hreduced, hadmissible⟩
    obtain ⟨correction, hsystem⟩ :=
      (exists_ownShiftExactificationSystem_iff_reduced_of_absorbing
        reward cycle value d habsorb).mpr hreduced
    have hglobal :=
      (ownShiftExactificationSystem_iff
        reward cycle value d correction hpolicy).mp hsystem
    let shiftedValue : Fin K → Payoff ι := fun phase who ↦
      value phase who + correction phase who
    refine ⟨shiftedValue, ⟨?_, ?_⟩, habsorb, hadmissible⟩
    · intro phase
      simpa [shiftedValue, IsOwnShiftPolicyCorrection] using hglobal.1 phase
    · intro phase
      apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        (ownShiftReward reward d) (shiftedValue (finRotate K phase))
          (cycle phase)).mp
      simpa [shiftedValue] using hglobal.2 phase
  · rintro ⟨shiftedValue, hsolved⟩
    let correction : Fin K → Payoff ι := fun phase who ↦
      shiftedValue phase who - value phase who
    have hpolicyCorrection :
        IsOwnShiftPolicyCorrection reward cycle value d correction := by
      intro phase
      simpa [correction] using hsolved.1.1 phase
    have hendpoint : ∀ phase,
        IsεQuittingRootEndpointNash (ownShiftReward reward d)
          (fun who ↦ value (finRotate K phase) who +
            correction (finRotate K phase) who)
          0 (cycle phase) := by
      intro phase
      apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        (ownShiftReward reward d)
          (fun who ↦ value (finRotate K phase) who +
            correction (finRotate K phase) who)
          (cycle phase)).mpr
      simpa [correction] using hsolved.1.2 phase
    have hsystem :
        OwnShiftExactificationSystem reward cycle value d correction :=
      (ownShiftExactificationSystem_iff
        reward cycle value d correction hpolicy).mpr
          ⟨hpolicyCorrection, hendpoint⟩
    exact ⟨
      (exists_ownShiftExactificationSystem_iff_reduced_of_absorbing
        reward cycle value d habsorb).mp ⟨correction, hsystem⟩,
      hsolved.2.2⟩

end GameTheory
