/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Stationary.Payoff
import GameTheory.Concepts.Stochastic.Models.Quitting.SimpleBranches

/-!
# Finite successor certificates for quitting-game roots

This file exposes the exact finite relations consumed by a direct
path-or-barrier calculation.  For a product root action `root` and a tail
payoff `tail`, `quittingRootSuccessorPayoff reward tail root` is the current
payoff `F(root, tail)`.  For each player, the two endpoint values are the
payoffs from pure Quit and pure Continue against the opponents' fixed root
marginals.

The prescribed payoff is their Bernoulli mixture.  Consequently root Nash is
equivalent to two scalar endpoint inequalities per player, including an exact
approximate-`ε` version.  The successor update is also written as absorbed
reward minus absorption mass times the old tail payoff.

No absorption-path object, projective zero-hazard blow-up, compact closure, or
tangency relation is introduced here.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The current payoff vector obtained from one product root action followed
by the declared all-continue tail payoff. -/
def quittingRootSuccessorPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) : Payoff ι :=
  fun who => quittingRootExpectedPayoff reward tail root who

/-- Player `who`'s payoff from quitting purely at the root against the other
root marginals. -/
def quittingRootQuitPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootExpectedPayoff reward tail
    (Function.update root who (PMF.pure true)) who

/-- Player `who`'s payoff from continuing purely at the root against the
other root marginals and using `tail who` if everyone continues. -/
def quittingRootContinuePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootExpectedPayoff reward tail
    (Function.update root who (PMF.pure false)) who

/-- Pure Quit minus pure Continue at the root. -/
def quittingRootEndpointDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootQuitPayoff reward tail root who -
    quittingRootContinuePayoff reward tail root who

/-- One-stage absorption probability of the product root action. -/
def quittingRootAbsorptionMass (root : ι → PMF Bool) : ℝ :=
  1 - quittingStationaryContinueMass root

/-- The pure product root at which every player continues. -/
def quittingAllContinueRoot : ι → PMF Bool :=
  fun _ => PMF.pure false

omit [Fintype ι] [DecidableEq ι] in
/-- The two real masses of a Boolean marginal sum to one. -/
  theorem quittingRoot_continueProbability_add_quitProbability
    (root : ι → PMF Bool) (who : ι) :
    (root who false).toReal + (root who true).toReal = 1 := by
  simpa [Fintype.sum_bool, add_comm] using
    (pmf_toReal_sum_one (root who))

/-- Replacing one marginal by an arbitrary Boolean law mixes exactly the two
pure endpoint payoffs. -/
theorem quittingRootExpectedPayoff_update_eq_endpointMix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (who : ι) (marginal : PMF Bool) :
    quittingRootExpectedPayoff reward tail
        (Function.update root who marginal) who =
      (marginal true).toReal *
          quittingRootQuitPayoff reward tail root who +
        (marginal false).toReal *
          quittingRootContinuePayoff reward tail root who := by
  unfold quittingRootExpectedPayoff quittingRootQuitPayoff
    quittingRootContinuePayoff
  rw [pmfPi_update_bind, expect_bind, expect_eq_sum, Fintype.sum_bool]
  rfl

/-- The root successor payoff is the player's own Quit/Continue Bernoulli
mixture. -/
theorem quittingRootSuccessorPayoff_eq_endpointMix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward tail root who =
      (root who true).toReal *
          quittingRootQuitPayoff reward tail root who +
        (root who false).toReal *
          quittingRootContinuePayoff reward tail root who := by
  simpa [quittingRootSuccessorPayoff] using
    (quittingRootExpectedPayoff_update_eq_endpointMix
      reward tail root who (root who))

/-- The approximate endpoint inequalities: pure Quit has regret
`continueProbability * difference`, while pure Continue has regret
`-quitProbability * difference`. -/
def IsεQuittingRootEndpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (ε : ℝ) (root : ι → PMF Bool) : Prop :=
  ∀ who,
    (root who false).toReal *
        quittingRootEndpointDifference reward tail root who ≤ ε ∧
      -ε ≤ (root who true).toReal *
        quittingRootEndpointDifference reward tail root who

/-- Testing the two endpoint inequalities is equivalent to testing every
mixed unilateral root deviation. -/
theorem isεQuittingRootEndpointNash_iff_isεQuittingRootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (ε : ℝ) (root : ι → PMF Bool) :
    IsεQuittingRootEndpointNash reward tail ε root ↔
      IsεQuittingRootNash reward tail ε root := by
  constructor
  · intro hendpoint who deviation
    have hendpointWho := hendpoint who
    have hrootSum :=
      quittingRoot_continueProbability_add_quitProbability root who
    have hdeviationSum :
        (deviation false).toReal + (deviation true).toReal = 1 := by
      simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one deviation
    have hrootMix :=
      quittingRootSuccessorPayoff_eq_endpointMix reward tail root who
    have hcontinueProbability :
        (root who false).toReal = 1 - (root who true).toReal := by
      linarith
    have hquitRegret :
        quittingRootQuitPayoff reward tail root who -
            quittingRootSuccessorPayoff reward tail root who =
          (root who false).toReal *
            (quittingRootQuitPayoff reward tail root who -
              quittingRootContinuePayoff reward tail root who) := by
      rw [hrootMix, hcontinueProbability]
      nlinarith
    have hcontinueRegret :
        quittingRootContinuePayoff reward tail root who -
            quittingRootSuccessorPayoff reward tail root who =
          -(root who true).toReal *
            (quittingRootQuitPayoff reward tail root who -
              quittingRootContinuePayoff reward tail root who) := by
      rw [hrootMix, hcontinueProbability]
      nlinarith
    change
      (root who false).toReal *
            (quittingRootQuitPayoff reward tail root who -
              quittingRootContinuePayoff reward tail root who) ≤ ε ∧
        -ε ≤ (root who true).toReal *
            (quittingRootQuitPayoff reward tail root who -
              quittingRootContinuePayoff reward tail root who)
      at hendpointWho
    have hquit :
        quittingRootQuitPayoff reward tail root who ≤
          quittingRootSuccessorPayoff reward tail root who + ε := by
      linarith [hquitRegret, hendpointWho.1]
    have hcontinue :
        quittingRootContinuePayoff reward tail root who ≤
          quittingRootSuccessorPayoff reward tail root who + ε := by
      linarith [hcontinueRegret, hendpointWho.2]
    rw [quittingRootExpectedPayoff_update_eq_endpointMix]
    change _ ≤ quittingRootSuccessorPayoff reward tail root who + ε
    calc
      (deviation true).toReal *
            quittingRootQuitPayoff reward tail root who +
          (deviation false).toReal *
            quittingRootContinuePayoff reward tail root who ≤
        (deviation true).toReal *
            (quittingRootSuccessorPayoff reward tail root who + ε) +
          (deviation false).toReal *
            (quittingRootSuccessorPayoff reward tail root who + ε) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hquit ENNReal.toReal_nonneg)
          (mul_le_mul_of_nonneg_left hcontinue ENNReal.toReal_nonneg)
      _ = quittingRootSuccessorPayoff reward tail root who + ε := by
        have hsum :
            (deviation true).toReal + (deviation false).toReal = 1 := by
          linarith
        rw [← add_mul, hsum, one_mul]
  · intro hnash who
    have hquit := hnash who (PMF.pure true)
    have hcontinue := hnash who (PMF.pure false)
    have hrootSum :=
      quittingRoot_continueProbability_add_quitProbability root who
    have hrootMix :=
      quittingRootSuccessorPayoff_eq_endpointMix reward tail root who
    have hcontinueProbability :
        (root who false).toReal = 1 - (root who true).toReal := by
      linarith
    have hquitRegret :
        quittingRootQuitPayoff reward tail root who -
            quittingRootSuccessorPayoff reward tail root who =
          (root who false).toReal *
            (quittingRootQuitPayoff reward tail root who -
              quittingRootContinuePayoff reward tail root who) := by
      rw [hrootMix, hcontinueProbability]
      nlinarith
    have hcontinueRegret :
        quittingRootContinuePayoff reward tail root who -
            quittingRootSuccessorPayoff reward tail root who =
          -(root who true).toReal *
            (quittingRootQuitPayoff reward tail root who -
              quittingRootContinuePayoff reward tail root who) := by
      rw [hrootMix, hcontinueProbability]
      nlinarith
    change quittingRootQuitPayoff reward tail root who ≤
      quittingRootSuccessorPayoff reward tail root who + ε at hquit
    change quittingRootContinuePayoff reward tail root who ≤
      quittingRootSuccessorPayoff reward tail root who + ε at hcontinue
    dsimp only [IsεQuittingRootEndpointNash,
      quittingRootEndpointDifference]
    constructor
    · linarith [hquitRegret, hquit]
    · linarith [hcontinueRegret, hcontinue]

/-- Exact endpoint form of root Nash. -/
theorem isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) :
    IsεQuittingRootEndpointNash reward tail 0 root ↔
      IsεQuittingRootNash reward tail 0 root :=
  isεQuittingRootEndpointNash_iff_isεQuittingRootNash
    reward tail 0 root

/-- At a zero Quit-probability endpoint, exact endpoint Nash says Quit minus
Continue is nonpositive. -/
theorem quittingRootEndpointDifference_nonpos_of_quitProbability_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hzero : (root who true).toReal = 0) :
    quittingRootEndpointDifference reward tail root who ≤ 0 := by
  have hendpoint := (hnash who).1
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  nlinarith

/-- At an interior marginal, exact endpoint Nash makes the two pure endpoint
payoffs equal. -/
theorem quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hcontinue : 0 < (root who false).toReal)
    (hquit : 0 < (root who true).toReal) :
    quittingRootEndpointDifference reward tail root who = 0 := by
  have hendpoint := hnash who
  apply le_antisymm
  · exact nonpos_of_mul_nonpos_left
      (by simpa [mul_comm] using hendpoint.1) hcontinue
  · exact nonneg_of_mul_nonneg_left
      (by simpa [mul_comm] using hendpoint.2) hquit

/-- At a zero Continue-probability endpoint, exact endpoint Nash says Quit
minus Continue is nonnegative. -/
theorem quittingRootEndpointDifference_nonneg_of_continueProbability_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hzero : (root who false).toReal = 0) :
    0 ≤ quittingRootEndpointDifference reward tail root who := by
  have hendpoint := (hnash who).2
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  nlinarith

omit [DecidableEq ι] in
/-- The root successor increment is the one-stage absorbing contribution
minus the total absorption mass times the old tail payoff. -/
theorem quittingRootSuccessorPayoff_sub_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward tail root who - tail who =
      quittingRootAbsorbingContribution reward root who -
        quittingRootAbsorptionMass root * tail who := by
  rw [show quittingRootSuccessorPayoff reward tail root who =
      quittingRootExpectedPayoff reward tail root who by rfl,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  unfold quittingRootAbsorptionMass
  ring

omit [DecidableEq ι] in
/-- Equivalent expectation form of the successor update: all-continue has
zero increment, while every absorbing action contributes `reward - tail`. -/
theorem quittingRootSuccessorPayoff_sub_tail_eq_expect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward tail root who - tail who =
      expect (pmfPi root) (fun action =>
        if h : (quittingQuitters action).Nonempty then
          reward ⟨quittingQuitters action, h⟩ who - tail who
        else 0) := by
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  calc
    expect (pmfPi root)
          (fun action => quittingRootPayoff reward tail action who) -
        tail who =
      expect (pmfPi root) (fun action =>
        quittingRootPayoff reward tail action who - tail who) := by
          rw [expect_sub, expect_const]
    _ = _ := by
      apply congrArg (expect (pmfPi root))
      funext action
      by_cases hquit : (quittingQuitters action).Nonempty <;>
        simp [quittingRootPayoff, hquit]

/-- The all-continue root gives pure Continue value equal to the declared
tail payoff. -/
@[simp] theorem quittingRootContinuePayoff_allContinueRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (who : ι) :
    quittingRootContinuePayoff reward tail
        (quittingAllContinueRoot : ι → PMF Bool) who = tail who := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
    quittingAllContinueRoot
  rw [show Function.update (fun _ : ι => PMF.pure false) who
      (PMF.pure false) = (fun _ : ι => PMF.pure false) by simp,
    pmfPi_pure, expect_pure]
  simp [quittingRootPayoff]

/-- Against an all-continue root, quitting purely yields the singleton
terminal reward. -/
@[simp] theorem quittingRootQuitPayoff_allContinueRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (who : ι) :
    quittingRootQuitPayoff reward tail
        (quittingAllContinueRoot : ι → PMF Bool) who =
      reward (quittingSingletonTerminal who) who := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
    quittingAllContinueRoot
  let quitAction : ι → Bool :=
    Function.update (fun _ : ι => false) who true
  have hfamily :
      Function.update (fun _ : ι => PMF.pure false) who (PMF.pure true) =
        fun player => PMF.pure (quitAction player) := by
    funext player
    by_cases hp : player = who
    · subst player
      simp [quitAction]
    · simp [Function.update_of_ne hp, quitAction]
  rw [hfamily, pmfPi_pure, expect_pure]
  have hset : quittingQuitters quitAction = {who} := by
    ext player
    by_cases hp : player = who <;>
      simp [quittingQuitters, quitAction, hp]
  have hnonempty : (quittingQuitters quitAction).Nonempty := by
    rw [hset]
    exact Finset.singleton_nonempty who
  rw [show quittingRootPayoff reward tail quitAction who =
      reward ⟨quittingQuitters quitAction, hnonempty⟩ who by
        simp [quittingRootPayoff, hnonempty]]
  congr

/-- At the all-continue endpoint, Quit minus Continue is exactly singleton
quitting reward minus tail payoff. -/
@[simp] theorem quittingRootEndpointDifference_allContinueRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (who : ι) :
    quittingRootEndpointDifference reward tail
        (quittingAllContinueRoot : ι → PMF Bool) who =
      reward (quittingSingletonTerminal who) who - tail who := by
  simp [quittingRootEndpointDifference]

/-- A root successor certificate records the correctly oriented equation
`current = F(root, tail)` together with the endpoint inequalities. -/
def IsεQuittingRootSuccessorCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (ε : ℝ) (root : ι → PMF Bool)
    (current tail : Payoff ι) : Prop :=
  current = quittingRootSuccessorPayoff reward tail root ∧
    IsεQuittingRootEndpointNash reward tail ε root

/-- The finite successor certificate is exactly the successor equation plus
ordinary mixed root Nash. -/
theorem isεQuittingRootSuccessorCertificate_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (ε : ℝ) (root : ι → PMF Bool)
    (current tail : Payoff ι) :
    IsεQuittingRootSuccessorCertificate reward ε root current tail ↔
      current = quittingRootSuccessorPayoff reward tail root ∧
        IsεQuittingRootNash reward tail ε root := by
  rw [IsεQuittingRootSuccessorCertificate,
    isεQuittingRootEndpointNash_iff_isεQuittingRootNash]

end GameTheory
