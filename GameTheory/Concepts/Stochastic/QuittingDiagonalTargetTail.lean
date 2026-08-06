/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingDiagonalTargetTailSelection
import GameTheory.Concepts.Stochastic.QuittingFiniteEndpointNashBellmanFactory

/-!
# Diagonal target-tail compiler

This module performs the game-facing assembly:

* a selected exceptional target and its closed suffix compile to a terminal
  `4 * M * δ`-Nash profile;
* small joint survival selects that target automatically;
* the arbitrary-endpoint Nash--Bellman factory supplies the exact prefix;
* stationary cap-attaining responses supply a concrete family of closed
  player-indexed suffixes; and
* terminal approximate equilibria at every accuracy yield a uniform-
  equilibrium payoff.

The final reductions assume only an accuracy-indexed small-joint-survival
certificate.  They make no compactness or boundary-continuity assertion over
varying stationary rows or anchors.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A selected exceptional target and its closed suffix compile the finite
prefix to a terminal `4*M*δ`-Nash profile. -/
theorem phaseSwitchProfile_isεAsymptoticNash_of_diagonalTarget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (tail : ι → ℕ → ι → PMF Bool)
    (target : ι) (switch : ℕ) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hendpoint : value switch = quittingDiagonalTailEndpoint reward tail)
    (hvalueBound : ∀ who, |value switch who| ≤ M)
    (hpolicy : ∀ time, time < switch →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (plan time))
    (hnash : ∀ time, time < switch →
      IsεQuittingRootNash reward (value (time + 1)) 0 (plan time))
    (hclosed : IsQuittingTargetClosedAt reward (tail target) target 0)
    (hother : ∀ who, who ≠ target →
      quittingOpponentSurvivalWeight plan who 0 switch ≤ δ) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (4 * M * δ)
      (quittingPhaseSwitchProfile reward plan (tail target) switch) := by
  intro who deviation
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingProfileLiveRoot_quittingPhaseSwitchProfile,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingProfileLiveRoot_quittingPhaseSwitchProfile]
  by_cases hwho : who = target
  · subst who
    have hmatch : value switch target =
        quittingRootSequenceTerminalValue reward (tail target) target 0 := by
      rw [hendpoint]
      rfl
    have hgap := quittingPhaseSwitchTargetHazardGap_le_zero
      reward plan (tail target) value target
        (quittingBehaviorLiveHazard reward deviation) switch
        hpolicy hnash hmatch hclosed
    have herror : 0 ≤ 4 * M * δ := by positivity
    linarith
  · have hgap :=
      quittingPhaseSwitchHazardGap_le_four_mul_opponentSurvival
        reward plan (tail target) value who
          (quittingBehaviorLiveHazard reward deviation) switch
          hM hreward (hvalueBound who) hpolicy hnash
    have hscaled := mul_le_mul_of_nonneg_left (hother who hwho)
      (by positivity : 0 ≤ 4 * M)
    nlinarith

/-- Small joint survival selects the exceptional target automatically. -/
theorem exists_phaseSwitchProfile_isεAsymptoticNash_of_diagonalJointSurvival
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (tail : ι → ℕ → ι → PMF Bool) (switch : ℕ) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hendpoint : value switch = quittingDiagonalTailEndpoint reward tail)
    (hvalueBound : ∀ who, |value switch who| ≤ M)
    (hpolicy : ∀ time, time < switch →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (plan time))
    (hnash : ∀ time, time < switch →
      IsεQuittingRootNash reward (value (time + 1)) 0 (plan time))
    (hclosed : ∀ target,
      IsQuittingTargetClosedAt reward (tail target) target 0)
    (hjoint : quittingJointSurvivalWeight plan 0 switch ≤ δ ^ 2) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (4 * M * δ) profile := by
  obtain ⟨target, hother⟩ :=
    exists_target_forall_opponentSurvivalWeight_le_of_joint_le_sq
      plan switch hδ hjoint
  exact ⟨quittingPhaseSwitchProfile reward plan (tail target) switch,
    phaseSwitchProfile_isεAsymptoticNash_of_diagonalTarget
      reward plan value tail target switch hM hδ hreward hendpoint
      hvalueBound hpolicy hnash (hclosed target) hother⟩

/-- The arbitrary-endpoint factory turns a small-joint-survival cutoff into a
terminal approximate Nash profile. -/
theorem exists_isεAsymptoticNash_of_finiteDiagonalEndpointFactory
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ι → ℕ → ι → PMF Bool) (cutoff : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hclosed : ∀ target,
      IsQuittingTargetClosedAt reward (tail target) target 0)
    (hjoint :
      quittingJointSurvivalWeight
          (quittingFiniteEndpointNashBellmanRoots reward
            (quittingDiagonalTailEndpoint reward tail)
            (abs_quittingDiagonalTailEndpoint_le reward tail) cutoff)
          0 cutoff ≤ δ ^ 2) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        (4 * quittingRewardBound reward * δ) profile := by
  let endpoint := quittingDiagonalTailEndpoint reward tail
  let hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward :=
    abs_quittingDiagonalTailEndpoint_le reward tail
  let plan := quittingFiniteEndpointNashBellmanRoots reward endpoint hendpoint cutoff
  let value := quittingFiniteEndpointNashBellmanValue reward endpoint hendpoint cutoff
  refine exists_phaseSwitchProfile_isεAsymptoticNash_of_diagonalJointSurvival
    reward plan value tail cutoff
      (quittingRewardBound_nonneg reward) hδ
      (abs_reward_le_quittingRewardBound reward) ?_ ?_ ?_ ?_ hclosed ?_
  · exact quittingFiniteEndpointNashBellmanValue_eq_endpoint_of_cutoff_le
      reward endpoint hendpoint cutoff cutoff le_rfl
  · intro who
    exact abs_quittingFiniteEndpointNashBellmanValue_le
      reward endpoint hendpoint cutoff cutoff who
  · exact quittingFiniteEndpointNashBellmanValue_eq_successor
      reward endpoint hendpoint cutoff
  · exact quittingFiniteEndpointNashBellmanRoots_isZeroNash
      reward endpoint hendpoint cutoff
  · exact hjoint

/-- Constant opponent rows instantiate the diagonal factory through actual
cap-attaining closed tails. -/
theorem exists_isεAsymptoticNash_of_stationaryCapDiagonalFactory
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (rows : ι → ι → PMF Bool) (cutoff : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hjoint :
      quittingJointSurvivalWeight
          (quittingFiniteEndpointNashBellmanRoots reward
            (quittingStationaryCapDiagonalEndpoint reward rows)
            (abs_quittingStationaryCapDiagonalEndpoint_le reward rows) cutoff)
          0 cutoff ≤ δ ^ 2) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        (4 * quittingRewardBound reward * δ) profile := by
  obtain ⟨tail, hclosed, htailValue⟩ :=
    exists_quittingTargetClosedTailFamily_of_stationaryRoots reward rows
  have hdiag :
      quittingDiagonalTailEndpoint reward tail =
        quittingStationaryCapDiagonalEndpoint reward rows := by
    funext target
    simpa only [quittingDiagonalTailEndpoint,
      quittingStationaryCapDiagonalEndpoint] using htailValue target
  let endpoint := quittingStationaryCapDiagonalEndpoint reward rows
  let endpointBound : ∀ who, |endpoint who| ≤ quittingRewardBound reward :=
    abs_quittingStationaryCapDiagonalEndpoint_le reward rows
  let plan :=
    quittingFiniteEndpointNashBellmanRoots reward endpoint endpointBound cutoff
  let value :=
    quittingFiniteEndpointNashBellmanValue reward endpoint endpointBound cutoff
  refine exists_phaseSwitchProfile_isεAsymptoticNash_of_diagonalJointSurvival
    reward plan value tail cutoff
      (quittingRewardBound_nonneg reward) hδ
      (abs_reward_le_quittingRewardBound reward) ?_ ?_ ?_ ?_ hclosed ?_
  · calc
      value cutoff = endpoint :=
        quittingFiniteEndpointNashBellmanValue_eq_endpoint_of_cutoff_le
          reward endpoint endpointBound cutoff cutoff le_rfl
      _ = quittingDiagonalTailEndpoint reward tail := hdiag.symm
  · intro who
    exact abs_quittingFiniteEndpointNashBellmanValue_le
      reward endpoint endpointBound cutoff cutoff who
  · exact quittingFiniteEndpointNashBellmanValue_eq_successor
      reward endpoint endpointBound cutoff
  · exact quittingFiniteEndpointNashBellmanRoots_isZeroNash
      reward endpoint endpointBound cutoff
  · simpa only [plan, endpoint, endpointBound] using hjoint

/-- **Stationary-cap one-scalar reduction.**  At each accuracy the rows and
endpoint may vary.  The only remaining producer is small joint survival for
the selected exact predecessor prefix of the diagonal cap endpoint. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_stationaryCapDiagonalJointSurvival
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcertificate : ∀ ε : ℝ, 0 < ε →
      ∃ (rows : ι → ι → PMF Bool) (cutoff : ℕ) (δ : ℝ),
        0 ≤ δ ∧
        4 * quittingRewardBound reward * δ ≤ ε ∧
        quittingJointSurvivalWeight
            (quittingFiniteEndpointNashBellmanRoots reward
              (quittingStationaryCapDiagonalEndpoint reward rows)
              (abs_quittingStationaryCapDiagonalEndpoint_le reward rows) cutoff)
            0 cutoff ≤ δ ^ 2) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
    reward
  intro ε hε
  obtain ⟨rows, cutoff, δ, hδ, hscale, hjoint⟩ :=
    hcertificate ε hε
  obtain ⟨profile, hprofile⟩ :=
    exists_isεAsymptoticNash_of_stationaryCapDiagonalFactory
      reward rows cutoff hδ hjoint
  exact ⟨profile, hprofile.mono hscale⟩

/-- **Accuracy-indexed diagonal certificate.**  The tail family and its
diagonal endpoint may vary with the requested accuracy.  This is the direct
semantic reduction: each certificate consists only of closed player-indexed
tails and one finite-factory joint-survival bound. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_diagonalTargetTailCertificates
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcertificate : ∀ ε : ℝ, 0 < ε →
      ∃ (tail : ι → ℕ → ι → PMF Bool) (cutoff : ℕ) (δ : ℝ),
        0 ≤ δ ∧
        4 * quittingRewardBound reward * δ ≤ ε ∧
        (∀ target,
          IsQuittingTargetClosedAt reward (tail target) target 0) ∧
        quittingJointSurvivalWeight
            (quittingFiniteEndpointNashBellmanRoots reward
              (quittingDiagonalTailEndpoint reward tail)
              (abs_quittingDiagonalTailEndpoint_le reward tail) cutoff)
            0 cutoff ≤ δ ^ 2) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
    reward
  intro ε hε
  obtain ⟨tail, cutoff, δ, hδ, hscale, hclosed, hjoint⟩ :=
    hcertificate ε hε
  obtain ⟨profile, hprofile⟩ :=
    exists_isεAsymptoticNash_of_finiteDiagonalEndpointFactory
      reward tail cutoff hδ hclosed hjoint
  exact ⟨profile, hprofile.mono hscale⟩

/-- **Final conditional uniform-payoff certificate.**  Closed player-indexed
tails plus arbitrarily small joint survival of the exact finite factory at
their diagonal endpoint imply a uniform-equilibrium payoff.  This isolates the
remaining producer as one scalar monotone quantity and uses no shared
punishment continuation. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_diagonalTargetTails
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ι → ℕ → ι → PMF Bool)
    (hclosed : ∀ target,
      IsQuittingTargetClosedAt reward (tail target) target 0)
    (hsmall : ∀ δ : ℝ, 0 < δ →
      ∃ cutoff : ℕ,
        quittingJointSurvivalWeight
            (quittingFiniteEndpointNashBellmanRoots reward
              (quittingDiagonalTailEndpoint reward tail)
              (abs_quittingDiagonalTailEndpoint_le reward tail) cutoff)
            0 cutoff ≤ δ ^ 2) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
    reward
  intro ε hε
  let M := quittingRewardBound reward
  let δ := ε / (4 * M + 1)
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hdenom : 0 < 4 * M + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hdenom
  obtain ⟨cutoff, hjoint⟩ := hsmall δ hδ
  obtain ⟨profile, hprofile⟩ :=
    exists_isεAsymptoticNash_of_finiteDiagonalEndpointFactory
      reward tail cutoff hδ.le hclosed hjoint
  have hscale : 4 * M * δ ≤ ε := by
  dsimp only [δ]
  have hratio : 4 * M / (4 * M + 1) ≤ 1 := by
    rw [div_le_iff₀ hdenom]
    linarith
  calc
    4 * M * (ε / (4 * M + 1)) =
        ε * (4 * M / (4 * M + 1)) := by ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio hε.le
    _ = ε := mul_one ε
  exact ⟨profile, hprofile.mono hscale⟩


end GameTheory
