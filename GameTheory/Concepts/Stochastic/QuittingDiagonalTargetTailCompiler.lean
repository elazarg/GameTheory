/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingDiagonalTargetTailSplice
import GameTheory.Concepts.Stochastic.QuittingExceptionalHazard
import GameTheory.Concepts.Stochastic.QuittingInfinitePathCompiler
import GameTheory.Concepts.Stochastic.QuittingTerminalUniformPayoffSelection

/-!
# Exceptional-target diagonal tail compiler

Small joint prefix survival leaves at most one large opponent-survival clock.
Selecting that player as the target and appending its closed tail yields a
`4 * M * δ` terminal approximate equilibrium.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Exceptional-target selection -/

/-- The live mass of a root-sequence profile is exactly the joint survival
product of its prescribed roots. -/
theorem quittingLiveMass_infinitePathProfile_eq_jointSurvivalWeight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) :
    ∀ fuel,
      quittingLiveMass reward (quittingInfinitePathProfile reward roots) fuel =
        quittingJointSurvivalWeight roots 0 fuel := by
  intro fuel
  induction fuel with
  | zero => simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  | succ fuel ih =>
      rw [quittingLiveMass_succ, quittingJointSurvivalWeight_succ, ih]
      congr 1
      unfold quittingJointContinueMass StochasticGame.stageActionDist
        quittingInfinitePathProfile quittingRootSequenceProfile
      rw [pmfPi_apply]

/-- Two distinct deleted survival clocks cannot both exceed the square root
scale of joint survival. -/
theorem quittingOpponentSurvivalWeight_mul_le_jointSurvivalWeight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {first second : ι}
    (hne : first ≠ second) (cutoff : ℕ) :
    quittingOpponentSurvivalWeight roots first 0 cutoff *
        quittingOpponentSurvivalWeight roots second 0 cutoff ≤
      quittingJointSurvivalWeight roots 0 cutoff := by
  let profile := quittingInfinitePathProfile reward roots
  have hmass := quittingOpponentLiveMass_mul_le_liveMass
    reward profile hne cutoff
  have hfirst :
      quittingOpponentSurvivalWeight roots first 0 cutoff =
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile first) cutoff := by
    rw [← quittingProfileLiveRoot_infinitePathProfile reward roots]
    exact quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
      reward profile first cutoff
  have hsecond :
      quittingOpponentSurvivalWeight roots second 0 cutoff =
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile second) cutoff := by
    rw [← quittingProfileLiveRoot_infinitePathProfile reward roots]
    exact quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
      reward profile second cutoff
  have hjoint :
      quittingJointSurvivalWeight roots 0 cutoff =
        quittingLiveMass reward profile cutoff := by
    exact (quittingLiveMass_infinitePathProfile_eq_jointSurvivalWeight
      reward roots cutoff).symm
  rw [hfirst, hsecond, hjoint]
  exact hmass

/-- If joint survival is at most `δ²`, at most one player has deleted survival
strictly above `δ`; selecting that possible exception leaves every other
clock bounded by `δ`. -/
theorem exists_quittingExceptionalTarget_of_jointSurvivalWeight_le_sq
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hjoint : quittingJointSurvivalWeight roots 0 cutoff ≤ δ ^ 2) :
    ∃ target : ι, ∀ who, who ≠ target →
      quittingOpponentSurvivalWeight roots who 0 cutoff ≤ δ := by
  classical
  by_cases hexception : ∃ target : ι,
      δ < quittingOpponentSurvivalWeight roots target 0 cutoff
  · obtain ⟨target, htarget⟩ := hexception
    refine ⟨target, ?_⟩
    intro who hwho
    by_contra hnot
    have hwhoLarge :
        δ < quittingOpponentSurvivalWeight roots who 0 cutoff :=
      lt_of_not_ge hnot
    have hproduct :=
      quittingOpponentSurvivalWeight_mul_le_jointSurvivalWeight
        reward roots (Ne.symm hwho) cutoff
    nlinarith
  · let target : ι := Classical.choice (inferInstance : Nonempty ι)
    refine ⟨target, ?_⟩
    intro who _
    exact le_of_not_gt (fun hlarge => hexception ⟨who, hlarge⟩)

/-! ## Behavior-profile compiler and uniform-payoff bridge -/

/-- **Finite exceptional-target compiler.**  Player-indexed tails only need to
be closed in their own coordinate.  The declared endpoint is diagonal across
those tails.  Small joint prefix survival selects a target after the prefix;
the target has zero gain and every other player has gain at most `4*M*δ`. -/
theorem exists_target_quittingPrefixThenTail_isεAsymptoticNash
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (headRoots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (tails : ι → ℕ → ι → PMF Bool) (cutoff : ℕ)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hendpoint : ∀ player,
      value cutoff player =
        quittingRootSequenceTerminalValue reward (tails player) player 0)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (headRoots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (headRoots time))
    (hclosed : ∀ player,
      IsQuittingTargetClosedAt reward (tails player) player 0)
    (hjoint : quittingJointSurvivalWeight headRoots 0 cutoff ≤ δ ^ 2) :
    ∃ target : ι,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (4 * M * δ)
        (quittingInfinitePathProfile reward
          (quittingPrefixThenTailRoots headRoots (tails target) cutoff)) := by
  obtain ⟨target, hreach⟩ :=
    exists_quittingExceptionalTarget_of_jointSurvivalWeight_le_sq
      reward headRoots cutoff hδ hjoint
  refine ⟨target, ?_⟩
  intro who deviation
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingProfileLiveRoot_infinitePathProfile,
    quittingTerminalPayoff_infinitePathProfile]
  by_cases hwho : who = target
  · subst who
    have hgain := quittingPrefixThenTargetTailHazardGap_le_zero
      reward headRoots (tails target) value target
      (quittingBehaviorLiveHazard reward deviation) cutoff hpolicy hnash
      (hclosed target) (hendpoint target)
    have herror0 : 0 ≤ 4 * M * δ := by positivity
    linarith
  · have hvalue : |value cutoff who| ≤ M := by
      rw [hendpoint who]
      exact abs_quittingRootSequenceTerminalValue_le reward
        (tails who) who 0 hM hreward
    have hgain :=
      quittingPrefixThenTailHazardGap_le_four_mul_bound_mul_survival
        reward headRoots (tails target) value who
          (quittingBehaviorLiveHazard reward deviation) cutoff
          hM hreward hvalue hpolicy hnash
    have hscale :
        4 * M * quittingOpponentSurvivalWeight headRoots who 0 cutoff ≤
          4 * M * δ := by
      exact mul_le_mul_of_nonneg_left (hreach who hwho) (by positivity)
    linarith

/-- A supplied family of diagonal target-tail certificates at every accuracy
implies the finite-quitting uniform-equilibrium-payoff conclusion.  The only
producer premise left is the small-joint-survival certificate itself. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_diagonalTargetTailCertificates
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcertificate : ∀ ε : ℝ, 0 < ε →
      ∃ (headRoots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
          (tails : ι → ℕ → ι → PMF Bool) (cutoff : ℕ) (δ : ℝ),
        0 ≤ δ ∧
        4 * quittingRewardBound reward * δ ≤ ε ∧
        (∀ player,
          value cutoff player =
            quittingRootSequenceTerminalValue reward (tails player) player 0) ∧
        (∀ time, time < cutoff →
          value time = quittingRootSuccessorPayoff reward
            (value (time + 1)) (headRoots time)) ∧
        (∀ time, time < cutoff →
          IsεQuittingRootNash reward (value (time + 1)) 0 (headRoots time)) ∧
        (∀ player,
          IsQuittingTargetClosedAt reward (tails player) player 0) ∧
        quittingJointSurvivalWeight headRoots 0 cutoff ≤ δ ^ 2) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro ε hε
  obtain ⟨headRoots, value, tails, cutoff, δ, hδ, hscale,
    hendpoint, hpolicy, hnash, hclosed, hjoint⟩ := hcertificate ε hε
  obtain ⟨target, htarget⟩ :=
    exists_target_quittingPrefixThenTail_isεAsymptoticNash
      reward headRoots value tails cutoff
      (quittingRewardBound_nonneg reward) hδ
      (abs_reward_le_quittingRewardBound reward)
      hendpoint hpolicy hnash hclosed hjoint
  refine ⟨quittingInfinitePathProfile reward
      (quittingPrefixThenTailRoots headRoots (tails target) cutoff), ?_⟩
  exact htarget.mono hscale

end GameTheory
