/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingDiagonalTargetTailCompiler

/-!
# Packaged diagonal target-tail certificates

The lower-level target-tail modules deliberately separate four ingredients:
player-indexed closed tails, their diagonal endpoint, an exact finite
Nash--Bellman prefix ending at that endpoint, and the small joint-survival
producer.  This file gives those ingredients explicit names and constructors.

No compact minimizer or continuity assertion is used.  The only hypothesis in
the final certificate that is not constructed here is the quantitative small
joint-survival inequality.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **Abstract exceptional-target selector.**  If every two distinct
playerwise survival quantities have product at most `joint`, and `joint` is
at most `δ²`, one player can be selected so that every other survival
quantity is at most `δ`. -/
theorem exists_exceptionalTarget_of_pairwise_mul_le_joint
    [Nonempty ι]
    (opponentSurvival : ι → ℝ) (joint δ : ℝ)
    (hδ : 0 ≤ δ)
    (hpair : ∀ {first second : ι}, first ≠ second →
      opponentSurvival first * opponentSurvival second ≤ joint)
    (hjoint : joint ≤ δ ^ 2) :
    ∃ target : ι, ∀ who, who ≠ target →
      opponentSurvival who ≤ δ := by
  classical
  by_cases hexception : ∃ target : ι, δ < opponentSurvival target
  · obtain ⟨target, htarget⟩ := hexception
    refine ⟨target, ?_⟩
    intro who hwho
    by_contra hnot
    have hwhoLarge : δ < opponentSurvival who := lt_of_not_ge hnot
    have hproduct := hpair (first := target) (second := who) (Ne.symm hwho)
    nlinarith
  · let target : ι := Classical.choice (inferInstance : Nonempty ι)
    refine ⟨target, ?_⟩
    intro who _
    exact le_of_not_gt (fun hlarge => hexception ⟨who, hlarge⟩)

/-- The diagonal endpoint selected from a player-indexed family of tails: only
player `i`'s payoff in tail `i` is used in coordinate `i`.  The tails need not
agree in any other coordinate. -/
def quittingDiagonalTailEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tails : ι → ℕ → ι → PMF Bool) : Payoff ι :=
  fun player =>
    quittingRootSequenceTerminalValue reward (tails player) player 0

/-- Every coordinate of the diagonal tail endpoint lies in the canonical
reward cube. -/
theorem abs_quittingDiagonalTailEndpoint_le_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tails : ι → ℕ → ι → PMF Bool) (player : ι) :
    |quittingDiagonalTailEndpoint reward tails player| ≤
      quittingRewardBound reward := by
  exact abs_quittingRootSequenceTerminalValue_le reward
    (tails player) player 0 (quittingRewardBound_nonneg reward)
    (abs_reward_le_quittingRewardBound reward)

/-- Choosing one stationary opponent row for each player produces an actual
player-indexed family of tails.  Tail `i` is exactly closed for player `i`,
attains the selected stationary cap in coordinate `i`, and preserves the
chosen row in every opponent coordinate. -/
theorem exists_quittingTargetClosedTailFamily_of_stationaryRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (stationaryRoots : ι → ι → PMF Bool) :
    ∃ tails : ι → ℕ → ι → PMF Bool,
      (∀ player,
        IsQuittingTargetClosedAt reward (tails player) player 0) ∧
      (∀ player,
        quittingDiagonalTailEndpoint reward tails player =
          quittingStationaryUnilateralCap reward
            (stationaryRoots player) player) ∧
      ∀ target time player, player ≠ target →
        tails target time player = stationaryRoots target player := by
  classical
  let tails : ι → ℕ → ι → PMF Bool := fun player =>
    Classical.choose
      (exists_quittingTargetClosedTail_of_stationaryRoot
        reward (stationaryRoots player) player)
  have hspec : ∀ player,
      IsQuittingTargetClosedAt reward (tails player) player 0 ∧
        quittingRootSequenceTerminalValue reward (tails player) player 0 =
          quittingStationaryUnilateralCap reward
            (stationaryRoots player) player ∧
        ∀ time opponent, opponent ≠ player →
          tails player time opponent = stationaryRoots player opponent := by
    intro player
    simpa only [tails] using
      (Classical.choose_spec
        (exists_quittingTargetClosedTail_of_stationaryRoot
          reward (stationaryRoots player) player))
  refine ⟨tails, ?_, ?_, ?_⟩
  · intro player
    exact (hspec player).1
  · intro player
    exact (hspec player).2.1
  · intro target time player hne
    exact (hspec target).2.2 time player hne

/-- The compact serial predecessor relation constructs one common exact
finite Nash--Bellman prefix ending at the diagonal endpoint of any supplied
tail family.  The root stored after the cutoff is only the factory's
all-Continue presentation coordinate; an actual selected tail is spliced in
by the diagonal compiler. -/
theorem exists_finiteDiagonalTailEndpointExactQuittingNashBellmanChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tails : ι → ℕ → ι → PMF Bool) (cutoff : ℕ) :
    ∃ (headRoots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι),
      (∀ time, cutoff ≤ time →
        headRoots time = (quittingAllContinueRoot : ι → PMF Bool)) ∧
      value cutoff = quittingDiagonalTailEndpoint reward tails ∧
      (∀ time, time < cutoff →
        value time = quittingRootSuccessorPayoff reward
          (value (time + 1)) (headRoots time)) ∧
      (∀ time, time < cutoff →
        IsεQuittingRootNash reward (value (time + 1)) 0
          (headRoots time)) ∧
      ∀ time player,
        |value time player| ≤ quittingRewardBound reward := by
  exact exists_finiteEndpointExactQuittingNashBellmanChain reward
    (quittingDiagonalTailEndpoint reward tails)
    (abs_quittingDiagonalTailEndpoint_le_rewardBound reward tails)
    cutoff

/-- One call constructs the full **stationary diagonal skeleton**: actual
player-indexed closed tails and one common exact finite Nash--Bellman prefix
ending at their diagonal endpoint.  The quantitative joint-survival bound is
intentionally absent; it is the remaining producer theorem. -/
theorem exists_stationaryDiagonalTargetTailSkeleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (stationaryRoots : ι → ι → PMF Bool) (cutoff : ℕ) :
    ∃ (tails : ι → ℕ → ι → PMF Bool)
        (headRoots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι),
      (∀ player,
        IsQuittingTargetClosedAt reward (tails player) player 0) ∧
      (∀ player,
        quittingDiagonalTailEndpoint reward tails player =
          quittingStationaryUnilateralCap reward
            (stationaryRoots player) player) ∧
      (∀ time, cutoff ≤ time →
        headRoots time = (quittingAllContinueRoot : ι → PMF Bool)) ∧
      value cutoff = quittingDiagonalTailEndpoint reward tails ∧
      (∀ time, time < cutoff →
        value time = quittingRootSuccessorPayoff reward
          (value (time + 1)) (headRoots time)) ∧
      (∀ time, time < cutoff →
        IsεQuittingRootNash reward (value (time + 1)) 0
          (headRoots time)) ∧
      (∀ time player,
        |value time player| ≤ quittingRewardBound reward) ∧
      ∀ target time player, player ≠ target →
        tails target time player = stationaryRoots target player := by
  obtain ⟨tails, hclosed, hcaps, hopponents⟩ :=
    exists_quittingTargetClosedTailFamily_of_stationaryRoots
      reward stationaryRoots
  obtain ⟨headRoots, value, hafter, hendpoint, hpolicy, hnash, hbound⟩ :=
    exists_finiteDiagonalTailEndpointExactQuittingNashBellmanChain
      reward tails cutoff
  exact ⟨tails, headRoots, value, hclosed, hcaps, hafter, hendpoint,
    hpolicy, hnash, hbound, hopponents⟩

/-- The complete finite diagonal target-tail certificate consumed by the
exceptional-target compiler.  All tails coexist only through their diagonal
endpoint; after the common prefix has been built, one tail is selected and
actually spliced. -/
def HasQuittingDiagonalTargetTailCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) : Prop :=
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
      IsεQuittingRootNash reward (value (time + 1)) 0
        (headRoots time)) ∧
    (∀ player,
      IsQuittingTargetClosedAt reward (tails player) player 0) ∧
    quittingJointSurvivalWeight headRoots 0 cutoff ≤ δ ^ 2

/-- Certificates at every positive accuracy imply a uniform-equilibrium
payoff.  The proof is exactly the exceptional-target diagonal compiler plus
the existing compact terminal-payoff selection theorem. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_hasDiagonalTargetTailCertificates
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcertificate : ∀ ε : ℝ, 0 < ε →
      HasQuittingDiagonalTargetTailCertificate reward ε) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply
    quittingGame_exists_uniformEquilibriumPayoff_of_diagonalTargetTailCertificates
      reward
  intro ε hε
  simpa only [HasQuittingDiagonalTargetTailCertificate] using
    hcertificate ε hε

end GameTheory
