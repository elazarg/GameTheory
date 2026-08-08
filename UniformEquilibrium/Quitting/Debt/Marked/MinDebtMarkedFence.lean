/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanMinimizer
import UniformEquilibrium.Quitting.Debt.Marked.FenceIteration

/-!
# Marked-fence iteration on minimum-debt finite chains

This module specializes the selector-free marked-fence iteration to the
fixed-cutoff chain which minimizes aggregate surviving singleton debt over
the full compact zero-boundary Nash--Bellman chain space.

The specialization does not claim that the minimum debts vanish with the
cutoff, nor that a repeated player flag already gives a strategically closed
SCC.  It only identifies the canonical finite chains on which those remaining
questions can now be asked.
-/

noncomputable section

namespace GameTheory

open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Operational root sequence of the full-space minimum-debt chain at one
fixed cutoff. -/
abbrev quittingFiniteMinDebtRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) : ℕ → ι → PMF Bool :=
  quittingFiniteNashBellmanPathRoots cutoff
    (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff)

/-- Operational value sequence of the full-space minimum-debt chain at one
fixed cutoff. -/
abbrev quittingFiniteMinDebtValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) : ℕ → Payoff ι :=
  quittingFiniteNashBellmanPathValue cutoff
    (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff)

/-- A negative player flag on the fixed-cutoff minimum-debt chain. -/
abbrev QuittingFiniteMinDebtNegativeFlagState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (θ : ℝ) :=
  QuittingNegativeFlagState
    (quittingFiniteMinDebtValue reward cutoff) cutoff θ

/-- The minimizing chain has the exact zero-boundary interface consumed by
the marked-fence construction. -/
theorem quittingFiniteMinDebtChain_exact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    quittingFiniteMinDebtValue reward cutoff cutoff = 0 ∧
      (∀ time, time < cutoff →
        quittingFiniteMinDebtValue reward cutoff time =
          quittingRootSuccessorPayoff reward
            (quittingFiniteMinDebtValue reward cutoff (time + 1))
            (quittingFiniteMinDebtRoots reward cutoff time)) ∧
      ∀ time, time < cutoff →
        IsεQuittingRootNash reward
          (quittingFiniteMinDebtValue reward cutoff (time + 1)) 0
          (quittingFiniteMinDebtRoots reward cutoff time) := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanDebtMinimizer_mem reward cutoff
  exact ⟨
    quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
      reward cutoff path hpath,
    quittingFiniteNashBellmanPathValue_eq_successor
      reward cutoff path hpath,
    quittingFiniteNashBellmanPathRoots_isZeroNash
      reward cutoff path hpath⟩

/-- **Minimum-debt marked-fence alternative.**  On the chain minimizing
aggregate terminal debt at a fixed cutoff, every negative initial flag has an
actual supported transfer walk of length at most `card ι`.  The walk reaches
a concrete good boundary, a same-owner/same-date recurrence, or a
same-owner/strictly-later-date repeat.

This is a specialization, not a vanishing-debt or SCC-closing theorem. -/
theorem exists_finiteMinDebtNegativeFlagWalk_good_or_sameTime_or_strictTimeRepeat
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (initial : QuittingFiniteMinDebtNegativeFlagState reward cutoff θ) :
    ∃ walk : ℕ → QuittingFiniteMinDebtNegativeFlagState reward cutoff θ,
      walk 0 = initial ∧
      (∀ n, n < Fintype.card ι →
        ¬(walk n).HasGoodBoundary reward
          (quittingFiniteMinDebtRoots reward cutoff)
          (quittingFiniteMinDebtValue reward cutoff) cutoff θ →
        (walk n).IsActualTransfer reward
          (quittingFiniteMinDebtRoots reward cutoff)
          (quittingFiniteMinDebtValue reward cutoff) cutoff θ
          (walk (n + 1))) ∧
      ((∃ n, n ≤ Fintype.card ι ∧
          (walk n).HasGoodBoundary reward
            (quittingFiniteMinDebtRoots reward cutoff)
            (quittingFiniteMinDebtValue reward cutoff) cutoff θ) ∨
        (∀ n, n ≤ Fintype.card ι →
          ¬(walk n).HasGoodBoundary reward
            (quittingFiniteMinDebtRoots reward cutoff)
            (quittingFiniteMinDebtValue reward cutoff) cutoff θ) ∧
          ((∃ m n, m < n ∧ n ≤ Fintype.card ι ∧
              (walk m).owner = (walk n).owner ∧
              (walk m).time = (walk n).time) ∨
            ∃ m n, m < n ∧ n ≤ Fintype.card ι ∧
              (walk m).owner = (walk n).owner ∧
              (walk m).time < (walk n).time)) := by
  obtain ⟨hterminal, hpolicy, hnash⟩ :=
    quittingFiniteMinDebtChain_exact reward cutoff
  exact
    exists_finiteActualNegativeFlagWalk_good_or_sameTime_or_strictTimeRepeat
      reward (quittingFiniteMinDebtRoots reward cutoff)
        (quittingFiniteMinDebtValue reward cutoff) cutoff θ
        (quittingRewardBound reward) hterminal hpolicy hnash hθ
        (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward) initial

end GameTheory
