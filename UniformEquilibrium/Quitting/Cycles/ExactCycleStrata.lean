/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Punishment.CompletedCycle
import GameTheory.Concepts.Stochastic.Models.Quitting.UniformPayoffExistenceClosure

/-!
# Exact-cycle strata of quitting reward tables

A finite cyclic Nash--Bellman policy is not automatically a behavioral
equilibrium.  A player whose opponents never quit can still escape the cycle
by continuing forever.  This module therefore distinguishes:

* `IsRawExactQuittingCycle`, exact cyclic policy evaluation and exact root
  Nash at every phase;
* `IsSolvedExactQuittingCycle`, raw exactness together with genuine absorption
  and the strongest landed punishment-admissibility condition;
* `HasSolvedExactQuittingCycle`, membership of a reward table in some solved
  finite-period stratum.

The solved strata give a finite-dimensional route to uniform equilibrium.
If they accumulate at a reward table, uniform-payoff existence for nearby
tables and reward-table closure give a uniform-equilibrium payoff at the
limit.  Consequently, any table without such a payoff is separated by a
positive reward-table radius from every solved finite cycle of every period.

This is a density consumer and a counterexample restriction.  It does not
assert that solved-cycle strata are dense or manufacture a cycle.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact cyclic policy evaluation and exact one-root Nash conditions.  This
does not by itself control infinite behavioral deviations. -/
def IsRawExactQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι) : Prop :=
  (∀ phase, value phase = quittingRootSuccessorPayoff reward
      (value (finRotate K phase)) (cycle phase)) ∧
    ∀ phase, IsεQuittingRootNash reward
      (value (finRotate K phase)) 0 (cycle phase)

/-- A finite cycle accepted by the punishment-completed cycle compiler: raw
exactness, genuine absorption during a turn, and coordinatewise contraction or
credible punishment. -/
def IsSolvedExactQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι) : Prop :=
  IsRawExactQuittingCycle reward cycle value ∧
    (∏ phase : Fin K, quittingStationaryContinueMass (cycle phase)) < 1 ∧
    IsQuittingCyclePunishmentAdmissible reward cycle

/-- A reward table belongs to some nonempty finite-period solved-cycle
stratum.  The phase witness rules out the vacuous period-zero carrier and is
also an initial phase for the compiled behavioral profile. -/
def HasSolvedExactQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ K : ℕ, Nonempty (Fin K) ∧
    ∃ cycle : Fin K → ι → PMF Bool, ∃ value : Fin K → Payoff ι,
        IsSolvedExactQuittingCycle reward cycle value

/-- The selected phase value of a solved exact cycle is a uniform-equilibrium
payoff. -/
theorem isUniformEquilibriumPayoff_of_isSolvedExactQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) (h : IsSolvedExactQuittingCycle reward cycle value) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (value phase) :=
  isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle
    reward cycle value phase h.1.1 h.1.2 h.2.1 h.2.2

/-- Every table in a solved-cycle stratum has a uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_isSolvedExactQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) (h : IsSolvedExactQuittingCycle reward cycle value) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  ⟨value phase,
    isUniformEquilibriumPayoff_of_isSolvedExactQuittingCycle
      reward cycle value phase h⟩

/-- Membership in any solved finite-cycle stratum implies existence of a
uniform-equilibrium payoff. -/
theorem HasSolvedExactQuittingCycle.exists_uniformEquilibriumPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (h : HasSolvedExactQuittingCycle reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨K, hK, cycle, value, hsolved⟩ := h
  let phase : Fin K := Classical.choice hK
  exact exists_uniformEquilibriumPayoff_of_isSolvedExactQuittingCycle
    reward cycle value phase hsolved

/-- If every reward-table neighborhood meets some solved finite-cycle
stratum, reward-table closure supplies a uniform-equilibrium payoff at the
original table. -/
theorem exists_uniformEquilibriumPayoff_of_arbitrarily_close_solvedExactCycles
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hdense : ∀ η : ℝ, 0 < η →
      ∃ nearby : {S : Finset ι // S.Nonempty} → Payoff ι,
        (∀ S who, |nearby S who - reward S who| ≤ η) ∧
          HasSolvedExactQuittingCycle nearby) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarily_close_rewards reward
  intro η hη
  obtain ⟨nearby, hnearby, hsolved⟩ := hdense η hη
  exact ⟨nearby, hnearby, hsolved.exists_uniformEquilibriumPayoff⟩

/-- **Robust solved-cycle exclusion for a counterexample.**  If a reward table
has no uniform-equilibrium payoff, then one whole positive-radius sup-norm
neighborhood is disjoint from every solved finite-cycle stratum, at every
period and support pattern. -/
theorem exists_rewardNeighborhood_without_solvedExactQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnoUE : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ η : ℝ, 0 < η ∧
      ∀ nearby : {S : Finset ι // S.Nonempty} → Payoff ι,
        (∀ S who, |nearby S who - reward S who| ≤ η) →
          ¬ HasSolvedExactQuittingCycle nearby := by
  by_contra hseparation
  apply hnoUE
  apply exists_uniformEquilibriumPayoff_of_arbitrarily_close_solvedExactCycles reward
  intro η hη
  have hexists :
      ∃ nearby : {S : Finset ι // S.Nonempty} → Payoff ι,
        (∀ S who, |nearby S who - reward S who| ≤ η) ∧
          HasSolvedExactQuittingCycle nearby := by
    by_contra hnone
    apply hseparation
    refine ⟨η, hη, ?_⟩
    intro nearby hnearby hsolved
    exact hnone ⟨nearby, hnearby, hsolved⟩
  exact hexists

end GameTheory
