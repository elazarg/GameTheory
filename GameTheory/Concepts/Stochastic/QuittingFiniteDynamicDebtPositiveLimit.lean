/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteDynamicDebtMonotonicity

/-!
# The positive optimized exact-debt limit branch

The attained finite-chain min-max exact debt is nonnegative and antitone in
the cutoff.  If its infimum is zero, the exact finite-chain compiler gives a
uniform-equilibrium payoff.  If the infimum is positive, compact projective
extraction from the minimizing chains gives an infinite exact dynamic-debt
path with a positive initial debt coordinate.  That coordinate forces the
corresponding opponent clock to be summable.

Thus the finite-chain program has a formal exhaustive split: success, or a
positive-debt summable-clock exceptional tail.  The exceptional branch is
not ruled out here, and no converse from unrestricted uniform equilibria to
finite exact Nash--Bellman chains is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## A maximum coordinate on the exact-debt box -/

/-- The largest debt coordinate of one exact-D augmented point. -/
def quittingDebtPointMaxDebt [Nonempty ι]
    (point : QuittingDebtPoint ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty point.2

omit [DecidableEq ι] in
/-- The maximum debt coordinate is continuous on the ambient product. -/
theorem continuous_quittingDebtPointMaxDebt [Nonempty ι] :
    Continuous (quittingDebtPointMaxDebt : QuittingDebtPoint ι → ℝ) := by
  unfold quittingDebtPointMaxDebt
  exact Continuous.finset_sup'_apply Finset.univ_nonempty fun who _ ↦ by
    fun_prop

/-- At time zero, the pointwise box maximum is exactly the finite path's
literal max exact-D objective. -/
theorem quittingDebtPointMaxDebt_finitePathDynamicDebtPoint_zero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff) :
    quittingDebtPointMaxDebt
        (quittingFiniteNashBellmanPathDynamicDebtPoint
          reward cutoff path 0) =
      quittingFiniteNashBellmanPathMaxDynamicDebt
        reward cutoff path := by
  simp [quittingDebtPointMaxDebt,
    quittingFiniteNashBellmanPathDynamicDebtPoint,
    quittingFiniteNashBellmanPathMaxDynamicDebt]

/-! ## The family of finite minimizers -/

/-- Exact-D annotations of the independently selected min-max chains.  The
annotation is padded after its own cutoff, so every family member is an
infinite sequence in one common compact box. -/
def quittingFiniteMinMaxDynamicDebtTail [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) : QuittingDebtPoint ι :=
  quittingFiniteNashBellmanPathDynamicDebtPoint reward cutoff
    (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
      reward cutoff) time

/-- Every point of every selected finite min-max tail lies in the common
compact exact-D box. -/
theorem quittingFiniteMinMaxDynamicDebtTail_mem_box [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) :
    quittingFiniteMinMaxDynamicDebtTail reward cutoff time ∈
      quittingDebtBox reward := by
  exact quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
    reward cutoff
    (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
      reward cutoff)
    (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff) time

/-- Before its cutoff, each selected finite min-max annotation follows the
literal exact dynamic-debt graph. -/
theorem quittingFiniteMinMaxDynamicDebtTail_edge [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) (htime : time < cutoff) :
    IsQuittingDynamicDebtEdge reward
      (quittingFiniteMinMaxDynamicDebtTail reward cutoff time)
      (quittingFiniteMinMaxDynamicDebtTail reward cutoff (time + 1)) := by
  exact quittingFiniteNashBellmanPathDynamicDebtPoint_edge
    reward cutoff
    (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
      reward cutoff)
    (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff) time htime

/-- The maximum initial coordinate of the selected tail is the attained
fixed-cutoff min-max value. -/
theorem quittingDebtPointMaxDebt_finiteMinMaxTail_zero [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    quittingDebtPointMaxDebt
        (quittingFiniteMinMaxDynamicDebtTail reward cutoff 0) =
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
        reward cutoff := by
  exact quittingDebtPointMaxDebt_finitePathDynamicDebtPoint_zero reward
    cutoff
    (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
      reward cutoff)

/-! ## Positive infimum extraction -/

/-- The infimum of the nonnegative fixed-cutoff min-max debts is
nonnegative. -/
theorem iInf_quittingFiniteMinMaxDynamicDebt_nonneg [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 ≤ ⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
        reward cutoff := by
  exact le_ciInf fun cutoff ↦
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_nonneg
      reward cutoff

-- The proof combines product compactness with a finite-coordinate maximum.
/-- A positive infimum of optimized finite exact debt produces an infinite
exact-D path with one positive initial coordinate and hence a summable
opponent clock. -/
theorem exists_projective_positiveDynamicDebtTail_of_iInf_minMax_pos
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpositive : 0 < ⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
        reward cutoff) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ)
        (who : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
          subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (limit time) (limit (time + 1))) ∧
      0 < (limit 0).2 who ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots limit) who) := by
  obtain ⟨limit, subseq, hsubseq, hlimit, hlimitBox, hlimitEdge⟩ :=
    exists_projective_quittingDynamicDebtTail_of_residualDepth_tendsto
      reward id (quittingFiniteMinMaxDynamicDebtTail reward)
      (quittingFiniteMinMaxDynamicDebtTail_mem_box reward)
      (quittingFiniteMinMaxDynamicDebtTail_edge reward)
      tendsto_id
  have hpointZero : Tendsto
      (fun family ↦
        quittingFiniteMinMaxDynamicDebtTail reward (subseq family) 0)
      atTop (nhds (limit 0)) :=
    ((continuous_apply 0).tendsto limit).comp hlimit
  have hmax : Tendsto
      (fun family ↦ quittingDebtPointMaxDebt
        (quittingFiniteMinMaxDynamicDebtTail reward (subseq family) 0))
      atTop (nhds (quittingDebtPointMaxDebt (limit 0))) :=
    (continuous_quittingDebtPointMaxDebt.tendsto (limit 0)).comp hpointZero
  have hbdd : BddBelow (Set.range fun cutoff : ℕ ↦
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
        reward cutoff) := by
    refine ⟨0, ?_⟩
    rintro value ⟨cutoff, rfl⟩
    exact quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_nonneg
      reward cutoff
  have hlower : ∀ family,
      (⨅ cutoff : ℕ,
          quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
            reward cutoff) ≤
        quittingDebtPointMaxDebt
          (quittingFiniteMinMaxDynamicDebtTail
            reward (subseq family) 0) := by
    intro family
    rw [quittingDebtPointMaxDebt_finiteMinMaxTail_zero]
    exact ciInf_le hbdd (subseq family)
  have hlimitLower :
      (⨅ cutoff : ℕ,
          quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
            reward cutoff) ≤
        quittingDebtPointMaxDebt (limit 0) :=
    ge_of_tendsto' hmax hlower
  have hmaxPositive : 0 < quittingDebtPointMaxDebt (limit 0) :=
    hpositive.trans_le hlimitLower
  obtain ⟨who, _, hwho⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (limit 0).2
  have hwhoPositive : 0 < (limit 0).2 who := by
    unfold quittingDebtPointMaxDebt at hmaxPositive
    rwa [hwho] at hmaxPositive
  have hclock := summable_clock_of_quittingDynamicDebtTail_pos
    reward limit hlimitBox hlimitEdge who 0 hwhoPositive
  exact ⟨limit, subseq, who, hsubseq, hlimit, hlimitBox, hlimitEdge,
    hwhoPositive, hclock⟩

/-! ## Exhaustive compiler-or-exceptional-tail split -/

/-- Every finite-player quitting game lies in one of two formally certified
branches: the optimized exact finite-chain debt vanishes and the compiler
produces a uniform-equilibrium payoff, or a projective exact-D tail retains
positive debt for a player whose opponent clock is summable. -/
theorem quittingGame_uniformEquilibriumPayoff_or_positiveDynamicDebtTail
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ)
        (who : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
          subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (limit time) (limit (time + 1))) ∧
      0 < (limit 0).2 who ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots limit) who) := by
  let obstruction := ⨅ cutoff : ℕ,
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff
  by_cases hzero : obstruction = 0
  · exact Or.inl
      (quittingGame_exists_uniformEquilibriumPayoff_of_iInf_finiteMinMaxDynamicDebt_eq_zero
        reward hzero)
  · apply Or.inr
    apply exists_projective_positiveDynamicDebtTail_of_iInf_minMax_pos
      reward
    exact lt_of_le_of_ne
      (iInf_quittingFiniteMinMaxDynamicDebt_nonneg reward)
      (Ne.symm hzero)

end GameTheory
