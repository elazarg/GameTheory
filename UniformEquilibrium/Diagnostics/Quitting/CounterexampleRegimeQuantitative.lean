/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime

/-!
# Quantitative restrictions on the quitting counterexample regime

This module connects terminal instability directly to the exact dynamic-debt
obstruction.  A zero-boundary exact-D chain compiles to a terminal approximate
Nash profile whose error is its largest initial debt.  Therefore every uniform
terminal exploitability gap is below the optimized exact-D value at every
cutoff, and below its limiting infimum.

The optimized debt is itself bounded by the largest positive own reward at a
singleton quitting terminal.  Thus, writing

`K = max_i max(0, r_i({i}))`,

every counterexample regime satisfies

`0 < terminalGap ≤ inf_N D_N ≤ D_N ≤ K ≤ quittingRewardBound reward`.

The projective compactness argument retains this quantitative margin: one
owner on the limiting exact-D tail has initial debt at least `terminalGap` and
a summable opponent clock.  No comparison with the dimensionless
punishment-floor absorption budget is asserted here.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-! ## Reward-scale cap -/

/-- The largest positive own reward at a singleton quitting terminal.  This
is also the largest terminal cap used by exact dynamic debt. -/
def quittingMaxPositiveSingletonDebtCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (quittingPositiveSingletonDebtCap reward)

omit [DecidableEq ι] in
/-- Every player's singleton-debt cap lies below the largest such cap. -/
theorem quittingPositiveSingletonDebtCap_le_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingPositiveSingletonDebtCap reward who ≤
      quittingMaxPositiveSingletonDebtCap reward := by
  exact Finset.le_sup'
    (quittingPositiveSingletonDebtCap reward) (Finset.mem_univ who)

omit [DecidableEq ι] in
/-- The largest positive singleton-debt cap is nonnegative. -/
theorem quittingMaxPositiveSingletonDebtCap_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 ≤ quittingMaxPositiveSingletonDebtCap reward := by
  let who : ι := Classical.choice inferInstance
  exact (le_max_left 0 _).trans
    (quittingPositiveSingletonDebtCap_le_max reward who)

omit [DecidableEq ι] in
/-- The singleton cap lies below the canonical bound on the whole reward
table. -/
theorem quittingMaxPositiveSingletonDebtCap_le_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingMaxPositiveSingletonDebtCap reward ≤
      quittingRewardBound reward := by
  unfold quittingMaxPositiveSingletonDebtCap
  apply Finset.sup'_le
  intro who _
  unfold quittingPositiveSingletonDebtCap
  apply max_le (quittingRewardBound_nonneg reward)
  exact (le_abs_self _).trans
    (abs_reward_le_quittingRewardBound reward
      (quittingSingletonTerminal who) who)

/-! ## Terminal gap versus optimized exact debt -/

/-- Every optimized min-max exact-D value is bounded by the largest positive
singleton reward. -/
theorem quittingFiniteMinMaxDynamicDebt_le_maxPositiveSingletonDebtCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff ≤
      quittingMaxPositiveSingletonDebtCap reward := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer reward cutoff
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff
  calc
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff ≤
        quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff path :=
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_le
        reward cutoff path hpath
    _ ≤ quittingMaxPositiveSingletonDebtCap reward := by
      unfold quittingFiniteNashBellmanPathMaxDynamicDebt
      apply Finset.sup'_le
      intro who _
      exact
        (quittingFiniteNashBellmanPathDynamicDebt_le_cap
            reward cutoff path hpath who 0 (Nat.zero_le cutoff)).trans
          (quittingPositiveSingletonDebtCap_le_max reward who)

/-- A terminal exploitability gap is below the optimized exact-D value at
every cutoff.  This is the direct quantitative connection between the
terminal and debt lanes. -/
theorem terminalExploitabilityGap_le_finiteMinMaxDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (cutoff : ℕ) :
    gap ≤
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer reward cutoff
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff
  let roots := quittingFiniteNashBellmanPathRoots cutoff path
  let value := quittingFiniteNashBellmanPathValue cutoff path
  let debt :=
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff
  have hnash :
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) debt
        (quittingInfinitePathProfile reward roots) := by
    apply finiteChainProfile_isεAsymptoticNash_of_dynamicDebt
      reward roots value cutoff debt
    · exact quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
        cutoff path
    · exact quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
        reward cutoff path hpath
    · exact quittingFiniteNashBellmanPathValue_eq_successor
        reward cutoff path hpath
    · intro who
      exact quittingFiniteNashBellmanPathDynamicDebt_le_max
        reward cutoff path who
  obtain ⟨who, dev, hgain⟩ :=
    hexploit (quittingInfinitePathProfile reward roots)
  have hbound := hnash who dev
  dsimp only [debt] at hbound ⊢
  linarith

/-- A terminal exploitability gap is below the limiting optimized exact-D
obstruction. -/
theorem terminalExploitabilityGap_le_iInf_finiteMinMaxDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap) :
    gap ≤ ⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff :=
  le_ciInf fun cutoff ↦
    terminalExploitabilityGap_le_finiteMinMaxDynamicDebt
      reward hexploit cutoff

namespace QuittingCounterexampleRegime

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The regime's terminal margin is below every optimized exact-D value. -/
theorem terminalGap_le_finiteMinMaxDynamicDebt
    (regime : QuittingCounterexampleRegime reward) (cutoff : ℕ) :
    regime.terminalGap ≤
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff :=
  terminalExploitabilityGap_le_finiteMinMaxDynamicDebt
    reward regime.terminalExploitability cutoff

/-- The regime's terminal margin is below the limiting exact-D
obstruction. -/
theorem terminalGap_le_iInf_minMaxDynamicDebt
    (regime : QuittingCounterexampleRegime reward) :
    regime.terminalGap ≤ ⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff :=
  terminalExploitabilityGap_le_iInf_finiteMinMaxDynamicDebt
    reward regime.terminalExploitability

/-- The limiting optimized exact-D obstruction is positive for every
counterexample regime. -/
theorem iInf_minMaxDynamicDebt_pos_of_terminalGap
    (regime : QuittingCounterexampleRegime reward) :
    0 < ⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff :=
  regime.terminalGap_pos.trans_le
    regime.terminalGap_le_iInf_minMaxDynamicDebt

/-- The terminal margin is bounded by the largest positive singleton
reward. -/
theorem terminalGap_le_maxPositiveSingletonDebtCap
    (regime : QuittingCounterexampleRegime reward) :
    regime.terminalGap ≤ quittingMaxPositiveSingletonDebtCap reward :=
  (regime.terminalGap_le_finiteMinMaxDynamicDebt 0).trans
    (quittingFiniteMinMaxDynamicDebt_le_maxPositiveSingletonDebtCap reward 0)

/-- A counterexample regime forces a player to have a strictly positive own
reward at their singleton quitting terminal. -/
theorem maxPositiveSingletonDebtCap_pos
    (regime : QuittingCounterexampleRegime reward) :
    0 < quittingMaxPositiveSingletonDebtCap reward :=
  regime.terminalGap_pos.trans_le
    regime.terminalGap_le_maxPositiveSingletonDebtCap

end QuittingCounterexampleRegime

/-! ## Quantitative projective tail -/

/-- A positive scalar below the optimized exact-D infimum survives in one
specific initial coordinate of the projective limit tail. -/
theorem exists_projectiveDynamicDebtTail_of_pos_le_iInf_minMax
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {floor : ℝ} (hfloor_pos : 0 < floor)
    (hfloor : floor ≤ ⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
        reward cutoff) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ) (who : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
          subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (limit time) (limit (time + 1))) ∧
      floor ≤ (limit 0).2 who ∧
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
  obtain ⟨who, _, hwho⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (limit 0).2
  have hfloor_who : floor ≤ (limit 0).2 who := by
    have hbound := hfloor.trans hlimitLower
    unfold quittingDebtPointMaxDebt at hbound
    rwa [hwho] at hbound
  have hwho_pos : 0 < (limit 0).2 who :=
    hfloor_pos.trans_le hfloor_who
  have hclock := summable_clock_of_quittingDynamicDebtTail_pos
    reward limit hlimitBox hlimitEdge who 0 hwho_pos
  exact ⟨limit, subseq, who, hsubseq, hlimit, hlimitBox, hlimitEdge,
    hfloor_who, hclock⟩

namespace QuittingCounterexampleRegime

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The regime has a projective exact-D tail with one owner whose initial
debt is at least the terminal exploitability gap and whose opponent clock is
summable. -/
theorem exists_terminalGapDynamicDebtTail
    (regime : QuittingCounterexampleRegime reward) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ) (who : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
          subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (limit time) (limit (time + 1))) ∧
      regime.terminalGap ≤ (limit 0).2 who ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots limit) who) :=
  exists_projectiveDynamicDebtTail_of_pos_le_iInf_minMax
    reward regime.terminalGap_pos
      regime.terminalGap_le_iInf_minMaxDynamicDebt

end QuittingCounterexampleRegime

end GameTheory
