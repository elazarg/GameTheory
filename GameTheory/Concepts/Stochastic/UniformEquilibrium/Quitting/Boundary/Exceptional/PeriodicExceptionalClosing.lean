/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Cycles.PeriodicClosing

/-!
# Periodic closing with one noncontracting opponent clock

A cyclic quitting profile need not contract every player's opponent-only
survival clock.  Exact phasewise root Nash still closes globally on the
exceptional branch when that player's singleton quitting reward is
nonnegative.  This file packages that branch at the hazard, behavioral, and
uniform-equilibrium levels.

The zero-error hypothesis on a noncontracting branch is essential here.  A
positive phase error repeats forever and its opponent-survival-weighted sum
need not be finite.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact cyclic root Nash controls every time-dependent unilateral hazard
when the selected player's opponent cycle either contracts or the player's
singleton quitting reward is nonnegative. -/
theorem quittingCyclicHazardTerminalValue_le_of_isZeroRootNash_of_branch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι)
    (deviation : ℕ → PMF Bool) (bound : ℝ)
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (hbranch :
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1 ∨
      0 ≤ reward (quittingSingletonTerminal who) who) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingCyclicRootSequence cycle phase) who deviation 0 ≤
      quittingCyclicTerminalValue reward cycle phase who := by
  let roots := quittingCyclicRootSequence cycle phase
  let prescribed := quittingRootSequenceTerminalValue reward roots who
  let profile := quittingCyclicBehaviorProfile reward cycle phase
  let opponentProfile := quittingOpponentOnlyProfile reward profile who
  let limit := quittingLiveMassLimit reward opponentProfile
  have hresidual : ∀ time,
      quittingPrescribedOneStepResidual reward roots who prescribed time =
        0 := by
    intro time
    exact quittingPrescribedOneStepResidual_cyclic_eq_zero
      reward cycle phase who hnash time
  have hsummable : Summable (fun time =>
      quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who prescribed time) :=
    by
      simpa only [hresidual, mul_zero] using
        (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have hweights : quittingOpponentSurvivalWeight roots who 0 =
      quittingLiveMass reward opponentProfile := by
    dsimp only [roots, opponentProfile, profile]
    rw [← quittingProfileLiveRoot_cyclicBehaviorProfile
      reward cycle phase]
    funext fuel
    exact quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
      reward (quittingCyclicBehaviorProfile reward cycle phase) who fuel
  have hlimit : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds limit) := by
    rw [hweights]
    exact tendsto_quittingLiveMass reward opponentProfile
  have hlimitBranch : limit = 0 ∨
      0 ≤ reward (quittingSingletonTerminal who) who := by
    rcases hbranch with hcontracts | hsolo
    · left
      have hzero : Tendsto
          (quittingOpponentSurvivalWeight roots who 0) atTop (nhds 0) := by
        dsimp only [roots]
        exact
          tendsto_zero_quittingOpponentSurvivalWeight_cyclicRootSequence
            cycle phase who hcontracts
      exact tendsto_nhds_unique hlimit hzero
    · exact Or.inr hsolo
  have hgap :=
    quittingRootSequenceHazardTerminalGap_le_tsum_residual_of_zero_or_nonnegativeSolo
      reward roots who deviation bound limit hbound0 hreward hlimit
        hlimitBranch hsummable
  have hsum : (∑' time,
      quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who prescribed time) =
      0 := by
    simp only [hresidual, mul_zero, tsum_zero]
  rw [hsum] at hgap
  have hbase : prescribed 0 =
      quittingCyclicTerminalValue reward cycle phase who := by
    dsimp only [prescribed, roots]
    rw [quittingRootSequenceTerminalValue_cyclic_eq]
    simp
  dsimp only [roots, prescribed] at hgap hbase ⊢
  linarith

/-- Exact phasewise root Nash and the contraction-or-nonnegative-solo branch
for every player make the cyclic behavior profile an exact terminal Nash
profile. -/
theorem isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_branches
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (bound : ℝ) (hbound0 : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (hbranches : ∀ who,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1 ∨
      0 ≤ reward (quittingSingletonTerminal who) who) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  intro who deviation
  have hhazard :=
    quittingCyclicHazardTerminalValue_le_of_isZeroRootNash_of_branch
      reward cycle phase who (quittingBehaviorLiveHazard reward deviation)
        bound hbound0 hreward hnash (hbranches who)
  rw [← quittingTerminalPayoff_cyclicBehaviorProfile
    reward cycle phase] at hhazard
  have hdeviation :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward (quittingCyclicBehaviorProfile reward cycle phase) who deviation
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile] at hdeviation
  rw [hdeviation]
  simpa using hhazard

/-- Finiteness supplies the reward bound in the exact exceptional cyclic
compiler. -/
theorem isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_branches_finite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (hbranches : ∀ who,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1 ∨
      0 ≤ reward (quittingSingletonTerminal who) who) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  exact isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_branches
    reward cycle phase (quittingRewardBound reward)
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) hnash hbranches

/-- The terminal vector of an exact cyclic profile satisfying the
contraction-or-nonnegative-solo branch is a uniform equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_branches
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (hbranches : ∀ who,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1 ∨
      0 ≤ reward (quittingSingletonTerminal who) who) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingCyclicTerminalValue reward cycle phase) := by
  let profile := quittingCyclicBehaviorProfile reward cycle phase
  have hterminalNash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 profile :=
    isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_branches_finite
      reward cycle phase hnash hbranches
  intro ε hε
  have huniform : (quittingGame reward).IsUniformεEquilibrium
      none ε profile :=
    quittingGame_isUniformεEquilibrium_of_terminalNash_finite
      reward profile hε hterminalNash
  obtain ⟨nashThreshold, hnashThreshold⟩ := huniform
  have heventuallyDelivery : ∀ᶠ horizon : ℕ in atTop, ∀ player,
      |(quittingGame reward).finiteAveragePayoff none horizon profile player -
        quittingCyclicTerminalValue reward cycle phase player| < ε := by
    apply Filter.eventually_all.mpr
    intro player
    have hball :=
      (tendsto_finiteAveragePayoff_quittingGame reward profile player).eventually
        (Metric.ball_mem_nhds
          (quittingTerminalPayoff reward profile player) hε)
    filter_upwards [hball] with horizon hhorizon
    simpa only [Metric.mem_ball, Real.dist_eq, profile,
      quittingTerminalPayoff_cyclicBehaviorProfile] using hhorizon
  obtain ⟨deliveryThreshold, hdeliveryThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨profile, max nashThreshold deliveryThreshold,
    fun horizon hhorizon => ?_⟩
  constructor
  · exact hnashThreshold horizon
      (le_trans (Nat.le_max_left _ _) hhorizon)
  · intro player
    exact (hdeliveryThreshold horizon
      (le_trans (Nat.le_max_right _ _) hhorizon) player).le

/-! ## Tail-relative finite-block closing

The prescribed block and the deviator's Snell block generally have different
residual budgets.  Keeping them separate gives the sharp sum of the two
geometric charges.  When the opponent clock approaches the noncontracting
endpoint, the relevant numerator is the positive part of the Snell residual;
at the endpoint itself the terminal Never payoff has to be retained
explicitly.
-/

/-- A finite-block prescribed residual and Snell residual contribute
separately to the closing gap.  This is the sharp two-budget version of
`finiteBlockClosingGap_le`. -/
theorem finiteBlockClosingGap_le_separateResiduals
    (T : ℝ → ℝ) {G σ σi δ ηV ηB V B w : ℝ}
    (hσ0 : 0 ≤ σ) (hσδ : σ ≤ δ)
    (hσi0 : 0 ≤ σi) (hσiδ : σi ≤ δ)
    (hδ1 : δ < 1) (hηV0 : 0 ≤ ηV) (hηB0 : 0 ≤ ηB)
    (hVfixed : V = G + σ * V)
    (hVresidual : |(G + σ * w) - w| ≤ ηV)
    (hTlipschitz : ∀ x y, |T x - T y| ≤ σi * |x - y|)
    (hBfixed : T B = B) (hTsuper : T w ≤ w + ηB) :
    B - V ≤ (ηV + ηB) / (1 - δ) := by
  have hprescribed := affineFixedPoint_dist_le_of_residual
    hσ0 hσδ hδ1 hηV0 hVfixed hVresidual
  have hcap := contractingFixedPoint_le_of_approximateSuperSolution
    T hσi0 hσiδ hδ1 hηB0 hTlipschitz hBfixed hTsuper
  have hcapGap : B - w ≤ ηB / (1 - δ) := by
    linarith
  have hprescribedGap : w - V ≤ ηV / (1 - δ) :=
    (le_abs_self (w - V)).trans
      (by simpa [abs_sub_comm] using hprescribed)
  calc
    B - V = (B - w) + (w - V) := by ring
    _ ≤ ηB / (1 - δ) + ηV / (1 - δ) :=
      add_le_add hcapGap hprescribedGap
    _ = (ηV + ηB) / (1 - δ) := by ring

/-- Tail-relative Snell closing.  For a contracting scalar block, the cap gap
is controlled by the positive part of the residual at the supplied tail
value.  In particular, a residual merely tending to zero is insufficient
when `σ` tends to one unless it is little-o of `1 - σ`. -/
theorem contractingFixedPoint_sub_le_positivePartResidual
    (T : ℝ → ℝ) {σ B w : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hTlipschitz : ∀ x y, |T x - T y| ≤ σ * |x - y|)
    (hBfixed : T B = B) :
    B - w ≤ max (T w - w) 0 / (1 - σ) := by
  let η := max (T w - w) 0
  have hη0 : 0 ≤ η := le_max_right _ _
  have hsuper : T w ≤ w + η := by
    dsimp only [η]
    have hresidual : T w - w ≤ max (T w - w) 0 :=
      le_max_left _ _
    linarith
  have hcap := contractingFixedPoint_le_of_approximateSuperSolution
    T hσ0 (le_refl σ) hσ1 hη0 hTlipschitz hBfixed hsuper
  dsimp only [η] at hcap
  linarith

/-- Exact player-specific closing for a contracting opponent clock.  The
prescribed block seam and the positive Snell residual are amplified by their
own survival denominators; no common contraction constant is required. -/
theorem finiteBlockClosingGap_le_tailRelative
    (T : ℝ → ℝ) {G σ σi V B w : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hσi0 : 0 ≤ σi) (hσi1 : σi < 1)
    (hVfixed : V = G + σ * V)
    (hTlipschitz : ∀ x y, |T x - T y| ≤ σi * |x - y|)
    (hBfixed : T B = B) :
    B - V ≤
      max (T w - w) 0 / (1 - σi) +
        |(G + σ * w) - w| / (1 - σ) := by
  have hprescribed := affineFixedPoint_dist_le_of_residual
    hσ0 (le_refl σ) hσ1 (abs_nonneg ((G + σ * w) - w)) hVfixed
      (le_refl |(G + σ * w) - w|)
  have hprescribedGap :
      w - V ≤ |(G + σ * w) - w| / (1 - σ) :=
    (le_abs_self (w - V)).trans
      (by simpa [abs_sub_comm] using hprescribed)
  have hcapGap := contractingFixedPoint_sub_le_positivePartResidual
    T (w := w) hσi0 hσi1 hTlipschitz hBfixed
  calc
    B - V = (B - w) + (w - V) := by ring
    _ ≤ max (T w - w) 0 / (1 - σi) +
        |(G + σ * w) - w| / (1 - σ) :=
      add_le_add hcapGap hprescribedGap

/-- Exact player-specific closing at the noncontracting opponent-clock
endpoint.  `max 0 quitValue` is the full terminal cap, including Never, so
its positive defect at the reference value replaces division by `1 - σi`. -/
theorem finiteBlockClosingGap_le_exceptionalBoundary
    {G σ quitValue V w : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hVfixed : V = G + σ * V) :
    max 0 quitValue - V ≤
      max (max 0 quitValue - w) 0 +
        |(G + σ * w) - w| / (1 - σ) := by
  have hprescribed := affineFixedPoint_dist_le_of_residual
    hσ0 (le_refl σ) hσ1 (abs_nonneg ((G + σ * w) - w)) hVfixed
      (le_refl |(G + σ * w) - w|)
  have hprescribedGap :
      w - V ≤ |(G + σ * w) - w| / (1 - σ) :=
    (le_abs_self (w - V)).trans
      (by simpa [abs_sub_comm] using hprescribed)
  have hcapGap :
      max 0 quitValue - w ≤ max (max 0 quitValue - w) 0 :=
    le_max_left _ _
  calc
    max 0 quitValue - V =
        (max 0 quitValue - w) + (w - V) := by ring
    _ ≤ max (max 0 quitValue - w) 0 +
        |(G + σ * w) - w| / (1 - σ) :=
      add_le_add hcapGap hprescribedGap

/-- Division-free exceptional endpoint.  If the opponent clock is exactly
noncontracting, its one-block Snell operator is `z ↦ max quitValue z`, while
the terminal cap is `max 0 quitValue`: the extra zero is the Never boundary.
A nonnegative exact super-solution therefore bounds the cap without dividing
by `1 - σ`. -/
theorem exceptionalSnellCap_le_of_nonnegative_superSolution
    {quitValue w : ℝ} (hw0 : 0 ≤ w)
    (hsuper : max quitValue w ≤ w) :
    max 0 quitValue ≤ w := by
  apply max_le hw0
  exact (le_max_left quitValue w).trans hsuper

/-- The exact exceptional-clock exploitability is the negative part of the
singleton quitting payoff.  This is the scalar regression that prevents a
local fixed-point equation from silently discarding Never. -/
theorem exceptionalSnellCap_sub_prescribed_eq_negativePart
    (soloReward : ℝ) :
    max 0 soloReward - soloReward = max (-soloReward) 0 := by
  by_cases hsolo : 0 ≤ soloReward
  · rw [max_eq_right hsolo, max_eq_right (neg_nonpos.mpr hsolo)]
    ring
  · have hsoloLe : soloReward ≤ 0 := le_of_not_ge hsolo
    rw [max_eq_left hsoloLe, max_eq_left (neg_nonneg.mpr hsoloLe)]
    ring

end GameTheory
