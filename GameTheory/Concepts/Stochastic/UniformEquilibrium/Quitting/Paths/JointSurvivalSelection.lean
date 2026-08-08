/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Paths.InfinitePathCompiler
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Paths.SupportWitnessPathCompiler

/-!
# Bellman-path selection from joint absorption

The existing nonperiodic path compiler selects bounded Bellman values under
playerwise opponent-survival contraction.  For support-witness paths obtained
by reversing absorbing circulation prefixes, the natural contraction is
instead the canonical joint all-continue survival weight.  This file records
the corresponding selection theorem and the absorption lower-bound criteria
that feed it.

Because a root successor depends affinely on the declared all-continue tail,
the difference of two policy-evaluation paths is multiplied exactly by the
joint continue mass at every stage.  Thus vanishing joint survival is already
sufficient for uniqueness.  A uniform positive one-stage absorption lower
bound makes joint survival geometric and also makes total absorption charge
nonsummable.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι]

/-- Iterating a homogeneous one-step difference estimate produces the exact
joint-survival prefix weight. -/
theorem abs_pathDifference_le_jointSurvival_mul
    (roots : ℕ → ι → PMF Bool)
    (difference : ℕ → ℝ)
    (hstep : ∀ time,
      |difference time| ≤
        quittingStationaryContinueMass (roots time) *
          |difference (time + 1)|) :
    ∀ start fuel,
      |difference start| ≤
        quittingJointSurvivalWeight roots start fuel *
          |difference (start + fuel)| := by
  classical
  intro start fuel
  have hone : ∀ liveStart,
      quittingJointSurvivalWeight roots liveStart 1 =
        quittingStationaryContinueMass (roots liveStart) := by
    intro liveStart
    rw [quittingJointSurvivalWeight_eq_prod]
    simp
  induction fuel generalizing start with
  | zero =>
      rw [quittingJointSurvivalWeight_eq_prod]
      simp
  | succ fuel ih =>
      have hfirst := hstep start
      have htail := ih (start + 1)
      have hmass0 := quittingStationaryContinueMass_nonneg (roots start)
      have hscaled := mul_le_mul_of_nonneg_left htail hmass0
      calc
        |difference start| ≤
            quittingStationaryContinueMass (roots start) *
              |difference (start + 1)| := hfirst
        _ ≤ quittingStationaryContinueMass (roots start) *
            (quittingJointSurvivalWeight roots (start + 1) fuel *
              |difference (start + 1 + fuel)|) := hscaled
        _ = quittingJointSurvivalWeight roots start fuel.succ *
            |difference (start + fuel.succ)| := by
          rw [show fuel.succ = 1 + fuel by omega,
            quittingJointSurvivalWeight_add, hone]
          ring_nf

/-- A positive lower bound on every one-stage absorption probability makes
joint survival geometric from every starting time. -/
theorem tendsto_zero_quittingJointSurvivalWeight_of_absorption_lower
    (roots : ℕ → ι → PMF Bool) {charge : ℝ}
    (hcharge : 0 < charge)
    (hlower : ∀ time,
      charge ≤ quittingRootAbsorptionMass (roots time))
    (start : ℕ) :
    Tendsto (quittingJointSurvivalWeight roots start) atTop (nhds 0) := by
  classical
  have hcharge1 : charge ≤ 1 := by
    have hl := hlower start
    unfold quittingRootAbsorptionMass at hl
    linarith [quittingStationaryContinueMass_nonneg (roots start)]
  have hrho0 : 0 ≤ 1 - charge := by linarith
  have hrho1 : 1 - charge < 1 := by linarith
  have hfactor : ∀ time,
      quittingStationaryContinueMass (roots time) ≤ 1 - charge := by
    intro time
    have hl := hlower time
    unfold quittingRootAbsorptionMass at hl
    linarith
  have hbound : ∀ fuel,
      quittingJointSurvivalWeight roots start fuel ≤
        (1 - charge) ^ fuel := by
    intro fuel
    rw [quittingJointSurvivalWeight_eq_prod]
    calc
      (∏ offset ∈ Finset.range fuel,
          quittingStationaryContinueMass (roots (start + offset))) ≤
        ∏ _offset ∈ Finset.range fuel, (1 - charge) := by
          apply Finset.prod_le_prod
          · intro offset _
            exact quittingStationaryContinueMass_nonneg
              (roots (start + offset))
          · intro offset _
            exact hfactor (start + offset)
      _ = (1 - charge) ^ fuel := by simp
  apply squeeze_zero
  · exact quittingJointSurvivalWeight_nonneg roots start
  · exact hbound
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one hrho0 hrho1

/-- Uniformly bounded exact Bellman values are uniquely selected by the
terminal root-sequence payoff once joint survival vanishes from every start. -/
theorem
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_jointSurvival_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (value : ℕ → Payoff ι)
    {bound : ℝ}
    (hsurvival : ∀ start,
      Tendsto (quittingJointSurvivalWeight roots start) atTop (nhds 0))
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) :
    ∀ time,
      value time =
        fun who ↦ quittingRootSequenceTerminalValue reward roots who time := by
  classical
  intro time
  funext who
  let terminal : ℕ → ℝ :=
    fun liveTime ↦
      quittingRootSequenceTerminalValue reward roots who liveTime
  let difference : ℕ → ℝ :=
    fun liveTime ↦ value liveTime who - terminal liveTime
  have hstep : ∀ liveTime,
      |difference liveTime| ≤
        quittingStationaryContinueMass (roots liveTime) *
          |difference (liveTime + 1)| := by
    intro liveTime
    have hvalue := congrFun (hpolicy liveTime) who
    have hterminal :=
      quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff
        reward roots who liveTime
    dsimp only [difference, terminal]
    rw [hvalue, hterminal,
      quittingRootSuccessorPayoff_sub_eq_continueMass_mul,
      abs_mul,
      abs_of_nonneg
        (quittingStationaryContinueMass_nonneg (roots liveTime))]
  have hiterate := abs_pathDifference_le_jointSurvival_mul
    roots difference hstep time
  have htailBound : ∀ fuel,
      |difference (time + fuel)| ≤ 2 * bound := by
    intro fuel
    have hvalue := hvalueBound (time + fuel) who
    have hterminal := abs_quittingTerminalPayoff_le reward
      (quittingRootSequenceProfile reward roots (time + fuel)) who
      hbound0 hreward
    dsimp only [difference, terminal,
      quittingRootSequenceTerminalValue] at hterminal ⊢
    exact (abs_sub _ _).trans (by linarith)
  have hbound : ∀ fuel,
      |difference time| ≤
        quittingJointSurvivalWeight roots time fuel * (2 * bound) := by
    intro fuel
    exact (hiterate fuel).trans
      (mul_le_mul_of_nonneg_left (htailBound fuel)
        (quittingJointSurvivalWeight_nonneg roots time fuel))
  have htendsto : Tendsto (fun fuel ↦
      quittingJointSurvivalWeight roots time fuel * (2 * bound))
      atTop (nhds 0) := by
    simpa using (hsurvival time).mul_const (2 * bound)
  have hzero : |difference time| ≤ 0 :=
    ge_of_tendsto' htendsto hbound
  have hdifference : difference time = 0 :=
    abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
  dsimp only [difference, terminal] at hdifference
  exact sub_eq_zero.mp hdifference

/-- Positive one-stage absorption is a direct sufficient condition for the
joint-survival selection theorem. -/
theorem
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_absorption_lower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (value : ℕ → Payoff ι)
    {charge bound : ℝ}
    (hcharge : 0 < charge)
    (hlower : ∀ time,
      charge ≤ quittingRootAbsorptionMass (roots time))
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) :
    ∀ time,
      value time =
        fun who ↦ quittingRootSequenceTerminalValue reward roots who time := by
  classical
  exact
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_jointSurvival_tendsto_zero
      reward roots value
      (tendsto_zero_quittingJointSurvivalWeight_of_absorption_lower
        roots hcharge hlower)
      hbound0 hreward hvalueBound hpolicy

/-- A uniform positive lower bound makes the total absorption charge
nonsummable. -/
theorem not_summable_quittingTotalAbsorptionCharge_of_uniform_lower
    (roots : ℕ → ι → PMF Bool) {charge : ℝ}
    (hcharge : 0 < charge)
    (hlower : ∀ time,
      charge ≤ quittingTotalAbsorptionCharge roots time) :
    ¬ Summable (quittingTotalAbsorptionCharge roots) := by
  classical
  intro hsummable
  have hzero := hsummable.tendsto_atTop_zero
  have heventually : ∀ᶠ time : ℕ in atTop,
      quittingTotalAbsorptionCharge roots time < charge :=
    (tendsto_order.1 hzero).2 charge hcharge
  obtain ⟨time, htime⟩ := heventually.exists
  exact (not_lt_of_ge (hlower time)) htime

end GameTheory
