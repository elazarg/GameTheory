/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingPhaseSwitchProfile
import GameTheory.Concepts.Stochastic.QuittingTerminalUniformization

/-!
# The one-sided deviation cap of a phase-switched quitting profile

This file assembles the folk-theorem inequality for the phase-switch
combinator of `QuittingPhaseSwitchProfile.lean`.  Fix a plan, a punishment
plan and a switch stage `T`, and suppose

* **(a)** the *truncated* plan -- the plan frozen to all-Continue from `T` on
  -- caps player `who`'s unilateral gain by `planError`;
* **(b)** the punishment plan caps every unilateral continuation payoff of
  `who` by `punishCap + punishError`;
* **(c)** the plan phase reaches `T` with opponent-survival mass at most
  `survivalCap`.

Then the switched profile caps `who`'s unilateral gain by
`planError + survivalCap * (max (punishCap + punishError) 0 + bound)`.

Hypothesis (b) is *hypothesised*, not proved: whether a punishment plan
attains a player's punishment level is the separate lower-bound question.
The value of the assembly is exactly that it turns any future punishment
bound into an existence engine for terminal -- hence uniform -- approximate
equilibria, via `quittingGame_isUniformεEquilibrium_of_terminalNash_finite`.

## Where the live-hazard collapse is load-bearing

The deviator is an **arbitrary behaviour strategy**, not a time-indexed
plan.  It is reduced to a time-indexed hazard exactly once, by
`quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue`
(`QuittingBehaviorPureTimeExtremality.lean`), which evaluates the deviation
along the quitting game's unique live public history.  Everything after that
reduction -- the plan-phase/punishment-phase split, the survival bookkeeping,
and the arithmetic -- is a statement about hazard sequences.  The converse
direction, `quittingRootSequenceHazardTerminalValue_eq_terminalPayoff_update`,
lets hypotheses (a) and (b) be discharged against behaviour strategies even
though they are stated for hazards.

## Main results

* `quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le` --
  the cap, for an arbitrary hazard deviation
* `quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le` -- the cap,
  for an arbitrary behaviour deviation
* `isεAsymptoticNash_quittingPhaseSwitchProfile` -- the terminal
  approximate-Nash consumer statement
* `isUniformεEquilibrium_quittingPhaseSwitchProfile` -- the uniform
  approximate-equilibrium consumer statement
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Opponent survival ignores the deviator's own coordinate -/

/-- Replacing player `who`'s own marginals leaves the opponent-survival
weight of `who` unchanged: the deviator cannot move the mass that his
opponents remove. -/
theorem quittingOpponentSurvivalWeight_quittingRootSequenceUpdate
    (roots : ℕ → ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool)
    (start fuel : ℕ) :
    quittingOpponentSurvivalWeight
        (quittingRootSequenceUpdate roots who hazard) who start fuel =
      quittingOpponentSurvivalWeight roots who start fuel := by
  unfold quittingOpponentSurvivalWeight quittingFixedOpponentsContinueMass
    quittingRootSequenceUpdate
  exact Finset.prod_congr rfl fun offset _ => by rw [Function.update_idem]

/-- Opponent survival over a window only sees the roots inside that
window. -/
theorem quittingOpponentSurvivalWeight_congr
    (x y : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ)
    (hagree : ∀ offset, offset < fuel → x (start + offset) = y (start + offset)) :
    quittingOpponentSurvivalWeight x who start fuel =
      quittingOpponentSurvivalWeight y who start fuel := by
  unfold quittingOpponentSurvivalWeight quittingFixedOpponentsContinueMass
  exact Finset.prod_congr rfl fun offset hoffset => by
    rw [hagree offset (Finset.mem_range.mp hoffset)]

/-- Over the plan phase the phase-switch sequence has the plan's opponent
survival. -/
theorem quittingOpponentSurvivalWeight_quittingPhaseSwitchRoots_plan
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι) :
    quittingOpponentSurvivalWeight (quittingPhaseSwitchRoots plan punish switch)
        who 0 switch =
      quittingOpponentSurvivalWeight plan who 0 switch := by
  refine quittingOpponentSurvivalWeight_congr _ _ who 0 switch fun offset hoffset => ?_
  rw [Nat.zero_add]
  exact quittingPhaseSwitchRoots_of_lt plan punish hoffset

/-- **The deviator cannot outlive the opponents.**  However player `who`
deviates over the plan phase, the joint survival of the deviated sequence is
at most the plan's own opponent-survival weight for `who`. -/
theorem quittingJointSurvivalWeight_update_le_quittingOpponentSurvivalWeight
    (plan : ℕ → ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool)
    (start fuel : ℕ) :
    quittingJointSurvivalWeight
        (quittingRootSequenceUpdate plan who hazard) start fuel ≤
      quittingOpponentSurvivalWeight plan who start fuel := by
  refine (quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
    (quittingRootSequenceUpdate plan who hazard) who start fuel).trans_eq ?_
  exact quittingOpponentSurvivalWeight_quittingRootSequenceUpdate plan who hazard
    start fuel

/-! ## The live-hazard collapse, in the direction hypotheses are checked -/

/-- Every hazard sequence is realised by a behaviour strategy, and its
root-sequence value is that strategy's terminal payoff.  This is the converse
of the live-hazard collapse: it lets a hypothesis stated for hazards be
discharged by a statement about behaviour strategies, and conversely. -/
theorem quittingRootSequenceHazardTerminalValue_eq_terminalPayoff_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 =
      quittingTerminalPayoff reward
        (Function.update (quittingRootSequenceProfile reward roots 0) who
          (fun time _history => hazard time)) who := by
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  rfl

/-! ## Bounding the two phase values -/

omit [DecidableEq ι] in
/-- Under a uniform reward bound every root-sequence terminal value is
bounded by the same constant. -/
theorem abs_quittingRootSequenceTerminalValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound) :
    |quittingRootSequenceTerminalValue reward roots who start| ≤ bound :=
  abs_quittingTerminalPayoff_le reward
    (quittingRootSequenceProfile reward roots start) who hbound hreward

/-! ## The cap -/

/-- **The one-sided deviation cap.**  Under a truncated-plan cap
`planError`, a punishment cap `punishCap + punishError`, and an
opponent-survival cap `survivalCap` at the switch stage, every unilateral
hazard deviation against the switched profile gains at most
`planError + survivalCap * (max (punishCap + punishError) 0 + bound)`.

Hypotheses (a) and (b) are stated for arbitrary hazard sequences, which by
`quittingRootSequenceHazardTerminalValue_eq_terminalPayoff_update` is exactly
the same as stating them for arbitrary behaviour strategies. -/
theorem quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    {planError punishError punishCap survivalCap bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hplan : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan switch) who g 0 ≤
        quittingRootSequenceTerminalValue reward
          (quittingTruncatedRoots plan switch) who 0 + planError)
    (hpunish : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        punishCap + punishError)
    (hsurvival : quittingOpponentSurvivalWeight plan who 0 switch ≤ survivalCap)
    (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who hazard 0 ≤
      quittingRootSequenceTerminalValue reward
          (quittingPhaseSwitchRoots plan punish switch) who 0 +
        planError +
        survivalCap * (max (punishCap + punishError) 0 + bound) := by
  set planValue := quittingRootSequenceTerminalValue reward
    (quittingTruncatedRoots plan switch) who 0 with hplanValue
  set punishValue := quittingRootSequenceTerminalValue reward punish who 0
    with hpunishValue
  set deviatedSurvival := quittingJointSurvivalWeight
    (quittingRootSequenceUpdate plan who hazard) 0 switch with hdeviatedSurvival
  set prescribedSurvival := quittingJointSurvivalWeight plan 0 switch
    with hprescribedSurvival
  -- The two exact decompositions.
  have hdeviated := quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots
    reward plan punish switch who hazard
  have hprescribed := quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots
    reward plan punish switch who
  -- Survival bookkeeping.
  have hdeviatedNonneg : 0 ≤ deviatedSurvival :=
    quittingJointSurvivalWeight_nonneg _ 0 switch
  have hprescribedNonneg : 0 ≤ prescribedSurvival :=
    quittingJointSurvivalWeight_nonneg _ 0 switch
  have hdeviatedLe : deviatedSurvival ≤ survivalCap :=
    (quittingJointSurvivalWeight_update_le_quittingOpponentSurvivalWeight
      plan who hazard 0 switch).trans hsurvival
  have hprescribedLe : prescribedSurvival ≤ survivalCap :=
    (quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight plan who 0
      switch).trans hsurvival
  have hcapNonneg : 0 ≤ survivalCap := hdeviatedNonneg.trans hdeviatedLe
  -- The punishment-phase and plan-phase estimates.
  have hpunishDeviation :
      quittingRootSequenceHazardTerminalValue reward punish who
          (fun offset => hazard (switch + offset)) 0 ≤
        max (punishCap + punishError) 0 :=
    (hpunish _).trans (le_max_left _ _)
  have hplanDeviation :
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan switch) who
          (quittingTruncatedHazard hazard switch) 0 ≤ planValue + planError :=
    hplan _
  have hpunishValueBound : |punishValue| ≤ bound :=
    abs_quittingRootSequenceTerminalValue_le reward punish who 0 hbound hreward
  -- Assemble.
  have hpunishTerm :
      deviatedSurvival *
          quittingRootSequenceHazardTerminalValue reward punish who
            (fun offset => hazard (switch + offset)) 0 ≤
        survivalCap * max (punishCap + punishError) 0 := by
    refine (mul_le_mul_of_nonneg_left hpunishDeviation hdeviatedNonneg).trans ?_
    exact mul_le_mul_of_nonneg_right hdeviatedLe (le_max_right _ _)
  have hprescribedTerm :
      -(prescribedSurvival * punishValue) ≤ survivalCap * bound := by
    have hneg : -punishValue ≤ bound := (neg_le_abs punishValue).trans hpunishValueBound
    calc -(prescribedSurvival * punishValue) = prescribedSurvival * (-punishValue) := by
          ring
      _ ≤ prescribedSurvival * bound :=
          mul_le_mul_of_nonneg_left hneg hprescribedNonneg
      _ ≤ survivalCap * bound := mul_le_mul_of_nonneg_right hprescribedLe hbound
  rw [hdeviated, hprescribed]
  nlinarith [hplanDeviation, hpunishTerm, hprescribedTerm]

/-- **The cap against an arbitrary behaviour deviation.**  The deviator is a
full behaviour strategy; the live-hazard collapse
(`quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue`) reduces
it to the hazard sequence it plays along the unique live public history, and
the hazard-level cap applies verbatim. -/
theorem quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    {planError punishError punishCap survivalCap bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hplan : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan switch) who g 0 ≤
        quittingRootSequenceTerminalValue reward
          (quittingTruncatedRoots plan switch) who 0 + planError)
    (hpunish : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        punishCap + punishError)
    (hsurvival : quittingOpponentSurvivalWeight plan who 0 switch ≤ survivalCap)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update (quittingPhaseSwitchProfile reward plan punish switch)
          who deviation) who ≤
      quittingTerminalPayoff reward
          (quittingPhaseSwitchProfile reward plan punish switch) who +
        planError +
        survivalCap * (max (punishCap + punishError) 0 + bound) := by
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingProfileLiveRoot_quittingPhaseSwitchProfile]
  exact quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le
    reward plan punish switch who hbound hreward hplan hpunish hsurvival
    (quittingBehaviorLiveHazard reward deviation)

/-! ## The consumer statements -/

/-- **The terminal approximate-Nash consumer statement.**  With the plan
cap, the punishment cap and the survival cap in force for *every* player,
the phase-switched profile is a terminal `ε`-Nash equilibrium for any `ε`
dominating the assembled per-player caps.

The punishment cap `punishCap` is allowed to vary with the player, as it
must: it is that player's hypothesised punishment level. -/
theorem isεAsymptoticNash_quittingPhaseSwitchProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ)
    {planError punishError survivalCap bound ε : ℝ} {punishCap : ι → ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hplan : ∀ (who : ι) (g : ℕ → PMF Bool),
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan switch) who g 0 ≤
        quittingRootSequenceTerminalValue reward
          (quittingTruncatedRoots plan switch) who 0 + planError)
    (hpunish : ∀ (who : ι) (g : ℕ → PMF Bool),
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        punishCap who + punishError)
    (hsurvival : ∀ who : ι,
      quittingOpponentSurvivalWeight plan who 0 switch ≤ survivalCap)
    (hε : ∀ who : ι,
      planError + survivalCap * (max (punishCap who + punishError) 0 + bound) ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
      (quittingPhaseSwitchProfile reward plan punish switch) := by
  intro who deviation
  have hcap := quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le
    reward plan punish switch who hbound hreward (hplan who) (hpunish who)
    (hsurvival who) deviation
  have hεwho := hε who
  linarith

/-- **The uniform approximate-equilibrium consumer statement.**  Feeding the
terminal cap into the tree's terminal-to-uniform selection makes the
phase-switched profiles the first existence engine here that is neither
stationary nor cyclic: any punishment bound, once supplied, yields uniform
`ε'`-equilibria. -/
theorem isUniformεEquilibrium_quittingPhaseSwitchProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ)
    {planError punishError survivalCap bound ε ε' : ℝ} {punishCap : ι → ℝ}
    (herror : ε < ε')
    (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hplan : ∀ (who : ι) (g : ℕ → PMF Bool),
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan switch) who g 0 ≤
        quittingRootSequenceTerminalValue reward
          (quittingTruncatedRoots plan switch) who 0 + planError)
    (hpunish : ∀ (who : ι) (g : ℕ → PMF Bool),
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        punishCap who + punishError)
    (hsurvival : ∀ who : ι,
      quittingOpponentSurvivalWeight plan who 0 switch ≤ survivalCap)
    (hε : ∀ who : ι,
      planError + survivalCap * (max (punishCap who + punishError) 0 + bound) ≤ ε) :
    (quittingGame reward).IsUniformεEquilibrium none ε'
      (quittingPhaseSwitchProfile reward plan punish switch) :=
  quittingGame_isUniformεEquilibrium_of_terminalNash_finite reward _ herror
    (isεAsymptoticNash_quittingPhaseSwitchProfile reward plan punish switch
      hbound hreward hplan hpunish hsurvival hε)

/-! ## Choosing the switch stage -/

/-- **The switch clock.**  If every player's opponent-survival curve along
the plan vanishes, then for every positive survival cap some fixed stage
meets hypothesis (c) simultaneously for all players.

This is the absorption clock the cap consumes.  It is *not*
`quittingPlannedSurvivalStoppingIndex`: that index is the first crossing of
a single player's own *prescribed* survival curve, which the deviator
controls and can therefore refuse to follow.  Hypothesis (c) has to be
carried by the opponents' curve, which a unilateral deviation cannot move
(`quittingOpponentSurvivalWeight_quittingRootSequenceUpdate`). -/
theorem exists_quittingPhaseSwitchStage_of_tendsto_zero
    (plan : ℕ → ι → PMF Bool) {survivalCap : ℝ} (hcap : 0 < survivalCap)
    (hplan : ∀ who : ι,
      Tendsto (quittingOpponentSurvivalWeight plan who 0) atTop (nhds 0)) :
    ∃ switch : ℕ, ∀ who : ι,
      quittingOpponentSurvivalWeight plan who 0 switch ≤ survivalCap := by
  have hcrossing : ∀ who : ι, ∃ stage : ℕ, ∀ fuel : ℕ, stage ≤ fuel →
      quittingOpponentSurvivalWeight plan who 0 fuel < survivalCap := by
    intro who
    exact eventually_atTop.1 ((tendsto_order.1 (hplan who)).2 survivalCap hcap)
  choose stage hstage using hcrossing
  refine ⟨Finset.univ.sup stage, fun who => ?_⟩
  exact (hstage who (Finset.univ.sup stage)
    (Finset.le_sup (Finset.mem_univ who))).le

end GameTheory
