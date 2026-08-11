/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCoalitionToggleDeletion
import UniformEquilibrium.Quitting.AbsorptionPath.CollisionConcentration
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailLimits
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchDeviationCap
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing

/-!
# Approximate deletion from a diffuse opponent clock

Exact coalition-toggle deletion assumes that inserting the distinguished
player into every nonempty opponent coalition is weakly unprofitable.  This
file keeps only the singleton insertion inequalities.  The missing
higher-rank inequalities are then charged to the probability that at least
two opponents quit simultaneously.

The charge is computed after forcing the distinguished player to Continue,
so it is fixed by the opponents and is unchanged by an arbitrary unilateral
behavioral deviation.  Pure-time extremality can therefore upgrade the
resulting deterministic-stopping estimates without introducing a
deviation-dependent clock.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The owner weakly loses by joining every singleton opponent coalition. -/
def QuittingOwnerSingletonJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : Prop :=
  ∀ other, other ≠ owner →
    reward
        ⟨{owner, other}, by simp⟩ owner ≤
      reward (quittingSingletonTerminal other) owner

omit [Fintype ι] in
/-- Full coalition antitonicity implies its singleton restriction. -/
theorem QuittingOwnerJoinAntitone.singleton
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {owner : ι}
    (hjoin : QuittingOwnerJoinAntitone reward owner) :
    QuittingOwnerSingletonJoinAntitone reward owner := by
  intro other hother
  have howner : owner ∉ ({other} : Finset ι) := by
    simp [Ne.symm hother]
  simpa [quittingSingletonTerminal, Finset.pair_comm] using
    hjoin ({other} : Finset ι) (by simp) howner

/-- With the owner continuing, a zero- or one-opponent outcome has
nonnegative Continue-minus-join advantage under singleton antitonicity. -/
theorem quittingTerminalOpponentAdvantage_nonneg_of_singletonJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hjoin : QuittingOwnerSingletonJoinAntitone reward owner)
    (action : ι → Bool) (howner : action owner = false)
    (hsmall : (quittingQuitters action).card ≤ 1) :
    0 ≤ quittingTerminalOpponentAdvantage reward owner action := by
  by_cases hquitters : (quittingQuitters action).Nonempty
  · have hcard : (quittingQuitters action).card = 1 := by
      have hpositive := Finset.card_pos.mpr hquitters
      omega
    obtain ⟨other, hotherSet⟩ := Finset.card_eq_one.mp hcard
    have hother : other ≠ owner := by
      intro heq
      subst other
      have : owner ∈ quittingQuitters action := by simp [hotherSet]
      simp [quittingQuitters, howner] at this
    unfold quittingTerminalOpponentAdvantage quittingRootPayoff
    rw [quittingQuitters_update_true_of_apply_false action owner,
      dif_pos hquitters,
      dif_pos (Finset.insert_nonempty owner (quittingQuitters action))]
    have hterminalBefore :
        (⟨quittingQuitters action, hquitters⟩ :
            {S : Finset ι // S.Nonempty}) =
          quittingSingletonTerminal other := by
      apply Subtype.ext
      exact hotherSet
    have hterminalAfter :
        (⟨insert owner (quittingQuitters action),
            Finset.insert_nonempty owner (quittingQuitters action)⟩ :
            {S : Finset ι // S.Nonempty}) =
          ⟨{owner, other}, by simp⟩ := by
      apply Subtype.ext
      simp [hotherSet]
    rw [hterminalBefore, hterminalAfter]
    exact sub_nonneg.mpr (hjoin other hother)
  · rw [quittingTerminalOpponentAdvantage_eq_zero_of_quitters_not_nonempty
      reward owner action hquitters]

/-- The terminal advantage is zero on actions at which the owner is already
set to Quit.  Such actions have zero mass under the forced-Continue law, but
the pointwise fact is convenient for expectation monotonicity. -/
theorem quittingTerminalOpponentAdvantage_eq_zero_of_owner_eq_true
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (action : ι → Bool) (howner : action owner = true) :
    quittingTerminalOpponentAdvantage reward owner action = 0 := by
  have hnonempty : (quittingQuitters action).Nonempty :=
    (quittingQuitters_nonempty_iff action).2 ⟨owner, howner⟩
  have hupdate : Function.update action owner true = action := by
    funext who
    by_cases hwho : who = owner
    · subst who
      simp [howner]
    · simp [Function.update_of_ne hwho]
  unfold quittingTerminalOpponentAdvantage quittingRootPayoff
  rw [dif_pos hnonempty, hupdate, dif_pos hnonempty]
  ring

/-- The expectation of the indicator of a multi-quitter outcome is the
product root's collision mass. -/
theorem expect_quittingCollisionIndicator_eq_collisionMass
    (root : ι → PMF Bool) :
    expect (pmfPi root) (fun action ↦
        if 2 ≤ (quittingQuitters action).card then (1 : ℝ) else 0) =
      quittingRootCollisionMass root := by
  classical
  have hroot :
      (fun i => if i ∈ Finset.univ then root i else PMF.pure false) = root := by
    funext i
    simp
  rw [← hroot]
  rw [expect_pmfPi_boolFamily_eq_sum_powerset'
    (t := Finset.univ) (q := root) (rest := fun _ => false)
    (k := fun action =>
      if 2 ≤ (quittingQuitters action).card then (1 : ℝ) else 0)]
  simp only [Finset.mem_univ, if_true, Finset.powerset_univ]
  rw [quittingRootCollisionMass_eq_sum_coalitionMass]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro coalition _
  have hquitters :
      quittingQuitters
          (fun i => if i ∈ coalition then true else false) = coalition := by
    ext i
    simp [quittingQuitters]
  rw [hquitters]
  by_cases hcard : 2 ≤ coalition.card <;>
    simp [hcard, quittingRootCoalitionMass, quittingRootQuitRates,
      coalitionMass, Finset.compl_eq_univ_sdiff]

/-- If every singleton insertion is unprofitable, the owner's entire
positive joining contribution is carried by outcomes with at least two
opponent quitters. -/
theorem quittingOutsiderJoiningContribution_le_two_mul_collisionMass_of_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hjoin : QuittingOwnerSingletonJoinAntitone reward owner) :
    quittingOutsiderJoiningContribution reward root owner ≤
      2 * M * quittingRootCollisionMass
        (Function.update root owner (PMF.pure false)) := by
  let opponentRoot := Function.update root owner (PMF.pure false)
  let advantage := quittingTerminalOpponentAdvantage reward owner
  have hpoint : ∀ action : ι → Bool,
      -advantage action ≤
        2 * M *
          (if 2 ≤ (quittingQuitters action).card then (1 : ℝ) else 0) := by
    intro action
    by_cases howner : action owner = true
    · rw [show advantage action = 0 by
        exact quittingTerminalOpponentAdvantage_eq_zero_of_owner_eq_true
          reward owner action howner]
      by_cases hcollision : 2 ≤ (quittingQuitters action).card <;>
        simp [hcollision, hM]
    · have hownerFalse : action owner = false :=
        Bool.eq_false_of_not_eq_true howner
      by_cases hcollision : 2 ≤ (quittingQuitters action).card
      · simp only [if_pos hcollision, mul_one]
        exact (neg_le_abs (advantage action)).trans
          (abs_quittingTerminalOpponentAdvantage_le_two_mul
            reward owner action hM hreward)
      · have hsmall : (quittingQuitters action).card ≤ 1 := by omega
        have hadvantage : 0 ≤ advantage action :=
          quittingTerminalOpponentAdvantage_nonneg_of_singletonJoinAntitone
            reward owner hjoin action hownerFalse hsmall
        simp only [if_neg hcollision, mul_zero]
        linarith
  have hmono := expect_mono (pmfPi opponentRoot)
    (fun action ↦ -advantage action)
    (fun action ↦ 2 * M *
      (if 2 ≤ (quittingQuitters action).card then (1 : ℝ) else 0)) hpoint
  have hleft :
      expect (pmfPi opponentRoot) (fun action ↦ -advantage action) =
        -expect (pmfPi opponentRoot) advantage := by
    rw [show (fun action ↦ -advantage action) =
        fun action ↦ (-1 : ℝ) * advantage action by
          funext action
          ring,
      expect_const_mul]
    ring
  have hright :
      expect (pmfPi opponentRoot) (fun action ↦ 2 * M *
          (if 2 ≤ (quittingQuitters action).card then (1 : ℝ) else 0)) =
        2 * M * quittingRootCollisionMass opponentRoot := by
    rw [expect_const_mul,
      expect_quittingCollisionIndicator_eq_collisionMass]
  unfold quittingOutsiderJoiningContribution
  change -expect (pmfPi opponentRoot) advantage ≤ _
  rw [← hleft, ← hright]
  exact hmono

/-- One-row approximate version of the Q175 ride inequality.  The only
error is the collision mass among opponents after deleting the owner. -/
theorem quittingPunishmentValue_ride_le_add_collision_of_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hjoin : QuittingOwnerSingletonJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (time : ℕ) :
    (1 - quittingFixedOpponentsContinueMass roots owner time) *
        quittingPunishmentValue reward owner ≤
      quittingFixedOpponentsContinueReward reward roots owner time +
        2 * M * quittingRootCollisionMass
          (Function.update (roots time) owner (PMF.pure false)) := by
  let root := roots time
  let mass := quittingFixedOpponentsContinueMass roots owner time
  let absorb := quittingFixedOpponentsContinueReward reward roots owner time
  let quitValue := quittingFixedOpponentsQuitValue reward roots owner time
  let solo := reward (quittingSingletonTerminal owner) owner
  let chi := quittingPunishmentValue reward owner
  let error := 2 * M * quittingRootCollisionMass
    (Function.update root owner (PMF.pure false))
  have hmass0 : 0 ≤ mass :=
    quittingFixedOpponentsContinueMass_nonneg roots owner time
  have hmass1 : mass ≤ 1 :=
    quittingFixedOpponentsContinueMass_le_one roots owner time
  have hjoining :=
    quittingOutsiderJoiningContribution_le_two_mul_collisionMass_of_singleton
      reward root owner hM hreward hjoin
  have hendpoint :=
    quittingRootEndpointDifference_eq_outsiderNever reward
      (fun _ => solo) root owner
  have hquit : quitValue ≤ absorb + mass * solo + error := by
    change quittingRootEndpointDifference reward (fun _ => solo) root owner =
        (1 - quittingRootAbsorptionMass
            (Function.update root owner (PMF.pure false))) *
          (solo - solo) +
            quittingOutsiderJoiningContribution reward root owner
      at hendpoint
    rw [quittingRootEndpointDifference,
      quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward roots owner (fun _ => solo) time,
      quittingRootContinuePayoff_eq_fixedOpponents
        reward roots owner (fun _ => solo) time] at hendpoint
    dsimp only [root, mass, absorb, quitValue, solo] at hendpoint
    dsimp only [error, root]
    linarith
  have herror0 : 0 ≤ error := by
    dsimp only [error]
    exact mul_nonneg (by positivity) (quittingRootCollisionMass_nonneg _)
  have hcap : chi ≤ max quitValue (absorb / (1 - mass)) := by
    have h := quittingPunishmentValue_le_stationaryUnilateralCap
      reward owner root
    rw [quittingStationaryUnilateralCap_eq_max_div,
      quittingStationaryFixedOpponentsQuitValue_apply,
      quittingStationaryFixedOpponentsContinueReward_apply,
      quittingStationaryFixedOpponentsContinueMass_apply] at h
    exact h
  by_cases hone : mass = 1
  · have habsorb : absorb = 0 := by
      dsimp only [absorb, mass, root]
      exact
        quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
          reward hone
    change (1 - mass) * chi ≤ absorb + error
    rw [hone, habsorb]
    simpa using herror0
  · have hmasslt : mass < 1 := lt_of_le_of_ne hmass1 hone
    have hdenom : 0 < 1 - mass := by linarith
    by_contra hnot
    have habsorbErrorLt : absorb + error < (1 - mass) * chi :=
      lt_of_not_ge hnot
    have habsorbLt : absorb < (1 - mass) * chi := by linarith
    have hratio : absorb / (1 - mass) < chi := by
      rw [div_lt_iff₀ hdenom]
      simpa [mul_comm] using habsorbLt
    have hquitLt : quitValue < chi := by
      change solo < chi at hsolo
      nlinarith
    have hmaxLt : max quitValue (absorb / (1 - mass)) < chi :=
      max_lt hquitLt hratio
    exact (not_lt_of_ge hcap) hmaxLt

/-- Survival-weighted higher-rank insertion error on a finite opponent
window. -/
def quittingOwnerCollisionErrorAccum
    (roots : ℕ → ι → PMF Bool) (owner : ι) (M : ℝ)
    (start fuel : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range fuel,
    quittingOpponentSurvivalWeight roots owner start offset *
      (2 * M * quittingRootCollisionMass
        (Function.update (roots (start + offset)) owner (PMF.pure false)))

@[simp] theorem quittingOwnerCollisionErrorAccum_zero
    (roots : ℕ → ι → PMF Bool) (owner : ι) (M : ℝ) (start : ℕ) :
    quittingOwnerCollisionErrorAccum roots owner M start 0 = 0 := by
  simp [quittingOwnerCollisionErrorAccum]

/-- Peeling one row from the collision-error ledger. -/
theorem quittingOwnerCollisionErrorAccum_shift
    (roots : ℕ → ι → PMF Bool) (owner : ι) (M : ℝ)
    (start fuel : ℕ) :
    quittingOwnerCollisionErrorAccum roots owner M start (fuel + 1) =
      2 * M * quittingRootCollisionMass
          (Function.update (roots start) owner (PMF.pure false)) +
        quittingFixedOpponentsContinueMass roots owner start *
          quittingOwnerCollisionErrorAccum roots owner M (start + 1) fuel := by
  unfold quittingOwnerCollisionErrorAccum
  rw [Finset.sum_range_succ']
  have hzero : quittingOpponentSurvivalWeight roots owner start 0 *
      (2 * M * quittingRootCollisionMass
        (Function.update (roots (start + 0)) owner (PMF.pure false))) =
      2 * M * quittingRootCollisionMass
        (Function.update (roots start) owner (PMF.pure false)) := by
    simp [quittingOpponentSurvivalWeight]
  rw [hzero, Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro offset _
  rw [quittingOpponentSurvivalWeight_shift,
    show start + (offset + 1) = start + 1 + offset by omega]
  ring

/-- Collision-error ledgers concatenate with the deleted-player survival
factor. -/
theorem quittingOwnerCollisionErrorAccum_add
    (roots : ℕ → ι → PMF Bool) (owner : ι) (M : ℝ)
    (start first second : ℕ) :
    quittingOwnerCollisionErrorAccum roots owner M start (first + second) =
      quittingOwnerCollisionErrorAccum roots owner M start first +
        quittingOpponentSurvivalWeight roots owner start first *
          quittingOwnerCollisionErrorAccum roots owner M (start + first)
            second := by
  unfold quittingOwnerCollisionErrorAccum
  rw [Finset.sum_range_add, Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro offset _
  rw [quittingOpponentSurvivalWeight_add]
  simp only [Nat.add_assoc]
  ring

/-- The finite collision-error ledger is nonnegative. -/
theorem quittingOwnerCollisionErrorAccum_nonneg
    (roots : ℕ → ι → PMF Bool) (owner : ι) {M : ℝ} (hM : 0 ≤ M)
    (start fuel : ℕ) :
    0 ≤ quittingOwnerCollisionErrorAccum roots owner M start fuel := by
  unfold quittingOwnerCollisionErrorAccum
  apply Finset.sum_nonneg
  intro offset _
  exact mul_nonneg
    (quittingOpponentSurvivalWeight_nonneg roots owner start offset)
    (mul_nonneg (by positivity) (quittingRootCollisionMass_nonneg _))

/-- One survival-weighted collision charge is contained in the prefix error
ledger ending just after that row. -/
theorem weighted_ownerCollisionError_le_accum_succ
    (roots : ℕ → ι → PMF Bool) (owner : ι) {M : ℝ} (hM : 0 ≤ M)
    (time : ℕ) :
    quittingOpponentSurvivalWeight roots owner 0 time *
        (2 * M * quittingRootCollisionMass
          (Function.update (roots time) owner (PMF.pure false))) ≤
      quittingOwnerCollisionErrorAccum roots owner M 0 (time + 1) := by
  unfold quittingOwnerCollisionErrorAccum
  rw [Finset.sum_range_succ]
  have hprefix : 0 ≤ ∑ offset ∈ Finset.range time,
      quittingOpponentSurvivalWeight roots owner 0 offset *
        (2 * M * quittingRootCollisionMass
          (Function.update (roots (0 + offset)) owner (PMF.pure false))) := by
    apply Finset.sum_nonneg
    intro offset _
    exact mul_nonneg
      (quittingOpponentSurvivalWeight_nonneg roots owner 0 offset)
      (mul_nonneg (by positivity) (quittingRootCollisionMass_nonneg _))
  simp only [Nat.zero_add] at hprefix ⊢
  linarith

/-- The owner-deleted absorption clock has the usual exact finite survival
telescope. -/
theorem sum_opponentSurvival_mul_opponentAbsorption
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ) :
    ∀ fuel,
      (∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots owner start offset *
          (1 - quittingFixedOpponentsContinueMass roots owner
            (start + offset))) =
        1 - quittingOpponentSurvivalWeight roots owner start fuel := by
  intro fuel
  induction fuel with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      rw [Finset.sum_range_succ, ih,
        quittingOpponentSurvivalWeight_succ]
      ring

/-- A uniform deleted-clock mesh bounds every finite collision-error prefix.
The constant is the product-law pair count. -/
theorem quittingOwnerCollisionErrorAccum_le_of_opponentAbsorptionMesh
    (roots : ℕ → ι → PMF Bool) (owner : ι) {M mesh : ℝ}
    (hM : 0 ≤ M) (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ time,
      quittingRootAbsorptionMass
          (Function.update (roots time) owner (PMF.pure false)) ≤ mesh)
    (horizon : ℕ) :
    quittingOwnerCollisionErrorAccum roots owner M 0 horizon ≤
      2 * M * ((Fintype.card ι).choose 2 : ℝ) * mesh := by
  let pairCount : ℝ := ((Fintype.card ι).choose 2 : ℝ)
  have hrow : ∀ time,
      2 * M * quittingRootCollisionMass
          (Function.update (roots time) owner (PMF.pure false)) ≤
        (2 * M * pairCount * mesh) *
          (1 - quittingFixedOpponentsContinueMass roots owner time) := by
    intro time
    let deleted := Function.update (roots time) owner (PMF.pure false)
    let absorption := quittingRootAbsorptionMass deleted
    have habsorption0 : 0 ≤ absorption :=
      quittingRootAbsorptionMass_nonneg deleted
    have habsorptionMesh : absorption ≤ mesh := hmesh time
    have hcollision :=
      quittingRootCollisionMass_le_choose_card_mul_absorption_sq deleted
    have hsquare : absorption ^ 2 ≤ mesh * absorption := by
      nlinarith
    have hpair0 : 0 ≤ pairCount := by positivity
    have hcollisionMesh :
        quittingRootCollisionMass deleted ≤ pairCount * mesh * absorption := by
      calc
        quittingRootCollisionMass deleted ≤ pairCount * absorption ^ 2 := by
          simpa [pairCount] using hcollision
        _ ≤ pairCount * (mesh * absorption) :=
          mul_le_mul_of_nonneg_left hsquare hpair0
        _ = pairCount * mesh * absorption := by ring
    have hscale : 0 ≤ 2 * M := by positivity
    have := mul_le_mul_of_nonneg_left hcollisionMesh hscale
    calc
      2 * M * quittingRootCollisionMass
            (Function.update (roots time) owner (PMF.pure false)) ≤
          2 * M * (pairCount * mesh * absorption) := by
        simpa [deleted] using this
      _ = (2 * M * pairCount * mesh) *
          (1 - quittingFixedOpponentsContinueMass roots owner time) := by
        dsimp only [absorption, deleted, pairCount]
        unfold quittingRootAbsorptionMass
        dsimp only [quittingFixedOpponentsContinueMass]
        ring
  have hsum : quittingOwnerCollisionErrorAccum roots owner M 0 horizon ≤
      ∑ offset ∈ Finset.range horizon,
        quittingOpponentSurvivalWeight roots owner 0 offset *
          ((2 * M * pairCount * mesh) *
            (1 - quittingFixedOpponentsContinueMass roots owner offset)) := by
    unfold quittingOwnerCollisionErrorAccum
    apply Finset.sum_le_sum
    intro offset _
    have hsurvival0 :=
      quittingOpponentSurvivalWeight_nonneg roots owner 0 offset
    have hscaled := mul_le_mul_of_nonneg_left (hrow offset) hsurvival0
    simpa using hscaled
  have htelescope :=
    sum_opponentSurvival_mul_opponentAbsorption roots owner 0 horizon
  simp only [Nat.zero_add] at htelescope
  have hcoefficient0 : 0 ≤ 2 * M * pairCount * mesh := by positivity
  have hsurvival0 :=
    quittingOpponentSurvivalWeight_nonneg roots owner 0 horizon
  calc
    quittingOwnerCollisionErrorAccum roots owner M 0 horizon ≤
        ∑ offset ∈ Finset.range horizon,
          quittingOpponentSurvivalWeight roots owner 0 offset *
            ((2 * M * pairCount * mesh) *
              (1 - quittingFixedOpponentsContinueMass roots owner offset)) :=
      hsum
    _ = (2 * M * pairCount * mesh) *
          (1 - quittingOpponentSurvivalWeight roots owner 0 horizon) := by
      calc
        (∑ offset ∈ Finset.range horizon,
            quittingOpponentSurvivalWeight roots owner 0 offset *
              ((2 * M * pairCount * mesh) *
                (1 - quittingFixedOpponentsContinueMass roots owner offset))) =
            ∑ offset ∈ Finset.range horizon,
              (2 * M * pairCount * mesh) *
                (quittingOpponentSurvivalWeight roots owner 0 offset *
                  (1 - quittingFixedOpponentsContinueMass roots owner offset)) := by
          apply Finset.sum_congr rfl
          intro offset _
          ring
        _ = (2 * M * pairCount * mesh) *
            (∑ offset ∈ Finset.range horizon,
              quittingOpponentSurvivalWeight roots owner 0 offset *
                (1 - quittingFixedOpponentsContinueMass roots owner offset)) := by
          rw [Finset.mul_sum]
        _ = _ := by rw [htelescope]
    _ ≤ 2 * M * pairCount * mesh := by
      nlinarith
    _ = 2 * M * ((Fintype.card ι).choose 2 : ℝ) * mesh := by
      rfl

/-- Perturbed live-ledger account.  Compared with the exact Q175 ledger,
the survival-weighted opponent-collision error is the only extra term. -/
theorem le_quittingLiveLedgerAccum_add_collisionError_add_survival_mul_from
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (target M : ℝ) :
    ∀ (start fuel : ℕ),
      (∀ offset < fuel,
        (1 - quittingFixedOpponentsContinueMass roots owner
            (start + offset)) * target ≤
          quittingFixedOpponentsContinueReward reward roots owner
              (start + offset) +
            2 * M * quittingRootCollisionMass
              (Function.update (roots (start + offset)) owner
                (PMF.pure false))) →
      target ≤ quittingLiveLedgerAccum reward roots owner start fuel +
        quittingOwnerCollisionErrorAccum roots owner M start fuel +
        quittingOpponentSurvivalWeight roots owner start fuel * target := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro _
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      intro hride
      have hstep := hride 0 (by omega)
      simp only [Nat.add_zero] at hstep
      have htail : ∀ offset < fuel,
          (1 - quittingFixedOpponentsContinueMass roots owner
              (start + 1 + offset)) * target ≤
            quittingFixedOpponentsContinueReward reward roots owner
                (start + 1 + offset) +
              2 * M * quittingRootCollisionMass
                (Function.update (roots (start + 1 + offset)) owner
                  (PMF.pure false)) := by
        intro offset hoffset
        have htime : start + (offset + 1) = start + 1 + offset := by omega
        rw [← htime]
        exact hride (offset + 1) (by omega)
      have hih := ih (start + 1) htail
      have hmass0 :=
        quittingFixedOpponentsContinueMass_nonneg roots owner start
      have hscaled := mul_le_mul_of_nonneg_left hih hmass0
      rw [quittingLiveLedgerAccum_shift,
        quittingOwnerCollisionErrorAccum_shift,
        quittingOpponentSurvivalWeight_shift]
      nlinarith

/-- Finite-horizon boundary form of approximate deletion.  The punishment
floor can fail for the literal `Never` payoff only through accumulated
opponent collisions or through the surviving boundary discrepancy. -/
theorem quittingPunishmentValue_sub_neverTail_le_collisionError_add_boundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hjoin : QuittingOwnerSingletonJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (start fuel : ℕ) :
    quittingPunishmentValue reward owner -
        quittingRootSequencePureTimeTerminalValue reward roots owner none start ≤
      quittingOwnerCollisionErrorAccum roots owner M start fuel +
        quittingOpponentSurvivalWeight roots owner start fuel *
          (quittingPunishmentValue reward owner -
            quittingRootSequencePureTimeTerminalValue reward roots owner none
              (start + fuel)) := by
  have haccount :=
    le_quittingLiveLedgerAccum_add_collisionError_add_survival_mul_from
      reward roots owner (quittingPunishmentValue reward owner) M start fuel
      (fun offset _ =>
        quittingPunishmentValue_ride_le_add_collision_of_singleton
          reward roots owner hjoin hsolo hM hreward (start + offset))
  rw [quittingRootSequencePureTimeTerminalValue_none_eq_ledger_add_tail
    reward roots owner start fuel]
  linarith

/-- Complete deleted-player survival kills the far punishment boundary.  No
punishment-floor statement is assumed for any conditioned suffix: boundedness
of the punishment value and of literal terminal values is enough. -/
theorem tendsto_opponentSurvival_mul_punishment_sub_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hchi : |quittingPunishmentValue reward owner| ≤ M)
    (hcomplete : Tendsto
      (quittingOpponentSurvivalWeight roots owner 0) atTop (nhds 0)) :
    Tendsto (fun horizon =>
      quittingOpponentSurvivalWeight roots owner 0 horizon *
        (quittingPunishmentValue reward owner -
          quittingRootSequencePureTimeTerminalValue reward roots owner none
            horizon)) atTop (nhds 0) := by
  have hvalue : ∀ horizon,
      |quittingRootSequencePureTimeTerminalValue reward roots owner none
          horizon| ≤ M := by
    intro horizon
    unfold quittingRootSequencePureTimeTerminalValue
    exact abs_quittingRootSequenceTerminalValue_le reward
      (quittingRootSequenceUpdate roots owner (quittingPureTimeHazard none))
      owner horizon hM hreward
  have hdifference : ∀ horizon,
      |quittingPunishmentValue reward owner -
          quittingRootSequencePureTimeTerminalValue reward roots owner none
            horizon| ≤ 2 * M := by
    intro horizon
    calc
      |quittingPunishmentValue reward owner -
          quittingRootSequencePureTimeTerminalValue reward roots owner none
            horizon| ≤
          |quittingPunishmentValue reward owner| +
            |quittingRootSequencePureTimeTerminalValue reward roots owner none
              horizon| := abs_sub _ _
      _ ≤ M + M := add_le_add hchi (hvalue horizon)
      _ = 2 * M := by ring
  have hscale : Tendsto
      (fun horizon =>
        quittingOpponentSurvivalWeight roots owner 0 horizon * (2 * M))
      atTop (nhds 0) := by
    simpa using hcomplete.mul_const (2 * M)
  refine squeeze_zero_norm' (Eventually.of_forall fun horizon => ?_) hscale
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg
      (quittingOpponentSurvivalWeight_nonneg roots owner 0 horizon)]
  exact mul_le_mul_of_nonneg_left (hdifference horizon)
    (quittingOpponentSurvivalWeight_nonneg roots owner 0 horizon)

/-- **The finite ledger closes the common-tail boundary.**  If the deleted
clock is complete and every global collision prefix costs at most `budget`,
then the survival-weighted punishment-floor shortfall at every intermediate
date costs at most that same budget.  No floor is transported through
conditioning. -/
theorem weighted_punishment_sub_never_le_collisionBudget_of_complete
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hjoin : QuittingOwnerSingletonJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    {M budget : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hchi : |quittingPunishmentValue reward owner| ≤ M)
    (hcomplete : Tendsto
      (quittingOpponentSurvivalWeight roots owner 0) atTop (nhds 0))
    (hbudget : ∀ horizon,
      quittingOwnerCollisionErrorAccum roots owner M 0 horizon ≤ budget)
    (start : ℕ) :
    quittingOpponentSurvivalWeight roots owner 0 start *
        (quittingPunishmentValue reward owner -
          quittingRootSequencePureTimeTerminalValue reward roots owner none
            start) ≤ budget := by
  let chi := quittingPunishmentValue reward owner
  let never : ℕ → ℝ := fun time =>
    quittingRootSequencePureTimeTerminalValue reward roots owner none time
  have hfar := tendsto_opponentSurvival_mul_punishment_sub_never
    reward roots owner hM hreward hchi hcomplete
  have hfarShift : Tendsto (fun fuel =>
      quittingOpponentSurvivalWeight roots owner 0 (start + fuel) *
        (chi - never (start + fuel))) atTop (nhds 0) := by
    apply (hfar.comp (tendsto_add_atTop_nat start)).congr'
    filter_upwards [] with fuel
    simp only [Function.comp_apply, chi, never, Nat.add_comm]
  have hlimit : Tendsto (fun fuel =>
      budget +
        quittingOpponentSurvivalWeight roots owner 0 (start + fuel) *
          (chi - never (start + fuel))) atTop (nhds budget) := by
    simpa using tendsto_const_nhds.add hfarShift
  apply ge_of_tendsto' hlimit
  intro fuel
  have hlocal :=
    quittingPunishmentValue_sub_neverTail_le_collisionError_add_boundary
      reward roots owner hjoin hsolo hM hreward start fuel
  have hprefix0 := quittingOpponentSurvivalWeight_nonneg roots owner 0 start
  have hscaled := mul_le_mul_of_nonneg_left hlocal hprefix0
  ring_nf at hscaled
  have hconcat := quittingOwnerCollisionErrorAccum_add
    roots owner M 0 start fuel
  have hprefixError0 :=
    quittingOwnerCollisionErrorAccum_nonneg roots owner hM 0 start
  have htailBudget :
      quittingOpponentSurvivalWeight roots owner 0 start *
          quittingOwnerCollisionErrorAccum roots owner M start fuel ≤ budget := by
    have hfull := hbudget (start + fuel)
    rw [hconcat] at hfull
    simp only [Nat.zero_add] at hfull
    linarith
  have hsurvivalConcat :=
    quittingOpponentSurvivalWeight_add roots owner 0 start fuel
  dsimp only [chi, never] at hscaled ⊢
  simp only [Nat.zero_add] at hsurvivalConcat
  rw [hsurvivalConcat]
  nlinarith

/-- **Deviation-uniform approximate deletion.**  The first hypothesis prices
the higher-rank owner insertion gain at every possible stopping date.  The
second is the surviving punishment-floor boundary error one date later.
Under singleton antitonicity these two fixed-opponent quantities bound every
behavioral deviation, not merely stationary deviations. -/
theorem quittingBestReplyValue_le_never_add_collision_and_boundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    (hjoin : QuittingOwnerSingletonJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    {M collisionBudget boundaryError : ℝ}
    (hM : 0 ≤ M)
    (hcollisionBudgetNonneg : 0 ≤ collisionBudget)
    (hboundaryErrorNonneg : 0 ≤ boundaryError)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcollisionBudget : ∀ time,
      quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward profile) owner 0 time *
        (2 * M * quittingRootCollisionMass
          (Function.update
            (quittingProfileLiveRoot reward profile time) owner
            (PMF.pure false))) ≤ collisionBudget)
    (hboundary : ∀ time,
      quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward profile) owner 0 (time + 1) *
        (quittingPunishmentValue reward owner -
          quittingRootSequencePureTimeTerminalValue reward
            (quittingProfileLiveRoot reward profile) owner none (time + 1)) ≤
        boundaryError) :
    quittingBestReplyValue reward profile owner ≤
      quittingTerminalPayoff reward
          (Function.update profile owner
            (quittingPureTimeBehaviorStrategy reward owner none)) owner +
        collisionBudget + boundaryError := by
  let roots := quittingProfileLiveRoot reward profile
  let chi := quittingPunishmentValue reward owner
  let never : ℕ → ℝ := fun start =>
    quittingRootSequencePureTimeTerminalValue reward roots owner none start
  have hpure : ∀ quitTime : Option ℕ,
      quittingRootSequencePureTimeTerminalValue reward roots owner quitTime 0 ≤
        never 0 + collisionBudget + boundaryError := by
    intro quitTime
    cases quitTime with
    | none =>
        dsimp only [never]
        linarith
    | some time =>
        let survival := quittingOpponentSurvivalWeight roots owner 0 time
        let mass := quittingFixedOpponentsContinueMass roots owner time
        let error := 2 * M * quittingRootCollisionMass
          (Function.update (roots time) owner (PMF.pure false))
        let quitValue := quittingFixedOpponentsQuitValue reward roots owner time
        let absorb := quittingFixedOpponentsContinueReward reward roots owner time
        let nextNever := never (time + 1)
        have hjoining :=
          quittingOutsiderJoiningContribution_le_two_mul_collisionMass_of_singleton
            reward (roots time) owner hM hreward hjoin
        have hendpoint :=
          quittingRootEndpointDifference_eq_outsiderNever reward
            (fun _ => nextNever) (roots time) owner
        rw [quittingRootEndpointDifference,
          quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
            reward roots owner (fun _ => nextNever) time,
          quittingRootContinuePayoff_eq_fixedOpponents
            reward roots owner (fun _ => nextNever) time] at hendpoint
        have hmassEq :
            1 - quittingRootAbsorptionMass
                (Function.update (roots time) owner (PMF.pure false)) = mass := by
          unfold quittingRootAbsorptionMass
          dsimp only [mass, quittingFixedOpponentsContinueMass]
          ring
        rw [hmassEq] at hendpoint
        have hmass0 : 0 ≤ mass :=
          quittingFixedOpponentsContinueMass_nonneg roots owner time
        have hlocal :
            quitValue - (absorb + mass * nextNever) ≤
              error + mass * (chi - nextNever) := by
          change reward (quittingSingletonTerminal owner) owner < chi at hsolo
          have hsoloScaled :
              mass * (reward (quittingSingletonTerminal owner) owner -
                  nextNever) ≤
                mass * (chi - nextNever) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hmass0
          calc
            quitValue - (absorb + mass * nextNever) =
                mass * (reward (quittingSingletonTerminal owner) owner -
                  nextNever) +
                    quittingOutsiderJoiningContribution reward
                      (roots time) owner := by
              simpa [roots, quitValue, absorb] using hendpoint
            _ ≤ mass * (chi - nextNever) +
                  quittingOutsiderJoiningContribution reward
                    (roots time) owner :=
              add_le_add hsoloScaled le_rfl
            _ ≤ mass * (chi - nextNever) + error := by
              exact add_le_add le_rfl (by simpa [roots, error] using hjoining)
            _ = error + mass * (chi - nextNever) := by ring
        have hsurvival0 : 0 ≤ survival :=
          quittingOpponentSurvivalWeight_nonneg roots owner 0 time
        have hscaled := mul_le_mul_of_nonneg_left hlocal hsurvival0
        ring_nf at hscaled
        have hcollision : survival * error ≤ collisionBudget := by
          simpa [roots, survival, error] using hcollisionBudget time
        have hsurvivalSucc : survival * mass =
            quittingOpponentSurvivalWeight roots owner 0 (time + 1) := by
          simpa [survival, mass] using
            (quittingOpponentSurvivalWeight_succ roots owner 0 time).symm
        have hboundaryTime :
            survival * mass * (chi - nextNever) ≤ boundaryError := by
          rw [hsurvivalSucc]
          simpa [roots, chi, never, nextNever] using hboundary time
        have hsome :=
          quittingRootSequencePureTimeTerminalValue_some_eq
            reward roots owner time
        have hneverSplit :=
          quittingRootSequencePureTimeTerminalValue_none_eq_ledger_add_tail
            reward roots owner 0 time
        have hneverStep :=
          quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents
            reward roots owner time
        dsimp only [never] at hneverStep ⊢
        dsimp only [survival, quitValue, absorb, mass, nextNever] at hscaled hsome hneverSplit
        simp only [Nat.zero_add] at hneverSplit
        rw [hneverStep] at hneverSplit
        linarith
  apply quittingBestReplyValue_le
  intro deviation
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨quitTime, htime⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward profile owner deviation hε
  have hpureTime := hpure quitTime
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy] at htime
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  dsimp only [roots, never] at hpureTime
  linarith

/-- Best-response-debt form of the deviation-uniform estimate, measured
against the literal Never face of the displayed opponents. -/
theorem quittingNeverFaceDebt_le_collision_and_boundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    (hjoin : QuittingOwnerSingletonJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    {M collisionBudget boundaryError : ℝ}
    (hM : 0 ≤ M)
    (hcollisionBudgetNonneg : 0 ≤ collisionBudget)
    (hboundaryErrorNonneg : 0 ≤ boundaryError)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcollisionBudget : ∀ time,
      quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward profile) owner 0 time *
        (2 * M * quittingRootCollisionMass
          (Function.update
            (quittingProfileLiveRoot reward profile time) owner
            (PMF.pure false))) ≤ collisionBudget)
    (hboundary : ∀ time,
      quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward profile) owner 0 (time + 1) *
        (quittingPunishmentValue reward owner -
          quittingRootSequencePureTimeTerminalValue reward
            (quittingProfileLiveRoot reward profile) owner none (time + 1)) ≤
        boundaryError) :
    quittingBestReplyValue reward profile owner -
        quittingTerminalPayoff reward
          (Function.update profile owner
            (quittingPureTimeBehaviorStrategy reward owner none)) owner ≤
      collisionBudget + boundaryError := by
  have h :=
    quittingBestReplyValue_le_never_add_collision_and_boundary
      reward profile owner hjoin hsolo hM hcollisionBudgetNonneg
      hboundaryErrorNonneg hreward hcollisionBudget hboundary
  linarith

/-- **Complete-clock approximate deletion.**  Singleton owner insertion
antitonicity, a complete owner-deleted clock, and a global collision budget
force the full behavioral Never-face debt below twice that budget.  In a
diffuse family where the collision budget vanishes this gives approximate
deletion; at zero collision budget it gives exact deletion. -/
theorem quittingNeverFaceDebt_le_two_mul_collisionBudget_of_complete
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    (hjoin : QuittingOwnerSingletonJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    {M budget : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hchi : |quittingPunishmentValue reward owner| ≤ M)
    (hcomplete : Tendsto
      (quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) owner 0) atTop (nhds 0))
    (hbudget : ∀ horizon,
      quittingOwnerCollisionErrorAccum
        (quittingProfileLiveRoot reward profile) owner M 0 horizon ≤ budget) :
    quittingBestReplyValue reward profile owner -
        quittingTerminalPayoff reward
          (Function.update profile owner
            (quittingPureTimeBehaviorStrategy reward owner none)) owner ≤
      2 * budget := by
  let roots := quittingProfileLiveRoot reward profile
  have hbudgetNonneg : 0 ≤ budget := by
    have h := hbudget 0
    simpa [quittingOwnerCollisionErrorAccum] using h
  have hcollision : ∀ time,
      quittingOpponentSurvivalWeight roots owner 0 time *
          (2 * M * quittingRootCollisionMass
            (Function.update (roots time) owner (PMF.pure false))) ≤ budget := by
    intro time
    exact (weighted_ownerCollisionError_le_accum_succ
      roots owner hM time).trans (hbudget (time + 1))
  have hboundary : ∀ time,
      quittingOpponentSurvivalWeight roots owner 0 (time + 1) *
          (quittingPunishmentValue reward owner -
            quittingRootSequencePureTimeTerminalValue reward roots owner none
              (time + 1)) ≤ budget := by
    intro time
    exact weighted_punishment_sub_never_le_collisionBudget_of_complete
      reward roots owner hjoin hsolo hM hreward hchi hcomplete hbudget
        (time + 1)
  have hdebt := quittingNeverFaceDebt_le_collision_and_boundary
    reward profile owner hjoin hsolo hM hbudgetNonneg hbudgetNonneg hreward
    hcollision hboundary
  linarith

/-- Mesh-facing form of complete-clock approximate deletion.  A uniform
owner-deleted absorption mesh gives the explicit vanishing debt bound
`4 * M * choose(card ι, 2) * mesh`. -/
theorem quittingNeverFaceDebt_le_four_mul_reward_mul_pairs_mul_mesh
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    (hjoin : QuittingOwnerSingletonJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    {M mesh : ℝ} (hM : 0 ≤ M) (hmesh0 : 0 ≤ mesh)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hchi : |quittingPunishmentValue reward owner| ≤ M)
    (hcomplete : Tendsto
      (quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) owner 0) atTop (nhds 0))
    (hmesh : ∀ time,
      quittingRootAbsorptionMass
          (Function.update (quittingProfileLiveRoot reward profile time) owner
            (PMF.pure false)) ≤ mesh) :
    quittingBestReplyValue reward profile owner -
        quittingTerminalPayoff reward
          (Function.update profile owner
            (quittingPureTimeBehaviorStrategy reward owner none)) owner ≤
      4 * M * ((Fintype.card ι).choose 2 : ℝ) * mesh := by
  have hbudget : ∀ horizon,
      quittingOwnerCollisionErrorAccum
          (quittingProfileLiveRoot reward profile) owner M 0 horizon ≤
        2 * M * ((Fintype.card ι).choose 2 : ℝ) * mesh := by
    intro horizon
    exact quittingOwnerCollisionErrorAccum_le_of_opponentAbsorptionMesh
      (quittingProfileLiveRoot reward profile) owner hM hmesh0 hmesh horizon
  have hdebt :=
    quittingNeverFaceDebt_le_two_mul_collisionBudget_of_complete
      reward profile owner hjoin hsolo hM hreward hchi hcomplete hbudget
  nlinarith

/-- **Exact diffuse deletion on a collision-free complete clock.**  If the
owner-deleted chronology is complete and never realizes two opponent
quitters at once, singleton insertion antitonicity already makes literal
`Never` a full behavioral best response.  Higher-rank payoff-table toggles
are irrelevant because their entire realization measure is zero. -/
theorem quittingNeverFaceDebt_eq_zero_of_complete_collisionFree
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    (hjoin : QuittingOwnerSingletonJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hchi : |quittingPunishmentValue reward owner| ≤ M)
    (hcomplete : Tendsto
      (quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) owner 0) atTop (nhds 0))
    (hcollisionFree : ∀ time,
      quittingRootCollisionMass
        (Function.update
          (quittingProfileLiveRoot reward profile time) owner
          (PMF.pure false)) = 0) :
    quittingBestReplyValue reward profile owner -
        quittingTerminalPayoff reward
          (Function.update profile owner
            (quittingPureTimeBehaviorStrategy reward owner none)) owner = 0 := by
  have hbudget : ∀ horizon,
      quittingOwnerCollisionErrorAccum
        (quittingProfileLiveRoot reward profile) owner M 0 horizon ≤ 0 := by
    intro horizon
    unfold quittingOwnerCollisionErrorAccum
    simp [hcollisionFree]
  have hupper :=
    quittingNeverFaceDebt_le_two_mul_collisionBudget_of_complete
      reward profile owner hjoin hsolo hM hreward hchi hcomplete hbudget
  have hlower := le_quittingBestReplyValue reward profile owner
    (quittingPureTimeBehaviorStrategy reward owner none)
  linarith

omit [Fintype ι] in
/-- Finite singleton dispatcher: either one opponent gives the owner a
strict profitable insertion toggle, or all singleton insertions are
nonpositive. -/
theorem exists_strict_owner_singleton_toggle_or_singletonJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    (∃ other, other ≠ owner ∧
      reward (quittingSingletonTerminal other) owner <
        reward ⟨{owner, other}, by simp⟩ owner) ∨
      QuittingOwnerSingletonJoinAntitone reward owner := by
  by_cases hjoin : QuittingOwnerSingletonJoinAntitone reward owner
  · exact Or.inr hjoin
  · left
    unfold QuittingOwnerSingletonJoinAntitone at hjoin
    push Not at hjoin
    exact hjoin

/-- **Game-facing diffuse deletion dispatcher.**  On a complete deleted
clock with collision budget `budget`, either a literal owner/opponent pair is
a strict atomic insertion toggle, or the owner's full behavioral Never-face
debt is at most `2 * budget`. -/
theorem exists_strict_owner_singleton_toggle_or_neverFaceDebt_le_two_mul_budget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    {M budget : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hchi : |quittingPunishmentValue reward owner| ≤ M)
    (hcomplete : Tendsto
      (quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) owner 0) atTop (nhds 0))
    (hbudget : ∀ horizon,
      quittingOwnerCollisionErrorAccum
        (quittingProfileLiveRoot reward profile) owner M 0 horizon ≤ budget) :
    (∃ other, other ≠ owner ∧
      reward (quittingSingletonTerminal other) owner <
        reward ⟨{owner, other}, by simp⟩ owner) ∨
      quittingBestReplyValue reward profile owner -
          quittingTerminalPayoff reward
            (Function.update profile owner
              (quittingPureTimeBehaviorStrategy reward owner none)) owner ≤
        2 * budget := by
  rcases
      exists_strict_owner_singleton_toggle_or_singletonJoinAntitone
        reward owner with htoggle | hjoin
  · exact Or.inl htoggle
  · exact Or.inr <|
      quittingNeverFaceDebt_le_two_mul_collisionBudget_of_complete
        reward profile owner hjoin hsolo hM hreward hchi hcomplete hbudget

/-- Zero-budget form of the diffuse deletion dispatcher.  This is exact for
the displayed opponent chronology.  It does not by itself justify subtype
deletion, which would require the universal-opponent conclusion of Q175. -/
theorem exists_strict_owner_singleton_toggle_or_neverFaceDebt_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hchi : |quittingPunishmentValue reward owner| ≤ M)
    (hcomplete : Tendsto
      (quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) owner 0) atTop (nhds 0))
    (hbudget : ∀ horizon,
      quittingOwnerCollisionErrorAccum
        (quittingProfileLiveRoot reward profile) owner M 0 horizon ≤ 0) :
    (∃ other, other ≠ owner ∧
      reward (quittingSingletonTerminal other) owner <
        reward ⟨{owner, other}, by simp⟩ owner) ∨
      quittingBestReplyValue reward profile owner -
          quittingTerminalPayoff reward
            (Function.update profile owner
              (quittingPureTimeBehaviorStrategy reward owner none)) owner = 0 := by
  rcases
      exists_strict_owner_singleton_toggle_or_neverFaceDebt_le_two_mul_budget
        reward profile owner hsolo hM hreward hchi hcomplete hbudget with
    htoggle | hdebt
  · exact Or.inl htoggle
  · right
    have hlower := le_quittingBestReplyValue reward profile owner
      (quittingPureTimeBehaviorStrategy reward owner none)
    linarith

end GameTheory
