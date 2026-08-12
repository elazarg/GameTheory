/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawDebtConvexity
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Finite splicing of a complete stopping-law reset

This module caps one player's stopping law at a finite date by moving all
later finite stopping mass and its `Never` atom to that date.  The comparison
keeps the other players' literal live-path roots.

The relevant error is sharper than an undifferentiated prefix-survival bound.
Finite mass after the cap date is charged absolutely, while the `Never` atom
is charged only when all players outside the reset mover and the payoff
observer survive to the cap.  The latter is the player-deleted clock needed
for uniform control over every behavioral deviation of the observer.

All suffix equalities below are equalities on the canonical live path.  No
off-path behavioral equality, player deletion, Nash chronology, or uniform
equilibrium is asserted.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Moving the late stopping-law mass to one finite date -/

/-- Keep a Boolean hazard strictly before `cutoff`, Quit surely at `cutoff`,
and Continue afterwards.  Thus every original stopping atom strictly after
`cutoff`, including `Never`, is moved to `cutoff`. -/
def quittingHazardCapAt (hazard : ℕ → PMF Bool) (cutoff : ℕ) : ℕ → PMF Bool :=
  fun time =>
    if time < cutoff then hazard time
    else if time = cutoff then PMF.pure true else PMF.pure false

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingHazardCapAt_of_lt
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) {time : ℕ}
    (htime : time < cutoff) :
    quittingHazardCapAt hazard cutoff time = hazard time := by
  simp [quittingHazardCapAt, htime]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingHazardCapAt_self
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingHazardCapAt hazard cutoff cutoff = PMF.pure true := by
  simp [quittingHazardCapAt]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingHazardCapAt_of_lt_time
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) {time : ℕ}
    (htime : cutoff < time) :
    quittingHazardCapAt hazard cutoff time = PMF.pure false := by
  simp [quittingHazardCapAt, show ¬ time < cutoff by omega,
    show time ≠ cutoff by omega]

/-- Behavioral realization of the capped live-path hazard. -/
def quittingStoppingLawFiniteCapBehaviorStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    (cutoff : ℕ) : (quittingGame reward).BehaviorStrategy mover :=
  fun time _history =>
    quittingHazardCapAt (quittingBehaviorLiveHazard reward strategy) cutoff time

omit [DecidableEq ι] in
@[simp] theorem quittingBehaviorLiveHazard_finiteCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    (cutoff : ℕ) :
    quittingBehaviorLiveHazard reward
        (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
          cutoff) =
      quittingHazardCapAt (quittingBehaviorLiveHazard reward strategy) cutoff :=
  rfl

/-- Total finite stopping mass strictly after `cutoff`; the `Never` atom is
not included. -/
def quittingHazardLateFiniteMass (hazard : ℕ → PMF Bool)
    (cutoff : ℕ) : ℝ :=
  ∑' offset : ℕ, quittingHazardStopMass hazard (cutoff + 1 + offset)

omit [Fintype ι] [DecidableEq ι] in
theorem quittingHazardSurvival_succ_eq_lateFinite_add_never
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingHazardSurvival hazard (cutoff + 1) =
      quittingHazardLateFiniteMass hazard cutoff +
        quittingHazardNeverMass hazard := by
  have hsummable := (hasSum_quittingHazardStopMass hazard).summable
  have hsplit := hsummable.sum_add_tsum_nat_add (cutoff + 1)
  have htotal := (hasSum_quittingHazardStopMass hazard).tsum_eq
  have hprefix := sum_quittingHazardStopMass hazard (cutoff + 1)
  have htail :
      (∑' offset : ℕ,
        quittingHazardStopMass hazard (offset + (cutoff + 1))) =
        ∑' offset : ℕ,
          quittingHazardStopMass hazard (cutoff + 1 + offset) := by
    apply tsum_congr
    intro offset
    congr 1
    omega
  unfold quittingHazardLateFiniteMass
  rw [htotal, hprefix, htail] at hsplit
  linarith

omit [Fintype ι] [DecidableEq ι] in
theorem quittingHazardLateFiniteMass_nonneg
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    0 ≤ quittingHazardLateFiniteMass hazard cutoff := by
  unfold quittingHazardLateFiniteMass
  exact tsum_nonneg fun _ => quittingHazardStopMass_nonneg _ _

/-! ## The player-deleted survival clock -/

/-- Survival through `fuel` rows after deleting both the reset mover and one
observer.  It is written as ordinary opponent survival after forcing the
observer to Continue. -/
def quittingPairDeletedSurvivalWeight
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (start fuel : ℕ) : ℝ :=
  quittingOpponentSurvivalWeight
    (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard)
    mover start fuel

theorem quittingPairDeletedSurvivalWeight_nonneg
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (start fuel : ℕ) :
    0 ≤ quittingPairDeletedSurvivalWeight roots mover observer start fuel :=
  quittingOpponentSurvivalWeight_nonneg _ _ _ _

theorem quittingPairDeletedSurvivalWeight_le_one
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (start fuel : ℕ) :
    quittingPairDeletedSurvivalWeight roots mover observer start fuel ≤ 1 :=
  quittingOpponentSurvivalWeight_le_one _ _ _ _

/-- The mover-deleted clock is the diagonal member of the pair-deleted
family. -/
@[simp] theorem quittingPairDeletedSurvivalWeight_self
    (roots : ℕ → ι → PMF Bool) (mover : ι) (start fuel : ℕ) :
    quittingPairDeletedSurvivalWeight roots mover mover start fuel =
      quittingOpponentSurvivalWeight roots mover start fuel := by
  unfold quittingPairDeletedSurvivalWeight quittingOpponentSurvivalWeight
  apply Finset.prod_congr rfl
  intro offset _
  unfold quittingFixedOpponentsContinueMass quittingRootSequenceUpdate
  simp

/-- Once `observer` is deleted from the clock, its supplied live-path hazard
is immaterial. -/
@[simp] theorem quittingPairDeletedSurvivalWeight_update_observer
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) :
    quittingPairDeletedSurvivalWeight
        (quittingRootSequenceUpdate roots observer hazard)
        mover observer start fuel =
      quittingPairDeletedSurvivalWeight roots mover observer start fuel := by
  unfold quittingPairDeletedSurvivalWeight
  congr 1
  funext time player
  unfold quittingRootSequenceUpdate
  by_cases hplayer : player = observer
  · subst player
    simp
  · simp [Function.update_of_ne hplayer]

/-- Largest pair-deleted survival clock over observers distinct from the
reset mover. -/
def quittingMaxPairDeletedSurvivalWeight [Nontrivial ι]
    (roots : ℕ → ι → PMF Bool) (mover : ι)
    (start fuel : ℕ) : ℝ :=
  (Finset.univ.erase mover).sup'
    (by
      obtain ⟨observer, hobserver⟩ := exists_ne mover
      exact ⟨observer, Finset.mem_erase.mpr
        ⟨hobserver, Finset.mem_univ observer⟩⟩) fun observer =>
    quittingPairDeletedSurvivalWeight roots mover observer start fuel

theorem quittingPairDeletedSurvivalWeight_le_max [Nontrivial ι]
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (hmoverObserver : mover ≠ observer)
    (start fuel : ℕ) :
    quittingPairDeletedSurvivalWeight roots mover observer start fuel ≤
      quittingMaxPairDeletedSurvivalWeight roots mover start fuel := by
  exact Finset.le_sup'
    (fun who => quittingPairDeletedSurvivalWeight roots mover who start fuel)
    (Finset.mem_erase.mpr ⟨Ne.symm hmoverObserver, Finset.mem_univ observer⟩)

theorem quittingMaxPairDeletedSurvivalWeight_nonneg [Nontrivial ι]
    (roots : ℕ → ι → PMF Bool) (mover : ι) (start fuel : ℕ) :
    0 ≤ quittingMaxPairDeletedSurvivalWeight roots mover start fuel := by
  obtain ⟨observer, hobserver⟩ := exists_ne mover
  exact (quittingPairDeletedSurvivalWeight_nonneg
      roots mover observer start fuel).trans
    (quittingPairDeletedSurvivalWeight_le_max roots mover observer
      (Ne.symm hobserver) start fuel)

theorem quittingMaxPairDeletedSurvivalWeight_le_one [Nontrivial ι]
    (roots : ℕ → ι → PMF Bool) (mover : ι) (start fuel : ℕ) :
    quittingMaxPairDeletedSurvivalWeight roots mover start fuel ≤ 1 := by
  unfold quittingMaxPairDeletedSurvivalWeight
  apply Finset.sup'_le
  intro observer _
  exact quittingPairDeletedSurvivalWeight_le_one roots mover observer start fuel

/-- Terminal pair-deleted survival, i.e. the probability that every player
outside the mover/observer pair continues forever. -/
def quittingPairDeletedSurvivalLimit
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (start : ℕ := 0) : ℝ :=
  quittingOpponentSurvivalLimit
    (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard)
    mover start

theorem tendsto_quittingPairDeletedSurvivalLimit
    (roots : ℕ → ι → PMF Bool) (mover observer : ι) (start : ℕ) :
    Tendsto (quittingPairDeletedSurvivalWeight roots mover observer start)
      atTop (nhds (quittingPairDeletedSurvivalLimit roots mover observer start)) :=
  tendsto_quittingOpponentSurvivalLimit _ mover start

/-- Maximum terminal pair-deleted survival over observers distinct from the
mover. -/
def quittingMaxPairDeletedSurvivalLimit [Nontrivial ι]
    (roots : ℕ → ι → PMF Bool) (mover : ι) (start : ℕ := 0) : ℝ :=
  (Finset.univ.erase mover).sup'
    (by
      obtain ⟨observer, hobserver⟩ := exists_ne mover
      exact ⟨observer, Finset.mem_erase.mpr
        ⟨hobserver, Finset.mem_univ observer⟩⟩) fun observer =>
    quittingPairDeletedSurvivalLimit roots mover observer start

theorem tendsto_quittingMaxPairDeletedSurvivalLimit [Nontrivial ι]
    (roots : ℕ → ι → PMF Bool) (mover : ι) (start : ℕ) :
    Tendsto (quittingMaxPairDeletedSurvivalWeight roots mover start)
      atTop (nhds (quittingMaxPairDeletedSurvivalLimit roots mover start)) := by
  unfold quittingMaxPairDeletedSurvivalWeight
    quittingMaxPairDeletedSurvivalLimit
  apply Tendsto.finset_sup'_nhds_apply
  intro observer _
  exact tendsto_quittingPairDeletedSurvivalLimit roots mover observer start

theorem quittingMaxPairDeletedSurvivalLimit_nonneg [Nontrivial ι]
    (roots : ℕ → ι → PMF Bool) (mover : ι) (start : ℕ) :
    0 ≤ quittingMaxPairDeletedSurvivalLimit roots mover start := by
  unfold quittingMaxPairDeletedSurvivalLimit
  obtain ⟨observer, hobserver⟩ := exists_ne mover
  exact (quittingOpponentSurvivalLimit_nonneg
      (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard)
      mover start).trans
    (Finset.le_sup'
      (fun who => quittingPairDeletedSurvivalLimit roots mover who start)
      (Finset.mem_erase.mpr ⟨hobserver, Finset.mem_univ observer⟩))

theorem quittingMaxPairDeletedSurvivalLimit_le_one [Nontrivial ι]
    (roots : ℕ → ι → PMF Bool) (mover : ι) (start : ℕ) :
    quittingMaxPairDeletedSurvivalLimit roots mover start ≤ 1 := by
  exact le_of_tendsto
    (tendsto_quittingMaxPairDeletedSurvivalLimit roots mover start)
    (Eventually.of_forall fun fuel =>
      quittingMaxPairDeletedSurvivalWeight_le_one roots mover start fuel)

omit [Fintype ι] [DecidableEq ι] in
theorem quittingHazardNeverMass_le_one (hazard : ℕ → PMF Bool) :
    quittingHazardNeverMass hazard ≤ 1 := by
  have hle := quittingHazardNeverMass_le_survival hazard 0
  simpa [quittingHazardSurvival, Math.survivalProduct] using hle

omit [Fintype ι] [DecidableEq ι] in
theorem tendsto_quittingHazardLateFiniteMass_zero (hazard : ℕ → PMF Bool) :
    Tendsto (quittingHazardLateFiniteMass hazard) atTop (nhds 0) := by
  have hshift := (tendsto_quittingHazardSurvival_neverMass hazard).comp
    (tendsto_add_atTop_nat 1)
  have hconst : Tendsto (fun _ : ℕ => quittingHazardNeverMass hazard)
      atTop (nhds (quittingHazardNeverMass hazard)) := tendsto_const_nhds
  have hsub := hshift.sub hconst
  simpa only [Function.comp_apply, sub_self] using hsub.congr'
    (Eventually.of_forall fun cutoff => by
      change quittingHazardSurvival hazard (cutoff + 1) -
        quittingHazardNeverMass hazard = _
      rw [quittingHazardSurvival_succ_eq_lateFinite_add_never]
      ring)

/-- Deleting an additional, distinct observer can only increase the reset
mover's opponent-survival clock. -/
theorem quittingOpponentSurvivalWeight_le_pairDeleted
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (hmoverObserver : mover ≠ observer) (start fuel : ℕ) :
    quittingOpponentSurvivalWeight roots mover start fuel ≤
      quittingPairDeletedSurvivalWeight roots mover observer start fuel := by
  unfold quittingOpponentSurvivalWeight quittingPairDeletedSurvivalWeight
  apply Finset.prod_le_prod
  · intro offset hoffset
    exact quittingStationaryContinueMass_nonneg
      (Function.update (roots (start + offset)) mover (PMF.pure false))
  · intro offset hoffset
    unfold quittingFixedOpponentsContinueMass quittingRootSequenceUpdate
    let forcedMover := Function.update (roots (start + offset)) mover
      (PMF.pure false)
    have hfactor :=
      quittingStationaryContinueMass_eq_forcedContinue_mul_own
        forcedMover observer
    have hcommute :
        Function.update forcedMover observer (PMF.pure false) =
          Function.update
            (Function.update (roots (start + offset)) observer
              (PMF.pure false)) mover (PMF.pure false) := by
      simpa [forcedMover] using
        (Function.update_comm hmoverObserver (PMF.pure false)
          (PMF.pure false) (roots (start + offset)))
    rw [hcommute] at hfactor
    rw [hfactor]
    exact mul_le_of_le_one_right
      (quittingStationaryContinueMass_nonneg _)
      (by
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top
          (PMF.coe_le_one (forcedMover observer) false))

/-! ## Uniform payoff comparison for one capped response -/

/-- Capping the reset mover's stopping law changes any terminal payoff by at
most the late finite mass plus the `Never` mass times the mover-deleted
opponent-survival clock.  This is the core estimate before choosing a common
clock for arbitrary behavioral observers. -/
theorem abs_quittingRootSequenceTerminalValue_finiteCap_sub_le_opponent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (hazard : ℕ → PMF Bool)
    (cutoff : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootSequenceTerminalValue reward
          (quittingRootSequenceUpdate roots mover hazard) observer 0 -
        quittingRootSequenceTerminalValue reward
          (quittingRootSequenceUpdate roots mover
            (quittingHazardCapAt hazard cutoff)) observer 0| ≤
      2 * M *
        (quittingHazardLateFiniteMass hazard cutoff +
          quittingHazardNeverMass hazard *
            quittingOpponentSurvivalWeight roots mover 0 cutoff) := by
  let x := quittingRootSequenceUpdate roots mover hazard
  let cappedHazard := quittingHazardCapAt hazard cutoff
  let y := quittingRootSequenceUpdate roots mover cappedHazard
  have hprefix : ∀ time, time < cutoff → x time = y time := by
    intro time htime
    dsimp only [x, y, cappedHazard, quittingRootSequenceUpdate]
    rw [quittingHazardCapAt_of_lt hazard cutoff htime]
  have hscaled :=
    quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul
      reward x y observer cutoff hprefix
  let xTail : Payoff ι := fun _ =>
    quittingRootSequenceTerminalValue reward x observer (cutoff + 1)
  let yTail : Payoff ι := fun _ =>
    quittingRootSequenceTerminalValue reward y observer (cutoff + 1)
  let forcedRoot := Function.update (roots cutoff) mover (PMF.pure true)
  have hxRecursion :
      quittingRootSequenceTerminalValue reward x observer cutoff =
        quittingRootExpectedPayoff reward xTail
          (Function.update (roots cutoff) mover (hazard cutoff)) observer := by
    rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff]
    rfl
  have hyRecursion :
      quittingRootSequenceTerminalValue reward y observer cutoff =
        quittingRootExpectedPayoff reward yTail forcedRoot observer := by
    rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff]
    have hyRoot : y cutoff = forcedRoot := by
      funext player
      simp [y, cappedHazard, forcedRoot, quittingRootSequenceUpdate]
    rw [hyRoot]
    rfl
  have hxTailBound : ∀ player, |xTail player| ≤ M := by
    intro player
    exact abs_quittingRootSequenceTerminalValue_le reward x observer
      (cutoff + 1) hM hreward
  have hforce := abs_quittingRootExpectedPayoff_forceQuit_sub_le
    reward xTail (Function.update (roots cutoff) mover (hazard cutoff))
      mover observer hreward hxTailBound
  have hforcedRoot :
      Function.update
          (Function.update (roots cutoff) mover (hazard cutoff)) mover
            (PMF.pure true) = forcedRoot := by
    simp [forcedRoot]
  rw [hforcedRoot] at hforce
  have hsure : QuittingRootHasSureQuitter forcedRoot := by
    exact quittingRootHasSureQuitter_update_pure_true (roots cutoff) mover
  have htailIndependent :
      quittingRootExpectedPayoff reward xTail forcedRoot observer =
        quittingRootExpectedPayoff reward yTail forcedRoot observer :=
    quittingRootExpectedPayoff_eq_of_hasSureQuitter reward forcedRoot hsure
      xTail yTail observer
  have hlocal :
      |quittingRootSequenceTerminalValue reward x observer cutoff -
          quittingRootSequenceTerminalValue reward y observer cutoff| ≤
        2 * M * (hazard cutoff false).toReal := by
    rw [hxRecursion, hyRecursion, ← htailIndependent]
    simpa [x, quittingRootSequenceUpdate] using hforce
  have hjoint :
      quittingJointSurvivalWeight y 0 cutoff =
        quittingOpponentSurvivalWeight roots mover 0 cutoff *
          quittingHazardSurvival hazard cutoff := by
    dsimp only [y, cappedHazard]
    rw [quittingJointSurvivalWeight_update_eq_opponent_mul_hazardSurvival]
    congr 1
    unfold quittingHazardSurvival Math.survivalProduct
    apply Finset.prod_congr rfl
    intro offset hoffset
    simp only [Nat.zero_add]
    rw [quittingHazardCapAt_of_lt hazard cutoff
      (Finset.mem_range.mp hoffset)]
  have hsurvivalStep :
      quittingHazardSurvival hazard cutoff *
          (hazard cutoff false).toReal =
        quittingHazardSurvival hazard (cutoff + 1) := by
    exact (quittingHazardSurvival_succ hazard cutoff).symm
  have hopponentNonneg :=
    quittingOpponentSurvivalWeight_nonneg roots mover 0 cutoff
  have hopponentOne :=
    quittingOpponentSurvivalWeight_le_one roots mover 0 cutoff
  have hlateNonneg := quittingHazardLateFiniteMass_nonneg hazard cutoff
  have hneverNonneg := quittingHazardNeverMass_nonneg hazard
  have hclockBound :
      quittingOpponentSurvivalWeight roots mover 0 cutoff *
          quittingHazardSurvival hazard (cutoff + 1) ≤
        quittingHazardLateFiniteMass hazard cutoff +
          quittingHazardNeverMass hazard *
            quittingOpponentSurvivalWeight roots mover 0 cutoff := by
    rw [quittingHazardSurvival_succ_eq_lateFinite_add_never]
    calc
      quittingOpponentSurvivalWeight roots mover 0 cutoff *
          (quittingHazardLateFiniteMass hazard cutoff +
            quittingHazardNeverMass hazard) =
        quittingOpponentSurvivalWeight roots mover 0 cutoff *
            quittingHazardLateFiniteMass hazard cutoff +
          quittingOpponentSurvivalWeight roots mover 0 cutoff *
            quittingHazardNeverMass hazard := by ring
      _ ≤ quittingHazardLateFiniteMass hazard cutoff +
          quittingHazardNeverMass hazard *
            quittingOpponentSurvivalWeight roots mover 0 cutoff := by
        have hfinite := mul_le_of_le_one_left hlateNonneg hopponentOne
        nlinarith
  change |quittingRootSequenceTerminalValue reward x observer 0 -
      quittingRootSequenceTerminalValue reward y observer 0| ≤ _
  rw [hscaled, abs_mul,
    abs_of_nonneg (quittingJointSurvivalWeight_nonneg y 0 cutoff), hjoint]
  calc
    (quittingOpponentSurvivalWeight roots mover 0 cutoff *
          quittingHazardSurvival hazard cutoff) *
        |quittingRootSequenceTerminalValue reward x observer cutoff -
          quittingRootSequenceTerminalValue reward y observer cutoff| ≤
      (quittingOpponentSurvivalWeight roots mover 0 cutoff *
          quittingHazardSurvival hazard cutoff) *
        (2 * M * (hazard cutoff false).toReal) :=
      mul_le_mul_of_nonneg_left hlocal
        (mul_nonneg hopponentNonneg
          (quittingHazardSurvival_nonneg hazard cutoff))
    _ = 2 * M *
        (quittingOpponentSurvivalWeight roots mover 0 cutoff *
          quittingHazardSurvival hazard (cutoff + 1)) := by
      rw [← hsurvivalStep]
      ring
    _ ≤ 2 * M *
        (quittingHazardLateFiniteMass hazard cutoff +
          quittingHazardNeverMass hazard *
            quittingOpponentSurvivalWeight roots mover 0 cutoff) :=
      mul_le_mul_of_nonneg_left hclockBound (mul_nonneg (by norm_num) hM)

/-- For a distinct observer, deleting that observer gives the sharper clock
which is independent of the observer's own behavioral deviation. -/
theorem abs_quittingRootSequenceTerminalValue_finiteCap_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (hmoverObserver : mover ≠ observer) (hazard : ℕ → PMF Bool)
    (cutoff : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootSequenceTerminalValue reward
          (quittingRootSequenceUpdate roots mover hazard) observer 0 -
        quittingRootSequenceTerminalValue reward
          (quittingRootSequenceUpdate roots mover
            (quittingHazardCapAt hazard cutoff)) observer 0| ≤
      2 * M *
        (quittingHazardLateFiniteMass hazard cutoff +
          quittingHazardNeverMass hazard *
            quittingPairDeletedSurvivalWeight roots mover observer 0 cutoff) := by
  have hcore :=
    abs_quittingRootSequenceTerminalValue_finiteCap_sub_le_opponent
      reward roots mover observer hazard cutoff hM hreward
  have hclock := quittingOpponentSurvivalWeight_le_pairDeleted roots mover
    observer hmoverObserver 0 cutoff
  have hnever := quittingHazardNeverMass_nonneg hazard
  have hscale : 0 ≤ 2 * M := mul_nonneg (by norm_num) hM
  calc
    |quittingRootSequenceTerminalValue reward
          (quittingRootSequenceUpdate roots mover hazard) observer 0 -
        quittingRootSequenceTerminalValue reward
          (quittingRootSequenceUpdate roots mover
            (quittingHazardCapAt hazard cutoff)) observer 0| ≤
        2 * M *
          (quittingHazardLateFiniteMass hazard cutoff +
            quittingHazardNeverMass hazard *
              quittingOpponentSurvivalWeight roots mover 0 cutoff) := hcore
    _ ≤ 2 * M *
          (quittingHazardLateFiniteMass hazard cutoff +
            quittingHazardNeverMass hazard *
              quittingPairDeletedSurvivalWeight roots mover observer 0 cutoff) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hclock hnever))
        hscale

/-- One cap error controls every payoff coordinate with the same maximum
player-deleted clock.  In particular this includes the mover's own payoff.
-/
theorem abs_quittingRootSequenceTerminalValue_finiteCap_sub_le_max
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootSequenceTerminalValue reward
          (quittingRootSequenceUpdate roots mover hazard) observer 0 -
        quittingRootSequenceTerminalValue reward
          (quittingRootSequenceUpdate roots mover
            (quittingHazardCapAt hazard cutoff)) observer 0| ≤
      2 * M *
        (quittingHazardLateFiniteMass hazard cutoff +
          quittingHazardNeverMass hazard *
            quittingMaxPairDeletedSurvivalWeight roots mover 0 cutoff) := by
  have hcore :=
    abs_quittingRootSequenceTerminalValue_finiteCap_sub_le_opponent
      reward roots mover observer hazard cutoff hM hreward
  obtain ⟨other, hother⟩ := exists_ne mover
  have hclock : quittingOpponentSurvivalWeight roots mover 0 cutoff ≤
      quittingMaxPairDeletedSurvivalWeight roots mover 0 cutoff :=
    (quittingOpponentSurvivalWeight_le_pairDeleted roots mover other
      (Ne.symm hother) 0 cutoff).trans
        (quittingPairDeletedSurvivalWeight_le_max roots mover other
          (Ne.symm hother) 0 cutoff)
  have hnever := quittingHazardNeverMass_nonneg hazard
  calc
    |quittingRootSequenceTerminalValue reward
          (quittingRootSequenceUpdate roots mover hazard) observer 0 -
        quittingRootSequenceTerminalValue reward
          (quittingRootSequenceUpdate roots mover
            (quittingHazardCapAt hazard cutoff)) observer 0| ≤
        2 * M *
          (quittingHazardLateFiniteMass hazard cutoff +
            quittingHazardNeverMass hazard *
              quittingOpponentSurvivalWeight roots mover 0 cutoff) := hcore
    _ ≤ 2 * M *
          (quittingHazardLateFiniteMass hazard cutoff +
            quittingHazardNeverMass hazard *
              quittingMaxPairDeletedSurvivalWeight roots mover 0 cutoff) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hclock hnever))
        (mul_nonneg (by norm_num) hM)

/-! ## Profile-level uniformity, including behavioral envelopes -/

/-- Dimensionless cap error: late finite stopping mass plus the cemetery atom
times the largest deleted-player survival clock. -/
def quittingFiniteSpliceError [Nontrivial ι]
    (roots : ℕ → ι → PMF Bool) (mover : ι)
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) : ℝ :=
  quittingHazardLateFiniteMass hazard cutoff +
    quittingHazardNeverMass hazard *
      quittingMaxPairDeletedSurvivalWeight roots mover 0 cutoff

theorem quittingFiniteSpliceError_nonneg [Nontrivial ι]
    (roots : ℕ → ι → PMF Bool) (mover : ι)
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    0 ≤ quittingFiniteSpliceError roots mover hazard cutoff := by
  unfold quittingFiniteSpliceError
  exact add_nonneg (quittingHazardLateFiniteMass_nonneg hazard cutoff)
    (mul_nonneg (quittingHazardNeverMass_nonneg hazard)
      (quittingMaxPairDeletedSurvivalWeight_nonneg roots mover 0 cutoff))

/-- At a fixed profile/law, the finite-cap error converges exactly to the
cemetery atom times the terminal maximum pair-deleted clock. -/
theorem tendsto_quittingFiniteSpliceError_terminal [Nontrivial ι]
    (roots : ℕ → ι → PMF Bool) (mover : ι)
    (hazard : ℕ → PMF Bool) :
    Tendsto (quittingFiniteSpliceError roots mover hazard) atTop
      (nhds (quittingHazardNeverMass hazard *
        quittingMaxPairDeletedSurvivalLimit roots mover 0)) := by
  unfold quittingFiniteSpliceError
  simpa using (tendsto_quittingHazardLateFiniteMass_zero hazard).add
    (tendsto_const_nhds.mul
      (tendsto_quittingMaxPairDeletedSurvivalLimit roots mover 0))

/-- Cap-tight diagonal selection.  If the product of the reset law's
`Never` atom and the terminal maximum pair-deleted clock vanishes along a
sequence, finite cutoffs can be chosen tending to infinity so that the full
finite-splice error vanishes along the same sequence. -/
theorem exists_finiteSpliceCutoffs_tendsto_zero_of_capTight
    [Nontrivial ι]
    (roots : ℕ → ℕ → ι → PMF Bool) (mover : ι)
    (hazard : ℕ → ℕ → PMF Bool)
    (hcap : Tendsto (fun n =>
      quittingHazardNeverMass (hazard n) *
        quittingMaxPairDeletedSurvivalLimit (roots n) mover 0)
      atTop (nhds 0)) :
    ∃ cutoffs : ℕ → ℕ,
      Tendsto cutoffs atTop atTop ∧
      Tendsto (fun n =>
        quittingFiniteSpliceError (roots n) mover (hazard n) (cutoffs n))
        atTop (nhds 0) := by
  let boundary : ℕ → ℝ := fun n =>
    quittingHazardNeverMass (hazard n) *
      quittingMaxPairDeletedSurvivalLimit (roots n) mover 0
  have hchoice : ∀ n : ℕ, ∃ cutoff : ℕ,
      n ≤ cutoff ∧
      |quittingFiniteSpliceError (roots n) mover (hazard n) cutoff -
          boundary n| < ((n + 1 : ℕ) : ℝ)⁻¹ := by
    intro n
    have ht := tendsto_quittingFiniteSpliceError_terminal
      (roots n) mover (hazard n)
    rw [Metric.tendsto_atTop] at ht
    have heps : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
    obtain ⟨threshold, hthreshold⟩ := ht _ heps
    let cutoff := max n threshold
    refine ⟨cutoff, le_max_left _ _, ?_⟩
    have hclose := hthreshold cutoff (le_max_right _ _)
    simpa [boundary, Real.dist_eq] using hclose
  choose cutoffs hcutoffsLarge hcutoffsClose using hchoice
  have hcutoffsTendsto : Tendsto cutoffs atTop atTop := by
    rw [tendsto_atTop]
    intro threshold
    exact eventually_atTop.2
      ⟨threshold, fun n hn => hn.trans (hcutoffsLarge n)⟩
  have hdiagonalDifference : Tendsto (fun n =>
      quittingFiniteSpliceError (roots n) mover (hazard n) (cutoffs n) -
        boundary n) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    have hinv := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    rw [Metric.tendsto_atTop] at hinv
    obtain ⟨threshold, hthreshold⟩ := hinv epsilon hepsilon
    refine ⟨threshold, fun n hn => ?_⟩
    have hupper := hthreshold n hn
    rw [Real.dist_eq, sub_zero]
    calc
      |quittingFiniteSpliceError (roots n) mover (hazard n) (cutoffs n) -
          boundary n| < ((n + 1 : ℕ) : ℝ)⁻¹ := hcutoffsClose n
      _ = 1 / ((n : ℝ) + 1) := by
        rw [Nat.cast_add, Nat.cast_one]
        simp only [one_div]
      _ < epsilon := by
        have hpositive : 0 < 1 / ((n : ℝ) + 1) := by positivity
        rw [Real.dist_eq, sub_zero, abs_of_pos hpositive] at hupper
        exact hupper
  refine ⟨cutoffs, hcutoffsTendsto, ?_⟩
  have hsum := hdiagonalDifference.add hcap
  simpa only [zero_add] using hsum.congr'
    (Eventually.of_forall fun n => by
      dsimp only [boundary]
      ring)

/-- The prescribed payoff vector is uniformly stable under finite capping of
one complete live-path stopping law. -/
theorem abs_quittingTerminalPayoff_finiteCap_sub_le [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (strategy : (quittingGame reward).BehaviorStrategy mover)
    (cutoff : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalPayoff reward
          (Function.update profile mover strategy) observer -
        quittingTerminalPayoff reward
          (Function.update profile mover
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
              cutoff)) observer| ≤
      2 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward strategy) cutoff := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingBehaviorLiveHazard_finiteCap]
  exact abs_quittingRootSequenceTerminalValue_finiteCap_sub_le_max
    reward (quittingProfileLiveRoot reward profile) mover observer
      (quittingBehaviorLiveHazard reward strategy) cutoff hM hreward

/-- The same cap error controls the payoff of every behavioral deviation by
a distinct observer.  The observer's hazard disappears from its own deleted
clock, so the bound is genuinely uniform over the deviation. -/
theorem abs_quittingTerminalPayoff_update_finiteCap_sub_le
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hmoverObserver : mover ≠ observer)
    (strategy : (quittingGame reward).BehaviorStrategy mover)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (cutoff : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalPayoff reward
          (Function.update (Function.update profile mover strategy)
            observer deviation) observer -
        quittingTerminalPayoff reward
          (Function.update
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer deviation) observer| ≤
      2 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward strategy) cutoff := by
  rw [Function.update_comm hmoverObserver,
    Function.update_comm hmoverObserver,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingBehaviorLiveHazard_finiteCap]
  have hbound := abs_quittingRootSequenceTerminalValue_finiteCap_sub_le
    reward
      (quittingProfileLiveRoot reward
        (Function.update profile observer deviation))
      mover observer hmoverObserver
      (quittingBehaviorLiveHazard reward strategy) cutoff hM hreward
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingPairDeletedSurvivalWeight_update_observer] at hbound
  have hclock := quittingPairDeletedSurvivalWeight_le_max
    (quittingProfileLiveRoot reward profile) mover observer hmoverObserver
      0 cutoff
  have hnever := quittingHazardNeverMass_nonneg
    (quittingBehaviorLiveHazard reward strategy)
  calc
    _ ≤
        2 * M *
          (quittingHazardLateFiniteMass
              (quittingBehaviorLiveHazard reward strategy) cutoff +
            quittingHazardNeverMass
                (quittingBehaviorLiveHazard reward strategy) *
              quittingPairDeletedSurvivalWeight
                (quittingProfileLiveRoot reward profile)
                mover observer 0 cutoff) := hbound
    _ ≤ 2 * M * quittingFiniteSpliceError
          (quittingProfileLiveRoot reward profile) mover
            (quittingBehaviorLiveHazard reward strategy) cutoff := by
      unfold quittingFiniteSpliceError
      exact mul_le_mul_of_nonneg_left
        (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hclock hnever))
        (mul_nonneg (by norm_num) hM)

/-- The full behavioral best-response envelope, not merely the pure-time
envelope, is uniformly stable under the finite cap. -/
theorem abs_quittingContinuationBestResponseValue_finiteCap_sub_le
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (strategy : (quittingGame reward).BehaviorStrategy mover)
    (cutoff : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingContinuationBestResponseValue reward
          (Function.update profile mover strategy) observer -
        quittingContinuationBestResponseValue reward
          (Function.update profile mover
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
              cutoff)) observer| ≤
      2 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward strategy) cutoff := by
  by_cases hsame : mover = observer
  · subst observer
    rw [quittingContinuationBestResponseValue_update_self,
      quittingContinuationBestResponseValue_update_self, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hM)
      (quittingFiniteSpliceError_nonneg
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward strategy) cutoff)
  · let sourceProfile := Function.update profile mover strategy
    let cappedProfile := Function.update profile mover
      (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy cutoff)
    let error := 2 * M * quittingFiniteSpliceError
      (quittingProfileLiveRoot reward profile) mover
        (quittingBehaviorLiveHazard reward strategy) cutoff
    have hpoint : ∀ deviation :
        (quittingGame reward).BehaviorStrategy observer,
        |quittingTerminalPayoff reward
              (Function.update sourceProfile observer deviation) observer -
            quittingTerminalPayoff reward
              (Function.update cappedProfile observer deviation) observer| ≤
          error := by
      intro deviation
      dsimp only [sourceProfile, cappedProfile, error]
      exact abs_quittingTerminalPayoff_update_finiteCap_sub_le
        reward profile mover observer hsame strategy deviation cutoff hM hreward
    have hsourceCapped :
        quittingContinuationBestResponseValue reward sourceProfile observer ≤
          quittingContinuationBestResponseValue reward cappedProfile observer +
            error := by
      unfold quittingContinuationBestResponseValue
      apply csSup_le
      · exact ⟨_, ⟨sourceProfile observer, rfl⟩⟩
      · rintro _ ⟨deviation, rfl⟩
        have hcap :=
          quittingTerminalPayoff_update_le_continuationBestResponseValue
            reward cappedProfile observer deviation hM hreward
        unfold quittingContinuationBestResponseValue at hcap
        have hp := hpoint deviation
        linarith [le_abs_self
          (quittingTerminalPayoff reward
              (Function.update sourceProfile observer deviation) observer -
            quittingTerminalPayoff reward
              (Function.update cappedProfile observer deviation) observer)]
    have hcappedSource :
        quittingContinuationBestResponseValue reward cappedProfile observer ≤
          quittingContinuationBestResponseValue reward sourceProfile observer +
            error := by
      unfold quittingContinuationBestResponseValue
      apply csSup_le
      · exact ⟨_, ⟨cappedProfile observer, rfl⟩⟩
      · rintro _ ⟨deviation, rfl⟩
        have hsource :=
          quittingTerminalPayoff_update_le_continuationBestResponseValue
            reward sourceProfile observer deviation hM hreward
        unfold quittingContinuationBestResponseValue at hsource
        have hp := hpoint deviation
        linarith [neg_le_abs
          (quittingTerminalPayoff reward
              (Function.update sourceProfile observer deviation) observer -
            quittingTerminalPayoff reward
              (Function.update cappedProfile observer deviation) observer)]
    change |quittingContinuationBestResponseValue reward sourceProfile observer -
      quittingContinuationBestResponseValue reward cappedProfile observer| ≤ error
    rw [abs_le]
    constructor <;> linarith

/-- Every best-response-debt coordinate changes by at most twice the payoff
error: one copy for the envelope and one for the prescribed payoff. -/
theorem abs_quittingTerminalSemanticDebt_finiteCap_sub_le
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (strategy : (quittingGame reward).BehaviorStrategy mover)
    (cutoff : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover strategy)) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff))) observer| ≤
      4 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward strategy) cutoff := by
  have hbest :=
    abs_quittingContinuationBestResponseValue_finiteCap_sub_le
      reward profile mover observer strategy cutoff hM hreward
  have hpay := abs_quittingTerminalPayoff_finiteCap_sub_le
    reward profile mover observer strategy cutoff hM hreward
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  calc
    |(quittingContinuationBestResponseValue reward
          (Function.update profile mover strategy) observer -
        quittingTerminalPayoff reward
          (Function.update profile mover strategy) observer) -
      (quittingContinuationBestResponseValue reward
          (Function.update profile mover
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
              cutoff)) observer -
        quittingTerminalPayoff reward
          (Function.update profile mover
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
              cutoff)) observer)| ≤
        |quittingContinuationBestResponseValue reward
            (Function.update profile mover strategy) observer -
          quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| +
        |quittingTerminalPayoff reward
            (Function.update profile mover strategy) observer -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| := by
      rw [show
        (quittingContinuationBestResponseValue reward
              (Function.update profile mover strategy) observer -
            quittingTerminalPayoff reward
              (Function.update profile mover strategy) observer) -
          (quittingContinuationBestResponseValue reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff)) observer -
            quittingTerminalPayoff reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff)) observer) =
          (quittingContinuationBestResponseValue reward
              (Function.update profile mover strategy) observer -
            quittingContinuationBestResponseValue reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff)) observer) +
          (quittingTerminalPayoff reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff)) observer -
            quittingTerminalPayoff reward
              (Function.update profile mover strategy) observer) by ring]
      simpa only [abs_sub_comm] using abs_add_le
        (quittingContinuationBestResponseValue reward
            (Function.update profile mover strategy) observer -
          quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer)
        (quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer -
          quittingTerminalPayoff reward
            (Function.update profile mover strategy) observer)
    _ ≤ 2 * M * quittingFiniteSpliceError
          (quittingProfileLiveRoot reward profile) mover
            (quittingBehaviorLiveHazard reward strategy) cutoff +
        2 * M * quittingFiniteSpliceError
          (quittingProfileLiveRoot reward profile) mover
            (quittingBehaviorLiveHazard reward strategy) cutoff :=
      add_le_add hbest hpay
    _ = 4 * M * quittingFiniteSpliceError
          (quittingProfileLiveRoot reward profile) mover
            (quittingBehaviorLiveHazard reward strategy) cutoff := by ring

/-- Total best-response debt is stable, with the expected cardinality cost
from summing the coordinatewise estimate. -/
theorem abs_quittingTerminalSemanticDebtSum_finiteCap_sub_le
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    (cutoff : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update profile mover strategy)) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)))| ≤
      (Fintype.card ι : ℝ) *
        (4 * M * quittingFiniteSpliceError
          (quittingProfileLiveRoot reward profile) mover
            (quittingBehaviorLiveHazard reward strategy) cutoff) := by
  unfold quittingTerminalSemanticDebtSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ observer,
        (quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover strategy)) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff))) observer)| ≤
        ∑ observer,
          |quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (Function.update profile mover strategy)) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (Function.update profile mover
                  (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                    cutoff))) observer| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _observer : ι,
          4 * M * quittingFiniteSpliceError
            (quittingProfileLiveRoot reward profile) mover
              (quittingBehaviorLiveHazard reward strategy) cutoff := by
      apply Finset.sum_le_sum
      intro observer _
      exact abs_quittingTerminalSemanticDebt_finiteCap_sub_le
        reward profile mover observer strategy cutoff hM hreward
    _ = (Fintype.card ι : ℝ) *
        (4 * M * quittingFiniteSpliceError
          (quittingProfileLiveRoot reward profile) mover
            (quittingBehaviorLiveHazard reward strategy) cutoff) := by
      simp

/-- Relative to any fixed source profile, replacing the mover by the capped
law changes the mover's endpoint gain by exactly the same amount as it
changes the mover's endpoint payoff. -/
theorem abs_quittingFiniteCap_moverGain_sub_le [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    (cutoff : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |(quittingTerminalPayoff reward
          (Function.update profile mover strategy) mover -
        quittingTerminalPayoff reward profile mover) -
      (quittingTerminalPayoff reward
          (Function.update profile mover
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
              cutoff)) mover -
        quittingTerminalPayoff reward profile mover)| ≤
      2 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward strategy) cutoff := by
  simpa only [sub_sub_sub_cancel_right] using
    abs_quittingTerminalPayoff_finiteCap_sub_le
      reward profile mover mover strategy cutoff hM hreward

/-! ## Lambda-scaled reset comparison -/

/-- When the capped law is used only on a `lambda` reset branch, prescribed
payoff error is multiplied by `lambda`. -/
theorem abs_quittingTerminalPayoff_mixtureFiniteCap_sub_le
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (cutoff : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalPayoff reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover
              source target lambda hlambda0 hlambda1)) observer -
        quittingTerminalPayoff reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target
                cutoff) lambda hlambda0 hlambda1)) observer| ≤
      lambda * (2 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward target) cutoff) := by
  rw [quittingTerminalPayoff_stoppingLawMixture_eq
      reward profile mover observer source target lambda hlambda0 hlambda1,
    quittingTerminalPayoff_stoppingLawMixture_eq
      reward profile mover observer source
        (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target cutoff)
        lambda hlambda0 hlambda1]
  rw [show
      ((1 - lambda) * quittingTerminalPayoff reward
          (Function.update profile mover source) observer +
        lambda * quittingTerminalPayoff reward
          (Function.update profile mover target) observer) -
      ((1 - lambda) * quittingTerminalPayoff reward
          (Function.update profile mover source) observer +
        lambda * quittingTerminalPayoff reward
          (Function.update profile mover
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target
              cutoff)) observer) =
      lambda *
        (quittingTerminalPayoff reward
            (Function.update profile mover target) observer -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target
                cutoff)) observer) by ring,
    abs_mul, abs_of_nonneg hlambda0]
  exact mul_le_mul_of_nonneg_left
    (abs_quittingTerminalPayoff_finiteCap_sub_le
      reward profile mover observer target cutoff hM hreward) hlambda0

/-- The lambda-scaled estimate remains uniform over every behavioral
deviation of a distinct observer. -/
theorem abs_quittingTerminalPayoff_update_mixtureFiniteCap_sub_le
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hmoverObserver : mover ≠ observer)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (cutoff : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalPayoff reward
          (Function.update
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                source target lambda hlambda0 hlambda1)) observer deviation)
          observer -
        quittingTerminalPayoff reward
          (Function.update
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target
                  cutoff) lambda hlambda0 hlambda1)) observer deviation)
          observer| ≤
      lambda * (2 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward target) cutoff) := by
  rw [Function.update_comm hmoverObserver,
    Function.update_comm hmoverObserver,
    quittingTerminalPayoff_stoppingLawMixture_eq
      reward (Function.update profile observer deviation) mover observer
        source target lambda hlambda0 hlambda1,
    quittingTerminalPayoff_stoppingLawMixture_eq
      reward (Function.update profile observer deviation) mover observer source
        (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target cutoff)
        lambda hlambda0 hlambda1]
  rw [show
      ((1 - lambda) * quittingTerminalPayoff reward
          (Function.update (Function.update profile observer deviation) mover
            source) observer +
        lambda * quittingTerminalPayoff reward
          (Function.update (Function.update profile observer deviation) mover
            target) observer) -
      ((1 - lambda) * quittingTerminalPayoff reward
          (Function.update (Function.update profile observer deviation) mover
            source) observer +
        lambda * quittingTerminalPayoff reward
          (Function.update (Function.update profile observer deviation) mover
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target
              cutoff)) observer) =
      lambda *
        (quittingTerminalPayoff reward
            (Function.update (Function.update profile observer deviation) mover
              target) observer -
          quittingTerminalPayoff reward
            (Function.update (Function.update profile observer deviation) mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target
                cutoff)) observer) by ring,
    abs_mul, abs_of_nonneg hlambda0]
  have hendpoint := abs_quittingTerminalPayoff_update_finiteCap_sub_le
    reward profile mover observer hmoverObserver target deviation cutoff hM hreward
  rw [Function.update_comm hmoverObserver,
    Function.update_comm hmoverObserver] at hendpoint
  exact mul_le_mul_of_nonneg_left hendpoint hlambda0

/-- The full behavioral best-response envelope also receives the exact
mixture factor `lambda`. -/
theorem abs_quittingContinuationBestResponseValue_mixtureFiniteCap_sub_le
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (cutoff : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingContinuationBestResponseValue reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover
              source target lambda hlambda0 hlambda1)) observer -
        quittingContinuationBestResponseValue reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target
                cutoff) lambda hlambda0 hlambda1)) observer| ≤
      lambda * (2 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward target) cutoff) := by
  by_cases hsame : mover = observer
  · subst observer
    rw [quittingContinuationBestResponseValue_update_self,
      quittingContinuationBestResponseValue_update_self, sub_self, abs_zero]
    exact mul_nonneg hlambda0
      (mul_nonneg (mul_nonneg (by norm_num) hM)
        (quittingFiniteSpliceError_nonneg
          (quittingProfileLiveRoot reward profile) mover
            (quittingBehaviorLiveHazard reward target) cutoff))
  · let targetProfile := Function.update profile mover
      (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
        lambda hlambda0 hlambda1)
    let cappedProfile := Function.update profile mover
      (quittingStoppingLawMixtureBehaviorStrategy reward mover source
        (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target cutoff)
        lambda hlambda0 hlambda1)
    let error := lambda * (2 * M * quittingFiniteSpliceError
      (quittingProfileLiveRoot reward profile) mover
        (quittingBehaviorLiveHazard reward target) cutoff)
    have hpoint : ∀ deviation :
        (quittingGame reward).BehaviorStrategy observer,
        |quittingTerminalPayoff reward
              (Function.update targetProfile observer deviation) observer -
            quittingTerminalPayoff reward
              (Function.update cappedProfile observer deviation) observer| ≤
          error := by
      intro deviation
      dsimp only [targetProfile, cappedProfile, error]
      exact abs_quittingTerminalPayoff_update_mixtureFiniteCap_sub_le
        reward profile mover observer hsame source target deviation lambda
          hlambda0 hlambda1 cutoff hM hreward
    have hforward :
        quittingContinuationBestResponseValue reward targetProfile observer ≤
          quittingContinuationBestResponseValue reward cappedProfile observer +
            error := by
      unfold quittingContinuationBestResponseValue
      apply csSup_le
      · exact ⟨_, ⟨targetProfile observer, rfl⟩⟩
      · rintro _ ⟨deviation, rfl⟩
        have hcap :=
          quittingTerminalPayoff_update_le_continuationBestResponseValue
            reward cappedProfile observer deviation hM hreward
        unfold quittingContinuationBestResponseValue at hcap
        have hp := hpoint deviation
        linarith [le_abs_self
          (quittingTerminalPayoff reward
              (Function.update targetProfile observer deviation) observer -
            quittingTerminalPayoff reward
              (Function.update cappedProfile observer deviation) observer)]
    have hbackward :
        quittingContinuationBestResponseValue reward cappedProfile observer ≤
          quittingContinuationBestResponseValue reward targetProfile observer +
            error := by
      unfold quittingContinuationBestResponseValue
      apply csSup_le
      · exact ⟨_, ⟨cappedProfile observer, rfl⟩⟩
      · rintro _ ⟨deviation, rfl⟩
        have htarget :=
          quittingTerminalPayoff_update_le_continuationBestResponseValue
            reward targetProfile observer deviation hM hreward
        unfold quittingContinuationBestResponseValue at htarget
        have hp := hpoint deviation
        linarith [neg_le_abs
          (quittingTerminalPayoff reward
              (Function.update targetProfile observer deviation) observer -
            quittingTerminalPayoff reward
              (Function.update cappedProfile observer deviation) observer)]
    change |quittingContinuationBestResponseValue reward targetProfile observer -
      quittingContinuationBestResponseValue reward cappedProfile observer| ≤ error
    rw [abs_le]
    constructor <;> linarith

end GameTheory
