/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteChainTerminalCompiler
import GameTheory.Concepts.Stochastic.QuittingStationaryMinMax
import GameTheory.Concepts.Stochastic.QuittingPhaseSwitchResiduals

/-!
# Target-anchored tails for finite quitting chains

A finite exact Nash--Bellman prefix need not be followed by one continuation
that punishes every player.  It is enough to choose one target player whose
actual tail is already a best reply against its own opponents.  The target
then has zero surviving tail debt.  Every other player's tail debt is bounded
by twice the reward bound and is multiplied by opponent-only survival through
the prefix; that survival contains the target's own prescribed survival as a
factor.

This module supplies the exact semantic compiler for that mechanism.  The
finite prefix is anchored at the actual payoff vector of the supplied suffix,
so no artificial zero-boundary seam appears.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The suffix beginning at `cutoff` is already a best reply for `target`
against its own opponents. -/
def IsQuittingTargetClosedAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (target : ι) (cutoff : ℕ) : Prop :=
  ∀ hazard : ℕ → PMF Bool,
    quittingRootSequenceHazardTerminalValue reward roots target hazard cutoff ≤
      quittingRootSequenceTerminalValue reward roots target cutoff

/-- Hazard values only see the opponents' root coordinates. -/
theorem quittingRootSequenceHazardTerminalValue_congr_of_opponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : ℕ → ι → PMF Bool} (who : ι)
    (hagree : ∀ time player, player ≠ who →
      first time player = second time player)
    (hazard : ℕ → PMF Bool) (start : ℕ) :
    quittingRootSequenceHazardTerminalValue reward first who hazard start =
      quittingRootSequenceHazardTerminalValue reward second who hazard start := by
  unfold quittingRootSequenceHazardTerminalValue
  apply congrArg
    (fun roots => quittingRootSequenceTerminalValue reward roots who start)
  funext time player
  unfold quittingRootSequenceUpdate
  by_cases hplayer : player = who
  · subst player
    simp
  · simp [Function.update_of_ne hplayer, hagree time player hplayer]

/-- Every constant opponent row admits a root-sequence tail whose prescribed
target payoff equals the row's exact stationary cap and which caps every
target deviation by that same number.  The target's own live hazard is chosen
from the stationary-cap attainment theorem; only the opponents remain
constant. -/
theorem exists_quittingTargetClosedTail_of_stationaryRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (target : ι) :
    ∃ tail : ℕ → ι → PMF Bool,
      IsQuittingTargetClosedAt reward tail target 0 ∧
      quittingRootSequenceTerminalValue reward tail target 0 =
        quittingStationaryUnilateralCap reward root target ∧
      ∀ time player, player ≠ target → tail time player = root player := by
  obtain ⟨response, hresponse⟩ :=
    exists_quittingTerminalPayoff_update_stationary_eq_cap
      reward root target
  let responseHazard : ℕ → PMF Bool :=
    quittingBehaviorLiveHazard reward response
  let tail : ℕ → ι → PMF Bool :=
    quittingRootSequenceUpdate (fun _ => root) target responseHazard
  have hcollapse :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward (quittingStationaryProfile reward root) target response
  rw [quittingProfileLiveRoot_stationary] at hcollapse
  have hvalue :
      quittingRootSequenceTerminalValue reward tail target 0 =
        quittingStationaryUnilateralCap reward root target := by
    dsimp [tail]
    change
      quittingRootSequenceHazardTerminalValue reward (fun _ => root)
          target responseHazard 0 =
        quittingStationaryUnilateralCap reward root target
    rw [← hcollapse]
    exact hresponse
  refine ⟨tail, ?_, hvalue, ?_⟩
  · intro hazard
    have hsame :
        quittingRootSequenceHazardTerminalValue reward tail target hazard 0 =
          quittingRootSequenceHazardTerminalValue reward (fun _ => root)
            target hazard 0 := by
      apply quittingRootSequenceHazardTerminalValue_congr_of_opponents
      intro time player hplayer
      simp [tail, quittingRootSequenceUpdate,
        Function.update_of_ne hplayer]
    calc
      quittingRootSequenceHazardTerminalValue reward tail target hazard 0 =
          quittingRootSequenceHazardTerminalValue reward (fun _ => root)
            target hazard 0 := hsame
      _ ≤ quittingStationaryUnilateralCap reward root target :=
        quittingRootSequenceHazardTerminalValue_const_le_cap
          reward root target hazard
      _ = quittingRootSequenceTerminalValue reward tail target 0 :=
        hvalue.symm
  · intro time player hplayer
    simp [tail, quittingRootSequenceUpdate,
      Function.update_of_ne hplayer]

/-- Arbitrary-boundary version of finite backward selection.  The boundary is
the actual payoff vector of the supplied suffix. -/
theorem eq_quittingRootSequenceTerminalValue_of_finiteBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (cutoff : ℕ)
    (hterminal : value cutoff =
      fun who => quittingRootSequenceTerminalValue reward roots who cutoff)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) :
    ∀ time, time ≤ cutoff →
      value time =
        fun who => quittingRootSequenceTerminalValue reward roots who time := by
  intro time htime
  exact Nat.decreasingInduction (n := cutoff) (motive := fun time _ =>
      value time =
        fun who => quittingRootSequenceTerminalValue reward roots who time)
    (fun liveTime hlive ih => by
      rw [hpolicy liveTime hlive]
      funext who
      rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff]
      unfold quittingRootSuccessorPayoff
      apply quittingRootExpectedPayoff_continuation_congr
      exact congrFun ih who)
    hterminal
    htime

/-- Exact local Nash before an arbitrary actual suffix removes every
pre-cutoff residual.  Only the suffix best-reply debt survives. -/
theorem quittingRootSequenceHazardTerminalGap_le_finiteExactChain_of_boundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (hazard : ℕ → PMF Bool) (cutoff : ℕ) (debt : ℝ)
    (hterminal : value cutoff =
      fun player => quittingRootSequenceTerminalValue reward roots player cutoff)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (hdebt :
      max
          (quittingRootSequenceHazardTerminalValue reward roots who hazard cutoff -
            quittingRootSequenceTerminalValue reward roots who cutoff)
          0 ≤ debt) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 -
        value 0 who ≤
      quittingOpponentSurvivalWeight roots who 0 cutoff * debt := by
  have hselected :=
    eq_quittingRootSequenceTerminalValue_of_finiteBoundary
      reward roots value cutoff hterminal hpolicy
  have hvalueZero : value 0 who =
      quittingRootSequenceTerminalValue reward roots who 0 :=
    congrFun (hselected 0 (Nat.zero_le cutoff)) who
  have hsum :
      (∑ time ∈ Finset.range cutoff,
          quittingOpponentSurvivalWeight roots who 0 time *
            quittingPrescribedOneStepResidual reward roots who
              (quittingRootSequenceTerminalValue reward roots who) time) = 0 := by
    apply Finset.sum_eq_zero
    intro time htime
    have hlt : time < cutoff := Finset.mem_range.mp htime
    rw [quittingFiniteChain_prescribedResidual_eq_zero_of_rootNash
      reward roots value who time
        (hselected (time + 1) (Nat.succ_le_of_lt hlt))
        (hnash time hlt), mul_zero]
  have hgap := quittingRootSequenceHazardTerminalGap_le_finiteBudget
    reward roots who hazard 0 cutoff debt
      (by simpa only [Nat.zero_add] using hdebt)
  rw [hsum, zero_add, ← hvalueZero] at hgap
  exact hgap

/-- One target-closed suffix and one small own-survival coordinate control all
players.  The target's suffix debt is zero; every other suffix debt is at most
`2*M`, and its opponent reach contains the target's own survival as a factor. -/
theorem quittingRootSequenceHazardTerminalGap_le_targetOwnSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (target who : ι) (hazard : ℕ → PMF Bool) (cutoff : ℕ)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hterminal : value cutoff =
      fun player => quittingRootSequenceTerminalValue reward roots player cutoff)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (hclosed : IsQuittingTargetClosedAt reward roots target cutoff)
    (hsurvival :
      quittingHazardSurvival
          (quittingRootSequenceOwnHazard roots target) cutoff ≤ δ) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 -
        value 0 who ≤ 2 * M * δ := by
  by_cases hwho : who = target
  · subst who
    have hdebt :
        max
            (quittingRootSequenceHazardTerminalValue reward roots target hazard cutoff -
              quittingRootSequenceTerminalValue reward roots target cutoff)
            0 ≤ 0 := by
      apply max_le
      · exact sub_nonpos.mpr (hclosed hazard)
      · exact le_rfl
    have hgap :=
      quittingRootSequenceHazardTerminalGap_le_finiteExactChain_of_boundary
        reward roots value target hazard cutoff 0
          hterminal hpolicy hnash hdebt
    have hrhs : 0 ≤ 2 * M * δ := by positivity
    simpa using hgap.trans hrhs
  · have hdeviation :
        |quittingRootSequenceHazardTerminalValue reward roots who hazard cutoff| ≤ M := by
      unfold quittingRootSequenceHazardTerminalValue
      exact abs_quittingRootSequenceTerminalValue_le
        reward (quittingRootSequenceUpdate roots who hazard) who cutoff hM hreward
    have hprescribed :
        |quittingRootSequenceTerminalValue reward roots who cutoff| ≤ M :=
      abs_quittingRootSequenceTerminalValue_le
        reward roots who cutoff hM hreward
    have hdebt :
        max
            (quittingRootSequenceHazardTerminalValue reward roots who hazard cutoff -
              quittingRootSequenceTerminalValue reward roots who cutoff)
            0 ≤ 2 * M := by
      rw [abs_le] at hdeviation hprescribed
      apply max_le
      · linarith
      · linarith
    have hgap :=
      quittingRootSequenceHazardTerminalGap_le_finiteExactChain_of_boundary
        reward roots value who hazard cutoff (2 * M)
          hterminal hpolicy hnash hdebt
    have hreach :
        quittingOpponentSurvivalWeight roots who 0 cutoff ≤ δ := by
      exact
        (quittingOpponentSurvivalWeight_le_quittingHazardSurvival_ownHazard
          roots hwho.symm cutoff).trans hsurvival
    have hscaled :
        quittingOpponentSurvivalWeight roots who 0 cutoff * (2 * M) ≤
          δ * (2 * M) :=
      mul_le_mul_of_nonneg_right hreach (by positivity)
    nlinarith [hgap, hscaled]

/-- Game-facing form of the one-coordinate target-tail compiler. -/
theorem finiteExactChainProfile_isεAsymptoticNash_of_targetClosedTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (target : ι) (cutoff : ℕ)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hterminal : value cutoff =
      fun player => quittingRootSequenceTerminalValue reward roots player cutoff)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (hclosed : IsQuittingTargetClosedAt reward roots target cutoff)
    (hsurvival :
      quittingHazardSurvival
          (quittingRootSequenceOwnHazard roots target) cutoff ≤ δ) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (2 * M * δ)
      (quittingInfinitePathProfile reward roots) := by
  intro who deviation
  have hgap :=
    quittingRootSequenceHazardTerminalGap_le_targetOwnSurvival
      reward roots value target who
        (quittingBehaviorLiveHazard reward deviation) cutoff
        hM hδ hreward hterminal hpolicy hnash hclosed hsurvival
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingProfileLiveRoot_infinitePathProfile,
    quittingTerminalPayoff_infinitePathProfile]
  have hselected :=
    eq_quittingRootSequenceTerminalValue_of_finiteBoundary
      reward roots value cutoff hterminal hpolicy
  rw [← congrFun (hselected 0 (Nat.zero_le cutoff)) who]
  linarith

end GameTheory
