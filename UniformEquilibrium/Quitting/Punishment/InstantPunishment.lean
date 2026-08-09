/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.CollisionRepairCharacterization
import UniformEquilibrium.Quitting.Boundary.Repair.CoupledPhaseSwitchCap
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalTargetSemantics

/-!
# Instant quitting equilibria completed by punishment

An instant profile prescribes that one player `owner` quits surely at the first
stage while every other player continues.  If play is unexpectedly still live
at stage one, the continuation punishes `owner`.  Since the stage-zero row
absorbs surely on path, the continuation is reached only after `owner` refuses
to quit.

The exact criterion has two independent parts:

* `owner`'s singleton payoff dominates its quitting punishment value;
* no other player gains by joining `owner`'s first-stage exit.

The first condition is the missing replacement for the passive-continuation
condition `0 ≤ r_owner({owner})`: a negative singleton payoff is enforceable
whenever an off-path punishment holds the owner weakly below it.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The stage-zero row of an instant profile: `owner` quits surely and every
other player continues surely. -/
def quittingInstantRoot (owner : ι) : ι → PMF Bool :=
  quittingSoloStationaryRoot owner (PMF.pure true)

/-- The instant-profile individual-rationality condition. -/
def IsQuittingInstantPunishmentIR
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : Prop :=
  quittingPunishmentValue reward owner ≤ quittingSoloReward reward owner owner

/-- The instant-profile no-join condition. -/
def IsQuittingInstantNoJoin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : Prop :=
  ∀ other, other ≠ owner →
    quittingSingletonCollisionReward reward owner other ≤
      quittingSoloReward reward owner other

/-- The instant mechanism works when every positive tolerance admits some
continuation profile, with the sure-solo row fixed at stage zero, that is a
terminal approximate Nash equilibrium.  The continuation is deliberately not
restricted to be stationary in this definition. -/
def QuittingInstantPunishmentWorks
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ profile : (quittingGame reward).BehaviorProfile,
      quittingProfileLiveRoot reward profile 0 = quittingInstantRoot owner ∧
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile

/-- Any profile whose stage-zero row is the sure-solo instant root realizes the
singleton payoff vector, independently of its off-path continuation. -/
theorem quittingTerminalPayoff_eq_soloReward_of_liveRoot_eq_instant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (profile : (quittingGame reward).BehaviorProfile)
    (hroot : quittingProfileLiveRoot reward profile 0 = quittingInstantRoot owner) :
    quittingTerminalPayoff reward profile = quittingSoloReward reward owner := by
  funext who
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingRootSequenceTerminalValue_zero_of_continueMass_eq_zero reward _ who]
  · rw [hroot]
    unfold quittingInstantRoot
    rw [quittingRootAbsorbingContribution_solo]
    simp
  · rw [hroot]
    simp [quittingInstantRoot]

/-- A constant product row approximates one player's exact quitting punishment
value from above. -/
theorem exists_quittingStationaryPunishmentRoot_lt_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ root : ι → PMF Bool,
      quittingStationaryUnilateralCap reward root who <
        quittingPunishmentValue reward who + ε := by
  haveI : Nonempty (ι → PMF Bool) := ⟨fun _ => PMF.pure false⟩
  refine exists_lt_of_ciInf_lt
    (f := fun root : ι → PMF Bool =>
      quittingStationaryUnilateralCap reward root who) ?_
  change quittingStationaryPunishmentValue reward who < _
  rw [← quittingPunishmentValue_eq_stationaryPunishmentValue]
  linarith

/-- Sufficiency at a supplied near-optimal stationary punishment row. -/
theorem isεAsymptoticNash_quittingInstantPunishmentProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hIR : IsQuittingInstantPunishmentIR reward owner)
    (hnoJoin : IsQuittingInstantNoJoin reward owner)
    {ε : ℝ} (hε : 0 ≤ ε) {punishRow : ι → PMF Bool}
    (hpunish : quittingStationaryUnilateralCap reward punishRow owner ≤
      quittingPunishmentValue reward owner + ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingOneStagePunishedProfile reward (quittingInstantRoot owner)
        punishRow) := by
  intro who deviation
  have hvalue : quittingTerminalPayoff reward
      (quittingOneStagePunishedProfile reward (quittingInstantRoot owner)
        punishRow) who = quittingSoloReward reward owner who := by
    have hroot := quittingProfileLiveRoot_oneStagePunishedProfile_zero
      reward (quittingInstantRoot owner) punishRow
    exact congrFun
      (quittingTerminalPayoff_eq_soloReward_of_liveRoot_eq_instant
        reward owner _ hroot) who
  have hcap := quittingTerminalPayoff_update_oneStagePunishedProfile_le reward
    (quittingInstantRoot owner) punishRow who deviation
  rw [ge_iff_le, hvalue]
  refine hcap.trans ?_
  by_cases hwho : who = owner
  · subst who
    unfold quittingInstantRoot at *
    rw [quittingStationaryFixedOpponentsQuitValue_solo_owner,
      quittingStationaryFixedOpponentsContinueReward_solo_owner,
      quittingStationaryFixedOpponentsContinueMass_solo_owner,
      zero_add, one_mul]
    exact max_le (by linarith) (by
      unfold IsQuittingInstantPunishmentIR at hIR
      linarith)
  · unfold quittingInstantRoot
    rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
        reward hwho (PMF.pure true),
      quittingStationaryFixedOpponentsContinueReward_solo_other
        reward hwho (PMF.pure true),
      quittingStationaryFixedOpponentsContinueMass_solo_other
        hwho (PMF.pure true)]
    simp only [PMF.pure_apply, if_true,
      if_neg (by decide : (false : Bool) ≠ true), ENNReal.toReal_one,
      ENNReal.toReal_zero, zero_mul, one_mul, zero_add, add_zero]
    exact max_le (by
      exact (hnoJoin who hwho).trans (le_add_of_nonneg_right hε))
      (le_add_of_nonneg_right hε)

/-- The two scalar conditions produce instant terminal approximate equilibria
at every accuracy. -/
theorem quittingInstantPunishmentWorks_of_conditions
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hIR : IsQuittingInstantPunishmentIR reward owner)
    (hnoJoin : IsQuittingInstantNoJoin reward owner) :
    QuittingInstantPunishmentWorks reward owner := by
  intro ε hε
  obtain ⟨punishRow, hpunish⟩ :=
    exists_quittingStationaryPunishmentRoot_lt_add reward owner hε
  refine ⟨quittingOneStagePunishedProfile reward (quittingInstantRoot owner)
    punishRow, quittingProfileLiveRoot_oneStagePunishedProfile_zero reward _ _, ?_⟩
  exact isεAsymptoticNash_quittingInstantPunishmentProfile
    reward owner hIR hnoJoin hε.le hpunish.le

/-- Necessity of the no-join inequalities. -/
theorem isQuittingInstantNoJoin_of_works
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hworks : QuittingInstantPunishmentWorks reward owner) :
    IsQuittingInstantNoJoin reward owner := by
  intro other hother
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨profile, hroot, hnash⟩ := hworks ε hε
  have hvalue := quittingTerminalPayoff_eq_soloReward_of_liveRoot_eq_instant
    reward owner profile hroot
  have hdev := hnash other
    (fun _time _history => (PMF.pure true : PMF Bool))
  rw [quittingTerminalPayoff_update_quitNow, hroot] at hdev
  rw [congrFun hvalue other] at hdev
  unfold quittingInstantRoot at hdev
  rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
      reward hother (PMF.pure true)] at hdev
  simpa using hdev

/-- Necessity of the punishment-value individual-rationality inequality. -/
theorem isQuittingInstantPunishmentIR_of_works
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hworks : QuittingInstantPunishmentWorks reward owner) :
    IsQuittingInstantPunishmentIR reward owner := by
  unfold IsQuittingInstantPunishmentIR
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨profile, hroot, hnash⟩ := hworks ε hε
  have hvalue := quittingTerminalPayoff_eq_soloReward_of_liveRoot_eq_instant
    reward owner profile hroot
  have htailCap : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward
        (fun time => quittingProfileLiveRoot reward profile (time + 1))
        owner g 0 ≤ quittingSoloReward reward owner owner + ε := by
    intro g
    obtain ⟨deviation, hdeviation⟩ :=
      exists_quittingTerminalPayoff_update_continueThen reward profile owner g
    have hdev := hnash owner deviation
    rw [hdeviation, congrFun hvalue owner, hroot] at hdev
    unfold quittingInstantRoot at hdev
    rw [quittingStationaryFixedOpponentsContinueReward_solo_owner,
      quittingStationaryFixedOpponentsContinueMass_solo_owner,
      zero_add, one_mul] at hdev
    exact hdev
  have hfloor := quittingStationaryPunishmentValue_le_of_forall_hazard_le reward
    (fun time => quittingProfileLiveRoot reward profile (time + 1)) owner htailCap
  rw [← quittingPunishmentValue_eq_stationaryPunishmentValue] at hfloor
  exact hfloor

/-- **Exact instant-punishment characterization.** -/
theorem quittingInstantPunishmentWorks_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    QuittingInstantPunishmentWorks reward owner ↔
      IsQuittingInstantPunishmentIR reward owner ∧
        IsQuittingInstantNoJoin reward owner := by
  constructor
  · intro hworks
    exact ⟨isQuittingInstantPunishmentIR_of_works reward owner hworks,
      isQuittingInstantNoJoin_of_works reward owner hworks⟩
  · rintro ⟨hIR, hnoJoin⟩
    exact quittingInstantPunishmentWorks_of_conditions reward owner hIR hnoJoin

/-- **Named-payoff consequence.**  The exact instant criterion makes the
singleton terminal vector a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_soloReward_of_instantPunishment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hIR : IsQuittingInstantPunishmentIR reward owner)
    (hnoJoin : IsQuittingInstantNoJoin reward owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_fixedTarget
  intro ε hε
  obtain ⟨profile, hroot, hnash⟩ :=
    quittingInstantPunishmentWorks_of_conditions reward owner hIR hnoJoin ε hε
  exact ⟨profile, hnash,
    quittingTerminalPayoff_eq_soloReward_of_liveRoot_eq_instant
      reward owner profile hroot⟩

end GameTheory
