/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Pure coalition locks in a quitting counterexample regime

A pure quitting coalition is *locked* when its exit payoff dominates the
behavioral punishment floor and no player gains by changing membership in the
coalition.  The associated pure root is then an exact Nash--Bellman self-loop.
If the coalition is nonempty, every traversal has absorption charge one, so
repeating the loop gives exact punishment-floor prefixes of arbitrary charge.

This module records that finite obstruction at three levels.

* `quittingCoalitionLockFinitePrefix` is the literal repeated exact prefix.
* `punishmentFloorPrefixChargeCapacity_eq_top_of_coalitionLock` shows that a
  lock makes the canonical prefix capacity infinite, while
  `quittingGame_exists_uniformPayoff_of_coalitionLock` feeds the same family to
  the finite-prefix compiler.
* `QuittingCounterexampleRegime.exists_strict_singleton_join_gain` specializes
  the obstruction to a positive singleton exit: some distinct outsider must
  strictly prefer joining it.

The last consequence is an independent capacity-side route to a restriction
for which the terminal-gap toggle theorem gives a stronger quantitative
version.  The reusable content here is the explicit connection from stable
pure coalitions to infinite canonical prefix capacity.

The singleton member's Continue deviation is not identified with the empty-set
payoff.  At the one-stage self-loop it reaches the same singleton continuation
value.  The fixed-point and root-Nash proofs below pass through the stationary
profile identity, which treats this boundary case exactly.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A nonempty pure quitting coalition whose exit payoff is above the
behavioral punishment floor and is stable against every unilateral membership
toggle. -/
def IsQuittingCoalitionLock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) : Prop :=
  S.Nonempty ∧
    (∀ who, quittingPunishmentValue reward who ≤
      quittingSetReward reward S who) ∧
    IsQuittingSureExitSet reward S

/-- The set reward is a Bellman fixed point of its pure set root.  This is
valid even for the empty set.  In particular, at a singleton the owner's
Continue endpoint rolls into the same singleton continuation value. -/
theorem quittingPureSetRoot_setReward_fixedPoint (S : Finset ι) :
    quittingSetReward reward S =
      quittingRootSuccessorPayoff reward (quittingSetReward reward S)
        (quittingPureSetRoot S) := by
  funext who
  let profile :=
    quittingStationaryProfile reward (quittingPureSetRoot S)
  calc
    quittingSetReward reward S who =
        quittingTerminalPayoff reward profile who := by
      symm
      exact quittingTerminalPayoff_pureSetRoot reward S who
    _ = quittingRootExpectedPayoff reward
          (fun player => quittingTerminalPayoff reward profile player)
          (quittingPureSetRoot S) who :=
      quittingTerminalPayoff_stationary_eq_rootExpectedPayoff
        reward (quittingPureSetRoot S) who
    _ = quittingRootExpectedPayoff reward
          (quittingSetReward reward S) (quittingPureSetRoot S) who := by
      apply quittingRootExpectedPayoff_continuation_congr
      exact quittingTerminalPayoff_pureSetRoot reward S who

/-- A stable pure quitting coalition is an exact root Nash action against its
own set reward.  The result includes singleton and empty coalitions. -/
theorem isZeroQuittingRootNash_pureSetRoot_setReward
    (S : Finset ι) (hstable : IsQuittingSureExitSet reward S) :
    IsεQuittingRootNash reward (quittingSetReward reward S) 0
      (quittingPureSetRoot S) := by
  have hbehavior :=
    (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet reward S).2
      hstable
  have hroot := isεQuittingRootNash_of_isεAsymptoticNash_stationary
    reward (quittingPureSetRoot S) 0 hbehavior
  simpa only [quittingTerminalPayoff_pureSetRoot] using hroot

/-- Stability already places a pure set reward above the behavioral
punishment floor: the punishment value is below the stationary unilateral
cap, and stability bounds both membership toggles by the set reward. -/
theorem quittingPunishmentValue_le_setReward_of_isQuittingSureExitSet
    (S : Finset ι) (hstable : IsQuittingSureExitSet reward S) (who : ι) :
    quittingPunishmentValue reward who ≤
      quittingSetReward reward S who := by
  have hfloor := quittingPunishmentValue_le_stationaryUnilateralCap
    reward who (quittingPureSetRoot S)
  rw [quittingStationaryUnilateralCap_pureSetRoot] at hfloor
  exact hfloor.trans
    ((isQuittingSureExitSet_iff_forall_max reward S).1 hstable who)

/-- Every nonempty stable pure quitting coalition canonically supplies a
coalition lock. -/
theorem isQuittingCoalitionLock_of_isQuittingSureExitSet
    {S : Finset ι} (hS : S.Nonempty)
    (hstable : IsQuittingSureExitSet reward S) :
    IsQuittingCoalitionLock reward S :=
  ⟨hS,
    fun who =>
      quittingPunishmentValue_le_setReward_of_isQuittingSureExitSet
        S hstable who,
    hstable⟩

/-- Repeat a coalition lock for a prescribed finite horizon.  Every row and
value is literally constant; the orientation is the forward-prefix
orientation used by `QuittingPunishmentFloorFinitePrefix`. -/
def quittingCoalitionLockFinitePrefix
    {S : Finset ι} (hlock : IsQuittingCoalitionLock reward S)
    (horizon : ℕ) : QuittingPunishmentFloorFinitePrefix reward where
  roots := fun _ => quittingPureSetRoot S
  value := fun _ => quittingSetReward reward S
  horizon := horizon
  value_mem := by
    intro _ _
    have hbound : ∀ who,
        |quittingSetReward reward S who| ≤ quittingRewardBound reward := by
      intro who
      rw [quittingSetReward_of_nonempty reward hlock.1]
      exact abs_reward_le_quittingRewardBound reward _ who
    constructor <;> intro who
    · exact (abs_le.mp (hbound who)).1
    · exact (abs_le.mp (hbound who)).2
  anchor_floor := hlock.2.1
  policy := by
    intro _ _
    exact quittingPureSetRoot_setReward_fixedPoint S
  exactNash := by
    intro _ _
    exact isZeroQuittingRootNash_pureSetRoot_setReward S hlock.2.2

/-- A repeated nonempty coalition lock has exactly one unit of absorption
charge per stage. -/
@[simp] theorem quittingCoalitionLockFinitePrefix_charge
    {S : Finset ι} (hlock : IsQuittingCoalitionLock reward S)
    (horizon : ℕ) :
    (quittingCoalitionLockFinitePrefix hlock horizon).charge = horizon := by
  simp [quittingCoalitionLockFinitePrefix,
    QuittingPunishmentFloorFinitePrefix.charge,
    quittingRootAbsorptionMass_pureSetRoot_of_nonempty hlock.1]

/-- A coalition lock makes the canonical exact punishment-floor prefix
capacity infinite. -/
theorem punishmentFloorPrefixChargeCapacity_eq_top_of_coalitionLock
    {S : Finset ι} (hlock : IsQuittingCoalitionLock reward S) :
    quittingPunishmentFloorPrefixChargeCapacity reward = ⊤ := by
  rw [punishmentFloorPrefixChargeCapacity_eq_top_iff]
  intro target _
  obtain ⟨horizon, hhorizon⟩ := exists_nat_gt target
  refine ⟨quittingCoalitionLockFinitePrefix hlock horizon, ?_⟩
  simpa using hhorizon

/-- The arbitrarily charged exact prefixes generated by a coalition lock
produce a uniform-equilibrium payoff through the finite-prefix compiler. -/
theorem quittingGame_exists_uniformPayoff_of_coalitionLock
    {S : Finset ι} (hlock : IsQuittingCoalitionLock reward S) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨member, hmember⟩ := hlock.1
  letI : Nonempty ι := ⟨member⟩
  apply quittingGame_exists_uniformPayoff_of_unbounded_floorPrefixCharge
    reward
  intro target _
  obtain ⟨horizon, hhorizon⟩ := exists_nat_ge target
  refine ⟨quittingCoalitionLockFinitePrefix hlock horizon, ?_⟩
  simpa using hhorizon

namespace QuittingCounterexampleRegime

/-- Finite prefix capacity forbids every nonempty punishment-floor-stable
pure quitting coalition in a counterexample regime. -/
theorem not_isQuittingCoalitionLock
    (regime : QuittingCounterexampleRegime reward) {S : Finset ι} :
    ¬ IsQuittingCoalitionLock reward S := by
  intro hlock
  exact regime.prefixChargeCapacity_ne_top
    (punishmentFloorPrefixChargeCapacity_eq_top_of_coalitionLock hlock)

/-- A counterexample regime has no nonempty stable pure quitting coalition.
The punishment-floor clause needed by the capacity argument is derived from
stability rather than assumed separately. -/
theorem not_isQuittingSureExitSet_of_nonempty_via_prefixCapacity
    (regime : QuittingCounterexampleRegime reward) {S : Finset ι}
    (hS : S.Nonempty) :
    ¬ IsQuittingSureExitSet reward S := by
  intro hstable
  exact regime.not_isQuittingCoalitionLock
    (isQuittingCoalitionLock_of_isQuittingSureExitSet hS hstable)

/-- **Singleton-lock consequence.**  If an owner's singleton exit pays that
owner nonnegatively, some distinct outsider strictly prefers joining the
exit.  Equivalently, a counterexample table cannot satisfy all singleton
join-lock inequalities around such an owner.

No cardinality assumption is needed: the conclusion itself supplies a second
player.  The quantitative counterexample regime separately provides an owner
with strictly positive singleton reward. -/
theorem exists_strict_singleton_join_gain
    (regime : QuittingCounterexampleRegime reward) {owner : ι}
    (howner : 0 ≤ quittingSoloReward reward owner owner) :
    ∃ outsider, outsider ≠ owner ∧
      quittingSoloReward reward owner outsider <
        quittingSingletonCollisionReward reward owner outsider := by
  by_contra hno
  push Not at hno
  have hstable :
      IsQuittingSureExitSet reward ({owner} : Finset ι) :=
    (isQuittingSureExitSet_singleton_iff reward owner).2
      ⟨howner, fun outsider hne => hno outsider hne⟩
  exact regime.not_isQuittingSureExitSet_of_nonempty_via_prefixCapacity
    (Finset.singleton_nonempty owner) hstable

end QuittingCounterexampleRegime

end GameTheory
