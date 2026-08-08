/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Shared punishment in two-player quitting games

A player's quitting punishment value fixes an opponent plan and then takes the
player's best reply.  A shared punishment uses one committed plan for every
possible designated player.  This is not an equilibrium or credibility
assertion.

For two players the shared problem factorizes exactly.  The plan used to
punish `false` contributes only player `true`'s strategy, while the plan used
to punish `true` contributes only player `false`'s strategy.  Those two
coordinates can therefore be spliced into one profile without changing either
best-reply value.  The same statement holds for constant product rows.

Consequently every coordinatewise property separately realizable by two plans
is simultaneously realizable by one plan; one stationary row approaches both
individual punishment floors at every positive accuracy; and the exact shared
excess is zero both for arbitrary behavior plans and for stationary rows.
Attainment is not asserted and can fail because the individual infima need
not be attained.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

/-! ## Opponent-coordinate congruence -/

/-- A best-reply value depends only on the opponents' behavior strategies. -/
theorem quittingBestReplyValue_congr_of_opponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    [Fintype ι] [DecidableEq ι]
    {first second : (quittingGame reward).BehaviorProfile} (who : ι)
    (hagree : ∀ player, player ≠ who → first player = second player) :
    quittingBestReplyValue reward first who =
      quittingBestReplyValue reward second who := by
  unfold quittingBestReplyValue
  congr 1
  funext deviation
  have hupdate : Function.update first who deviation =
      Function.update second who deviation := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp
    · simp [Function.update_of_ne hplayer, hagree player hplayer]
  rw [hupdate]

/-! ## Exact two-player splicing -/

/-- Splice one plan per designated player into a shared two-player plan.
The strategy of `player` is taken from the plan intended to punish the other
player. -/
def quittingTwoPlayerSharedProfile
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (plans : Bool → (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  fun player => plans (!player) player

/-- Splice one product row per designated player into a shared row. -/
def quittingTwoPlayerSharedRoot
    (roots : Bool → (Bool → PMF Bool)) : Bool → PMF Bool :=
  fun player => roots (!player) player

/-- The shared profile preserves each designated player's separate
best-reply value exactly. -/
theorem quittingBestReplyValue_twoPlayerSharedProfile
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (plans : Bool → (quittingGame reward).BehaviorProfile) (who : Bool) :
    quittingBestReplyValue reward
        (quittingTwoPlayerSharedProfile reward plans) who =
      quittingBestReplyValue reward (plans who) who := by
  apply quittingBestReplyValue_congr_of_opponents reward who
  intro player hplayer
  cases who <;> cases player <;>
    simp_all [quittingTwoPlayerSharedProfile]

/-- The shared row preserves each designated player's separate stationary
cap exactly. -/
theorem quittingStationaryUnilateralCap_twoPlayerSharedRoot
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (roots : Bool → (Bool → PMF Bool)) (who : Bool) :
    quittingStationaryUnilateralCap reward
        (quittingTwoPlayerSharedRoot roots) who =
      quittingStationaryUnilateralCap reward (roots who) who := by
  apply quittingStationaryUnilateralCap_congr_of_opponents reward who
  intro player hplayer
  cases who <;> cases player <;>
    simp_all [quittingTwoPlayerSharedRoot]

/-- **Behavior-plan factorization.**  Any property imposed separately on the
two designated best-reply values can be imposed by one shared plan. -/
theorem exists_quittingTwoPlayerSharedProfile_iff
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (property : Bool → ℝ → Prop) :
    (∃ profile : (quittingGame reward).BehaviorProfile,
        ∀ who, property who (quittingBestReplyValue reward profile who)) ↔
      ∀ who, ∃ profile : (quittingGame reward).BehaviorProfile,
        property who (quittingBestReplyValue reward profile who) := by
  constructor
  · rintro ⟨profile, hprofile⟩ who
    exact ⟨profile, hprofile who⟩
  · intro hseparate
    choose plans hplans using hseparate
    refine ⟨quittingTwoPlayerSharedProfile reward plans, ?_⟩
    intro who
    rw [quittingBestReplyValue_twoPlayerSharedProfile]
    exact hplans who

/-- **Stationary-row factorization.**  Any property imposed separately on the
two stationary caps can be imposed by one shared row. -/
theorem exists_quittingTwoPlayerSharedRoot_iff
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (property : Bool → ℝ → Prop) :
    (∃ root : Bool → PMF Bool,
        ∀ who, property who
          (quittingStationaryUnilateralCap reward root who)) ↔
      ∀ who, ∃ root : Bool → PMF Bool,
        property who
          (quittingStationaryUnilateralCap reward root who) := by
  constructor
  · rintro ⟨root, hroot⟩ who
    exact ⟨root, hroot who⟩
  · intro hseparate
    choose roots hroots using hseparate
    refine ⟨quittingTwoPlayerSharedRoot roots, ?_⟩
    intro who
    rw [quittingStationaryUnilateralCap_twoPlayerSharedRoot]
    exact hroots who

/-! ## Simultaneous approximation of the individual floors -/

/-- One committed behavior plan simultaneously approaches both individual
punishment values from above. -/
theorem exists_quittingTwoPlayerSharedPunishmentProfile_lt_add
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile, ∀ who,
      quittingBestReplyValue reward profile who <
        quittingPunishmentValue reward who + ε := by
  haveI : Nonempty ((quittingGame reward).BehaviorProfile) :=
    ⟨quittingAlwaysContinueProfile reward⟩
  have hseparate : ∀ who : Bool,
      ∃ profile : (quittingGame reward).BehaviorProfile,
        quittingBestReplyValue reward profile who <
          quittingPunishmentValue reward who + ε := by
    intro who
    have hlt : quittingPunishmentValue reward who <
        quittingPunishmentValue reward who + ε :=
      lt_add_of_pos_right _ hε
    simpa only [quittingPunishmentValue] using
      (exists_lt_of_ciInf_lt
        (f := fun profile : (quittingGame reward).BehaviorProfile =>
          quittingBestReplyValue reward profile who) hlt)
  exact (exists_quittingTwoPlayerSharedProfile_iff reward
    (fun who value => value < quittingPunishmentValue reward who + ε)).2
      hseparate

/-- One constant product row simultaneously approaches both stationary
punishment floors from above. -/
theorem exists_quittingTwoPlayerSharedStationaryRoot_lt_add
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ root : Bool → PMF Bool, ∀ who,
      quittingStationaryUnilateralCap reward root who <
        quittingStationaryPunishmentValue reward who + ε := by
  have hseparate : ∀ who : Bool, ∃ root : Bool → PMF Bool,
      quittingStationaryUnilateralCap reward root who <
        quittingStationaryPunishmentValue reward who + ε := by
    intro who
    have hlt : quittingStationaryPunishmentValue reward who <
        quittingStationaryPunishmentValue reward who + ε :=
      lt_add_of_pos_right _ hε
    simpa only [quittingStationaryPunishmentValue] using
      (exists_lt_of_ciInf_lt
        (f := fun root : Bool → PMF Bool =>
          quittingStationaryUnilateralCap reward root who) hlt)
  exact (exists_quittingTwoPlayerSharedRoot_iff reward
    (fun who value =>
      value < quittingStationaryPunishmentValue reward who + ε)).2 hseparate

/-- Stationarity costs nothing for simultaneous two-player punishment: one
constant row approaches the actual committed-plan punishment value of every
player at once. -/
theorem exists_quittingTwoPlayerSharedStationaryPunishmentRoot_lt_add
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ root : Bool → PMF Bool, ∀ who,
      quittingStationaryUnilateralCap reward root who <
        quittingPunishmentValue reward who + ε := by
  simpa only [quittingPunishmentValue_eq_stationaryPunishmentValue] using
    (exists_quittingTwoPlayerSharedStationaryRoot_lt_add reward hε)

/-! ## Exact price: zero shared excess -/

/-- The shared committed-plan excess above the two individual punishment
floors. -/
def quittingTwoPlayerSharedPunishmentExcess
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) : ℝ :=
  ⨅ profile : (quittingGame reward).BehaviorProfile,
    max (quittingBestReplyValue reward profile false -
      quittingPunishmentValue reward false)
      (quittingBestReplyValue reward profile true -
        quittingPunishmentValue reward true)

/-- The shared constant-row excess above the two individual stationary
floors. -/
def quittingTwoPlayerSharedStationaryPunishmentExcess
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) : ℝ :=
  ⨅ root : Bool → PMF Bool,
    max (quittingStationaryUnilateralCap reward root false -
      quittingStationaryPunishmentValue reward false)
      (quittingStationaryUnilateralCap reward root true -
        quittingStationaryPunishmentValue reward true)

private theorem bddBelow_range_quittingTwoPlayerSharedPunishmentGap
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) :
    BddBelow (Set.range fun profile : (quittingGame reward).BehaviorProfile =>
      max (quittingBestReplyValue reward profile false -
        quittingPunishmentValue reward false)
        (quittingBestReplyValue reward profile true -
          quittingPunishmentValue reward true)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨profile, rfl⟩
  have hgap : 0 ≤ quittingBestReplyValue reward profile false -
      quittingPunishmentValue reward false :=
    sub_nonneg.mpr (quittingPunishmentValue_le reward false profile)
  exact hgap.trans (le_max_left _ _)

private theorem bddBelow_range_quittingTwoPlayerSharedStationaryGap
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) :
    BddBelow (Set.range fun root : Bool → PMF Bool =>
      max (quittingStationaryUnilateralCap reward root false -
        quittingStationaryPunishmentValue reward false)
        (quittingStationaryUnilateralCap reward root true -
          quittingStationaryPunishmentValue reward true)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨root, rfl⟩
  have hgap : 0 ≤ quittingStationaryUnilateralCap reward root false -
      quittingStationaryPunishmentValue reward false :=
    sub_nonneg.mpr (quittingStationaryPunishmentValue_le reward false root)
  exact hgap.trans (le_max_left _ _)

/-- **Zero price of shared punishment at two coordinates.** -/
theorem quittingTwoPlayerSharedPunishmentExcess_eq_zero
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) :
    quittingTwoPlayerSharedPunishmentExcess reward = 0 := by
  haveI : Nonempty ((quittingGame reward).BehaviorProfile) :=
    ⟨quittingAlwaysContinueProfile reward⟩
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨profile, hprofile⟩ :=
      exists_quittingTwoPlayerSharedPunishmentProfile_lt_add reward hε
    have hfalse : quittingBestReplyValue reward profile false -
        quittingPunishmentValue reward false ≤ ε := by
      linarith [hprofile false]
    have htrue : quittingBestReplyValue reward profile true -
        quittingPunishmentValue reward true ≤ ε := by
      linarith [hprofile true]
    have hmax : max
        (quittingBestReplyValue reward profile false -
          quittingPunishmentValue reward false)
        (quittingBestReplyValue reward profile true -
          quittingPunishmentValue reward true) ≤ ε :=
      max_le hfalse htrue
    exact (ciInf_le
      (bddBelow_range_quittingTwoPlayerSharedPunishmentGap reward) profile).trans
        (by simpa using hmax)
  · unfold quittingTwoPlayerSharedPunishmentExcess
    exact le_ciInf fun profile => by
      have hgap : 0 ≤ quittingBestReplyValue reward profile false -
          quittingPunishmentValue reward false :=
        sub_nonneg.mpr (quittingPunishmentValue_le reward false profile)
      exact hgap.trans (le_max_left _ _)

/-- The stationary shared excess is also exactly zero. -/
theorem quittingTwoPlayerSharedStationaryPunishmentExcess_eq_zero
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) :
    quittingTwoPlayerSharedStationaryPunishmentExcess reward = 0 := by
  haveI : Nonempty (Bool → PMF Bool) :=
    ⟨fun _ => PMF.pure false⟩
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨root, hroot⟩ :=
      exists_quittingTwoPlayerSharedStationaryRoot_lt_add reward hε
    have hfalse : quittingStationaryUnilateralCap reward root false -
        quittingStationaryPunishmentValue reward false ≤ ε := by
      linarith [hroot false]
    have htrue : quittingStationaryUnilateralCap reward root true -
        quittingStationaryPunishmentValue reward true ≤ ε := by
      linarith [hroot true]
    have hmax : max
        (quittingStationaryUnilateralCap reward root false -
          quittingStationaryPunishmentValue reward false)
        (quittingStationaryUnilateralCap reward root true -
          quittingStationaryPunishmentValue reward true) ≤ ε :=
      max_le hfalse htrue
    exact (ciInf_le
      (bddBelow_range_quittingTwoPlayerSharedStationaryGap reward) root).trans
        (by simpa using hmax)
  · unfold quittingTwoPlayerSharedStationaryPunishmentExcess
    exact le_ciInf fun root => by
      have hgap : 0 ≤ quittingStationaryUnilateralCap reward root false -
          quittingStationaryPunishmentValue reward false :=
        sub_nonneg.mpr (quittingStationaryPunishmentValue_le reward false root)
      exact hgap.trans (le_max_left _ _)

/-- Arbitrary behavior plans and stationary rows have the same shared
punishment price at two coordinates. -/
theorem quittingTwoPlayerSharedPunishmentExcess_eq_stationary
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) :
    quittingTwoPlayerSharedPunishmentExcess reward =
      quittingTwoPlayerSharedStationaryPunishmentExcess reward := by
  rw [quittingTwoPlayerSharedPunishmentExcess_eq_zero,
    quittingTwoPlayerSharedStationaryPunishmentExcess_eq_zero]

end GameTheory
