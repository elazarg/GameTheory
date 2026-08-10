/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedSoloExtraction
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseCompiler
import UniformEquilibrium.Quitting.Punishment.ApproximateCompletedCycle

/-!
# Completion seam for a deficient conditioned deleted clock

A summable player-deleted conditioned clock forces the full conditioned payoff
vector to converge to that player's singleton payoff vector.  This file turns
that analytic extraction into an equilibrium object.

The closure has two steps.

* A singleton vector satisfying every inactive player's weak singleton-floor
  inequality is compiled by vanishing positive solo hazards.  The only error
  is collision with the owner, bounded by `2 M h` at hazard `h`.
* At a singleton-tight conditioned boundary, the inherited source floor passes
  to the extracted limit.  Hence a deficient deleted clock supplies exactly
  the weak inequalities required by the first step.

The final dichotomy removes the deleted-completeness hypothesis from the
existing diffuse compiler: either a deleted clock is summable and produces a
uniform solo payoff, or every deleted clock is complete and the diffuse
rescaled path is an explicit asymptotic Nash profile.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Viable solo vectors compile directly -/

/-- A singleton payoff vector above every player's own-singleton floor is a
uniform-equilibrium payoff, provided the active owner can be punished down to
its own singleton payoff.

The approximating stationary roots let only `owner` quit, with hazard
`1 / (n + 1)`.  An inactive player's Quit value is a mixture of its own
singleton reward and its collision reward with `owner`.  The weak floor
inequality controls the first term; boundedness charges the collision by at
most `2 M / (n + 1)`. -/
theorem isUniformEquilibriumPayoff_soloReward_of_weakSingletonFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hfloor : ∀ other,
      quittingSoloReward reward other other ≤
        quittingSoloReward reward owner other)
    (hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  let rate : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1)
  have hratePositive : ∀ n, 0 < rate n := by
    intro n
    dsimp only [rate]
    positivity
  have hrateNonneg : ∀ n, 0 ≤ rate n := fun n => (hratePositive n).le
  have hrateOne : ∀ n, rate n ≤ 1 := by
    intro n
    dsimp only [rate]
    have hden : 0 < (n : ℝ) + 1 := by positivity
    apply (div_le_one hden).2
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hrateVanish : Tendsto rate atTop (nhds 0) := by
    simpa only [rate] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0))
  let hazard : ℕ → PMF Bool := fun n =>
    quittingHazardCoin (rate n) (hrateNonneg n) (hrateOne n)
  let error : ℕ → ℝ := fun n => 2 * M * rate n
  have hhazardPositive : ∀ n, 0 < (hazard n true).toReal := by
    intro n
    dsimp only [hazard]
    simpa using hratePositive n
  apply isUniformEquilibriumPayoff_soloReward_of_approximate_caps
    reward owner hazard error hhazardPositive
  · intro n
    dsimp only [error]
    exact mul_nonneg (mul_nonneg (by norm_num) hM) (hrateNonneg n)
  · have hscaled := hrateVanish.const_mul (2 * M)
    simpa only [error] using hscaled
  · intro n other hother
    rw [quittingStationaryUnilateralCap_solo_other
      reward hother (hazard n) (hhazardPositive n)]
    apply max_le
    · rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
        reward hother (hazard n)]
      dsimp only [hazard, error]
      rw [quittingHazardCoin_false_toReal,
        quittingHazardCoin_true_toReal]
      have hcollisionAbs :
          |quittingSingletonCollisionReward reward owner other| ≤ M := by
        simpa [quittingSingletonCollisionReward] using
          hreward ⟨{owner, other}, by simp⟩ other
      have htargetAbs :
          |quittingSoloReward reward owner other| ≤ M := by
        simpa [quittingSoloReward] using
          hreward (quittingSingletonTerminal owner) other
      have hspread :
          quittingSingletonCollisionReward reward owner other -
              quittingSoloReward reward owner other ≤ 2 * M := by
        have hcollisionUpper := (abs_le.mp hcollisionAbs).2
        have htargetLower := (abs_le.mp htargetAbs).1
        linarith
      have hfloorTerm :
          (1 - rate n) *
              (quittingSoloReward reward other other -
                quittingSoloReward reward owner other) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          (sub_nonneg.mpr (hrateOne n))
          (sub_nonpos.mpr (hfloor other))
      have hcollisionTerm :
          rate n *
              (quittingSingletonCollisionReward reward owner other -
                quittingSoloReward reward owner other - 2 * M) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (hrateNonneg n) (by linarith)
      have hgap :
          (1 - rate n) * quittingSoloReward reward other other +
                rate n * quittingSingletonCollisionReward reward owner other -
              (quittingSoloReward reward owner other + 2 * M * rate n) ≤ 0 := by
        calc
          _ = (1 - rate n) *
                (quittingSoloReward reward other other -
                  quittingSoloReward reward owner other) +
              rate n *
                (quittingSingletonCollisionReward reward owner other -
                  quittingSoloReward reward owner other - 2 * M) := by ring
          _ ≤ 0 := add_nonpos hfloorTerm hcollisionTerm
      exact sub_nonpos.mp hgap
    · dsimp only [error]
      exact le_add_of_nonneg_right
        (mul_nonneg (mul_nonneg (by norm_num) hM) (hrateNonneg n))
  · exact hpunishment

/-! ## Summable deleted clock to solo equilibrium -/

/-- A summable conditioned clock with `owner` deleted produces the owner's
uniform singleton payoff whenever the conditioned source carries the
singleton floor and the owner satisfies the punishment inequality. -/
theorem isUniformEquilibriumPayoff_soloReward_of_summableConditionedOpponentWeight
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0))
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (htight : ∀ who,
      boundary who = quittingSoloBaseline reward who)
    (hsourceFloor : ∀ time who,
      quittingSoloBaseline reward who ≤ value time who)
    (owner : ι)
    (hclock : Summable (fun time =>
      quittingTailConditionedOpponentWeight roots time owner))
    (hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  have hconditionedFloor : ∀ time who,
      quittingSoloBaseline reward who ≤
        quittingTailConditionedValue roots value boundary time who := by
    intro time who
    exact quittingSoloBaseline_le_conditionedValue_of_tightBoundary
      roots value boundary time who (hpositive time) (htight who)
        (hsourceFloor time who)
  have hconverges :=
    tendsto_quittingTailConditionedValue_solo_of_summableOpponentWeight
      (reward := reward) roots value boundary hpolicy hM hreward hpositive
        heventualZero hconditionedBound owner hclock
  have hlimitFloor : ∀ other,
      quittingSoloReward reward other other ≤
        quittingSoloReward reward owner other := by
    intro other
    have hle :
        quittingSoloBaseline reward other ≤
          reward (quittingSingletonTerminal owner) other :=
      le_of_tendsto_of_tendsto tendsto_const_nhds (hconverges other)
        (Eventually.of_forall fun time => hconditionedFloor time other)
    simpa [quittingSoloBaseline, quittingSoloReward,
      quittingSingletonTerminal] using hle
  exact isUniformEquilibriumPayoff_soloReward_of_weakSingletonFloor
    reward owner hM hreward hlimitFloor hpunishment

/-- Boundary form of the deficient-clock completion.  At a singleton-tight
counterexample boundary the owner punishment inequality follows by comparing
the punishment value with the boundary coordinate. -/
theorem isUniformEquilibriumPayoff_soloReward_of_summableConditionedOpponentWeight_of_boundary
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0))
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (htight : ∀ who,
      boundary who = quittingSoloBaseline reward who)
    (hsourceFloor : ∀ time who,
      quittingSoloBaseline reward who ≤ value time who)
    (hboundaryPunishment : ∀ who,
      quittingPunishmentValue reward who ≤ boundary who)
    (owner : ι)
    (hclock : Summable (fun time =>
      quittingTailConditionedOpponentWeight roots time owner)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  have hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner := by
    calc
      quittingPunishmentValue reward owner ≤ boundary owner :=
        hboundaryPunishment owner
      _ = quittingSoloBaseline reward owner := htight owner
      _ = quittingSoloReward reward owner owner :=
        quittingSoloBaseline_apply reward owner
  exact isUniformEquilibriumPayoff_soloReward_of_summableConditionedOpponentWeight
    roots value boundary hpolicy hM hreward hpositive heventualZero
      hconditionedBound htight hsourceFloor owner hclock hpunishment

/-! ## Deleted-clock dichotomy -/

/-- **Deficient-clock breakthrough.**  The deleted-completeness side condition
of the diffuse rescaling compiler can be discharged internally.

If some suffix of a player-deleted conditioned clock is summable, summability
of the whole clock follows after restoring its finite prefix, and the player
supplies a uniform singleton payoff.  Otherwise all deleted clocks are
complete and the existing diffuse compiler applies unchanged. -/
theorem conditionedDiffuseRescaledRoots_deletedClockDichotomy
    [Nonempty ι]
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {M rho : ℝ} (hM : 0 ≤ M) (hrho : 0 ≤ rho)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0))
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (htight : ∀ who,
      boundary who = quittingSoloBaseline reward who)
    (hsourceFloor : ∀ time who,
      quittingSoloBaseline reward who ≤ value time who)
    (hboundaryPunishment : ∀ who,
      quittingPunishmentValue reward who ≤ boundary who)
    (hmesh : ∀ time,
      quittingTailConditionedAbsorptionWeight roots time ≤ rho)
    (hsmall : ∀ time, Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1)
    (hhalf : ∀ time,
      quittingTailConditionedAbsorptionWeight roots time ≤ 1 / 2) :
    (∃ owner,
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingSoloReward reward owner)) ∨
      ((quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward)
          ((6 * M * Fintype.card ι * rho) +
            (2 * M * Fintype.card ι * rho) +
            ((7 * Fintype.card ι + 16) * M * rho))
          (quittingInfinitePathProfile reward
            (quittingTailDiffuseRescaledRoots roots hpositive)) ∧
        ∀ who,
          |quittingTerminalPayoff reward
              (quittingInfinitePathProfile reward
                (quittingTailDiffuseRescaledRoots roots hpositive)) who -
            quittingTailConditionedValue roots value boundary 0 who| ≤
          6 * M * Fintype.card ι * rho) := by
  by_cases hdeletedComplete : ∀ who start,
      ¬Summable (fun offset =>
        quittingTailConditionedOpponentWeight roots (start + offset) who)
  · exact Or.inr <|
      conditionedDiffuseRescaledRoots_isεAsymptoticNash_and_approximates
        (reward := reward) roots value boundary hpolicy hnash hM hrho hreward
          hpositive hconditionedBound htight hsourceFloor hmesh hsmall hhalf
            hdeletedComplete
  · push Not at hdeletedComplete
    obtain ⟨owner, start, hsuffix⟩ := hdeletedComplete
    have hshift : Summable (fun offset =>
        quittingTailConditionedOpponentWeight roots (offset + start) owner) := by
      simpa [Nat.add_comm] using hsuffix
    have hclock : Summable (fun time =>
        quittingTailConditionedOpponentWeight roots time owner) :=
      (summable_nat_add_iff start).1 hshift
    refine Or.inl ⟨owner, ?_⟩
    exact
      isUniformEquilibriumPayoff_soloReward_of_summableConditionedOpponentWeight_of_boundary
        roots value boundary hpolicy hM hreward hpositive heventualZero
          hconditionedBound htight hsourceFloor hboundaryPunishment owner hclock

end GameTheory
