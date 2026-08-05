/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSingletonStationaryRoot
import GameTheory.Concepts.Stochastic.QuittingPositiveDynamicDebtProvenance
import GameTheory.Concepts.Stochastic.QuittingExceptionalTailProfileAdapter
import GameTheory.Concepts.Stochastic.QuittingTerminalUniformization

/-!
# Owner-solo certification, or a universal joining obstruction

The positive branch of the exact dynamic-debt split supplies a debt owner
with a strictly positive singleton reward, and terminal provenance identifies
the owner's optimal deviation as Continue-through-prefix followed by a solo
Quit.  This file certifies that deviation as prescribed play: the owner's
solo stationary root at any rate `p ∈ (0,1]` is an exact terminal Nash
equilibrium when every opponent's exact inactive inequality

`(1-p) * r_other({other}) + p * r_other({owner, other}) ≤ r_other({owner})`

holds.  The certified payoff is exactly `quittingSoloReward reward owner`.

Consequently positive debt has a sharper dichotomy.  Either some solo rate
certifies that payoff uniformly, or every positive rate has a strict joining
obstruction.  The obstruction supplies both a sure-rate strict joiner and,
by a finite minimum-gap argument, a weak preemptor at the vanishing-rate end.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Exact owner-solo certification -/

/-- **Exact owner-solo certification criterion.**  If the owner's singleton
reward is nonnegative and every opponent's inactive-Quit mixture is bounded
by that opponent's payoff under the owner's solo absorption, then the solo
stationary root is an exact terminal Nash equilibrium. -/
theorem isεAsymptoticNash_soloStationary_exact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal)
    (howner : 0 ≤ quittingSoloReward reward owner owner)
    (hinactive : ∀ other, other ≠ owner →
      (hazard false).toReal * quittingSoloReward reward other other +
        (hazard true).toReal *
          quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot owner hazard)) := by
  intro who deviation
  rw [quittingTerminalPayoff_soloStationary reward owner who hazard
    hpositive, add_zero]
  by_cases hwho : who = owner
  · subst who
    exact (quittingTerminalPayoff_update_solo_owner_le
      reward owner hazard deviation).trans (max_le howner le_rfl)
  · refine (quittingTerminalPayoff_update_stationary_le_unilateralCap
      reward (quittingSoloStationaryRoot owner hazard) who deviation
      (quittingStationaryFixedOpponentsContinueMass_solo_other_lt_one
        hwho hazard hpositive)).trans ?_
    rw [quittingStationaryUnilateralCap_solo_other reward hwho hazard
        hpositive,
      quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
        reward hwho hazard]
    exact max_le (hinactive who hwho) le_rfl

/-- The exact terminal-Nash property of a positive-hazard owner-solo root
forces both parts of the scalar certification test.  Never supplies the
owner inequality, while quitting immediately supplies each inactive-player
inequality. -/
theorem soloStationary_exact_conditions_of_isεAsymptoticNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot owner hazard))) :
    0 ≤ quittingSoloReward reward owner owner ∧
      ∀ other, other ≠ owner →
        (hazard false).toReal * quittingSoloReward reward other other +
          (hazard true).toReal *
            quittingSingletonCollisionReward reward owner other ≤
          quittingSoloReward reward owner other := by
  constructor
  · have hnever := hnash owner
      (quittingAlwaysContinueStrategy reward owner)
    have hprofiles :
        Function.update
            (quittingStationaryProfile reward
              (quittingSoloStationaryRoot owner hazard)) owner
              (quittingAlwaysContinueStrategy reward owner) =
          quittingAlwaysContinueProfile reward := by
      funext player time history
      by_cases hplayer : player = owner
      · subst player
        simp [quittingAlwaysContinueStrategy,
          quittingAlwaysContinueProfile,
          StochasticGame.stationaryBehaviorProfile]
      · simp [quittingStationaryProfile, quittingSoloStationaryRoot,
          quittingAlwaysContinueProfile, hplayer,
          StochasticGame.stationaryBehaviorProfile]
        rfl
    rw [hprofiles, quittingTerminalPayoff_quittingAlwaysContinue,
      quittingTerminalPayoff_soloStationary reward owner owner hazard
        hpositive,
      add_zero] at hnever
    exact hnever
  · intro other hother
    have hquit := hnash other
      (quittingPureTimeBehaviorStrategy reward other (some 0))
    rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue,
      quittingProfileLiveRoot_stationary,
      quittingTerminalPayoff_soloStationary reward owner other hazard
        hpositive,
      add_zero,
      quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
        reward hother hazard] at hquit
    exact hquit

/-- **Exact owner-solo characterization.**  At every positive solo hazard,
the terminal Nash property is equivalent to the owner Never inequality and
the finite family of inactive-player affine inequalities. -/
theorem isεAsymptoticNash_soloStationary_exact_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner hazard)) ↔
      0 ≤ quittingSoloReward reward owner owner ∧
        ∀ other, other ≠ owner →
          (hazard false).toReal * quittingSoloReward reward other other +
            (hazard true).toReal *
              quittingSingletonCollisionReward reward owner other ≤
            quittingSoloReward reward owner other := by
  constructor
  · exact soloStationary_exact_conditions_of_isεAsymptoticNash
      reward owner hazard hpositive
  · rintro ⟨howner, hinactive⟩
    exact isεAsymptoticNash_soloStationary_exact
      reward owner hazard hpositive howner hinactive

/-! ## Exact terminal Nash delivers its own terminal payoff uniformly -/

/-- An exact terminal Nash profile's own terminal payoff is a
uniform-equilibrium payoff. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 profile) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingTerminalPayoff reward profile) := by
  intro ε hε
  obtain ⟨nashThreshold, hnashThreshold⟩ :=
    quittingGame_isUniformεEquilibrium_of_terminalNash_finite
      reward profile hε hnash
  have heventuallyDelivery : ∀ᶠ horizon : ℕ in Filter.atTop, ∀ who,
      |(quittingGame reward).finiteAveragePayoff none horizon profile who -
        quittingTerminalPayoff reward profile who| ≤ ε := by
    apply Filter.eventually_all.mpr
    intro who
    have hball :=
      (tendsto_finiteAveragePayoff_quittingGame reward profile who).eventually
        (Metric.ball_mem_nhds
          (quittingTerminalPayoff reward profile who) hε)
    filter_upwards [hball] with horizon hhorizon
    simpa [Metric.mem_ball, Real.dist_eq] using hhorizon.le
  obtain ⟨deliveryThreshold, hdeliveryThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨profile, max nashThreshold deliveryThreshold,
    fun horizon hhorizon ↦ ⟨?_, ?_⟩⟩
  · exact hnashThreshold horizon
      (le_trans (Nat.le_max_left _ _) hhorizon)
  · exact hdeliveryThreshold horizon
      (le_trans (Nat.le_max_right _ _) hhorizon)

/-- The certified owner-solo payoff vector is a uniform-equilibrium
payoff. -/
theorem isUniformEquilibriumPayoff_soloReward_of_inactive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal)
    (howner : 0 ≤ quittingSoloReward reward owner owner)
    (hinactive : ∀ other, other ≠ owner →
      (hazard false).toReal * quittingSoloReward reward other other +
        (hazard true).toReal *
          quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  have hpayoff := quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    reward _ (isεAsymptoticNash_soloStationary_exact
      reward owner hazard hpositive howner hinactive)
  have heq : quittingTerminalPayoff reward
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot owner hazard)) =
      quittingSoloReward reward owner :=
    funext fun who ↦
      quittingTerminalPayoff_soloStationary reward owner who hazard hpositive
  rwa [heq] at hpayoff

/-! ## The rate dichotomy -/

/-- Some opponent strictly prefers quitting against the owner's solo rate
`p` to receiving the owner's solo absorption payoff. -/
def QuittingSoloJoiningObstruction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (p : ℝ) : Prop :=
  ∃ other, other ≠ owner ∧
    quittingSoloReward reward owner other <
      (1 - p) * quittingSoloReward reward other other +
        p * quittingSingletonCollisionReward reward owner other

omit [Fintype ι] in
/-- Either some rate in `(0,1]` satisfies every opponent's inactive
inequality, or every rate has a strict joiner or preemptor. -/
theorem soloCertification_or_universalJoining
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    (∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ other, other ≠ owner →
      (1 - p) * quittingSoloReward reward other other +
        p * quittingSingletonCollisionReward reward owner other ≤
          quittingSoloReward reward owner other) ∨
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      QuittingSoloJoiningObstruction reward owner p := by
  by_cases hfeasible : ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ other, other ≠ owner →
      (1 - p) * quittingSoloReward reward other other +
        p * quittingSingletonCollisionReward reward owner other ≤
          quittingSoloReward reward owner other
  · exact Or.inl hfeasible
  · right
    intro p hp0 hp1
    push Not at hfeasible
    obtain ⟨other, hne, hgt⟩ := hfeasible p hp0 hp1
    exact ⟨other, hne, hgt⟩

omit [Fintype ι] in
/-- A universal joining obstruction has a weak preemptor: some opponent's
own solo exit is at least as valuable as the owner's solo absorption payoff.
The proof uses a finite minimum gap, not a limiting choice of opponents. -/
theorem exists_weak_preemptor_of_universalJoining
    [Finite ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hobstruction : ∀ p : ℝ, 0 < p → p ≤ 1 →
      QuittingSoloJoiningObstruction reward owner p) :
    ∃ other, other ≠ owner ∧
      quittingSoloReward reward owner other ≤
        quittingSoloReward reward other other := by
  letI := Fintype.ofFinite ι
  by_contra hnot
  push Not at hnot
  obtain ⟨witness, hwitnessNe, _⟩ := hobstruction 1 one_pos le_rfl
  have hwitnessMem : witness ∈ Finset.univ.erase owner :=
    Finset.mem_erase.mpr ⟨hwitnessNe, Finset.mem_univ witness⟩
  have hopponents : (Finset.univ.erase owner).Nonempty :=
    ⟨witness, hwitnessMem⟩
  obtain ⟨gapArg, hgapMem, hgapMin⟩ := Finset.exists_min_image
    (Finset.univ.erase owner)
    (fun other ↦ quittingSoloReward reward owner other -
      quittingSoloReward reward other other) hopponents
  obtain ⟨spreadArg, _, hspreadMax⟩ := Finset.exists_max_image
    (Finset.univ.erase owner)
    (fun other ↦ |quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward other other|) hopponents
  set δ := quittingSoloReward reward owner gapArg -
    quittingSoloReward reward gapArg gapArg with hδdef
  set spread := |quittingSingletonCollisionReward reward owner spreadArg -
    quittingSoloReward reward spreadArg spreadArg| with hspreaddef
  have hδ : 0 < δ := by
    have := hnot gapArg (Finset.mem_erase.mp hgapMem).1
    rw [hδdef]
    linarith
  have hspread0 : 0 ≤ spread := abs_nonneg _
  set p := δ / (spread + δ) with hpdef
  have hdenominator : 0 < spread + δ := by linarith
  have hp0 : 0 < p := div_pos hδ hdenominator
  have hp1 : p ≤ 1 := (div_le_one hdenominator).mpr (by linarith)
  obtain ⟨other, hotherNe, hgt⟩ := hobstruction p hp0 hp1
  have hotherMem : other ∈ Finset.univ.erase owner :=
    Finset.mem_erase.mpr ⟨hotherNe, Finset.mem_univ other⟩
  have hspreadBound :
      quittingSingletonCollisionReward reward owner other -
        quittingSoloReward reward other other ≤ spread :=
    le_trans (le_abs_self _) (hspreadMax other hotherMem)
  have hgapBound : δ ≤ quittingSoloReward reward owner other -
      quittingSoloReward reward other other :=
    hgapMin other hotherMem
  have hsmall : p * spread < δ := by
    rw [hpdef, div_mul_eq_mul_div, div_lt_iff₀ hdenominator]
    nlinarith
  have hmix : (1 - p) * quittingSoloReward reward other other +
      p * quittingSingletonCollisionReward reward owner other =
      quittingSoloReward reward other other +
        p * (quittingSingletonCollisionReward reward owner other -
          quittingSoloReward reward other other) := by
    ring
  nlinarith [mul_le_mul_of_nonneg_left hspreadBound (le_of_lt hp0)]

omit [Fintype ι] in
/-- At the sure-quit rate `p = 1`, a universal obstruction supplies an
opponent which strictly gains by joining the owner's exit. -/
theorem exists_sure_joiner_of_universalJoining
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hobstruction : ∀ p : ℝ, 0 < p → p ≤ 1 →
      QuittingSoloJoiningObstruction reward owner p) :
    ∃ other, other ≠ owner ∧
      quittingSoloReward reward owner other <
        quittingSingletonCollisionReward reward owner other := by
  obtain ⟨other, hne, hlt⟩ := hobstruction 1 one_pos le_rfl
  refine ⟨other, hne, ?_⟩
  simpa using hlt

/-! ## The positive-debt refinement -/

/-- **Positive-debt owner-solo refinement.**  Positive exact dynamic debt
either produces the owner-solo uniform-equilibrium payoff—the value of the
deviation measured by the debt—or every solo rate of the owner has a strict
joining obstruction. -/
theorem uniformPayoff_or_universalJoining_of_positiveDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (owner : ι) (start : ℕ) (hstart : start ≤ cutoff)
    (hdebt : 0 < quittingFiniteNashBellmanPathDynamicDebt
      reward cutoff path owner start) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingSoloReward reward owner) ∨
      ∀ p : ℝ, 0 < p → p ≤ 1 →
        QuittingSoloJoiningObstruction reward owner p := by
  have hsolo : 0 < quittingSoloReward reward owner owner := by
    have hsingleton := positiveSingletonReward_of_finiteDynamicDebt_pos_at
      reward cutoff path hpath owner start hstart hdebt
    simpa [quittingSoloReward, quittingSingletonTerminal] using hsingleton
  rcases soloCertification_or_universalJoining reward owner with
    ⟨p, hp0, hp1, hinactive⟩ | hobstruction
  · left
    refine isUniformEquilibriumPayoff_soloReward_of_inactive
      reward owner (quittingHazardCoin p (le_of_lt hp0) hp1) ?_
        (le_of_lt hsolo) ?_
    · rw [quittingHazardCoin_true_toReal p (le_of_lt hp0) hp1]
      exact hp0
    · intro other hne
      rw [quittingHazardCoin_true_toReal p (le_of_lt hp0) hp1,
        quittingHazardCoin_false_toReal p (le_of_lt hp0) hp1]
      exact hinactive other hne
  · exact Or.inr hobstruction

end GameTheory
