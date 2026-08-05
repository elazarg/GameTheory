/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingExceptionalTailProfileAdapter
import GameTheory.Concepts.Stochastic.QuittingInfinitePathCompiler
import GameTheory.Concepts.Stochastic.QuittingMarkedTimeAdvance
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Divergent and summable opponent clocks

This file isolates the exact analytic split available after a compatible
sequence of quitting roots has been selected.  The one-stage charge for a
player is the probability that one of that player's opponents quits.  If
the charge series diverges, the corresponding finite opponent-survival
products tend to zero.  If it is summable, some suffix instead has strictly
positive opponent survival; in fact that suffix can be chosen with limiting
survival at least `1 / 2`.

Thus every root path has an exhaustive dichotomy:

* every player's opponent clock diverges, and every conditional opponent
  survival tail vanishes; or
* one player has a summable opponent clock and a positive-survival suffix.

The second branch is only a probabilistic boundary.  It does **not** by
itself imply that the prescribed path absorbs, that its Bellman values are
Cauchy, or that its live suffixes are terminal Nash profiles.  The final
theorem records the additional all-tail absorption and terminal-Nash
hypotheses consumed by the existing exceptional stationary fallback.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The additive opponent clock associated with a root path. -/
def quittingOpponentClockCharge
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) : ℝ :=
  quittingRootOpponentAbsorptionMass (roots time) who

/-- Opponent charge is one minus the corresponding one-stage opponent
continue mass. -/
theorem quittingOpponentClockCharge_eq_one_sub
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingOpponentClockCharge roots who time =
      1 - quittingFixedOpponentsContinueMass roots who time := by
  rfl

/-- Every opponent-clock charge is nonnegative. -/
theorem quittingOpponentClockCharge_nonneg
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    0 ≤ quittingOpponentClockCharge roots who time := by
  rw [quittingOpponentClockCharge_eq_one_sub]
  exact sub_nonneg.mpr
    (quittingStationaryContinueMass_le_one
      (Function.update (roots time) who (PMF.pure false)))

/-- Every opponent-clock charge is at most one. -/
theorem quittingOpponentClockCharge_le_one
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingOpponentClockCharge roots who time ≤ 1 := by
  rw [quittingOpponentClockCharge_eq_one_sub]
  have hmass := quittingStationaryContinueMass_nonneg
    (Function.update (roots time) who (PMF.pure false))
  change 0 ≤ quittingFixedOpponentsContinueMass roots who time at hmass
  linarith

/-- The elementary union bound: finite opponent survival is at least one
minus the accumulated additive opponent charge. -/
theorem one_sub_sum_quittingOpponentClockCharge_le_survival
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ start fuel,
      1 - (∑ offset ∈ Finset.range fuel,
          quittingOpponentClockCharge roots who (start + offset)) ≤
        quittingOpponentSurvivalWeight roots who start fuel := by
  intro start fuel
  induction fuel with
  | zero =>
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      let accumulated := ∑ offset ∈ Finset.range fuel,
        quittingOpponentClockCharge roots who (start + offset)
      let charge := quittingOpponentClockCharge roots who (start + fuel)
      let survival := quittingOpponentSurvivalWeight roots who start fuel
      have hcontinue :
          quittingFixedOpponentsContinueMass roots who (start + fuel) =
            1 - charge := by
        dsimp only [charge]
        rw [quittingOpponentClockCharge_eq_one_sub]
        ring
      have hfactor0 : 0 ≤ 1 - charge := by
        rw [← hcontinue]
        exact quittingStationaryContinueMass_nonneg
          (Function.update (roots (start + fuel)) who (PMF.pure false))
      have haccumulated0 : 0 ≤ accumulated := by
        exact Finset.sum_nonneg fun offset _ ↦
          quittingOpponentClockCharge_nonneg roots who (start + offset)
      rw [Finset.sum_range_succ,
        quittingOpponentSurvivalWeight_succ, hcontinue]
      change 1 - (accumulated + charge) ≤ survival * (1 - charge)
      have hscaled : (1 - accumulated) * (1 - charge) ≤
          survival * (1 - charge) :=
        mul_le_mul_of_nonneg_right ih hfactor0
      calc
        1 - (accumulated + charge) ≤
            (1 - accumulated) * (1 - charge) := by
          nlinarith [mul_nonneg haccumulated0
            (quittingOpponentClockCharge_nonneg roots who (start + fuel))]
        _ ≤ survival * (1 - charge) := hscaled

/-- Finite opponent survival is bounded by the exponential of minus the
accumulated additive charge. -/
theorem quittingOpponentSurvivalWeight_le_exp_neg_sum_charge
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ start fuel,
      quittingOpponentSurvivalWeight roots who start fuel ≤
        Real.exp (-(∑ offset ∈ Finset.range fuel,
          quittingOpponentClockCharge roots who (start + offset))) := by
  intro start fuel
  induction fuel with
  | zero =>
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      let accumulated := ∑ offset ∈ Finset.range fuel,
        quittingOpponentClockCharge roots who (start + offset)
      let charge := quittingOpponentClockCharge roots who (start + fuel)
      have hcontinue :
          quittingFixedOpponentsContinueMass roots who (start + fuel) =
            1 - charge := by
        dsimp only [charge]
        rw [quittingOpponentClockCharge_eq_one_sub]
        ring
      rw [Finset.sum_range_succ,
        quittingOpponentSurvivalWeight_succ, hcontinue]
      change
        quittingOpponentSurvivalWeight roots who start fuel * (1 - charge) ≤
          Real.exp (-(accumulated + charge))
      calc
        quittingOpponentSurvivalWeight roots who start fuel * (1 - charge) ≤
            Real.exp (-accumulated) * Real.exp (-charge) := by
          exact mul_le_mul ih (Real.one_sub_le_exp_neg charge)
            (by
              rw [← hcontinue]
              exact quittingStationaryContinueMass_nonneg
                (Function.update (roots (start + fuel)) who
                  (PMF.pure false)))
            (Real.exp_nonneg _)
        _ = Real.exp (-(accumulated + charge)) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- A divergent additive opponent clock forces the matching multiplicative
opponent-survival tail to zero. -/
theorem tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (hdiverges : ¬Summable (fun offset ↦
      quittingOpponentClockCharge roots who (start + offset))) :
    Tendsto (quittingOpponentSurvivalWeight roots who start)
      atTop (nhds 0) := by
  have hsum : Tendsto (fun fuel : ℕ ↦
      ∑ offset ∈ Finset.range fuel,
        quittingOpponentClockCharge roots who (start + offset))
      atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun offset ↦ quittingOpponentClockCharge_nonneg roots who
        (start + offset))).1 hdiverges
  have hexp : Tendsto (fun fuel : ℕ ↦
      Real.exp (-(∑ offset ∈ Finset.range fuel,
        quittingOpponentClockCharge roots who (start + offset))))
      atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hsum
  exact squeeze_zero
    (quittingOpponentSurvivalWeight_nonneg roots who start)
    (quittingOpponentSurvivalWeight_le_exp_neg_sum_charge
      roots who start) hexp

/-- A summable opponent clock has a suffix whose every finite survival
product is at least one half.  This formulation also handles finitely many
earlier zero factors. -/
theorem exists_suffix_half_le_quittingOpponentSurvivalWeight_of_summable
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hsummable : Summable (quittingOpponentClockCharge roots who)) :
    ∃ start, ∀ fuel,
      (1 / 2 : ℝ) ≤ quittingOpponentSurvivalWeight roots who start fuel := by
  have htail : Tendsto (fun start : ℕ ↦
      ∑' offset : ℕ,
        quittingOpponentClockCharge roots who (offset + start))
      atTop (nhds 0) :=
    tendsto_sum_nat_add (quittingOpponentClockCharge roots who)
  have heventually : ∀ᶠ start : ℕ in atTop,
      (∑' offset : ℕ,
        quittingOpponentClockCharge roots who (offset + start)) <
          (1 / 2 : ℝ) :=
    htail.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨start, hstart⟩ := heventually.exists
  refine ⟨start, fun fuel ↦ ?_⟩
  have hsuffix : Summable (fun offset ↦
      quittingOpponentClockCharge roots who (start + offset)) := by
    have hadd : Summable (fun offset ↦
        quittingOpponentClockCharge roots who (offset + start)) :=
      (summable_nat_add_iff start).2 hsummable
    simpa [Nat.add_comm] using hadd
  have hfinite :
      (∑ offset ∈ Finset.range fuel,
          quittingOpponentClockCharge roots who (start + offset)) ≤
        ∑' offset : ℕ,
          quittingOpponentClockCharge roots who (start + offset) :=
    hsuffix.sum_le_tsum (Finset.range fuel) fun offset _ ↦
      quittingOpponentClockCharge_nonneg roots who (start + offset)
  have htailRewrite :
      (∑' offset : ℕ,
          quittingOpponentClockCharge roots who (start + offset)) =
        ∑' offset : ℕ,
          quittingOpponentClockCharge roots who (offset + start) := by
    congr 1
    funext offset
    rw [Nat.add_comm]
  rw [htailRewrite] at hfinite
  have hunion := one_sub_sum_quittingOpponentClockCharge_le_survival
    roots who start fuel
  linarith

/-- A summable clock therefore exposes a canonical live suffix with
strictly positive limiting opponent survival. -/
theorem exists_suffix_positive_opponentLiveMassLimit_of_summable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hsummable : Summable (quittingOpponentClockCharge roots who)) :
    ∃ start,
      0 < quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward
          (quittingAllContinueProfileSpine reward
            (quittingInfinitePathProfile reward roots) start) who) := by
  obtain ⟨start, hhalf⟩ :=
    exists_suffix_half_le_quittingOpponentSurvivalWeight_of_summable
      roots who hsummable
  let profile := quittingInfinitePathProfile reward roots
  let tail := quittingAllContinueProfileSpine reward profile start
  let opponentTail := quittingOpponentOnlyProfile reward tail who
  have hweights : ∀ fuel,
      quittingOpponentSurvivalWeight roots who start fuel =
        quittingLiveMass reward opponentTail fuel := by
    intro fuel
    have h := quittingOpponentSurvivalWeight_eq_liveMass_allContinueSpine
      reward profile who start fuel
    simpa only [profile, opponentTail, tail,
      quittingProfileLiveRoot_infinitePathProfile] using h
  have hlower : ∀ fuel,
      (1 / 2 : ℝ) ≤ quittingLiveMass reward opponentTail fuel := by
    intro fuel
    rw [← hweights fuel]
    exact hhalf fuel
  have hlimit : (1 / 2 : ℝ) ≤
      quittingLiveMassLimit reward opponentTail :=
    ge_of_tendsto' (tendsto_quittingLiveMass reward opponentTail) hlower
  refine ⟨start, ?_⟩
  simpa only [profile, opponentTail, tail] using
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hlimit)

/-- **Global opponent-clock dichotomy.**  Either every player's additive
opponent clock diverges and every one of its conditional survival tails
vanishes, or one player has a summable clock and a positive-survival suffix.
No recurrence or periodic closing hypothesis is used. -/
theorem divergent_opponentClocks_or_positive_exceptionalSuffix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) :
    (∀ who,
        ¬Summable (quittingOpponentClockCharge roots who) ∧
        ∀ start, Tendsto
          (quittingOpponentSurvivalWeight roots who start)
          atTop (nhds 0)) ∨
      ∃ owner,
        Summable (quittingOpponentClockCharge roots owner) ∧
        ∃ start,
          0 < quittingLiveMassLimit reward
            (quittingOpponentOnlyProfile reward
              (quittingAllContinueProfileSpine reward
                (quittingInfinitePathProfile reward roots) start) owner) := by
  classical
  by_cases hall : ∀ who,
      ¬Summable (quittingOpponentClockCharge roots who)
  · left
    intro who
    refine ⟨hall who, fun start ↦ ?_⟩
    apply tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge
    intro hsuffix
    have hshift : Summable (fun offset ↦
        quittingOpponentClockCharge roots who (offset + start)) := by
      simpa [Nat.add_comm] using hsuffix
    exact hall who ((summable_nat_add_iff start).1 hshift)
  · right
    push Not at hall
    obtain ⟨owner, howner⟩ := hall
    refine ⟨owner, howner, ?_⟩
    exact exists_suffix_positive_opponentLiveMassLimit_of_summable
      reward roots owner howner

/-- The exact extra hypotheses which turn a positive opponent-survival
clock into the landed exceptional stationary fallback.  The positivity
hypothesis alone supplies none of `habsorbs` or `htailNash`; an actual-suffix
extraction must establish both independently. -/
theorem exists_exceptionalStationaryFallback_of_positiveClock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) {β M : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingLiveMassLimit reward
      (quittingOpponentOnlyProfile reward profile owner))
    (habsorbs : ∀ start,
      quittingLiveMassLimit reward
        (quittingAllContinueProfileSpine reward profile start) = 0)
    (htailNash : ∀ start,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) β
        (quittingAllContinueProfileSpine reward profile start)) :
    ∀ ζ > 0, ∃ time,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (β + ζ)
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner
            (quittingProfileLiveRoot reward profile time owner))) := by
  exact exists_isεAsymptoticNash_soloStationary_of_exceptional_profile
    reward profile owner hβ hM hreward habsorbs htailNash hpositive

end GameTheory
