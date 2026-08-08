/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Examples.BigMatch.NoMarkov
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Fink.Endpoint
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Fink.MarkovEndpoint

/-!
# Discounted Fink values in the Big Match

Every discounted stationary Bellman equilibrium of the Big Match has the
same value vector.  In particular its live-state value is `(1/2, -1/2)` for
every discount factor strictly below one.  Thus every fixed point used by the
Fink endpoint decodes to that same value.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace BigMatch

open Math.Probability Math.PMFProduct

theorem expect_next_value_live (V : State → Payoff Player)
    (m : Player → PMF Bool) (who : Player) :
    expect (pmfPi m) (fun a =>
        expect (game.transition .live a) (fun s' => V s' who)) =
      (1 - (m false true).toReal) * V .live who +
        (m false true).toReal * (m true true).toReal * V .zero who +
        (m false true).toReal * (1 - (m true true).toReal) * V .one who := by
  have hdecomp : (fun s => V s who) = fun s =>
      V .live who * liveIndicator s + V .zero who * zeroIndicator s +
        V .one who * oneIndicator s := by
    funext s
    cases s <;> simp [liveIndicator, zeroIndicator, oneIndicator]
  rw [hdecomp]
  simp_rw [expect_add, expect_const_mul]
  rw [expect_next_liveIndicator, expect_next_zeroIndicator,
    expect_next_oneIndicator]
  simp [liveIndicator, zeroIndicator, oneIndicator]
  ring

theorem discountedAuxEU_live_maximizer (β : ℝ)
    (V : State → Payoff Player) (m : Player → PMF Bool) :
    game.discountedAuxEU β V .live m false =
      (1 - β) *
          ((m false true).toReal * (1 - (m true true).toReal) +
            (1 - (m false true).toReal) * (m true true).toReal) +
        β * ((1 - (m false true).toReal) * V .live false +
          (m false true).toReal * (m true true).toReal * V .zero false +
          (m false true).toReal * (1 - (m true true).toReal) * V .one false) := by
  rw [game.discountedAuxEU_eq]
  have hstage : expect (pmfPi m) (fun a => game.stagePayoff .live a false) =
      (m false true).toReal * (1 - (m true true).toReal) +
        (1 - (m false true).toReal) * (m true true).toReal := by
    rw [show (fun a => game.stagePayoff .live a false) =
        fun a => reward .live a by
      funext a
      exact payoff_maximizer .live a]
    exact expect_live_reward m
  rw [hstage, expect_next_value_live]

theorem discountedAuxEU_live_minimizer (β : ℝ)
    (V : State → Payoff Player) (m : Player → PMF Bool) :
    game.discountedAuxEU β V .live m true =
      -(1 - β) *
          ((m false true).toReal * (1 - (m true true).toReal) +
            (1 - (m false true).toReal) * (m true true).toReal) +
        β * ((1 - (m false true).toReal) * V .live true +
          (m false true).toReal * (m true true).toReal * V .zero true +
          (m false true).toReal * (1 - (m true true).toReal) * V .one true) := by
  rw [game.discountedAuxEU_eq]
  have hstage : expect (pmfPi m) (fun a => game.stagePayoff .live a true) =
      -((m false true).toReal * (1 - (m true true).toReal) +
        (1 - (m false true).toReal) * (m true true).toReal) := by
    rw [show (fun a => game.stagePayoff .live a true) =
        fun a => (-1 : ℝ) * reward .live a by
      funext a
      rw [payoff_minimizer]
      rw [payoff_maximizer]
      ring]
    rw [expect_const_mul]
    simpa using congrArg ((-1 : ℝ) * ·)
      (expect_live_reward m)
  rw [hstage, expect_next_value_live]
  ring

theorem discountedAuxEU_zero (β : ℝ) (V : State → Payoff Player)
    (m : Player → PMF Bool) (who : Player) :
    game.discountedAuxEU β V .zero m who = β * V .zero who := by
  simp [discountedAuxEU, discountedAuxPayoff, payoff, reward, transition,
    nextState]

theorem discountedAuxEU_one_maximizer (β : ℝ)
    (V : State → Payoff Player) (m : Player → PMF Bool) :
    game.discountedAuxEU β V .one m false =
      (1 - β) + β * V .one false := by
  simp [discountedAuxEU, discountedAuxPayoff, payoff, reward, transition,
    nextState]

theorem discountedAuxEU_one_minimizer (β : ℝ)
    (V : State → Payoff Player) (m : Player → PMF Bool) :
    game.discountedAuxEU β V .one m true =
      -(1 - β) + β * V .one true := by
  simp [discountedAuxEU, discountedAuxPayoff, payoff, reward, transition,
    nextState]

/-- The normalized discounted Bellman value of the Big Match is independent
of the discount factor. -/
theorem discountedStationaryBellmanEq_values
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {x : game.StationaryMixedProfile} {V : State → Payoff Player}
    (hF : game.IsDiscountedStationaryBellmanEq β x V) :
    (∀ who, V .zero who = 0) ∧ V .one false = 1 ∧
      V .one true = -1 ∧ V .live false = (1 / 2 : ℝ) ∧
      V .live true = -(1 / 2 : ℝ) := by
  have hzero : ∀ who, V .zero who = 0 := by
    intro who
    have h := hF.2 .zero who
    rw [discountedAuxEU_zero] at h
    nlinarith only [h, hβ1]
  have honeMax : V .one false = 1 := by
    have h := hF.2 .one false
    rw [discountedAuxEU_one_maximizer] at h
    nlinarith only [h, hβ1]
  have honeMin : V .one true = -1 := by
    have h := hF.2 .one true
    rw [discountedAuxEU_one_minimizer] at h
    nlinarith only [h, hβ1]
  let p : ℝ := ((x .live false) true).toReal
  let q : ℝ := ((x .live true) true).toReal
  let v : ℝ := V .live false
  let w : ℝ := V .live true
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      ((x .live false).coe_le_one true)
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hq1 : q ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      ((x .live true).coe_le_one true)
  have hvEq := hF.2 .live false
  rw [discountedAuxEU_live_maximizer, hzero false, honeMax] at hvEq
  have hwEq := hF.2 .live true
  rw [discountedAuxEU_live_minimizer, hzero true, honeMin] at hwEq
  have hsum : v + w = β * (1 - p) * (v + w) := by
    dsimp [p, q, v, w]
    nlinarith only [hvEq, hwEq]
  have hprod : β * (1 - p) < 1 := by
    calc
      β * (1 - p) ≤ β * 1 :=
        mul_le_mul_of_nonneg_left (by linarith only [hp0]) hβ0
      _ < 1 := by simpa using hβ1
  have hcoef : 0 < 1 - β * (1 - p) := by linarith only [hprod]
  have hfactor : (1 - β * (1 - p)) * (v + w) = 0 := by
    calc
      (1 - β * (1 - p)) * (v + w) =
          (v + w) - β * (1 - p) * (v + w) := by ring
      _ = 0 := sub_eq_zero.mpr hsum
  have hwneg : w = -v := by
    have hvw : v + w = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left (ne_of_gt hcoef)
    linarith only [hvw]
  have hcontinue := hF.1 .live false (PMF.pure false)
  rw [hF.2 .live false, discountedAuxEU_live_maximizer,
    hzero false, honeMax] at hcontinue
  have hstop := hF.1 .live false (PMF.pure true)
  rw [hF.2 .live false, discountedAuxEU_live_maximizer,
    hzero false, honeMax] at hstop
  have hcontinue' : (1 - β) * q + β * v ≤ v := by
    simpa [p, q, v, Function.update_apply] using hcontinue
  have hstop' : 1 - q ≤ v := by
    simp at hstop
    dsimp [q, v]
    nlinarith only [hstop]
  have hqv : q ≤ v := by
    by_contra hn
    have hqgt : v < q := lt_of_not_ge hn
    have hpos := mul_pos (sub_pos.mpr hβ1) (sub_pos.mpr hqgt)
    nlinarith only [hcontinue', hpos]
  have hvLower : (1 / 2 : ℝ) ≤ v := by linarith only [hstop', hqv]
  have hleft := hF.1 .live true (PMF.pure false)
  rw [hF.2 .live true, discountedAuxEU_live_minimizer,
    hzero true, honeMin] at hleft
  have hright := hF.1 .live true (PMF.pure true)
  rw [hF.2 .live true, discountedAuxEU_live_minimizer,
    hzero true, honeMin] at hright
  have hleft' : v ≤ p + (1 - p) * β * v := by
    simp [v, w, hwneg] at hleft
    dsimp [p, v]
    nlinarith only [hleft]
  have hright' : v ≤ (1 - p) * ((1 - β) + β * v) := by
    simp [v, w, hwneg] at hright
    dsimp [p, v]
    nlinarith only [hright]
  have hupperSum :
      2 * v ≤ (1 - β + β * p) + 2 * β * (1 - p) * v := by
    nlinarith only [hleft', hright']
  have hDpos : 0 < 1 - β + β * p :=
    add_pos_of_pos_of_nonneg (sub_pos.mpr hβ1) (mul_nonneg hβ0 hp0)
  have hproduct : (1 - β + β * p) * (2 * v - 1) ≤ 0 := by
    calc
      (1 - β + β * p) * (2 * v - 1) =
          2 * v - ((1 - β + β * p) + 2 * β * (1 - p) * v) := by
            ring
      _ ≤ 0 := by linarith only [hupperSum]
  have hvUpper : v ≤ (1 / 2 : ℝ) := by
    by_contra hn
    have hvgt : (1 / 2 : ℝ) < v := lt_of_not_ge hn
    have hvpos : 0 < 2 * v - 1 := by
      linarith only [hvgt]
    have := mul_pos hDpos hvpos
    linarith only [this, hproduct]
  have hv : v = (1 / 2 : ℝ) := le_antisymm hvUpper hvLower
  refine ⟨hzero, honeMax, honeMin, ?_, ?_⟩
  · exact hv
  · rw [show V .live true = w from rfl, hwneg, hv]

/-- The maximizer's stopping probability in every discounted stationary
Bellman equilibrium is forced by the discount complement. With
`lam = 1 - β`, it is `lam / (1 + lam)`. This rate is the Big-Match
acceptance test for any strategy obtained by feeding a history-dependent
discount index into stationary discounted equilibria. -/
theorem live_maximizer_stopProbability_eq
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {x : game.StationaryMixedProfile} {V : State → Payoff Player}
    (hF : game.IsDiscountedStationaryBellmanEq β x V) :
    ((x .live false) true).toReal = (1 - β) / (2 - β) := by
  obtain ⟨hzero, _honeMax, honeMin, hliveMax, hliveMin⟩ :=
    discountedStationaryBellmanEq_values hβ0 hβ1 hF
  let p : ℝ := ((x .live false) true).toReal
  let v : ℝ := V .live false
  let w : ℝ := V .live true
  have hwneg : w = -v := by
    dsimp [v, w]
    linarith only [hliveMax, hliveMin]
  have hleft := hF.1 .live true (PMF.pure false)
  rw [hF.2 .live true, discountedAuxEU_live_minimizer,
    hzero true, honeMin] at hleft
  have hright := hF.1 .live true (PMF.pure true)
  rw [hF.2 .live true, discountedAuxEU_live_minimizer,
    hzero true, honeMin] at hright
  have hleft' : v ≤ p + (1 - p) * β * v := by
    simp [v, w, hwneg] at hleft
    dsimp [p, v]
    nlinarith only [hleft]
  have hright' : v ≤ (1 - p) * ((1 - β) + β * v) := by
    simp [v, w, hwneg] at hright
    dsimp [p, v]
    nlinarith only [hright]
  have hpEq : (2 - β) * p = 1 - β := by
    dsimp [v] at hleft' hright'
    rw [hliveMax] at hleft' hright'
    nlinarith only [hleft', hright']
  change p = (1 - β) / (2 - β)
  apply (eq_div_iff (by linarith only [hβ1])).2
  simpa only [mul_comm] using hpEq

/-- The semantic property required by the corrected-calendar endpoint. -/
def HasHalfLiveValueForDiscountedBellmanEquilibria : Prop :=
  ∀ (β : ℝ) (x : game.StationaryMixedProfile)
    (V : game.State → Payoff Player),
    0 ≤ β → β < 1 → game.IsDiscountedStationaryBellmanEq β x V →
      V .live = fun who => if who then -(1 / 2 : ℝ) else (1 / 2 : ℝ)

theorem hasHalfLiveValueForDiscountedBellmanEquilibria :
    HasHalfLiveValueForDiscountedBellmanEquilibria := by
  intro β x V hβ0 hβ1 hF
  obtain ⟨_hzero, _honeMax, _honeMin, hliveMax, hliveMin⟩ :=
    discountedStationaryBellmanEq_values hβ0 hβ1 hF
  funext who
  cases who <;> simp [hliveMax, hliveMin]

/-- Every literal fixed point of Fink's discounted map decodes to the same
Big-Match value: zero at the zero state, `(1,-1)` at the one state, and
`(1/2,-1/2)` at the live state. -/
theorem finkValue_eq_of_finkMap_fixedPoint
    (β U : ℝ) (hβ0 : 0 ≤ β) (hβle : β ≤ 1) (hβ1 : β < 1)
    (hpay : ∀ s a who, |game.stagePayoff s a who| ≤ U)
    (z : game.finkDomain U)
    (hfix : game.finkMap β U hβ0 hβle hpay z = z) :
    (∀ who, game.finkValue z .zero who = 0) ∧
      game.finkValue z .one false = 1 ∧
      game.finkValue z .one true = -1 ∧
      game.finkValue z .live false = (1 / 2 : ℝ) ∧
      game.finkValue z .live true = -(1 / 2 : ℝ) := by
  have hF := game.isDiscountedStationaryBellmanEq_of_finkMap_fixedPoint
    β U hβ0 hβle hpay z hfix
  exact discountedStationaryBellmanEq_values hβ0 hβ1 hF

end BigMatch
end StochasticGame
end GameTheory
