/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Correlation.CorrelationRegimes

/-!
# A private-recommendation target separated from ordinary mixed play

This file records the finite algebraic core of the correlation-implementation
obstruction.  The two-player binary game

```text
          C          D
 C      (6,6)/7    (2,7)/7
 D      (7,2)/7    (0,0)
```

has a correlated equilibrium which chooses `CC`, `CD`, and `DC` uniformly and
delivers `(5/7, 5/7)`.  Independent mixed play cannot simultaneously approach
that target and cap the two pure deviations to `D` more closely than

`deltaStar = (41 - 7 * sqrt 34) / 21`.

The result is deliberately stated at the strategic-form level.  It neither
defines an autonomous correlation device nor claims a compiler theorem.  A
stochastic-game realization and the claimed horizonwise transport are not
defined or proved here.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace KernelGame
namespace PrivateRecommendationTargetSeparator

open Math.Probability Math.PMFProduct

abbrev Player := Bool
abbrev Action (_ : Player) := Bool

/-- `false` labels player 1 and `true` labels player 2.  The action `true`
is `C`; `false` is `D`. -/
def payoff (profile : Player → Bool) (who : Player) : ℝ :=
  if profile false then
    if profile true then 6 / 7
    else if who then 1 else 2 / 7
  else if profile true then
    if who then 2 / 7 else 1
  else 0

/-- The deterministic strategic-form game used by the separator. -/
noncomputable abbrev game : KernelGame Player :=
  KernelGame.ofPureEU Action payoff

private instance : Finite game.Outcome :=
  inferInstanceAs (Finite (Player → Bool))

/-- The three recommendations in the private correlated law. -/
def cc : Profile game := fun _ => true
def cd : Profile game := fun who => !who
def dc : Profile game := fun who => who

def recommendation (slot : Fin 3) : Profile game :=
  if slot = 0 then cc else if slot = 1 then cd else dc

/-- Uniform private recommendations on `CC`, `CD`, and `DC`. -/
noncomputable def recommendationLaw : PMF (Profile game) :=
  PMF.map recommendation (PMF.uniformOfFintype (Fin 3))

theorem expect_recommendationLaw (f : Profile game → ℝ) :
    expect recommendationLaw f = (f cc + f cd + f dc) / 3 := by
  rw [recommendationLaw, expect_map, expect_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_mul_eq_div]
  rw [Fin.sum_univ_three]
  simp [recommendation]
  ring

@[simp] theorem eu_cc (who : Player) : game.eu cc who = 6 / 7 := by
  cases who <;> norm_num [game, cc, payoff]

@[simp] theorem eu_cd_playerOne : game.eu cd false = 2 / 7 := by
  norm_num [game, cd, payoff]

@[simp] theorem eu_cd_playerTwo : game.eu cd true = 1 := by
  norm_num [game, cd, payoff]

@[simp] theorem eu_dc_playerOne : game.eu dc false = 1 := by
  norm_num [game, dc, payoff]

@[simp] theorem eu_dc_playerTwo : game.eu dc true = 2 / 7 := by
  norm_num [game, dc, payoff]

/-- The private recommendation law gives each player exactly `5/7`. -/
theorem correlatedEu_recommendationLaw (who : Player) :
    game.correlatedEu recommendationLaw who = 5 / 7 := by
  rw [game.correlatedEu_eq_expect_eu, expect_recommendationLaw]
  cases who <;> norm_num [game, cc, cd, dc, payoff]

/-- Obedience is an exact correlated equilibrium.  This checks every
recommendation-dependent Boolean deviation, not only constant deviations. -/
theorem recommendationLaw_isCorrelatedEq :
    game.IsCorrelatedEq recommendationLaw := by
  intro who dev
  rw [game.correlatedEu_eq_expect_eu,
    game.correlatedEu_unilateralDeviationDistribution_eq_expect_update]
  rw [expect_recommendationLaw, expect_recommendationLaw]
  cases who <;> cases hC : dev true <;> cases hD : dev false <;>
    norm_num [game, cc, cd, dc, payoff, hC, hD, Function.update]

/-! ## Independent mixed play -/

/-- A mixed profile for this binary game, written without the dependent
`mixedExtension.Strategy` projection so that its Bernoulli coordinates remain
transparent to the algebra below. -/
abbrev MixedProfile := Player → PMF Bool

/-- Probability that `who` chooses `C`. -/
def probC (profile : MixedProfile) (who : Player) : ℝ :=
  ((profile who) true).toReal

theorem probC_nonneg (profile : MixedProfile) (who : Player) :
    0 ≤ probC profile who :=
  ENNReal.toReal_nonneg

theorem probC_le_one (profile : MixedProfile) (who : Player) :
    probC profile who ≤ 1 := by
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    ((profile who).coe_le_one true)

private theorem prob_false_toReal (profile : MixedProfile)
    (who : Player) :
    ((profile who) false).toReal = 1 - probC profile who := by
  have h := expect_const (profile who) (1 : ℝ)
  rw [expect_eq_sum, Fintype.sum_bool] at h
  norm_num at h
  change ((profile who) false).toReal =
    1 - ((profile who) true).toReal
  linarith

private theorem expect_pmfPi_bool
    (profile : MixedProfile)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi profile) f =
      expect (profile false) (fun a =>
        expect (profile true) (fun b =>
          f (fun who => if who then b else a))) := by
  classical
  have hfalse : Function.update profile false (profile false) = profile :=
    Function.update_eq_self false profile
  rw [← hfalse, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (profile false))
  funext a
  have htrue : Function.update (Function.update profile false (PMF.pure a))
      true (profile true) = Function.update profile false (PMF.pure a) := by
    funext who
    cases who <;> simp
  rw [← htrue, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (profile true))
  funext b
  have hpure : Function.update (Function.update profile false (PMF.pure a))
        true (PMF.pure b) =
      fun who => PMF.pure (if who then b else a) := by
    funext who
    cases who <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

/-- Player 1's expected payoff under independent mixing. -/
theorem mixedEu_playerOne (profile : MixedProfile) :
    game.mixedExtension.eu profile false =
      (2 * probC profile false + 7 * probC profile true -
        3 * probC profile false * probC profile true) / 7 := by
  rw [game.mixedExtension_eu]
  simp only [KernelGame.eu_ofPureEU]
  change expect (pmfPi profile) (fun s : Player → Bool => payoff s false) = _
  rw [expect_pmfPi_bool]
  simp [expect_eq_sum, payoff, probC, prob_false_toReal]
  ring

/-- Player 2's expected payoff under independent mixing. -/
theorem mixedEu_playerTwo (profile : MixedProfile) :
    game.mixedExtension.eu profile true =
      (7 * probC profile false + 2 * probC profile true -
        3 * probC profile false * probC profile true) / 7 := by
  rw [game.mixedExtension_eu]
  simp only [KernelGame.eu_ofPureEU]
  change expect (pmfPi profile) (fun s : Player → Bool => payoff s true) = _
  rw [expect_pmfPi_bool]
  simp [expect_eq_sum, payoff, probC, prob_false_toReal]
  ring

/-- If player 1 switches to pure `D`, its payoff is player 2's probability
of `C`. -/
theorem mixedEu_playerOne_forceD (profile : MixedProfile) :
    game.mixedExtension.eu
        (Function.update profile false (PMF.pure false)) false =
      probC profile true := by
  rw [mixedEu_playerOne]
  simp [probC]

/-- If player 2 switches to pure `D`, its payoff is player 1's probability
of `C`. -/
theorem mixedEu_playerTwo_forceD (profile : MixedProfile) :
    game.mixedExtension.eu
        (Function.update profile true (PMF.pure false)) true =
      probC profile false := by
  rw [mixedEu_playerTwo]
  simp [probC]

/-! ## The sharp quantitative gap -/

/-- Exact smallest simultaneous delivery/cap tolerance. -/
def deltaStar : ℝ := (41 - 7 * Real.sqrt 34) / 21

/-- The symmetric independent mixing probability attaining the gap. -/
def sharpMix : ℝ := (8 - Real.sqrt 34) / 3

private theorem sqrt34_sq : (Real.sqrt 34) ^ 2 = (34 : ℝ) := by
  norm_num

theorem sqrt34_lt_41_div_7 : Real.sqrt 34 < (41 : ℝ) / 7 := by
  have hs := Real.sqrt_nonneg 34
  nlinarith [sqrt34_sq]

theorem deltaStar_pos : 0 < deltaStar := by
  rw [deltaStar]
  have h := sqrt34_lt_41_div_7
  linarith

theorem deltaStar_lt_two_sevenths : deltaStar < (2 : ℝ) / 7 := by
  rw [deltaStar]
  have hs := Real.sqrt_nonneg 34
  have hs5 : 5 < Real.sqrt 34 := by
    nlinarith [sqrt34_sq]
  linarith

theorem sharpMix_eq_target_add_deltaStar :
    sharpMix = (5 : ℝ) / 7 + deltaStar := by
  rw [sharpMix, deltaStar]
  ring

theorem sharpMix_nonneg : 0 ≤ sharpMix := by
  rw [sharpMix]
  have hs := Real.sqrt_nonneg 34
  have hs6 : Real.sqrt 34 < 6 := by
    nlinarith [sqrt34_sq]
  linarith

theorem sharpMix_le_one : sharpMix ≤ 1 := by
  rw [sharpMix]
  have hs := Real.sqrt_nonneg 34
  have hs5 : 5 < Real.sqrt 34 := by
    nlinarith [sqrt34_sq]
  linarith

theorem two_thirds_lt_sharpMix : (2 : ℝ) / 3 < sharpMix := by
  rw [sharpMix]
  have hs := Real.sqrt_nonneg 34
  have hs6 : Real.sqrt 34 < 6 := by
    nlinarith [sqrt34_sq]
  linarith

/-- The Bernoulli strategy which chooses `C` with the sharp probability. -/
noncomputable def sharpBernoulli : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ENNReal.ofReal sharpMix
      else ENNReal.ofReal (1 - sharpMix))
    (by
      rw [Fintype.sum_bool]
      simp only [if_true, if_false, Bool.false_eq_true]
      rw [← ENNReal.ofReal_add sharpMix_nonneg (by linarith [sharpMix_le_one])]
      norm_num)

@[simp] theorem sharpBernoulli_true_toReal :
    (sharpBernoulli true).toReal = sharpMix := by
  simp [sharpBernoulli, PMF.ofFintype_apply, sharpMix_nonneg]

/-- The symmetric independent mixed profile attaining the lower bound. -/
noncomputable def sharpMixedProfile : MixedProfile :=
  fun _ => sharpBernoulli

@[simp] theorem probC_sharpMixedProfile (who : Player) :
    probC sharpMixedProfile who = sharpMix := by
  simp [probC, sharpMixedProfile]

theorem deltaStar_quadratic :
    147 * deltaStar ^ 2 - 574 * deltaStar + 5 = 0 := by
  rw [deltaStar]
  nlinarith [sqrt34_sq]

/-- Algebraic heart of the obstruction.  If probabilities `p,q` lie in the
unit square, the pure-`D` caps bound each by `5/7 + delta`, and mean delivery
is at least `5/7 - delta`, then `delta` is no smaller than `deltaStar`. -/
theorem deltaStar_le_of_delivery_and_caps
    {p q delta : ℝ}
    (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1)
    (_hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (_hdelta : 0 ≤ delta)
    (hpCap : p ≤ 5 / 7 + delta)
    (hqCap : q ≤ 5 / 7 + delta)
    (hdelivery :
      5 / 7 - delta ≤ (9 * (p + q) - 6 * p * q) / 14) :
    deltaStar ≤ delta := by
  by_contra hnot
  have hlt : delta < deltaStar := lt_of_not_ge hnot
  let x : ℝ := 5 / 7 + delta
  have hx1 : x < 1 := by
    dsimp [x]
    linarith [deltaStar_lt_two_sevenths]
  have hpX : p ≤ x := hpCap
  have hqX : q ≤ x := hqCap
  have hqCoeff : 0 ≤ 9 - 6 * q := by linarith
  have hxCoeff : 0 ≤ 9 - 6 * x := by linarith
  have hfirst : 0 ≤ (x - p) * (9 - 6 * q) :=
    mul_nonneg (sub_nonneg.mpr hpX) hqCoeff
  have hsecond : 0 ≤ (x - q) * (9 - 6 * x) :=
    mul_nonneg (sub_nonneg.mpr hqX) hxCoeff
  have hmeanUpper :
      (9 * (p + q) - 6 * p * q) / 14 ≤
        (18 * x - 6 * x ^ 2) / 14 := by
    nlinarith
  have hpoly : 147 * delta ^ 2 - 574 * delta + 5 ≤ 0 := by
    dsimp [x] at hmeanUpper
    nlinarith
  have hsumSmall : 147 * (delta + deltaStar) - 574 < 0 := by
    have hstar := deltaStar_lt_two_sevenths
    nlinarith
  have hfactorPos :
      0 < (delta - deltaStar) *
        (147 * (delta + deltaStar) - 574) :=
    mul_pos_of_neg_of_neg (sub_neg.mpr hlt) hsumSmall
  have hpolyStar := deltaStar_quadratic
  nlinarith

/-- Exact equality witness for the scalar obstruction. -/
theorem sharpMix_attains_delivery_boundary :
    (9 * (sharpMix + sharpMix) - 6 * sharpMix * sharpMix) / 14 =
      5 / 7 - deltaStar := by
  rw [sharpMix_eq_target_add_deltaStar]
  nlinarith [deltaStar_quadratic]

/-- The sharp mixing probability saturates both pure-`D` cap bounds. -/
theorem sharpMix_attains_cap_boundary :
    sharpMix = 5 / 7 + deltaStar :=
  sharpMix_eq_target_add_deltaStar

/-- At the sharp independent profile, both delivered payoffs lie exactly
`deltaStar` below the private-recommendation target. -/
theorem mixedEu_sharpMixedProfile (who : Player) :
    game.mixedExtension.eu sharpMixedProfile who = 5 / 7 - deltaStar := by
  cases who
  · rw [mixedEu_playerOne]
    simp only [probC_sharpMixedProfile]
    nlinarith [sharpMix_attains_delivery_boundary]
  · rw [mixedEu_playerTwo]
    simp only [probC_sharpMixedProfile]
    nlinarith [sharpMix_attains_delivery_boundary]

/-- Pure `D` attains the common cap at the sharp independent profile. -/
theorem mixedEu_sharpMixedProfile_forceD (who : Player) :
    game.mixedExtension.eu
        (Function.update sharpMixedProfile who (PMF.pure false)) who =
      5 / 7 + deltaStar := by
  cases who
  · rw [mixedEu_playerOne_forceD, probC_sharpMixedProfile,
      sharpMix_eq_target_add_deltaStar]
  · rw [mixedEu_playerTwo_forceD, probC_sharpMixedProfile,
      sharpMix_eq_target_add_deltaStar]

/-- The delivery error at the sharp independent profile is exactly
`deltaStar` for each player. -/
theorem abs_mixedEu_sharpMixedProfile_sub_target (who : Player) :
    |game.mixedExtension.eu sharpMixedProfile who - 5 / 7| = deltaStar := by
  rw [mixedEu_sharpMixedProfile]
  have hnonneg : 0 ≤ deltaStar := deltaStar_pos.le
  rw [show 5 / 7 - deltaStar - 5 / 7 = -deltaStar by ring,
    abs_neg, abs_of_nonneg hnonneg]

/-- No mixed unilateral deviation beats pure `D` at the sharp profile.  Thus
the scalar equality witness is also a strategy-level sharpness witness for the
full unilateral cap, not only for the two deviations used in the lower-bound
proof. -/
theorem mixedEu_update_sharpMixedProfile_le (who : Player) (deviation : PMF Bool) :
    game.mixedExtension.eu
        (Function.update sharpMixedProfile who deviation) who ≤
      5 / 7 + deltaStar := by
  have hp0 : 0 ≤ ((deviation true).toReal) := ENNReal.toReal_nonneg
  have hcoefficient : 2 - 3 * sharpMix < 0 := by
    linarith [two_thirds_lt_sharpMix]
  cases who
  · rw [mixedEu_playerOne]
    simp only [probC, Function.update_self,
      Function.update_of_ne (by decide : true ≠ false),
      sharpMixedProfile, sharpBernoulli_true_toReal]
    rw [← sharpMix_eq_target_add_deltaStar]
    nlinarith
  · rw [mixedEu_playerTwo]
    simp only [probC, Function.update_self,
      Function.update_of_ne Bool.false_ne_true,
      sharpMixedProfile, sharpBernoulli_true_toReal]
    rw [← sharpMix_eq_target_add_deltaStar]
    nlinarith

/-- Strategy-level sharpness packet: exact delivery error, a cap against every
unilateral mixed deviation, and equality of that cap for pure `D`. -/
theorem sharpMixedProfile_exact_tolerance :
    (∀ who,
      |game.mixedExtension.eu sharpMixedProfile who - 5 / 7| = deltaStar) ∧
    (∀ who (deviation : PMF Bool),
      game.mixedExtension.eu
          (Function.update sharpMixedProfile who deviation) who ≤
        5 / 7 + deltaStar) ∧
    (∀ who,
      game.mixedExtension.eu
          (Function.update sharpMixedProfile who (PMF.pure false)) who =
        5 / 7 + deltaStar) :=
  ⟨abs_mixedEu_sharpMixedProfile_sub_target,
    mixedEu_update_sharpMixedProfile_le,
    mixedEu_sharpMixedProfile_forceD⟩

/-- A strategy-level version of the quantitative obstruction.  It assumes
delivery for both players and caps only the two pure-`D` deviations; therefore
it also applies whenever all unilateral mixed deviations are capped. -/
theorem deltaStar_le_of_mixed_delivery_and_pureDCaps
    (profile : MixedProfile) {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (hdelivery : ∀ who,
      |game.mixedExtension.eu profile who - 5 / 7| ≤ delta)
    (hcapOne :
      game.mixedExtension.eu
          (Function.update profile false (PMF.pure false)) false ≤
        5 / 7 + delta)
    (hcapTwo :
      game.mixedExtension.eu
          (Function.update profile true (PMF.pure false)) true ≤
        5 / 7 + delta) :
    deltaStar ≤ delta := by
  let p := probC profile false
  let q := probC profile true
  apply deltaStar_le_of_delivery_and_caps
      (p := p) (q := q) (delta := delta)
      (probC_nonneg profile false) (probC_le_one profile false)
      (probC_nonneg profile true) (probC_le_one profile true) hdelta
  · rw [mixedEu_playerTwo_forceD] at hcapTwo
    exact hcapTwo
  · rw [mixedEu_playerOne_forceD] at hcapOne
    exact hcapOne
  · have hOne := (abs_le.mp (hdelivery false)).1
    have hTwo := (abs_le.mp (hdelivery true)).1
    rw [mixedEu_playerOne] at hOne
    rw [mixedEu_playerTwo] at hTwo
    dsimp [p, q]
    nlinarith

end PrivateRecommendationTargetSeparator
end KernelGame
end GameTheory
