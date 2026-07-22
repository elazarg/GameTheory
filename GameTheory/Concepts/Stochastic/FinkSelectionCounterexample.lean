/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.FinkTangentCounterexample

/-!
# A selection-resistant Fink tangent obstruction

This strengthens `FinkTangentCounterexample` by giving player 2 a
matching-pennies payoff at the live state.  Player 1's discounted indifference
still forces player 2's rare action to have probability
`(1 - β) / β`, while player 2's indifference forces player 1 to mix
equally.  Thus the first-order vanishing action is part of the isolated live
auxiliary equilibrium, rather than an avoidable choice from a continuum of
equilibria.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace FinkSelectionCounterexample

open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

namespace Base

open FinkTangentCounterexample

abbrev CState := FinkTangentCounterexample.State
abbrev Player := FinkTangentCounterexample.Player
abbrev Action := FinkTangentCounterexample.Action

/-- Player 1 keeps the payoff from the tangent counterexample.  At the live
state player 2 receives the matching-pennies payoff: `+1` when the two Boolean
actions agree and `-1` when they differ.  Player 2 receives zero after
absorption. -/
def payoff (s : CState) (a : Player → Bool) (who : Player) : ℝ :=
  if who then
    match s with
    | .live => if a false = a true then 1 else -1
    | .high | .low => 0
  else FinkTangentCounterexample.payoff s a who

/-- The selection-resistant variant has the same states, actions, and
transition as the tangent counterexample. -/
abbrev game : StochasticGame Player where
  State := CState
  Act := Action
  stagePayoff := payoff
  transition := FinkTangentCounterexample.transition
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

instance : Fintype game.State := inferInstanceAs (Fintype CState)
instance : DecidableEq game.State := inferInstanceAs (DecidableEq CState)
instance (who : Player) : Fintype (game.Act who) :=
  inferInstanceAs (Fintype Bool)

/-- The explicit stationary profile.  Its underlying type is definitionally
the same as in the tangent counterexample. -/
def profile (n : ℕ) : game.StationaryMixedProfile :=
  fun s who =>
    (stdSimplexEquiv (α := Bool)).symm
      ⟨FinkTangentCounterexample.weight n (s, who),
        FinkTangentCounterexample.weight_mem_simplex n (s, who)⟩

def value (s : game.State) (who : Player) : ℝ :=
  FinkTangentCounterexample.value s who

@[simp] lemma expect_transition_value (s : CState) (a : Player → Bool)
    (who : Player) :
    expect (FinkTangentCounterexample.transition s a)
        (fun t => value t who) =
      FinkTangentCounterexample.continuationValue s a who := by
  simpa only [value] using
    FinkTangentCounterexample.expect_transition_value s a who

@[simp] lemma profile_apply_toReal (n : ℕ) (s : CState) (who : Player)
    (d : Bool) : ((profile n s who) d).toReal =
      FinkTangentCounterexample.weight n (s, who) d := by
  change ((ofVector (FinkTangentCounterexample.weight n (s, who))
    (FinkTangentCounterexample.weight_mem_simplex n (s, who)) d).toReal =
      FinkTangentCounterexample.weight n (s, who) d)
  exact ofVector_toReal
    (FinkTangentCounterexample.weight_mem_simplex n (s, who)) d

lemma profile_eq_base (n : ℕ) :
    profile n = FinkTangentCounterexample.profile n := by
  rfl

lemma abs_value_le_one (s : CState) (who : Player) : |value s who| ≤ 1 :=
  FinkTangentCounterexample.abs_value_le_one s who

def point (n : ℕ) : game.finkDomain 1 :=
  game.finkPointOfProfileValue (profile n) value abs_value_le_one

@[simp] lemma finkValue_point (n : ℕ) : game.finkValue (point n) = value :=
  rfl

lemma playerOne_pure_discountedAuxEU_eq (n : ℕ) (s : CState) (d : Bool) :
    game.discountedAuxEU (FinkTangentCounterexample.discount n) value s
        (Function.update (profile n s) false (PMF.pure d)) false =
      value s false := by
  rw [profile_eq_base]
  change FinkTangentCounterexample.game.discountedAuxEU
      (FinkTangentCounterexample.discount n)
      FinkTangentCounterexample.value s
      (Function.update (FinkTangentCounterexample.profile n s)
        false (PMF.pure d)) false =
    FinkTangentCounterexample.value s false
  exact FinkTangentCounterexample.pure_discountedAuxEU_eq n s false d

/-- Equal mixing by player 1 makes both pure actions of player 2 worth zero.
This is the second indifference equation missing from the original tangent
counterexample. -/
lemma playerTwo_pure_discountedAuxEU_eq (n : ℕ) (s : CState) (d : Bool) :
    game.discountedAuxEU (FinkTangentCounterexample.discount n) value s
        (Function.update (profile n s) true (PMF.pure d)) true =
      value s true := by
  unfold StochasticGame.discountedAuxEU
  rw [FinkTangentCounterexample.expect_pmfPi_bool]
  cases s <;> cases d <;>
    simp only [discountedAuxPayoff, payoff, value,
      FinkTangentCounterexample.value,
      expect_eq_sum,
      Fintype.sum_bool, Function.update_self, ne_eq,
      Bool.false_eq_true, not_false_eq_true,
      Function.update_of_ne, Bool.if_false_right, Bool.if_true_right]
  all_goals
    rw [profile_apply_toReal]
    norm_num [FinkTangentCounterexample.weight]
  all_goals ring_nf
  all_goals
    rw [profile_apply_toReal]
    norm_num [FinkTangentCounterexample.weight]

lemma pure_discountedAuxEU_eq (n : ℕ) (s : CState) (who : Player)
    (d : Bool) :
    game.discountedAuxEU (FinkTangentCounterexample.discount n) value s
        (Function.update (profile n s) who (PMF.pure d)) who =
      value s who := by
  cases who
  · exact playerOne_pure_discountedAuxEU_eq n s d
  · exact playerTwo_pure_discountedAuxEU_eq n s d

lemma mixedDeviation_discountedAuxEU_eq (n : ℕ) (s : CState)
    (who : Player) (dev : PMF Bool) :
    game.discountedAuxEU (FinkTangentCounterexample.discount n) value s
        (Function.update (profile n s) who dev) who = value s who := by
  unfold StochasticGame.discountedAuxEU
  rw [pmfPi_update_bind, expect_bind]
  change expect dev (fun d => game.discountedAuxEU
    (FinkTangentCounterexample.discount n) value s
      (Function.update (profile n s) who (PMF.pure d)) who) = value s who
  have hfun : (fun d => game.discountedAuxEU
      (FinkTangentCounterexample.discount n) value s
        (Function.update (profile n s) who (PMF.pure d)) who) =
      fun _ => value s who := by
    funext d
    exact pure_discountedAuxEU_eq n s who d
  rw [hfun, expect_const]

lemma profile_discountedAuxEU_eq (n : ℕ) (s : CState) (who : Player) :
    game.discountedAuxEU (FinkTangentCounterexample.discount n) value s
        (profile n s) who = value s who := by
  rw [← Function.update_eq_self who (profile n s)]
  exact mixedDeviation_discountedAuxEU_eq n s who (profile n s who)

/-- The strengthened profile/value pair is a genuine discounted stationary
Bellman equilibrium. -/
lemma isDiscountedStationaryBellmanEq (n : ℕ) :
    game.IsDiscountedStationaryBellmanEq
      (FinkTangentCounterexample.discount n) (profile n) value := by
  constructor
  · intro s who dev
    rw [mixedDeviation_discountedAuxEU_eq, profile_discountedAuxEU_eq]
  · exact profile_discountedAuxEU_eq n

lemma abs_payoff_le_one (s : CState) (a : Player → Bool) (who : Player) :
    |game.stagePayoff s a who| ≤ 1 := by
  cases s <;> cases who <;>
    simp only [payoff, Bool.false_eq_true, if_false, if_true,
      FinkTangentCounterexample.payoff]
  all_goals try split <;> norm_num
  all_goals norm_num

/-- Every member of the forced rare-action branch is an actual Fink fixed
point, not merely a solution of the displayed indifference equations. -/
theorem finkMap_point_eq (n : ℕ) :
    game.finkMap (FinkTangentCounterexample.discount n) 1
        (FinkTangentCounterexample.discount_nonneg n)
        (FinkTangentCounterexample.discount_le_one n)
        abs_payoff_le_one (point n) = point n := by
  exact game.finkMap_finkPointOfProfileValue_eq_self
    (FinkTangentCounterexample.discount n) 1
      (FinkTangentCounterexample.discount_nonneg n)
      (FinkTangentCounterexample.discount_le_one n)
      abs_payoff_le_one (profile n) value abs_value_le_one
      (isDiscountedStationaryBellmanEq n)

/-! ## The two exact live-state mixing equations -/

/- End of section heading. -/

/-- Against a player-2 mixture putting real probability `q` on `Q`, player
1's pure-`A` auxiliary payoff minus pure-`B` auxiliary payoff is
`2 * (β*q - (1-β))`.  The continuation value at the live state cancels;
only the two absorbing values `+1` and `-1` enter. -/
lemma playerOne_live_pureDifference
    (β q liveValue : ℝ) :
    ((1 - β) * (-1) + β * ((1 - q) * liveValue + q * 1)) -
        ((1 - β) * 1 + β * ((1 - q) * liveValue + q * (-1))) =
      2 * (β * q - (1 - β)) := by
  ring

/-- Hence indifference of player 1 forces the rare-action probability
exactly, provided `β ≠ 0`. -/
lemma rareProbability_eq_of_playerOne_indifferent
    {β q liveValue : ℝ} (hβ : β ≠ 0)
    (hindiff :
      (1 - β) * (-1) + β * ((1 - q) * liveValue + q * 1) =
        (1 - β) * 1 + β * ((1 - q) * liveValue + q * (-1))) :
    q = (1 - β) / β := by
  have hzero : 2 * (β * q - (1 - β)) = 0 := by
    rw [← playerOne_live_pureDifference β q liveValue, hindiff]
    ring
  have hmul : β * q = 1 - β := by linarith
  exact (eq_div_iff hβ).2 (by simpa [mul_comm] using hmul)

/-- If player 2 assigns positive probability to both `C` and `Q`, its two
Bellman equalities force player 1's live mixing probability `r` to be `1/2`.
Here `r` is the probability of `B` and `v` is player 2's live value. -/
lemma half_eq_of_playerTwo_indifferent
    {β r v : ℝ} (hβ : β < 1)
    (hC : (1 - β) * (1 - 2 * r) + β * v = v)
    (hQ : (1 - β) * (2 * r - 1) = v) :
    r = 1 / 2 := by
  have hfactor : (1 - β) * (2 - β) * (1 - 2 * r) = 0 := by
    calc
      (1 - β) * (2 - β) * (1 - 2 * r) =
          ((1 - β) * (1 - 2 * r) + β * v) - v := by
            rw [← hQ]
            ring
      _ = 0 := by rw [hC]; ring
  rcases mul_eq_zero.mp hfactor with hzero | hzero
  · rcases mul_eq_zero.mp hzero with hzero | hzero
    · linarith
    · linarith
  · linarith

lemma playerTwo_liveValue_eq_zero_of_indifferent
    {β r v : ℝ} (hβ : β < 1)
    (hC : (1 - β) * (1 - 2 * r) + β * v = v)
    (hQ : (1 - β) * (2 * r - 1) = v) :
    v = 0 := by
  have hr := half_eq_of_playerTwo_indifferent hβ hC hQ
  rw [hr] at hQ
  norm_num at hQ
  exact hQ.symm

/-- The two support equalities isolate exactly the branch used above.  This
is the algebraic core showing why semialgebraic or support-minimal selection
cannot improve its first-order rate once the live equilibrium is fully
mixed. -/
theorem unique_live_mix_of_both_indifferent
    {β q r vOne vTwo : ℝ} (hβ0 : β ≠ 0) (hβ1 : β < 1)
    (hOne :
      (1 - β) * (-1) + β * ((1 - q) * vOne + q * 1) =
        (1 - β) * 1 + β * ((1 - q) * vOne + q * (-1)))
    (hC : (1 - β) * (1 - 2 * r) + β * vTwo = vTwo)
    (hQ : (1 - β) * (2 * r - 1) = vTwo) :
    q = (1 - β) / β ∧ r = 1 / 2 ∧ vTwo = 0 := by
  exact ⟨rareProbability_eq_of_playerOne_indifferent hβ0 hOne,
    half_eq_of_playerTwo_indifferent hβ1 hC hQ,
    playerTwo_liveValue_eq_zero_of_indifferent hβ1 hC hQ⟩

/-- Scalar live-state equilibrium certificate.  The four implications are
exactly the two players' best-response inequalities on actions having
positive probability, and `hBell` is player 2's on-profile Bellman equation.
For `1/2 < β < 1` they rule out both boundary and semi-mixed profiles and
force the unique live mixture.

This theorem is deliberately stated at the matrix-coordinate interface: it
can be applied to any semantic Fink equilibrium once its four Boolean
expectations have been expanded. -/
theorem unique_live_mix_of_bellman_bestResponses
    {β q r v : ℝ}
    (hβlow : 1 / 2 < β) (hβhigh : β < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hA : r < 1 → 0 ≤ β * q - (1 - β))
    (hB : 0 < r → β * q - (1 - β) ≤ 0)
    (hC : q < 1 →
      (1 - β) * (2 * r - 1) ≤
        (1 - β) * (1 - 2 * r) + β * v)
    (hQ : 0 < q →
      (1 - β) * (1 - 2 * r) + β * v ≤
        (1 - β) * (2 * r - 1))
    (hBell : v =
      (1 - q) * ((1 - β) * (1 - 2 * r) + β * v) +
        q * ((1 - β) * (2 * r - 1))) :
    q = (1 - β) / β ∧ r = 1 / 2 ∧ v = 0 := by
  have hβpos : 0 < β := by linarith
  have hlambda : 0 < 1 - β := sub_pos.mpr hβhigh
  have hqpos : 0 < q := by
    by_contra hnot
    have hq : q = 0 := le_antisymm (le_of_not_gt hnot) hq0
    have hr : r = 1 := by
      apply le_antisymm hr1
      by_contra hnotr
      have := hA (lt_of_not_ge hnotr)
      rw [hq] at this
      nlinarith
    have hCused := hC (by rw [hq]; norm_num)
    have hBell0 := hBell
    rw [hq, hr] at hBell0
    have hvfactor : (1 - β) * (v + 1) = 0 := by
      linear_combination hBell0
    have hv : v = -1 := by
      rcases mul_eq_zero.mp hvfactor with hzero | hzero
      · linarith
      · linarith
    rw [hr, hv] at hCused
    nlinarith
  have hqlt : q < 1 := by
    by_contra hnot
    have hq : q = 1 := le_antisymm hq1 (le_of_not_gt hnot)
    have hr : r = 0 := by
      apply le_antisymm
      · by_contra hnotr
        have := hB (lt_of_not_ge hnotr)
        rw [hq] at this
        nlinarith
      · exact hr0
    have hQused := hQ (by rw [hq]; norm_num)
    have hv : v = -(1 - β) := by
      rw [hBell, hq, hr]
      ring
    rw [hr, hv] at hQused
    nlinarith [mul_pos hlambda hlambda]
  have hCused := hC hqlt
  have hQused := hQ hqpos
  have hCQ :
      (1 - β) * (1 - 2 * r) + β * v =
        (1 - β) * (2 * r - 1) :=
    le_antisymm hQused hCused
  have hvQ : (1 - β) * (2 * r - 1) = v := by
    calc
      (1 - β) * (2 * r - 1) =
          (1 - q) * ((1 - β) * (1 - 2 * r) + β * v) +
            q * ((1 - β) * (2 * r - 1)) := by rw [hCQ]; ring
      _ = v := hBell.symm
  have hCv : (1 - β) * (1 - 2 * r) + β * v = v :=
    hCQ.trans hvQ
  have hr : r = 1 / 2 :=
    half_eq_of_playerTwo_indifferent hβhigh hCv hvQ
  have hv : v = 0 :=
    playerTwo_liveValue_eq_zero_of_indifferent hβhigh hCv hvQ
  have hdelta : β * q - (1 - β) = 0 := by
    apply le_antisymm
    · exact hB (by rw [hr]; norm_num)
    · exact hA (by rw [hr]; norm_num)
  have hq : q = (1 - β) / β := by
    apply (eq_div_iff hβpos.ne').2
    nlinarith
  exact ⟨hq, hr, hv⟩

end Base

end FinkSelectionCounterexample
end StochasticGame
end GameTheory

namespace GameTheory
namespace StochasticGame
namespace FinkSelectionCounterexample
namespace Base

open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

/-! ## Semantic uniqueness of the live Bellman equilibrium -/

lemma pmfBool_false_toReal (μ : PMF Bool) :
    (μ false).toReal = 1 - (μ true).toReal := by
  have h := expect_const μ (1 : ℝ)
  rw [expect_eq_sum, Fintype.sum_bool] at h
  norm_num at h ⊢
  linarith

lemma pmfBool_toReal_nonneg (μ : PMF Bool) (d : Bool) :
    0 ≤ (μ d).toReal := ENNReal.toReal_nonneg

lemma pmfBool_toReal_le_one (μ : PMF Bool) (d : Bool) :
    (μ d).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (μ.coe_le_one d)

/-- Bellman consistency fixes all continuation values at the two absorbing
states, independently of the stationary profile. -/
lemma absorbing_values_of_bellman
    {β : ℝ} {x : game.StationaryMixedProfile}
    {V : game.State → Payoff Player} (hβ : β < 1)
    (hF : game.IsDiscountedStationaryBellmanEq β x V) :
    V .high false = 1 ∧ V .low false = -1 ∧
      V .high true = 0 ∧ V .low true = 0 := by
  have hHighOne := hF.2 .high false
  have hLowOne := hF.2 .low false
  have hHighTwo := hF.2 .high true
  have hLowTwo := hF.2 .low true
  unfold StochasticGame.discountedAuxEU at hHighOne hLowOne hHighTwo hLowTwo
  simp [discountedAuxPayoff, payoff,
    FinkTangentCounterexample.payoff,
    FinkTangentCounterexample.expect_transition,
    FinkTangentCounterexample.nextState,
    expect_const] at hHighOne hLowOne hHighTwo hLowTwo
  constructor
  · nlinarith [sub_pos.mpr hβ]
  constructor
  · nlinarith [sub_pos.mpr hβ]
  constructor <;> nlinarith [sub_pos.mpr hβ]

/-- A Boolean player's on-profile auxiliary payoff is the probability-weighted
average of its two pure auxiliary payoffs. -/
lemma discountedAuxEU_eq_bool_mix
    (β : ℝ) (x : game.StationaryMixedProfile)
    (V : game.State → Payoff Player) (s : game.State) (who : Player) :
    game.discountedAuxEU β V s (x s) who =
      (1 - ((x s who) true).toReal) *
          game.discountedAuxEU β V s
            (Function.update (x s) who (PMF.pure false)) who +
        ((x s who) true).toReal *
          game.discountedAuxEU β V s
            (Function.update (x s) who (PMF.pure true)) who := by
  calc
    game.discountedAuxEU β V s (x s) who =
        game.discountedAuxEU β V s
          (Function.update (x s) who (x s who)) who := by
            rw [Function.update_eq_self]
    _ = _ := by
      unfold StochasticGame.discountedAuxEU
      rw [pmfPi_update_bind, expect_bind, expect_eq_sum, Fintype.sum_bool]
      rw [pmfBool_false_toReal]
      exact add_comm _ _

/-- Player 1's two live pure auxiliary payoffs in semantic coordinates. -/
lemma playerOne_live_pure_values
    {β : ℝ} {x : game.StationaryMixedProfile}
    {V : game.State → Payoff Player}
    (hHigh : V .high false = 1) (hLow : V .low false = -1) :
    let q := ((x .live true) true).toReal
    let v := V .live false
    game.discountedAuxEU β V .live
        (Function.update (x .live) false (PMF.pure false)) false =
          (1 - β) * (-1) + β * ((1 - q) * v + q * 1) ∧
      game.discountedAuxEU β V .live
        (Function.update (x .live) false (PMF.pure true)) false =
          (1 - β) * 1 + β * ((1 - q) * v + q * (-1)) := by
  dsimp only
  unfold StochasticGame.discountedAuxEU
  rw [FinkTangentCounterexample.expect_pmfPi_bool,
    FinkTangentCounterexample.expect_pmfPi_bool]
  simp [discountedAuxPayoff, payoff,
    FinkTangentCounterexample.payoff,
    FinkTangentCounterexample.expect_transition,
    FinkTangentCounterexample.nextState]
  rw [expect_eq_sum, expect_eq_sum, Fintype.sum_bool, Fintype.sum_bool]
  simp [hHigh, hLow]
  simp_rw [pmfBool_false_toReal]
  constructor <;> ring

lemma playerTwo_live_pure_values
    {β : ℝ} {x : game.StationaryMixedProfile}
    {V : game.State → Payoff Player}
    (hHigh : V .high true = 0) (hLow : V .low true = 0) :
    let r := ((x .live false) true).toReal
    let v := V .live true
    game.discountedAuxEU β V .live
        (Function.update (x .live) true (PMF.pure false)) true =
          (1 - β) * (1 - 2 * r) + β * v ∧
      game.discountedAuxEU β V .live
        (Function.update (x .live) true (PMF.pure true)) true =
          (1 - β) * (2 * r - 1) := by
  dsimp only
  unfold StochasticGame.discountedAuxEU
  rw [FinkTangentCounterexample.expect_pmfPi_bool,
    FinkTangentCounterexample.expect_pmfPi_bool]
  simp [discountedAuxPayoff, payoff,
    FinkTangentCounterexample.expect_transition,
    FinkTangentCounterexample.nextState]
  rw [expect_eq_sum, expect_eq_sum, Fintype.sum_bool, Fintype.sum_bool]
  simp [hHigh, hLow]
  simp_rw [pmfBool_false_toReal]
  constructor <;> ring

/-- Every discounted stationary Bellman equilibrium on the selection-resistant
game has the same live-state coordinates once `1 / 2 < β < 1`.  In
particular, the rare action cannot be removed or made smaller by choosing a
different semantic equilibrium. -/
theorem unique_live_coordinates_of_isDiscountedStationaryBellmanEq
    {β : ℝ} {x : game.StationaryMixedProfile}
    {V : game.State → Payoff Player}
    (hβlow : 1 / 2 < β) (hβhigh : β < 1)
    (hF : game.IsDiscountedStationaryBellmanEq β x V) :
    ((x .live true) true).toReal = (1 - β) / β ∧
      ((x .live false) true).toReal = 1 / 2 ∧
        V .live true = 0 := by
  let q : ℝ := ((x .live true) true).toReal
  let r : ℝ := ((x .live false) true).toReal
  let vOne : ℝ := V .live false
  let vTwo : ℝ := V .live true
  let uA : ℝ := game.discountedAuxEU β V .live
    (Function.update (x .live) false (PMF.pure false)) false
  let uB : ℝ := game.discountedAuxEU β V .live
    (Function.update (x .live) false (PMF.pure true)) false
  let uC : ℝ := game.discountedAuxEU β V .live
    (Function.update (x .live) true (PMF.pure false)) true
  let uQ : ℝ := game.discountedAuxEU β V .live
    (Function.update (x .live) true (PMF.pure true)) true
  obtain ⟨hHighOne, hLowOne, hHighTwo, hLowTwo⟩ :=
    absorbing_values_of_bellman hβhigh hF
  have hOne :
      uA = (1 - β) * (-1) + β * ((1 - q) * vOne + q * 1) ∧
      uB = (1 - β) * 1 + β * ((1 - q) * vOne + q * (-1)) := by
    simpa only [uA, uB, q, vOne] using
      playerOne_live_pure_values (β := β) (x := x) (V := V)
        hHighOne hLowOne
  have hTwo :
      uC = (1 - β) * (1 - 2 * r) + β * vTwo ∧
      uQ = (1 - β) * (2 * r - 1) := by
    simpa only [uC, uQ, r, vTwo] using
      playerTwo_live_pure_values (β := β) (x := x) (V := V)
        hHighTwo hLowTwo
  have hBellOne : vOne = (1 - r) * uA + r * uB := by
    have hm := discountedAuxEU_eq_bool_mix β x V .live false
    have hb := hF.2 .live false
    dsimp only [vOne, r, uA, uB]
    exact hb.symm.trans hm
  have hBellTwo : vTwo = (1 - q) * uC + q * uQ := by
    have hm := discountedAuxEU_eq_bool_mix β x V .live true
    have hb := hF.2 .live true
    dsimp only [vTwo, q, uC, uQ]
    exact hb.symm.trans hm
  have hAdev : uA ≤ vOne := by
    have h := hF.1 .live false (PMF.pure false)
    rw [hF.2 .live false] at h
    exact h
  have hBdev : uB ≤ vOne := by
    have h := hF.1 .live false (PMF.pure true)
    rw [hF.2 .live false] at h
    exact h
  have hCdev : uC ≤ vTwo := by
    have h := hF.1 .live true (PMF.pure false)
    rw [hF.2 .live true] at h
    exact h
  have hQdev : uQ ≤ vTwo := by
    have h := hF.1 .live true (PMF.pure true)
    rw [hF.2 .live true] at h
    exact h
  have hOneDiff : uA - uB = 2 * (β * q - (1 - β)) := by
    rw [hOne.1, hOne.2]
    exact playerOne_live_pureDifference β q vOne
  have hA : r < 1 → 0 ≤ β * q - (1 - β) := by
    intro hr
    have hfactor : vOne - uB = (1 - r) * (uA - uB) := by
      rw [hBellOne]
      ring
    have hmul : 0 ≤ (1 - r) * (uA - uB) := by
      rw [← hfactor]
      exact sub_nonneg.mpr hBdev
    have hdiff : 0 ≤ uA - uB :=
      nonneg_of_mul_nonneg_right hmul (sub_pos.mpr hr)
    rw [hOneDiff] at hdiff
    linarith
  have hB : 0 < r → β * q - (1 - β) ≤ 0 := by
    intro hr
    have hfactor : vOne - uA = r * (uB - uA) := by
      rw [hBellOne]
      ring
    have hmul : 0 ≤ r * (uB - uA) := by
      rw [← hfactor]
      exact sub_nonneg.mpr hAdev
    have hdiff : 0 ≤ uB - uA :=
      nonneg_of_mul_nonneg_right hmul hr
    linarith [hOneDiff]
  have hC : q < 1 → uQ ≤ uC := by
    intro hq
    have hfactor : vTwo - uQ = (1 - q) * (uC - uQ) := by
      rw [hBellTwo]
      ring
    have hmul : 0 ≤ (1 - q) * (uC - uQ) := by
      rw [← hfactor]
      exact sub_nonneg.mpr hQdev
    exact sub_nonneg.mp
      (nonneg_of_mul_nonneg_right hmul (sub_pos.mpr hq))
  have hQ : 0 < q → uC ≤ uQ := by
    intro hq
    have hfactor : vTwo - uC = q * (uQ - uC) := by
      rw [hBellTwo]
      ring
    have hmul : 0 ≤ q * (uQ - uC) := by
      rw [← hfactor]
      exact sub_nonneg.mpr hCdev
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hmul hq)
  have hq0 : 0 ≤ q := pmfBool_toReal_nonneg _ _
  have hq1 : q ≤ 1 := pmfBool_toReal_le_one _ _
  have hr0 : 0 ≤ r := pmfBool_toReal_nonneg _ _
  have hr1 : r ≤ 1 := pmfBool_toReal_le_one _ _
  have hresult := unique_live_mix_of_bellman_bestResponses
    hβlow hβhigh hq0 hq1 hr0 hr1 hA hB
    (fun hq => by rw [← hTwo.1, ← hTwo.2]; exact hC hq)
    (fun hq => by rw [← hTwo.1, ← hTwo.2]; exact hQ hq)
    (by simpa only [hTwo.1, hTwo.2] using hBellTwo)
  simpa only [q, r, vTwo] using hresult

/-- Fixed-point form of semantic live-state uniqueness.  Any Fink fixed point
for this game in the discount range `1 / 2 < β < 1` decodes to the forced
rare-action probability, the forced half mixture of player 1, and zero live
value for player 2. -/
theorem unique_live_coordinates_of_finkMap_fixedPoint
    {β U : ℝ} (hβlow : 1 / 2 < β) (hβhigh : β < 1)
    (hpay : ∀ s a who, |game.stagePayoff s a who| ≤ U)
    (z : game.finkDomain U)
    (hfix : game.finkMap β U (le_trans (by norm_num) hβlow.le)
        hβhigh.le hpay z = z) :
    ((game.finkProfile z .live true) true).toReal = (1 - β) / β ∧
      ((game.finkProfile z .live false) true).toReal = 1 / 2 ∧
        game.finkValue z .live true = 0 := by
  have hF := game.isDiscountedStationaryBellmanEq_of_finkMap_fixedPoint
    β U (le_trans (by norm_num) hβlow.le) hβhigh.le hpay z hfix
  exact unique_live_coordinates_of_isDiscountedStationaryBellmanEq
    hβlow hβhigh hF

/-- The forced rare action survives exactly at reciprocal-bias scale.  Thus
no selection of Fink fixed points can make this scaled live coordinate tend
to zero. -/
theorem scaled_live_playerTwo_Q_of_finkMap_fixedPoint
    {β U : ℝ} (hβlow : 1 / 2 < β) (hβhigh : β < 1)
    (hpay : ∀ s a who, |game.stagePayoff s a who| ≤ U)
    (z : game.finkDomain U)
    (hfix : game.finkMap β U (le_trans (by norm_num) hβlow.le)
        hβhigh.le hpay z = z) :
    (β / (1 - β)) *
        ((game.finkProfile z .live true) true).toReal = 1 := by
  have hq := (unique_live_coordinates_of_finkMap_fixedPoint
    hβlow hβhigh hpay z hfix).1
  rw [hq]
  have hβ : β ≠ 0 := ne_of_gt (lt_trans (by norm_num) hβlow)
  have hOne : 1 - β ≠ 0 := ne_of_gt (sub_pos.mpr hβhigh)
  field_simp [hβ, hOne]

end Base
end FinkSelectionCounterexample
end StochasticGame
end GameTheory
