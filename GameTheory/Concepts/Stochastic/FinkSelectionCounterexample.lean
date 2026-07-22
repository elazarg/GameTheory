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
