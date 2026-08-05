/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCyclePinnedDebt
import GameTheory.Concepts.Stochastic.QuittingSoloQuitterEquilibrium

/-!
# The cyclic companion map contracts, and the mismatch vanishes

Fix a coordinate `who` and a stage root `y`.  Freezing the opponents'
marginals turns the backward Nash--Bellman value recursion into a *scalar*
one-stage map, the **companion map**

`quittingRootCompanionMap reward y who : w ↦ max {Σ(y), A(y) + c(y) * w}`,

whose three coefficients are the fixed-opponents quit value, the
fixed-opponents continue reward and the fixed-opponents continue mass of
`QuittingPureTimeExtremality.lean`, read off a single root
(`quittingRootDeletedQuitValue_eq_fixedOpponents` and friends are `rfl`).

Along a window of a root sequence the phase maps compose into
`quittingCompanionComposite`, and around a cycle of length `period` the
composite is the map `T_who` of the program notes, with Lipschitz constant
the deleted survival product `P_who = quittingOpponentSurvivalWeight roots
who 0 period`.

## The three steps

1. **Lipschitz.**  `|max a (b + c * w) - max a (b + c * w')| ≤ c * |w - w'|`
   for `c ≥ 0`, so each phase map is `c(y_k)`-Lipschitz
   (`abs_quittingRootCompanionMap_sub_le`) and the composite is
   `P`-Lipschitz (`abs_quittingCompanionComposite_sub_le`).
2. **Fixed point.**  At an *exactly* endpoint-Nash root the one-stage value
   map is literally the companion map
   (`quittingRootSuccessorPayoff_eq_companionMap_of_endpointNash`); this is
   the only place the max form is consumed, and it is where complementarity
   at every phase is used.  Hence a cyclic block's own value at `who` is a
   fixed point of the composite (`quittingCompanionComposite_value`).
3. **Contraction.**  A `c`-Lipschitz real self-map fixing `z` satisfies
   `|f^[N] w - z| ≤ c ^ N * |w - z|` for *every real* `w`
   (`abs_iterate_sub_le_of_lipschitz_of_fixed`), so `c < 1` forces
   `f^[N] w → z` (`tendsto_iterate_of_lipschitz_lt_one`).

## No sign hypothesis anywhere

The estimate of step 3 is two-sided: it never asks whether `w - z` is
nonnegative.  This is the whole point.  The unrolled transport law
`quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps` carries the
hypothesis `0 ≤ terminalDebt`, and that hypothesis is *not* automatic on
absorbing complementary cycles: the terminal gap
`max {0, r_who({who})} - z who` can be strictly negative there.  The route
below therefore does not use the transport law at all.  The elementary
real-number step of that law is genuinely sign-dependent, and
`max_sub_max_zero_eq_max_zero_sub_of_nonneg_fails` records a two-number
witness of its failure without `0 ≤ x`.

## What is proved and what is not

The headline `quittingCyclicContinuationBlock_mismatch_eq_zero` says: for an
absorbing cyclic continuation block of any period, if the deleted survival
product at `who` is strictly below one, then the companion composite's
iterates from *any* real starting point -- in particular from the solo-quit
anchor `quittingPositiveSingletonDebtCap reward who = max {0, r_who({who})}`
-- converge to the block's own value at `who`, so the anchored mismatch is
zero.

The complementary branch `P_who = 1` is **not** treated here.  Nothing below
computes the mismatch in the isolated configuration, and no statement is made
about the deviation gain of the infinitely repeated block beyond the scalar
companion recursion.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

/-! ## A sign-free contraction estimate for real self-maps

These three lemmas are ordinary real analysis; they are kept here because
they are exactly the shape consumed below, and because the second is the
statement whose *two-sidedness* is the point of this file. -/

/-- `max` is `1`-Lipschitz in its right argument. -/
theorem abs_max_sub_max_right_le (fixedArg first second : ℝ) :
    |max fixedArg first - max fixedArg second| ≤ |first - second| := by
  rw [max_comm fixedArg first, max_comm fixedArg second]
  exact abs_max_sub_max_le_abs first second fixedArg

/-- **The contraction estimate, for either sign.**  A `factor`-Lipschitz real
self-map fixing `fixedPoint` moves its `N`-th iterate to within
`factor ^ N * |start - fixedPoint|`.  The hypothesis list contains no
inequality relating `start` and `fixedPoint`: the bound holds on both sides
of the fixed point. -/
theorem abs_iterate_sub_le_of_lipschitz_of_fixed
    {map : ℝ → ℝ} {factor fixedPoint : ℝ} (hfactor : 0 ≤ factor)
    (hlipschitz : ∀ first second : ℝ,
      |map first - map second| ≤ factor * |first - second|)
    (hfixed : map fixedPoint = fixedPoint) (start : ℝ) (N : ℕ) :
    |map^[N] start - fixedPoint| ≤ factor ^ N * |start - fixedPoint| := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply']
      calc
        |map (map^[N] start) - fixedPoint|
            = |map (map^[N] start) - map fixedPoint| := by rw [hfixed]
        _ ≤ factor * |map^[N] start - fixedPoint| := hlipschitz _ _
        _ ≤ factor * (factor ^ N * |start - fixedPoint|) :=
            mul_le_mul_of_nonneg_left ih hfactor
        _ = factor ^ (N + 1) * |start - fixedPoint| := by ring

/-- A strictly contracting real self-map drives every orbit to its fixed
point, from any real starting point. -/
theorem tendsto_iterate_of_lipschitz_lt_one
    {map : ℝ → ℝ} {factor fixedPoint : ℝ} (hfactor : 0 ≤ factor)
    (hlt : factor < 1)
    (hlipschitz : ∀ first second : ℝ,
      |map first - map second| ≤ factor * |first - second|)
    (hfixed : map fixedPoint = fixedPoint) (start : ℝ) :
    Filter.Tendsto (fun N : ℕ => map^[N] start) Filter.atTop
      (nhds fixedPoint) := by
  have hbound : ∀ N : ℕ,
      ‖map^[N] start - fixedPoint‖ ≤ factor ^ N * |start - fixedPoint| := by
    intro N
    rw [Real.norm_eq_abs]
    exact abs_iterate_sub_le_of_lipschitz_of_fixed hfactor hlipschitz hfixed
      start N
  have hzero : Filter.Tendsto
      (fun N : ℕ => factor ^ N * |start - fixedPoint|) Filter.atTop
      (nhds 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hfactor hlt
    simpa using hpow.mul_const |start - fixedPoint|
  have hdiff : Filter.Tendsto (fun N : ℕ => map^[N] start - fixedPoint)
      Filter.atTop (nhds 0) := squeeze_zero_norm hbound hzero
  simpa using hdiff.add_const fixedPoint

/-- **The transport law's elementary step is genuinely sign-dependent.**
`max_sub_max_zero_eq_max_zero_sub_of_nonneg` assumes `0 ≤ x`, and the
identity is false without it: at `h = -2`, `x = -1` the left side is `-1`
and the right side is `0`.

This is a fence on the *scalar* identity underlying
`quittingFiniteDynamicDebt_succ_eq_max_zero_stageGap`, not a game-level
counterexample; it records only that the nonnegativity hypothesis of the
transport law cannot be dropped by a purely algebraic argument. -/
theorem max_sub_max_zero_eq_max_zero_sub_of_nonneg_fails :
    ∃ h x : ℝ, x < 0 ∧ max h x - max h 0 ≠ max 0 (x - max 0 h) := by
  refine ⟨-2, -1, by norm_num, ?_⟩
  norm_num

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The deleted coefficients of a single root

`quittingFixedOpponentsQuitValue` and its two companions are stated for a
root *sequence* and a time.  The three definitions below are the same
quantities read off a single root; every bridge lemma is `rfl`. -/

/-- The payoff to `who` from quitting now against the opponents' fixed
marginals at `root` (`Σ_who(root)` in the program notes). -/
def quittingRootDeletedQuitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootAbsorbingContribution reward
    (Function.update root who (PMF.pure true)) who

/-- The immediate absorbing contribution to `who` when `who` continues at
`root` (`A_who(root)`). -/
def quittingRootDeletedContinueReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootAbsorbingContribution reward
    (Function.update root who (PMF.pure false)) who

/-- The probability that every opponent of `who` continues at `root`
(`c_{-who}(root)`). -/
def quittingRootDeletedContinueMass (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingStationaryContinueMass (Function.update root who (PMF.pure false))

theorem quittingRootDeletedQuitValue_eq_fixedOpponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingRootDeletedQuitValue reward (roots time) who =
      quittingFixedOpponentsQuitValue reward roots who time := rfl

theorem quittingRootDeletedContinueReward_eq_fixedOpponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingRootDeletedContinueReward reward (roots time) who =
      quittingFixedOpponentsContinueReward reward roots who time := rfl

theorem quittingRootDeletedContinueMass_eq_fixedOpponents
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingRootDeletedContinueMass (roots time) who =
      quittingFixedOpponentsContinueMass roots who time := rfl

theorem quittingRootDeletedContinueMass_nonneg
    (root : ι → PMF Bool) (who : ι) :
    0 ≤ quittingRootDeletedContinueMass root who :=
  quittingStationaryContinueMass_nonneg _

theorem quittingRootDeletedContinueMass_le_one
    (root : ι → PMF Bool) (who : ι) :
    quittingRootDeletedContinueMass root who ≤ 1 :=
  quittingStationaryContinueMass_le_one _

/-! ## The companion map of one root -/

/-- The **companion map** of `root` at `who`: the scalar one-stage backward
value map obtained by freezing the opponents' marginals,
`w ↦ max {Σ_who(root), A_who(root) + c_{-who}(root) * w}`. -/
def quittingRootCompanionMap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (continuation : ℝ) : ℝ :=
  max (quittingRootDeletedQuitValue reward root who)
    (quittingRootDeletedContinueReward reward root who +
      quittingRootDeletedContinueMass root who * continuation)

/-- **Step 1.**  The companion map is `c_{-who}(root)`-Lipschitz. -/
theorem abs_quittingRootCompanionMap_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (first second : ℝ) :
    |quittingRootCompanionMap reward root who first -
        quittingRootCompanionMap reward root who second| ≤
      quittingRootDeletedContinueMass root who * |first - second| := by
  refine (abs_max_sub_max_right_le _ _ _).trans (le_of_eq ?_)
  rw [show quittingRootDeletedContinueReward reward root who +
        quittingRootDeletedContinueMass root who * first -
      (quittingRootDeletedContinueReward reward root who +
        quittingRootDeletedContinueMass root who * second) =
      quittingRootDeletedContinueMass root who * (first - second) by ring,
    abs_mul, abs_of_nonneg (quittingRootDeletedContinueMass_nonneg root who)]

/-! ## Step 2: the value recursion is the companion map -/

/-- Quitting purely absorbs, so the pure-Quit endpoint does not read the
continuation at all. -/
theorem quittingRootQuitPayoff_eq_deletedQuitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootQuitPayoff reward tail root who =
      quittingRootDeletedQuitValue reward root who := by
  unfold quittingRootQuitPayoff quittingRootDeletedQuitValue
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingStationaryContinueMass_update_pure_true_eq_zero]
  ring

/-- The pure-Continue endpoint is affine in the continuation with scalar
linear part the deleted continue mass. -/
theorem quittingRootContinuePayoff_eq_deleted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootContinuePayoff reward tail root who =
      quittingRootDeletedContinueReward reward root who +
        quittingRootDeletedContinueMass root who * tail who := by
  unfold quittingRootContinuePayoff quittingRootDeletedContinueReward
    quittingRootDeletedContinueMass
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]

/-- **Exactness turns the mixture into a maximum.**  The successor value is
the player's own Quit/Continue Bernoulli mixture; exact (`ε = 0`) endpoint
Nash forces that mixture to sit at the larger endpoint. -/
theorem quittingRootSuccessorPayoff_eq_max_endpoints_of_endpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) :
    quittingRootSuccessorPayoff reward tail root who =
      max (quittingRootQuitPayoff reward tail root who)
        (quittingRootContinuePayoff reward tail root who) := by
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix reward tail root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  obtain ⟨hcontinueSide, hquitSide⟩ := hnash who
  simp only [quittingRootEndpointDifference] at hcontinueSide hquitSide
  have hquitMass : (0 : ℝ) ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hcontinueMass : (0 : ℝ) ≤ (root who false).toReal :=
    ENNReal.toReal_nonneg
  rcases le_total (quittingRootQuitPayoff reward tail root who)
      (quittingRootContinuePayoff reward tail root who) with hle | hle
  · rw [max_eq_right hle, hmix]
    have hzero : (root who true).toReal *
        (quittingRootQuitPayoff reward tail root who -
          quittingRootContinuePayoff reward tail root who) = 0 :=
      le_antisymm
        (mul_nonpos_of_nonneg_of_nonpos hquitMass (sub_nonpos.mpr hle))
        (by linarith)
    linear_combination hzero +
      quittingRootContinuePayoff reward tail root who * hsum
  · rw [max_eq_left hle, hmix]
    have hzero : (root who false).toReal *
        (quittingRootQuitPayoff reward tail root who -
          quittingRootContinuePayoff reward tail root who) = 0 :=
      le_antisymm hcontinueSide
        (mul_nonneg hcontinueMass (sub_nonneg.mpr hle))
    linear_combination -hzero +
      quittingRootQuitPayoff reward tail root who * hsum

/-- **Step 2.**  At an exactly endpoint-Nash root the one-stage backward
value map is literally the companion map.  This is where the max form
`value = max {quit, continue}` is consumed. -/
theorem quittingRootSuccessorPayoff_eq_companionMap_of_endpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) :
    quittingRootSuccessorPayoff reward tail root who =
      quittingRootCompanionMap reward root who (tail who) := by
  rw [quittingRootSuccessorPayoff_eq_max_endpoints_of_endpointNash
      reward tail root who hnash,
    quittingRootQuitPayoff_eq_deletedQuitValue,
    quittingRootContinuePayoff_eq_deleted]
  rfl

/-! ## Period one -/

/-- **Fixed point at period one.**  A root that reproduces `value` and is
exactly endpoint Nash against it makes every coordinate of `value` a fixed
point of its companion map. -/
theorem quittingRootCompanionMap_fixed_of_selfSuccessor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : Payoff ι) (root : ι → PMF Bool)
    (hvalue : value = quittingRootSuccessorPayoff reward value root)
    (hnash : IsεQuittingRootEndpointNash reward value 0 root) (who : ι) :
    quittingRootCompanionMap reward root who (value who) = value who := by
  rw [← quittingRootSuccessorPayoff_eq_companionMap_of_endpointNash
    reward value root who hnash]
  exact (congrFun hvalue who).symm

/-- **Contraction at period one, for either sign.**  Every iterate of the
companion map started anywhere on the line is within `c ^ N` of the row's own
value.  No hypothesis relates `start` to `value who`. -/
theorem abs_iterate_quittingRootCompanionMap_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : Payoff ι) (root : ι → PMF Bool)
    (hvalue : value = quittingRootSuccessorPayoff reward value root)
    (hnash : IsεQuittingRootEndpointNash reward value 0 root) (who : ι)
    (start : ℝ) (N : ℕ) :
    |(quittingRootCompanionMap reward root who)^[N] start - value who| ≤
      quittingRootDeletedContinueMass root who ^ N *
        |start - value who| :=
  abs_iterate_sub_le_of_lipschitz_of_fixed
    (quittingRootDeletedContinueMass_nonneg root who)
    (abs_quittingRootCompanionMap_sub_le reward root who)
    (quittingRootCompanionMap_fixed_of_selfSuccessor reward value root hvalue
      hnash who)
    start N

/-- **Zero mismatch at period one.**  If the deleted survival factor is
strictly below one, the companion orbit from *any* real starting point
converges to the row's own value. -/
theorem tendsto_iterate_quittingRootCompanionMap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : Payoff ι) (root : ι → PMF Bool)
    (hvalue : value = quittingRootSuccessorPayoff reward value root)
    (hnash : IsεQuittingRootEndpointNash reward value 0 root) (who : ι)
    (hmass : quittingRootDeletedContinueMass root who < 1) (start : ℝ) :
    Filter.Tendsto
      (fun N : ℕ => (quittingRootCompanionMap reward root who)^[N] start)
      Filter.atTop (nhds (value who)) :=
  tendsto_iterate_of_lipschitz_lt_one
    (quittingRootDeletedContinueMass_nonneg root who) hmass
    (abs_quittingRootCompanionMap_sub_le reward root who)
    (quittingRootCompanionMap_fixed_of_selfSuccessor reward value root hvalue
      hnash who)
    start

/-! ## Period one against a cyclic continuation block -/

/-- Simplex coordinates of a product root, inverse to
`quittingRootOfSimplex`. -/
def quittingSimplexOfRoot (root : ι → PMF Bool) : QuittingRootSimplex ι :=
  fun who ↦ stdSimplexEquiv (root who)

omit [DecidableEq ι] in
@[simp] theorem quittingRootOfSimplex_simplexOfRoot (root : ι → PMF Bool) :
    quittingRootOfSimplex (quittingSimplexOfRoot root) = root := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)

/-- The length-one block sitting at `value` with root `root`. -/
def quittingRowBlock (value : Payoff ι) (root : ι → PMF Bool) :
    QuittingFiniteNashBellmanPath ι 1 :=
  fun _ ↦ (value, quittingSimplexOfRoot root)

omit [DecidableEq ι] in
@[simp] theorem quittingRootOfSimplex_quittingRowBlock
    (value : Payoff ι) (root : ι → PMF Bool) (index : Fin 2) :
    quittingRootOfSimplex (quittingRowBlock value root index).2 = root :=
  quittingRootOfSimplex_simplexOfRoot root

/-- **Every bounded absorbing complementary row is a cyclic continuation
block of length one.**  This is the constructor that turns a row-level
certificate -- such as the solo-quitter certificate of
`QuittingSoloQuitterEquilibrium.lean` -- into an object the contraction
theorems above consume. -/
theorem quittingRowBlock_isQuittingCyclicContinuationBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : Payoff ι) (root : ι → PMF Bool)
    (hbound : ∀ who, |value who| ≤ quittingRewardBound reward)
    (hvalue : value = quittingRootSuccessorPayoff reward value root)
    (hnash : IsεQuittingRootEndpointNash reward value 0 root)
    (habsorb : 0 < quittingRootAbsorptionMass root) :
    IsQuittingCyclicContinuationBlock reward value 1
      (quittingRowBlock value root) := by
  have hedge : IsQuittingNashBellmanEdge reward
      ((value, quittingSimplexOfRoot root) : QuittingNashBellmanPoint ι)
      ((value, quittingSimplexOfRoot root) : QuittingNashBellmanPoint ι) := by
    constructor
    · change value = quittingRootSuccessorPayoff reward value
        (quittingRootOfSimplex (quittingSimplexOfRoot root))
      rw [quittingRootOfSimplex_simplexOfRoot]
      exact hvalue
    · change IsεQuittingRootEndpointNash reward value 0
        (quittingRootOfSimplex (quittingSimplexOfRoot root))
      rw [quittingRootOfSimplex_simplexOfRoot]
      exact hnash
  refine ⟨⟨fun _ ↦ ?_, rfl, fun _ ↦ hedge⟩, rfl, ⟨0, ?_⟩⟩
  · change value ∈ Set.Icc (fun _ : ι ↦ -(quittingRewardBound reward))
      (fun _ ↦ quittingRewardBound reward)
    exact ⟨fun who ↦ (abs_le.mp (hbound who)).1,
      fun who ↦ (abs_le.mp (hbound who)).2⟩
  · change 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex (quittingSimplexOfRoot root))
    rw [quittingRootOfSimplex_simplexOfRoot]
    exact habsorb

/-- The origin edge of a cyclic continuation block of length one is exactly
(`ε = 0`) endpoint Nash against the block's own value.  This is the companion
of `quittingCyclicContinuationBlock_one_fixed`, which supplies the value
equation. -/
theorem quittingCyclicContinuationBlock_one_endpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (block : QuittingFiniteNashBellmanPath ι 1)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal 1 block) :
    IsεQuittingRootEndpointNash reward terminal 0
      (quittingRootOfSimplex (block 0).2) := by
  have hedge := hblock.1.2.2 0
  have hlast : (block (Fin.succ 0)).1 = terminal := hblock.1.2.1
  have hcast : Fin.castSucc (0 : Fin 1) = (0 : Fin 2) := rfl
  have hnash := hedge.2
  rw [hcast, hlast] at hnash
  exact hnash

/-- **Headline, period one.**  For an absorbing cyclic continuation block of
length one whose deleted survival factor at `who` is strictly below one, the
companion orbit from *any* real starting point converges to the block's own
value at `who`. -/
theorem tendsto_iterate_companionMap_cyclicBlock_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (block : QuittingFiniteNashBellmanPath ι 1)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal 1 block)
    (who : ι)
    (hmass : quittingRootDeletedContinueMass
      (quittingRootOfSimplex (block 0).2) who < 1)
    (start : ℝ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (quittingRootCompanionMap reward
          (quittingRootOfSimplex (block 0).2) who)^[N] start)
      Filter.atTop (nhds (terminal who)) :=
  tendsto_iterate_quittingRootCompanionMap reward terminal
    (quittingRootOfSimplex (block 0).2)
    (quittingCyclicContinuationBlock_one_fixed reward terminal block hblock)
    (quittingCyclicContinuationBlock_one_endpointNash reward terminal block
      hblock)
    who hmass start

/-- **Zero mismatch at period one.**  Any limit of the companion orbit
started at the solo-quit anchor equals the block's own value.  The anchor may
lie on either side of that value; no sign hypothesis is used. -/
theorem quittingCyclicContinuationBlock_one_mismatch_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (block : QuittingFiniteNashBellmanPath ι 1)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal 1 block)
    (who : ι)
    (hmass : quittingRootDeletedContinueMass
      (quittingRootOfSimplex (block 0).2) who < 1)
    (anchorLimit : ℝ)
    (hanchor : Filter.Tendsto
      (fun N : ℕ =>
        (quittingRootCompanionMap reward
          (quittingRootOfSimplex (block 0).2) who)^[N]
          (quittingPositiveSingletonDebtCap reward who))
      Filter.atTop (nhds anchorLimit)) :
    anchorLimit - terminal who = 0 := by
  have hunique := tendsto_nhds_unique hanchor
    (tendsto_iterate_companionMap_cyclicBlock_one reward terminal block hblock
      who hmass _)
  rw [hunique, sub_self]

/-! ## The composite around a general cycle -/

/-- The composite of the phase companion maps along the window
`[start, start + fuel)` of a root sequence:
`composite start (fuel + 1) = φ_start ∘ composite (start + 1) fuel`. -/
def quittingCompanionComposite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) : ℕ → ℕ → ℝ → ℝ
  | _, 0 => id
  | start, fuel + 1 => fun continuation =>
      quittingRootCompanionMap reward (roots start) who
        (quittingCompanionComposite reward roots who (start + 1) fuel
          continuation)

@[simp] theorem quittingCompanionComposite_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) (continuation : ℝ) :
    quittingCompanionComposite reward roots who start 0 continuation =
      continuation := rfl

theorem quittingCompanionComposite_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ)
    (continuation : ℝ) :
    quittingCompanionComposite reward roots who start (fuel + 1)
        continuation =
      quittingRootCompanionMap reward (roots start) who
        (quittingCompanionComposite reward roots who (start + 1) fuel
          continuation) := rfl

/-- Peeling the first factor off a survival weight. -/
theorem quittingOpponentSurvivalWeight_succ_left
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingOpponentSurvivalWeight roots who start (fuel + 1) =
      quittingFixedOpponentsContinueMass roots who start *
        quittingOpponentSurvivalWeight roots who (start + 1) fuel := by
  rw [show fuel + 1 = 1 + fuel by omega, quittingOpponentSurvivalWeight_add]
  have hone : quittingOpponentSurvivalWeight roots who start 1 =
      quittingFixedOpponentsContinueMass roots who start := by
    simp [quittingOpponentSurvivalWeight]
  rw [hone]

/-- **Step 1 around the cycle.**  The composite is `P`-Lipschitz, where `P`
is the deleted survival product over the traversed window. -/
theorem abs_quittingCompanionComposite_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ)
    (first second : ℝ) :
    |quittingCompanionComposite reward roots who start fuel first -
        quittingCompanionComposite reward roots who start fuel second| ≤
      quittingOpponentSurvivalWeight roots who start fuel *
        |first - second| := by
  induction fuel generalizing start with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      rw [quittingCompanionComposite_succ, quittingCompanionComposite_succ,
        quittingOpponentSurvivalWeight_succ_left,
        ← quittingRootDeletedContinueMass_eq_fixedOpponents roots who start]
      calc
        |quittingRootCompanionMap reward (roots start) who
              (quittingCompanionComposite reward roots who (start + 1) fuel
                first) -
            quittingRootCompanionMap reward (roots start) who
              (quittingCompanionComposite reward roots who (start + 1) fuel
                second)|
            ≤ quittingRootDeletedContinueMass (roots start) who *
              |quittingCompanionComposite reward roots who (start + 1) fuel
                  first -
                quittingCompanionComposite reward roots who (start + 1) fuel
                  second| :=
              abs_quittingRootCompanionMap_sub_le reward (roots start) who _ _
        _ ≤ quittingRootDeletedContinueMass (roots start) who *
              (quittingOpponentSurvivalWeight roots who (start + 1) fuel *
                |first - second|) :=
              mul_le_mul_of_nonneg_left (ih (start + 1))
                (quittingRootDeletedContinueMass_nonneg (roots start) who)
        _ = quittingRootDeletedContinueMass (roots start) who *
              quittingOpponentSurvivalWeight roots who (start + 1) fuel *
              |first - second| := by ring

/-- **Step 2 around the cycle.**  If every stage of the window carries the
exact value equation and an exact endpoint-Nash certificate against the next
displayed value, the composite transports the window's terminal value back to
its initial value. -/
theorem quittingCompanionComposite_value
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (value : ℕ → Payoff ι) (bound : ℕ)
    (hvalue : ∀ time, time < bound →
      value time =
        quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time, time < bound →
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time)) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingCompanionComposite reward roots who start fuel
          (value (start + fuel) who) =
        value start who := by
  intro start fuel
  induction fuel generalizing start with
  | zero => intro _; simp
  | succ fuel ih =>
      intro hwindow
      rw [quittingCompanionComposite_succ,
        show start + (fuel + 1) = start + 1 + fuel by omega,
        ih (start + 1) (by omega),
        ← quittingRootSuccessorPayoff_eq_companionMap_of_endpointNash
          reward (value (start + 1)) (roots start) who
          (hnash start (by omega))]
      exact (congrFun (hvalue start (by omega)) who).symm

/-- **Contraction around the cycle, for either sign.**  If the composite over
`[0, period)` fixes `anchor`, every iterate from any real starting point is
within `P ^ N` of it. -/
theorem abs_iterate_quittingCompanionComposite_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ) {anchor : ℝ}
    (hfixed : quittingCompanionComposite reward roots who 0 period anchor =
      anchor)
    (start : ℝ) (N : ℕ) :
    |(quittingCompanionComposite reward roots who 0 period)^[N] start -
        anchor| ≤
      quittingOpponentSurvivalWeight roots who 0 period ^ N *
        |start - anchor| :=
  abs_iterate_sub_le_of_lipschitz_of_fixed
    (quittingOpponentSurvivalWeight_nonneg roots who 0 period)
    (abs_quittingCompanionComposite_sub_le reward roots who 0 period)
    hfixed start N

/-- **Zero mismatch around the cycle.**  A deleted survival product strictly
below one drives every companion orbit to the cycle's own value. -/
theorem tendsto_iterate_quittingCompanionComposite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ) {anchor : ℝ}
    (hfixed : quittingCompanionComposite reward roots who 0 period anchor =
      anchor)
    (hsurvival : quittingOpponentSurvivalWeight roots who 0 period < 1)
    (start : ℝ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward roots who 0 period)^[N] start)
      Filter.atTop (nhds anchor) :=
  tendsto_iterate_of_lipschitz_lt_one
    (quittingOpponentSurvivalWeight_nonneg roots who 0 period) hsurvival
    (abs_quittingCompanionComposite_sub_le reward roots who 0 period) hfixed
    start

/-! ## Reading a cyclic continuation block as a root sequence -/

/-- The value projection of an anchored chain obeys its exact Bellman
equation before the cutoff.  Same proof as the zero-boundary version; only
the terminal clause of the chain family differs, and it is not used. -/
theorem quittingAnchoredPathValue_eq_successor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteAnchoredNashBellmanChainSet reward terminal cutoff)
    (time : ℕ) (htime : time < cutoff) :
    quittingFiniteNashBellmanPathValue cutoff path time =
      quittingRootSuccessorPayoff reward
        (quittingFiniteNashBellmanPathValue cutoff path (time + 1))
        (quittingFiniteNashBellmanPathRoots cutoff path time) := by
  have htime0 : time < cutoff + 1 := lt_trans htime (Nat.lt_succ_self cutoff)
  have htime1 : time + 1 < cutoff + 1 := Nat.succ_lt_succ htime
  simpa [quittingFiniteNashBellmanPathValue,
    quittingFiniteNashBellmanPathRoots, htime, htime0, htime1] using
    (hpath.2.2 (⟨time, htime⟩ : Fin cutoff)).1

/-- Every pre-terminal root of an anchored chain is exactly endpoint Nash
against its displayed successor value. -/
theorem quittingAnchoredPathRoots_isZeroEndpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteAnchoredNashBellmanChainSet reward terminal cutoff)
    (time : ℕ) (htime : time < cutoff) :
    IsεQuittingRootEndpointNash reward
      (quittingFiniteNashBellmanPathValue cutoff path (time + 1)) 0
      (quittingFiniteNashBellmanPathRoots cutoff path time) := by
  have htime1 : time + 1 < cutoff + 1 := Nat.succ_lt_succ htime
  simpa [quittingFiniteNashBellmanPathValue,
    quittingFiniteNashBellmanPathRoots, htime, htime1] using
    (hpath.2.2 (⟨time, htime⟩ : Fin cutoff)).2

/-- The displayed value at the cutoff of an anchored chain is the anchor. -/
theorem quittingAnchoredPathValue_at_cutoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteAnchoredNashBellmanChainSet reward terminal cutoff) :
    quittingFiniteNashBellmanPathValue cutoff path cutoff = terminal := by
  rw [quittingFiniteNashBellmanPathValue, dif_pos (Nat.lt_succ_self cutoff)]
  exact hpath.2.1

/-- The displayed value at the origin of a cyclic continuation block is the
anchor. -/
theorem quittingCyclicBlockValue_at_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block) :
    quittingFiniteNashBellmanPathValue period block 0 = terminal := by
  rw [quittingFiniteNashBellmanPathValue, dif_pos (Nat.succ_pos period)]
  exact hblock.2.1

/-- **The cycle's own value is a fixed point of the cyclic composite.**  This
is the fixed-point half of the argument, at arbitrary period. -/
theorem quittingCompanionComposite_cyclicBlock_fixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    (who : ι) :
    quittingCompanionComposite reward
        (quittingFiniteNashBellmanPathRoots period block) who 0 period
        (terminal who) =
      terminal who := by
  have hstep := quittingCompanionComposite_value reward
    (quittingFiniteNashBellmanPathRoots period block) who
    (quittingFiniteNashBellmanPathValue period block) period
    (fun time htime ↦ quittingAnchoredPathValue_eq_successor reward terminal
      period block hblock.1 time htime)
    (fun time htime ↦ quittingAnchoredPathRoots_isZeroEndpointNash reward
      terminal period block hblock.1 time htime)
    0 period (by omega)
  have hcutoff : quittingFiniteNashBellmanPathValue period block period =
      terminal :=
    quittingAnchoredPathValue_at_cutoff reward terminal period block hblock.1
  have hzero : quittingFiniteNashBellmanPathValue period block 0 = terminal :=
    quittingCyclicBlockValue_at_zero reward terminal period block hblock
  rw [zero_add, hcutoff, hzero] at hstep
  exact hstep

/-- **Contraction around a cyclic continuation block, for either sign.**
Every iterate of the cyclic composite started anywhere on the line is within
`P_who ^ N` of the block's own value.  No sign hypothesis is used. -/
theorem abs_iterate_quittingCompanionComposite_cyclicBlock_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    (who : ι) (start : ℝ) (N : ℕ) :
    |(quittingCompanionComposite reward
          (quittingFiniteNashBellmanPathRoots period block) who 0
          period)^[N] start - terminal who| ≤
      quittingOpponentSurvivalWeight
          (quittingFiniteNashBellmanPathRoots period block) who 0 period ^ N *
        |start - terminal who| :=
  abs_iterate_quittingCompanionComposite_sub_le reward _ who period
    (quittingCompanionComposite_cyclicBlock_fixed reward terminal period block
      hblock who)
    start N

/-- **Headline, arbitrary period.**  If the deleted survival product of a
cyclic continuation block at `who` is strictly below one, the cyclic
companion orbit from *any* real starting point converges to the block's own
value at `who`. -/
theorem tendsto_iterate_quittingCompanionComposite_cyclicBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    (who : ι)
    (hsurvival : quittingOpponentSurvivalWeight
      (quittingFiniteNashBellmanPathRoots period block) who 0 period < 1)
    (start : ℝ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward
          (quittingFiniteNashBellmanPathRoots period block) who 0
          period)^[N] start)
      Filter.atTop (nhds (terminal who)) :=
  tendsto_iterate_quittingCompanionComposite reward _ who period
    (quittingCompanionComposite_cyclicBlock_fixed reward terminal period block
      hblock who)
    hsurvival start

/-! ## The anchored mismatch -/

omit [Fintype ι] [DecidableEq ι] in
/-- The **solo-quit anchor** `Λ_who = max {0, r_who({who})}` from which the
mismatch is measured: against permanently silent opponents the deviating
coordinate's achievable payoffs are exactly `{r_who({who}), 0}`.  This is
literally `quittingPositiveSingletonDebtCap`. -/
theorem quittingSoloQuitAnchor_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingPositiveSingletonDebtCap reward who =
      max 0 (reward (quittingSingletonTerminal who) who) := rfl

/-- **The mismatch anchor converges to the cycle's own value.**  Starting the
cyclic companion iteration at the solo-quit anchor -- which may sit on either
side of the block's value -- the orbit converges to the block's value. -/
theorem tendsto_iterate_soloQuitAnchor_cyclicBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    (who : ι)
    (hsurvival : quittingOpponentSurvivalWeight
      (quittingFiniteNashBellmanPathRoots period block) who 0 period < 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward
          (quittingFiniteNashBellmanPathRoots period block) who 0
          period)^[N] (quittingPositiveSingletonDebtCap reward who))
      Filter.atTop (nhds (terminal who)) :=
  tendsto_iterate_quittingCompanionComposite_cyclicBlock reward terminal
    period block hblock who hsurvival _

/-- **The mismatch is zero.**  Any limit of the anchored companion orbit
equals the block's own value, so the mismatch `anchorLimit - terminal who`
vanishes whenever the deleted survival product is strictly below one.

No hypothesis on the sign of `quittingPositiveSingletonDebtCap reward who -
terminal who` appears anywhere in the hypothesis list or in the proof; this
is exactly what the transport-law route could not deliver.

`HEADLINE` — the contraction half of the mismatch characterization. Supplies
the admissibility hypothesis consumed by the conditional reduction. The
remaining half, where the deleted survival product equals one, is not
formalized. -/
theorem quittingCyclicContinuationBlock_mismatch_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    (who : ι)
    (hsurvival : quittingOpponentSurvivalWeight
      (quittingFiniteNashBellmanPathRoots period block) who 0 period < 1)
    (anchorLimit : ℝ)
    (hanchor : Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward
          (quittingFiniteNashBellmanPathRoots period block) who 0
          period)^[N] (quittingPositiveSingletonDebtCap reward who))
      Filter.atTop (nhds anchorLimit)) :
    anchorLimit - terminal who = 0 := by
  have hunique := tendsto_nhds_unique hanchor
    (tendsto_iterate_soloQuitAnchor_cyclicBlock reward terminal period block
      hblock who hsurvival)
  rw [hunique, sub_self]

/-! ## Regression: the transport-law route really is unavailable

The adversarial audit's witness, formalized.  Two coordinates, indexed by
`Bool` with `false` playing the role of coordinate `1`.  The row is the
solo-quitter row of `QuittingSoloQuitterEquilibrium.lean` at owner `true` and
rate `1/2`, so it is an absorbing exact complementary row, and it is a
length-one cyclic continuation block by
`quittingRowBlock_isQuittingCyclicContinuationBlock`.

At the non-owner coordinate `false` the terminal gap is
`Λ_false - z_false = 0 - 1 = -1 < 0` (`terminalGap_eq_neg_one`), so the
hypothesis `0 ≤ terminalDebt` of
`quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps` fails on
this absorbing complementary cycle.  Its geometric closed form would predict
`0` here, whereas the true anchored deviation is `-(1/2) ^ N` at horizon `N`
(`iterate_sub_value_eq`), never zero.  The contraction route is unaffected:
`P_false = 1/2 < 1`, so the orbit converges to `z_false` and the mismatch is
zero in the limit (`tendsto_iterate_soloQuitAnchor`). -/

namespace QuittingCycleMismatchAudit

/-- The audit weight.  Writing `1` for `false` and `2` for `true`:
`r_1({1}) = 0`, `r_1({2}) = 1`, `r_1({1,2}) = 0`, `r_2({2}) = 1/2`, and every
remaining entry is `0`.  Equivalently: every coalition containing `false`
pays nothing, and the coalition `{true}` pays `(1, 1/2)`. -/
def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun S who ↦ if false ∈ S.1 then 0 else if who then 1 / 2 else 1

theorem hazardRate_pos : (0 : ℝ) < 1 / 2 := by norm_num

theorem hazardRate_le_one : (1 : ℝ) / 2 ≤ 1 := by norm_num

/-- The owner `true` quits at rate `1/2`; the coordinate `false` continues
surely. -/
def hazard : PMF Bool :=
  quittingHazardCoin (1 / 2) hazardRate_pos.le hazardRate_le_one

/-- The audit row. -/
def root : Bool → PMF Bool := quittingSoloStationaryRoot true hazard

/-- The audit value `z = (1, 1/2)`, indexed `(false, true)`. -/
def value : Payoff Bool := quittingSoloReward reward true

@[simp] theorem hazard_true : (hazard true).toReal = 1 / 2 :=
  quittingHazardCoin_true_toReal _ _ _

@[simp] theorem hazard_false : (hazard false).toReal = 1 / 2 := by
  rw [hazard, quittingHazardCoin_false_toReal]
  norm_num

@[simp] theorem value_false : value false = 1 := by
  simp [value, quittingSoloReward, reward]

@[simp] theorem value_true : value true = 1 / 2 := by
  simp [value, quittingSoloReward, reward]

theorem ne_owner : (false : Bool) ≠ true := by decide

/-- The row reproduces its own value, at every rate. -/
theorem value_eq_successor :
    value = quittingRootSuccessorPayoff reward value root :=
  (quittingRootSuccessorPayoff_soloStationaryRoot_self reward true hazard).symm

/-- The row is exactly (`ε = 0`) endpoint Nash against its own value: the
owner is indifferent and the other coordinate strictly prefers to wait
(`0 ≤ 1`). -/
theorem isEndpointNash : IsεQuittingRootEndpointNash reward value 0 root := by
  refine isεQuittingRootEndpointNash_soloStationaryRoot reward true hazard ?_
  intro other hother
  cases other with
  | false =>
      rw [hazard_true, hazard_false]
      norm_num [quittingSoloReward, quittingSingletonCollisionReward, reward]
  | true => exact absurd rfl hother

/-- The row absorbs at rate `1/2`. -/
theorem absorptionMass_pos : 0 < quittingRootAbsorptionMass root := by
  rw [root, quittingRootAbsorptionMass_soloStationaryRoot, hazard_true]
  norm_num

/-- Every coordinate of the value is bounded by the canonical reward
bound. -/
theorem abs_value_le : ∀ who, |value who| ≤ quittingRewardBound reward :=
  fun who ↦
    abs_reward_le_quittingRewardBound reward (quittingSingletonTerminal true) who

/-- **The audit row is a cyclic continuation block of length one.** -/
theorem isCyclicContinuationBlock :
    IsQuittingCyclicContinuationBlock reward value 1
      (quittingRowBlock value root) :=
  quittingRowBlock_isQuittingCyclicContinuationBlock reward value root
    abs_value_le value_eq_successor isEndpointNash absorptionMass_pos

/-! ### The negative terminal gap -/

/-- The solo-quit anchor at `false` is `max {0, r_false({false})} = 0`. -/
@[simp] theorem soloQuitCap_false :
    quittingPositiveSingletonDebtCap reward false = 0 := by
  simp [quittingPositiveSingletonDebtCap, quittingSingletonTerminal, reward]

/-- **The transport law's nonnegativity hypothesis fails here.**  The
terminal gap at `false` on this absorbing exact complementary cycle is
`-1 < 0`. -/
theorem terminalGap_eq_neg_one :
    quittingPositiveSingletonDebtCap reward false - value false = -1 := by
  rw [soloQuitCap_false, value_false]
  norm_num

/-! ### The companion map at the non-owner coordinate -/

@[simp] theorem deletedContinueMass_false :
    quittingRootDeletedContinueMass root false = 1 / 2 := by
  rw [quittingRootDeletedContinueMass]
  simp only [root]
  rw [update_quittingSoloStationaryRoot_other ne_owner,
    quittingStationaryContinueMass_solo, hazard_false]

@[simp] theorem deletedQuitValue_false :
    quittingRootDeletedQuitValue reward root false = 0 := by
  rw [← quittingRootQuitPayoff_eq_deletedQuitValue reward (0 : Payoff Bool)]
  simp only [root]
  rw [quittingRootQuitPayoff_soloStationaryRoot_other reward ne_owner,
    hazard_true, hazard_false]
  norm_num [quittingSoloReward, quittingSingletonCollisionReward, reward]

@[simp] theorem deletedContinueReward_false :
    quittingRootDeletedContinueReward reward root false = 1 / 2 := by
  have hdeleted := quittingRootContinuePayoff_eq_deleted reward
    (0 : Payoff Bool) root false
  have hsolo : quittingRootContinuePayoff reward (0 : Payoff Bool) root false =
      (hazard true).toReal * quittingSoloReward reward true false +
        (hazard false).toReal * (0 : Payoff Bool) false :=
    quittingRootContinuePayoff_soloStationaryRoot_other reward ne_owner hazard
      (0 : Payoff Bool)
  have hz : quittingSoloReward reward true false = 1 := value_false
  rw [hsolo, hz, hazard_true, hazard_false] at hdeleted
  simp only [Pi.zero_apply, mul_zero, add_zero] at hdeleted
  linarith [hdeleted]

/-- The audit companion map at `false` is `w ↦ max {0, 1/2 + w/2}`. -/
theorem companionMap_false (continuation : ℝ) :
    quittingRootCompanionMap reward root false continuation =
      max 0 (1 / 2 + 1 / 2 * continuation) := by
  rw [quittingRootCompanionMap, deletedQuitValue_false,
    deletedContinueReward_false, deletedContinueMass_false]

/-- **The exact orbit from the solo-quit anchor.**  `T^[N](0) = 1 - 2^{-N}`. -/
theorem iterate_companionMap_eq (N : ℕ) :
    (quittingRootCompanionMap reward root false)^[N] 0 =
      1 - (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply', ih, companionMap_false]
      have hpow : ((1 : ℝ) / 2) ^ N ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      rw [max_eq_right (by linarith)]
      ring

/-- **The anchored deviation is strictly negative at every horizon.**  It is
`-(1/2) ^ N`, whereas the geometric closed form of the transport law -- whose
hypothesis `0 ≤ terminalDebt` fails here by `terminalGap_eq_neg_one` --
predicts `0`. -/
theorem iterate_sub_value_eq (N : ℕ) :
    (quittingRootCompanionMap reward root false)^[N]
        (quittingPositiveSingletonDebtCap reward false) - value false =
      -(1 / 2 : ℝ) ^ N := by
  rw [soloQuitCap_false, iterate_companionMap_eq, value_false]
  ring

theorem iterate_sub_value_ne_zero (N : ℕ) :
    (quittingRootCompanionMap reward root false)^[N]
        (quittingPositiveSingletonDebtCap reward false) - value false ≠ 0 := by
  rw [iterate_sub_value_eq]
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ N := by positivity
  exact ne_of_lt (by linarith)

/-- **The contraction route is unaffected.**  `P_false = 1/2 < 1`, so the
anchored orbit converges to the cycle's own value even though it approaches
it strictly from below. -/
theorem tendsto_iterate_soloQuitAnchor :
    Filter.Tendsto
      (fun N : ℕ =>
        (quittingRootCompanionMap reward root false)^[N]
          (quittingPositiveSingletonDebtCap reward false))
      Filter.atTop (nhds (value false)) :=
  tendsto_iterate_quittingRootCompanionMap reward value root value_eq_successor
    isEndpointNash false (by rw [deletedContinueMass_false]; norm_num) _

end QuittingCycleMismatchAudit

end GameTheory
