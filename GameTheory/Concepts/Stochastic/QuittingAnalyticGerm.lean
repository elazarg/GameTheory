/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticBellmanExistence
import GameTheory.Concepts.Stochastic.QuittingStationaryGain
import Math.AnalyticOrderComparison

/-!
# Analytic Bellman germs of quitting games

This file connects two previously disjoint layers of the repository: the
quitting-game layer (`QuittingGame.lean` and its stationary root algebra) and
the analytic Bellman-germ layer (`BellmanGerm.lean`,
`AnalyticBellmanExistence.lean`).  Before this file no module imported both.

`quittingGame reward` is a finite stochastic game with finite nonempty
decidable action sets, and those are the *entire* hypotheses of
`GameTheory.StochasticGame.analyticBellmanGermExistence`.  So every quitting
weight admits a real-analytic vanishing-discount branch of discounted
stationary Bellman equilibria.  The `discount := 0` field of `quittingGame` is
irrelevant here: it plays no role anywhere in this development, and
`IsDiscountedStationaryBellmanEq` carries the discount factor as an explicit
argument.

## The dictionary

Along a germ `g`, write `λ = t ^ g.ramification` for the discount complement
(this is exact, by `AnalyticBellmanGerm.discountCoordinate`), `β = 1 - λ`,
`W = quittingGermValue g t` for the active-state value vector and
`y = quittingGermRoot g ht` for the decoded stationary root action.  Then, for
every `t` in the germ's punctured interval:

* absorbed states are pinned: `g.assignment t (val (some S) i) = reward S i`;
* the active state satisfies the discounted root recursion
  `W i = β * quittingRootSuccessorPayoff reward W y i`, equivalently
  `W i * (1 - β * c(y)) = β * R_i(y)` with `c` the all-continue mass and `R`
  the one-stage absorbing contribution;
* the two pure best responses at the active state are
  `β * quittingRootQuitPayoff reward W y i ≤ W i` and
  `β * quittingRootContinuePayoff reward W y i ≤ W i`, and together with the
  recursion they are **exactly** `IsεQuittingRootEndpointNash reward W 0 y`,
  the quitting layer's own zero-regret root complementarity, whose gap
  `quittingRootEndpointDifference reward W y i` equals
  `Σ_i(y) - (A_i(y) + c_{-i}(y) * W i)` in the deleted quit value / deleted
  continue reward / deleted survival mass of the quitting layer.

## Rates

`quittingGermQuitRate g i` is the germ's `mix none i true` coordinate, i.e.
player `i`'s quit probability; it is `AnalyticAt ℝ · 0` and nonnegative on a
right neighbourhood of `0`.  That is exactly the input of
`Math.AnalyticOrderComparison`, so the normalized quit direction
`y_i / ∑_j y_j` *converges* (not merely subsequentially), and comparing the
discount complement `t ^ q` against the family's leading order is a comparison
of two natural numbers.

The one-stage absorption probability along the germ is
`quittingGermAbsorption g t = 1 - ∏_j (1 - y_j t)`.  It is analytic at `0` and
squeezed between the total quit mass and its `|ι|`-th part, so the comparison
against `t ^ q` transfers verbatim from the quit mass to absorption
(`tendsto_pow_div_quittingGermAbsorption_nhds_zero` and
`..._atTop`).  Only the *matching* case `q = m` is not transferred: there the
squeeze bounds the limit between `1/(|ι| · ∑ a)` and `1/∑ a` rather than
pinning it.

## Scope and gaps

* The order package needs one hypothesis that is **not** automatic: some player
  must quit with positive probability arbitrarily close to `t = 0`.  A germ
  along which everybody continues forever has the identically-zero quit family
  and no normalized direction.  This is `hne` in
  `exists_quittingGermQuitRate_leadingOrder_normalization`.
* `AnalyticBellmanGerm` retains only `IsPolynomialBellmanSolution`, discarding
  the sign pattern `τ` of the sign cell it came from.  Consequently nothing
  here freezes *which* best-response inequalities are slack along the germ; the
  complementarity below is re-derived pointwise at each `t`.  Freezing the
  pattern requires going through
  `exists_analyticBellmanGerm_of_positiveCoordinateArc` directly.
* `analyticBellmanGermExistence` prescribes the endpoint of the germ it
  produces; it does not regularize a *given* sequence of discounted
  complementary rows.  Putting a prescribed point in the closure of a sign cell
  is extra work not done here.

## Main results

* `nonempty_analyticBellmanGerm_quittingGame` — germ existence for quitting
  games
* `quittingGerm_assignment_val_some` — absorbed states are pinned to the weight
* `quittingGermValue_eq_smul_rootSuccessorPayoff`,
  `quittingGermValue_mul_one_sub` — the active-state recursion
* `isεQuittingRootEndpointNash_zero_iff_of_rootRecursion` — the two pure
  best-response inequalities are *equivalent* to the quitting layer's
  complementarity, given the recursion at a positive discount factor
* `isεQuittingRootEndpointNash_quittingGermRoot` — the germ's root action is an
  exact endpoint Nash of the quitting root game at the germ's own value
* `quittingGerm_dictionary` — the whole dictionary in one statement
* `analyticAt_quittingGermQuitRate`, `quittingGerm_discountComplement` — the
  rates are analytic and the discount complement is exactly `t ^ q`
* `quittingGermAbsorption`, `quittingGermAbsorption_bounds`,
  `analyticAt_quittingGermAbsorption` — the absorption curve, its `|ι|`-fold
  two-sided comparison with the total quit mass, and its analyticity
* `exists_quittingGermQuitRate_leadingOrder_normalization` — the leading-order
  normalization of the quit family
* `tendsto_pow_div_quittingGermAbsorption_nhds_zero`,
  `tendsto_pow_div_quittingGermAbsorption_atTop` — the transfer of the
  comparison from the quit mass to absorption
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Set Topology
open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Finiteness instances for quitting games -/

instance instFintypeStateQuittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Fintype (quittingGame reward).State :=
  inferInstanceAs (Fintype (Option {S : Finset ι // S.Nonempty}))

instance instFintypeActQuittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (i : ι) :
    Fintype ((quittingGame reward).Act i) :=
  inferInstanceAs (Fintype Bool)

instance instDecidableEqActQuittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (i : ι) :
    DecidableEq ((quittingGame reward).Act i) :=
  inferInstanceAs (DecidableEq Bool)

instance instNonemptyActQuittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (i : ι) :
    Nonempty ((quittingGame reward).Act i) :=
  inferInstanceAs (Nonempty Bool)

/-! ## Germ existence -/

/-- **Every quitting weight has a real-analytic vanishing-discount branch.**
A quitting game is a finite stochastic game with finite nonempty decidable
action sets, which is the whole hypothesis list of
`analyticBellmanGermExistence`. -/
theorem nonempty_analyticBellmanGerm_quittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Nonempty (quittingGame reward).AnalyticBellmanGerm :=
  AnalyticBellmanGermExistence.forGame analyticBellmanGermExistence
    (quittingGame reward)

/-! ## One-stage identities for quitting games -/

section OneStage

variable (reward : {S : Finset ι // S.Nonempty} → Payoff ι)

omit [DecidableEq ι] in
/-- At an absorbed state the auxiliary discounted payoff is the one-step
mixture of the repeated terminal reward and the continuation value; no action
influences it. -/
theorem discountedAuxEU_quittingGame_some (β : ℝ)
    (V : (quittingGame reward).State → Payoff ι)
    (S : {S : Finset ι // S.Nonempty}) (m : ι → PMF Bool) (who : ι) :
    (quittingGame reward).discountedAuxEU β V (some S) m who =
      (1 - β) * reward S who + β * V (some S) who := by
  have key : ∀ a : ι → Bool,
      (quittingGame reward).discountedAuxPayoff β V (some S) a who =
        (1 - β) * reward S who + β * V (some S) who := by
    intro a
    have htrans : (quittingGame reward).transition (some S) a =
        PMF.pure (show (quittingGame reward).State from some S) := rfl
    have hstage : (quittingGame reward).stagePayoff (some S) a who =
        reward S who := rfl
    rw [StochasticGame.discountedAuxPayoff, htrans, hstage, expect_pure]
  calc (quittingGame reward).discountedAuxEU β V (some S) m who
      = expect (pmfPi m)
          (fun a => (quittingGame reward).discountedAuxPayoff β V (some S) a who) := rfl
    _ = expect (pmfPi m) (fun _ => (1 - β) * reward S who + β * V (some S) who) := by
        simp_rw [key]
    _ = (1 - β) * reward S who + β * V (some S) who := expect_const _ _

omit [DecidableEq ι] in
/-- The one-stage transition expectation at the active state is exactly the
quitting layer's one-stage root payoff, read against the value vector. -/
theorem expect_transition_quittingGame_none
    (V : (quittingGame reward).State → Payoff ι) (action : ι → Bool) (who : ι) :
    expect ((quittingGame reward).transition none action) (fun s' => V s' who) =
      quittingRootPayoff (fun S => V (some S)) (fun j => V none j) action who := by
  rw [quittingGame_transition_none]
  unfold quittingRootPayoff quittingQuitters
  by_cases h : ({j | action j = true} : Finset ι).Nonempty
  · rw [dif_pos h, dif_pos h, expect_pure]
  · rw [dif_neg h, dif_neg h, expect_pure]

omit [DecidableEq ι] in
/-- **The active state carries no stage payoff.**  Hence the auxiliary
discounted payoff at the active state is the discount factor times the
quitting layer's one-stage root expectation. -/
theorem discountedAuxEU_quittingGame_none (β : ℝ)
    (V : (quittingGame reward).State → Payoff ι) (m : ι → PMF Bool) (who : ι) :
    (quittingGame reward).discountedAuxEU β V none m who =
      β * quittingRootExpectedPayoff (fun S => V (some S)) (fun j => V none j) m who := by
  have key : ∀ a : ι → Bool,
      (quittingGame reward).discountedAuxPayoff β V none a who =
        β * quittingRootPayoff (fun S => V (some S)) (fun j => V none j) a who := by
    intro a
    have hstage : (quittingGame reward).stagePayoff none a who = 0 := rfl
    rw [StochasticGame.discountedAuxPayoff, hstage,
      expect_transition_quittingGame_none reward V a who]
    ring
  calc (quittingGame reward).discountedAuxEU β V none m who
      = expect (pmfPi m)
          (fun a => (quittingGame reward).discountedAuxPayoff β V none a who) := rfl
    _ = expect (pmfPi m)
          (fun a => β * quittingRootPayoff (fun S => V (some S))
            (fun j => V none j) a who) := by simp_rw [key]
    _ = β * expect (pmfPi m)
          (fun a => quittingRootPayoff (fun S => V (some S))
            (fun j => V none j) a who) := expect_const_mul _ _ _
    _ = β * quittingRootExpectedPayoff (fun S => V (some S))
          (fun j => V none j) m who := rfl

/-- **The survey's claimed equivalence, isolated from any germ.**  Suppose a
value vector `W` satisfies the discounted root recursion at a strictly
positive discount factor `β`.  Then the two pure best-response inequalities at
the active state are *equivalent* to the quitting layer's zero-regret endpoint
complementarity `IsεQuittingRootEndpointNash reward W 0 root`, i.e. to
"`y_i > 0` forces a nonnegative gap and `y_i < 1` forces a nonpositive gap".

Both directions come from the same two algebraic identities, obtained by
substituting the recursion into the mixture decomposition
`quittingRootSuccessorPayoff_eq_endpointMix`. -/
theorem isεQuittingRootEndpointNash_zero_iff_of_rootRecursion (β : ℝ)
    (hβ : 0 < β) (W : Payoff ι) (root : ι → PMF Bool)
    (hrec : ∀ who, W who = β * quittingRootSuccessorPayoff reward W root who) :
    IsεQuittingRootEndpointNash reward W 0 root ↔
      ∀ who, β * quittingRootQuitPayoff reward W root who ≤ W who ∧
        β * quittingRootContinuePayoff reward W root who ≤ W who := by
  have main : ∀ who : ι,
      (β * (((root who) false).toReal *
          quittingRootEndpointDifference reward W root who) =
        β * quittingRootQuitPayoff reward W root who - W who) ∧
      (β * (((root who) true).toReal *
          quittingRootEndpointDifference reward W root who) =
        W who - β * quittingRootContinuePayoff reward W root who) := by
    intro who
    have hmix := quittingRootSuccessorPayoff_eq_endpointMix reward W root who
    have hval := hrec who
    rw [hmix] at hval
    have hprob := quittingRoot_continueProbability_add_quitProbability root who
    have hdiff : quittingRootEndpointDifference reward W root who =
        quittingRootQuitPayoff reward W root who -
          quittingRootContinuePayoff reward W root who := rfl
    rw [hdiff]
    constructor
    · rw [hval]
      linear_combination (β * quittingRootQuitPayoff reward W root who) * hprob
    · rw [hval]
      linear_combination (-(β * quittingRootContinuePayoff reward W root who)) * hprob
  constructor
  · intro hnash who
    obtain ⟨hquitId, hcontId⟩ := main who
    obtain ⟨hquitSign, hcontSign⟩ := hnash who
    have h1 : β * (((root who) false).toReal *
        quittingRootEndpointDifference reward W root who) ≤ 0 := by
      simpa using mul_le_mul_of_nonneg_left hquitSign hβ.le
    have h2 : 0 ≤ β * (((root who) true).toReal *
        quittingRootEndpointDifference reward W root who) := by
      refine mul_nonneg hβ.le ?_
      linarith
    rw [hquitId] at h1
    rw [hcontId] at h2
    exact ⟨by linarith, by linarith⟩
  · intro hbest who
    obtain ⟨hquitId, hcontId⟩ := main who
    obtain ⟨hquit, hcont⟩ := hbest who
    have h1 : β * (((root who) false).toReal *
        quittingRootEndpointDifference reward W root who) ≤ 0 := by
      rw [hquitId]; linarith
    have h2 : 0 ≤ β * (((root who) true).toReal *
        quittingRootEndpointDifference reward W root who) := by
      rw [hcontId]; linarith
    refine ⟨?_, ?_⟩
    · by_contra hc
      exact absurd h1 (not_le.mpr (mul_pos hβ (not_le.mp hc)))
    · have hpos : 0 ≤ ((root who) true).toReal *
          quittingRootEndpointDifference reward W root who := by
        by_contra hc
        exact absurd h2 (not_le.mpr (mul_neg_of_pos_of_neg hβ (not_le.mp hc)))
      linarith

end OneStage

/-! ## Absorption versus total quit mass

Two elementary comparisons between the one-stage absorption probability
`1 - ∏_j (1 - y_j)` and the total quit mass `∑_j y_j`: a union bound in one
direction and a crude `|ι|`-fold bound in the other.  Together they say the
two quantities are within a fixed factor of each other, which is what lets a
leading-order statement about the quit family be read as a statement about
vanishing absorption. -/

omit [Fintype ι] [DecidableEq ι] in
/-- **Union bound.**  Independent absorption is at most the total quit mass. -/
theorem one_sub_prod_one_sub_le_sum (w : ι → ℝ)
    (h0 : ∀ j, 0 ≤ w j) (h1 : ∀ j, w j ≤ 1) (s : Finset ι) :
    1 - ∏ j ∈ s, (1 - w j) ≤ ∑ j ∈ s, w j := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  have hprod : ∏ j ∈ s, (1 - w j) ≤ 1 :=
    Finset.prod_le_one (fun j _ => by linarith [h1 j]) (fun j _ => by linarith [h0 j])
  have hexp : 1 - (1 - w a) * ∏ j ∈ s, (1 - w j) =
      (1 - ∏ j ∈ s, (1 - w j)) + w a * ∏ j ∈ s, (1 - w j) := by ring
  have hle : w a * ∏ j ∈ s, (1 - w j) ≤ w a := by
    calc w a * ∏ j ∈ s, (1 - w j) ≤ w a * 1 :=
          mul_le_mul_of_nonneg_left hprod (h0 a)
      _ = w a := mul_one _
  rw [hexp]
  linarith

omit [DecidableEq ι] in
/-- Every individual quit probability is at most the absorption probability. -/
theorem le_one_sub_prod_one_sub (w : ι → ℝ) (h0 : ∀ j, 0 ≤ w j)
    (h1 : ∀ j, w j ≤ 1) (k : ι) :
    w k ≤ 1 - ∏ j, (1 - w j) := by
  classical
  have hsplit : (1 - w k) * ∏ j ∈ Finset.univ.erase k, (1 - w j) =
      ∏ j, (1 - w j) :=
    Finset.mul_prod_erase Finset.univ (fun j => 1 - w j) (Finset.mem_univ k)
  have hrest : ∏ j ∈ Finset.univ.erase k, (1 - w j) ≤ 1 :=
    Finset.prod_le_one (fun j _ => by linarith [h1 j]) (fun j _ => by linarith [h0 j])
  have hnonneg : (0 : ℝ) ≤ 1 - w k := by linarith [h1 k]
  have hle : ∏ j, (1 - w j) ≤ 1 - w k := by
    rw [← hsplit]
    calc (1 - w k) * ∏ j ∈ Finset.univ.erase k, (1 - w j) ≤ (1 - w k) * 1 :=
          mul_le_mul_of_nonneg_left hrest hnonneg
      _ = 1 - w k := mul_one _
  linarith

omit [DecidableEq ι] in
/-- The total quit mass is at most `|ι|` times the absorption probability. -/
theorem sum_le_card_mul_one_sub_prod_one_sub (w : ι → ℝ) (h0 : ∀ j, 0 ≤ w j)
    (h1 : ∀ j, w j ≤ 1) :
    ∑ j, w j ≤ (Fintype.card ι : ℝ) * (1 - ∏ j, (1 - w j)) := by
  calc ∑ j, w j ≤ ∑ _j : ι, (1 - ∏ k, (1 - w k)) :=
        Finset.sum_le_sum fun j _ => le_one_sub_prod_one_sub w h0 h1 j
    _ = (Fintype.card ι : ℝ) * (1 - ∏ k, (1 - w k)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

omit [DecidableEq ι] in
/-- The all-continue mass of a product root action is the product of the
individual continue masses. -/
theorem quittingStationaryContinueMass_eq_prod (root : ι → PMF Bool) :
    quittingStationaryContinueMass root = ∏ j, ((root j) false).toReal := by
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  rfl

/-! ## The germ dictionary -/

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The active-state value vector carried by an analytic Bellman germ of a
quitting game. -/
def quittingGermValue (g : (quittingGame reward).AnalyticBellmanGerm) (t : ℝ) :
    Payoff ι :=
  fun i => g.assignment t (BellmanVar.val none i)

/-- The stationary root action decoded from an analytic Bellman germ of a
quitting game at a positive parameter. -/
def quittingGermRoot (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) : ι → PMF Bool :=
  (quittingGame reward).bellmanDecodeProfile (g.solution t ht) none

/-- **The quit-rate curve of a germ**: player `i`'s probability of quitting at
the active state, read off the germ's `mix none i true` coordinate. -/
def quittingGermQuitRate (g : (quittingGame reward).AnalyticBellmanGerm)
    (i : ι) (t : ℝ) : ℝ :=
  g.assignment t (BellmanVar.mix none i true)

/-- The decoded root action's masses *are* the germ's mixing coordinates. -/
theorem quittingGermRoot_apply_toReal
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (i : ι) (b : Bool) :
    ((quittingGermRoot g ht i) b).toReal =
      g.assignment t (BellmanVar.mix none i b) :=
  (quittingGame reward).bellmanDecodeProfile_apply_toReal (g.solution t ht)
    none i b

/-- The decoded root action's quit mass *is* the germ's `mix none i true`
coordinate. -/
theorem quittingGermRoot_apply_true_toReal
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (i : ι) :
    ((quittingGermRoot g ht i) true).toReal = quittingGermQuitRate g i t :=
  quittingGermRoot_apply_toReal g ht i true

/-- The decoded root action's continue mass is one minus the germ's mixing
coordinate. -/
theorem quittingGermRoot_apply_false_toReal
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (i : ι) :
    ((quittingGermRoot g ht i) false).toReal = 1 - quittingGermQuitRate g i t := by
  have h := quittingRoot_continueProbability_add_quitProbability
    (quittingGermRoot g ht) i
  rw [quittingGermRoot_apply_true_toReal] at h
  linarith

/-- The discount complement along a germ is exactly `t ^ q`. -/
theorem quittingGerm_discountComplement
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) :
    1 - (quittingGame reward).bellmanDecodeDiscount (g.assignment t) =
      t ^ g.ramification := by
  rw [StochasticGame.bellmanDecodeDiscount, g.discountCoordinate t ht]
  ring

/-- The Bellman datum carried by the germ at a positive parameter, written
with the discount factor `1 - t ^ q` and the decoded root action. -/
theorem quittingGerm_isDiscountedStationaryBellmanEq
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) :
    (quittingGame reward).IsDiscountedStationaryBellmanEq
      (1 - t ^ g.ramification)
      ((quittingGame reward).bellmanDecodeProfile (g.solution t ht))
      ((quittingGame reward).bellmanDecodeValue (g.assignment t)) :=
  g.isDiscountedStationaryBellmanEq ht

/-- **Absorbed states are pinned.**  Along any analytic Bellman germ of a
quitting game, the value at an absorbed state is the terminal reward of that
quitter set — no residual discount dependence. -/
theorem quittingGerm_assignment_val_some
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (S : {S : Finset ι // S.Nonempty}) (i : ι) :
    g.assignment t (BellmanVar.val (some S) i) = reward S i := by
  have hEq := quittingGerm_isDiscountedStationaryBellmanEq g ht
  have hval := hEq.2 (some S) i
  rw [discountedAuxEU_quittingGame_some] at hval
  have hpow : t ^ g.ramification ≠ 0 := ne_of_gt (pow_pos ht.1 _)
  have hmul : t ^ g.ramification *
      (reward S i - g.assignment t (BellmanVar.val (some S) i)) = 0 := by
    have hval' : (1 - (1 - t ^ g.ramification)) * reward S i +
        (1 - t ^ g.ramification) * g.assignment t (BellmanVar.val (some S) i) =
        g.assignment t (BellmanVar.val (some S) i) := hval
    linear_combination hval'
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd h hpow
  · linarith

/-- Along the germ the decoded absorbed values *are* the quitting weight. -/
theorem quittingGerm_decodeValue_some_eq
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) :
    (fun S => (quittingGame reward).bellmanDecodeValue (g.assignment t) (some S)) =
      reward := by
  funext S i
  exact quittingGerm_assignment_val_some g ht S i

/-- **The active-state recursion.**  The germ's active value is the discount
factor times the quitting layer's one-stage root payoff at the germ's own
decoded root action and value. -/
theorem quittingGermValue_eq_smul_rootSuccessorPayoff
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (who : ι) :
    quittingGermValue g t who =
      (1 - t ^ g.ramification) *
        quittingRootSuccessorPayoff reward (quittingGermValue g t)
          (quittingGermRoot g ht) who := by
  have hEq := quittingGerm_isDiscountedStationaryBellmanEq g ht
  have hval := hEq.2 none who
  rw [discountedAuxEU_quittingGame_none, quittingGerm_decodeValue_some_eq g ht] at hval
  exact hval.symm

/-- The active-state recursion in absorbing-contribution form:
`W_i * (1 - β * c(y)) = β * R_i(y)`, with `c` the all-continue mass and `R`
the one-stage absorbing contribution.  This is the discounted analogue of the
stationary balance law of `QuittingStationaryPayoff.lean`. -/
theorem quittingGermValue_mul_one_sub
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (who : ι) :
    quittingGermValue g t who *
        (1 - (1 - t ^ g.ramification) *
          quittingStationaryContinueMass (quittingGermRoot g ht)) =
      (1 - t ^ g.ramification) *
        quittingRootAbsorbingContribution reward (quittingGermRoot g ht) who := by
  have hval := quittingGermValue_eq_smul_rootSuccessorPayoff g ht who
  rw [quittingRootSuccessorPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add] at hval
  linear_combination hval

/-- The pure-Quit best response at the active state. -/
theorem quittingGerm_bestResponse_quit
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (who : ι) :
    (1 - t ^ g.ramification) *
        quittingRootQuitPayoff reward (quittingGermValue g t)
          (quittingGermRoot g ht) who ≤
      quittingGermValue g t who := by
  have hEq := quittingGerm_isDiscountedStationaryBellmanEq g ht
  have hdev := hEq.1 none who (PMF.pure true)
  have hon := hEq.2 none who
  rw [hon] at hdev
  rw [discountedAuxEU_quittingGame_none, quittingGerm_decodeValue_some_eq g ht] at hdev
  exact hdev

/-- The pure-Continue best response at the active state. -/
theorem quittingGerm_bestResponse_continue
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (who : ι) :
    (1 - t ^ g.ramification) *
        quittingRootContinuePayoff reward (quittingGermValue g t)
          (quittingGermRoot g ht) who ≤
      quittingGermValue g t who := by
  have hEq := quittingGerm_isDiscountedStationaryBellmanEq g ht
  have hdev := hEq.1 none who (PMF.pure false)
  have hon := hEq.2 none who
  rw [hon] at hdev
  rw [discountedAuxEU_quittingGame_none, quittingGerm_decodeValue_some_eq g ht] at hdev
  exact hdev

/-- The germ's endpoint gap in the quitting layer's deleted coordinates:
`Σ_i(y) - (A_i(y) + c_{-i}(y) * W_i)`, the deleted quit value minus the
deleted continue reward and the deleted survival mass times the active
value. -/
theorem quittingGerm_endpointDifference_eq
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (who : ι) :
    quittingRootEndpointDifference reward (quittingGermValue g t)
        (quittingGermRoot g ht) who =
      quittingStationaryFixedOpponentsQuitValue reward (quittingGermRoot g ht) who -
        (quittingStationaryFixedOpponentsContinueReward reward
            (quittingGermRoot g ht) who +
          quittingStationaryFixedOpponentsContinueMass (quittingGermRoot g ht) who *
            quittingGermValue g t who) := by
  have hquit : quittingRootQuitPayoff reward (quittingGermValue g t)
      (quittingGermRoot g ht) who =
      quittingStationaryFixedOpponentsQuitValue reward (quittingGermRoot g ht) who :=
    quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
      (fun _ => quittingGermRoot g ht) who (quittingGermValue g t) 0
  have hcont : quittingRootContinuePayoff reward (quittingGermValue g t)
      (quittingGermRoot g ht) who =
      quittingStationaryFixedOpponentsContinueReward reward
          (quittingGermRoot g ht) who +
        quittingStationaryFixedOpponentsContinueMass (quittingGermRoot g ht) who *
          quittingGermValue g t who :=
    quittingRootContinuePayoff_eq_fixedOpponents reward
      (fun _ => quittingGermRoot g ht) who (quittingGermValue g t) 0
  rw [quittingRootEndpointDifference, hquit, hcont]

/-- The discount factor along the germ is strictly positive below `t = 1`. -/
theorem quittingGerm_discountFactor_pos
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (ht1 : t < 1) :
    0 < 1 - t ^ g.ramification := by
  have h : t ^ g.ramification < 1 := pow_lt_one₀ ht.1.le ht1 g.ramification_pos.ne'
  linarith

/-- **The dictionary capstone.**  For `0 < t < min (radius) 1`, the germ's
decoded root action is an *exact* zero-regret endpoint Nash point of the
quitting root game against the germ's own active value vector.  This is the
quitting layer's complementarity condition, obtained from the two polynomial
best-response inequalities plus the Bellman equality. -/
theorem isεQuittingRootEndpointNash_quittingGermRoot
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (ht1 : t < 1) :
    IsεQuittingRootEndpointNash reward (quittingGermValue g t) 0
      (quittingGermRoot g ht) :=
  (isεQuittingRootEndpointNash_zero_iff_of_rootRecursion reward
      (1 - t ^ g.ramification) (quittingGerm_discountFactor_pos g ht ht1)
      (quittingGermValue g t) (quittingGermRoot g ht)
      (quittingGermValue_eq_smul_rootSuccessorPayoff g ht)).mpr
    fun who => ⟨quittingGerm_bestResponse_quit g ht who,
      quittingGerm_bestResponse_continue g ht who⟩

/-- **The dictionary, in one statement.**  At every parameter `0 < t < 1`
inside the germ's radius:

* absorbed states are pinned to the quitting weight;
* the discount complement is exactly `t ^ q`;
* the `mix none i true` coordinate is player `i`'s quit probability;
* the active value obeys `W_i * (1 - β * c(y)) = β * R_i(y)`;
* the decoded root action is an exact zero-regret endpoint Nash point of the
  quitting root game at the germ's own active value. -/
theorem quittingGerm_dictionary
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (ht1 : t < 1) :
    (∀ S i, g.assignment t (BellmanVar.val (some S) i) = reward S i) ∧
      (1 - (quittingGame reward).bellmanDecodeDiscount (g.assignment t) =
        t ^ g.ramification) ∧
      (∀ i, ((quittingGermRoot g ht i) true).toReal =
        quittingGermQuitRate g i t) ∧
      (∀ who, quittingGermValue g t who *
          (1 - (1 - t ^ g.ramification) *
            quittingStationaryContinueMass (quittingGermRoot g ht)) =
        (1 - t ^ g.ramification) *
          quittingRootAbsorbingContribution reward (quittingGermRoot g ht) who) ∧
      IsεQuittingRootEndpointNash reward (quittingGermValue g t) 0
        (quittingGermRoot g ht) :=
  ⟨fun S i => quittingGerm_assignment_val_some g ht S i,
    quittingGerm_discountComplement g ht,
    fun i => quittingGermRoot_apply_true_toReal g ht i,
    fun who => quittingGermValue_mul_one_sub g ht who,
    isεQuittingRootEndpointNash_quittingGermRoot g ht ht1⟩

/-! ## Analyticity of the quit rates -/

/-- Every quit rate of a germ is analytic at `0`. -/
theorem analyticAt_quittingGermQuitRate
    (g : (quittingGame reward).AnalyticBellmanGerm) (i : ι) :
    AnalyticAt ℝ (quittingGermQuitRate g i) 0 :=
  g.analytic_coordinate (BellmanVar.mix none i true)

/-- The germ's punctured interval is a right neighbourhood of `0`. -/
theorem eventually_mem_Ioo_radius
    (g : (quittingGame reward).AnalyticBellmanGerm) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) g.radius := by
  have hlt : ∀ᶠ t in 𝓝 (0 : ℝ), t < g.radius := Iio_mem_nhds g.radius_pos
  filter_upwards [self_mem_nhdsWithin, hlt.filter_mono nhdsWithin_le_nhds] with t h0 h1
  exact ⟨h0, h1⟩

/-- Quit rates are nonnegative: they are probabilities, and the simplex
inequalities are part of `IsPolynomialBellmanSolution`. -/
theorem quittingGermQuitRate_nonneg
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (i : ι) :
    0 ≤ quittingGermQuitRate g i t := by
  have h := (g.solution t ht).2.1 none i true
  rwa [StochasticGame.simplexNonnegPoly, MvPolynomial.eval_X] at h

/-- Quit rates are at most `1`. -/
theorem quittingGermQuitRate_le_one
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (i : ι) :
    quittingGermQuitRate g i t ≤ 1 := by
  have h := (g.solution t ht).2.1 none i false
  rw [StochasticGame.simplexNonnegPoly, MvPolynomial.eval_X] at h
  have hfalse : g.assignment t (BellmanVar.mix none i false) =
      1 - quittingGermQuitRate g i t := by
    rw [← quittingGermRoot_apply_toReal g ht i false]
    exact quittingGermRoot_apply_false_toReal g ht i
  rw [hfalse] at h
  linarith

/-- Quit rates are nonnegative on a right neighbourhood of `0`. -/
theorem eventually_quittingGermQuitRate_nonneg
    (g : (quittingGame reward).AnalyticBellmanGerm) (i : ι) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ quittingGermQuitRate g i t := by
  filter_upwards [eventually_mem_Ioo_radius g] with t ht
  exact quittingGermQuitRate_nonneg g ht i

/-- Quit rates are at most `1` on a right neighbourhood of `0`. -/
theorem eventually_quittingGermQuitRate_le_one
    (g : (quittingGame reward).AnalyticBellmanGerm) (i : ι) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), quittingGermQuitRate g i t ≤ 1 := by
  filter_upwards [eventually_mem_Ioo_radius g] with t ht
  exact quittingGermQuitRate_le_one g ht i

/-! ## Absorption along the germ -/

/-- The germ's all-continue mass is the product of the individual continue
probabilities `1 - y_j`. -/
theorem quittingStationaryContinueMass_quittingGermRoot
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) :
    quittingStationaryContinueMass (quittingGermRoot g ht) =
      ∏ j, (1 - quittingGermQuitRate g j t) := by
  rw [quittingStationaryContinueMass_eq_prod]
  exact Finset.prod_congr rfl fun j _ => quittingGermRoot_apply_false_toReal g ht j

/-- The germ's one-stage absorption probability, in the quit rates. -/
theorem quittingRootAbsorptionMass_quittingGermRoot
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) :
    quittingRootAbsorptionMass (quittingGermRoot g ht) =
      1 - ∏ j, (1 - quittingGermQuitRate g j t) := by
  rw [quittingRootAbsorptionMass, quittingStationaryContinueMass_quittingGermRoot g ht]

/-- **Absorption and total quit mass are within a factor `|ι|`.**  This is the
bridge that turns a leading-order statement about the quit family into one
about vanishing absorption: the two curves have the same asymptotic scale. -/
theorem quittingRootAbsorptionMass_quittingGermRoot_bounds
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) :
    quittingRootAbsorptionMass (quittingGermRoot g ht) ≤
        ∑ j, quittingGermQuitRate g j t ∧
      ∑ j, quittingGermQuitRate g j t ≤
        (Fintype.card ι : ℝ) *
          quittingRootAbsorptionMass (quittingGermRoot g ht) := by
  have h0 : ∀ j, 0 ≤ quittingGermQuitRate g j t :=
    fun j => quittingGermQuitRate_nonneg g ht j
  have h1 : ∀ j, quittingGermQuitRate g j t ≤ 1 :=
    fun j => quittingGermQuitRate_le_one g ht j
  rw [quittingRootAbsorptionMass_quittingGermRoot g ht]
  exact ⟨one_sub_prod_one_sub_le_sum _ h0 h1 Finset.univ,
    sum_le_card_mul_one_sub_prod_one_sub _ h0 h1⟩

/-- **The absorption curve of a germ**, as a total function of the curve
parameter: `1 - ∏_j (1 - y_j t)`.  On the germ's punctured interval it is the
decoded root action's one-stage absorption probability
(`quittingGermAbsorption_eq`), but unlike the latter it does not mention the
membership proof, so it can be fed to the analytic machinery. -/
def quittingGermAbsorption (g : (quittingGame reward).AnalyticBellmanGerm)
    (t : ℝ) : ℝ :=
  1 - ∏ j, (1 - quittingGermQuitRate g j t)

theorem quittingGermAbsorption_eq
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) :
    quittingGermAbsorption g t =
      quittingRootAbsorptionMass (quittingGermRoot g ht) :=
  (quittingRootAbsorptionMass_quittingGermRoot g ht).symm

/-- The absorption curve is analytic at `0`. -/
theorem analyticAt_quittingGermAbsorption
    (g : (quittingGame reward).AnalyticBellmanGerm) :
    AnalyticAt ℝ (quittingGermAbsorption g) 0 :=
  analyticAt_const.sub
    (Finset.analyticAt_fun_prod Finset.univ
      fun j _ => analyticAt_const.sub (analyticAt_quittingGermQuitRate g j))

/-- The absorption curve is squeezed between the total quit mass and its
`|ι|`-th part. -/
theorem quittingGermAbsorption_bounds
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) :
    quittingGermAbsorption g t ≤ ∑ j, quittingGermQuitRate g j t ∧
      ∑ j, quittingGermQuitRate g j t ≤
        (Fintype.card ι : ℝ) * quittingGermAbsorption g t := by
  rw [quittingGermAbsorption_eq g ht]
  exact quittingRootAbsorptionMass_quittingGermRoot_bounds g ht

/-- Wherever the total quit mass is positive, so is the absorption. -/
theorem quittingGermAbsorption_pos
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius)
    (hsum : 0 < ∑ j, quittingGermQuitRate g j t) :
    0 < quittingGermAbsorption g t := by
  have hzero : ∑ _j : ι, (0 : ℝ) < ∑ j, quittingGermQuitRate g j t := by
    simpa using hsum
  obtain ⟨k, -, hk⟩ := Finset.exists_lt_of_sum_lt hzero
  exact lt_of_lt_of_le hk
    (le_one_sub_prod_one_sub _ (fun j => quittingGermQuitRate_nonneg g ht j)
      (fun j => quittingGermQuitRate_le_one g ht j) k)

/-! ## Feeding the order machinery -/

/-- The quit family of a germ admits a simultaneous leading-order
factorization as soon as some player does not quit with probability
identically zero near `t = 0`. -/
theorem nonempty_leadingOrderJet_quittingGermQuitRate
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hne : ∃ i, ¬∀ᶠ t in 𝓝[>] (0 : ℝ), quittingGermQuitRate g i t = 0) :
    Nonempty (Math.LeadingOrderJet (quittingGermQuitRate g)) :=
  Math.exists_leadingOrderJet (fun i => analyticAt_quittingGermQuitRate g i) hne

/-- The nondegeneracy hypothesis in the form "not everybody continues, near
`t = 0`". -/
theorem exists_not_eventually_quittingGermQuitRate_eq_zero_iff
    (g : (quittingGame reward).AnalyticBellmanGerm) :
    (∃ i, ¬∀ᶠ t in 𝓝[>] (0 : ℝ), quittingGermQuitRate g i t = 0) ↔
      ¬∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, quittingGermQuitRate g i t = 0 := by
  rw [Filter.eventually_all]
  exact (not_forall).symm

/-- **The leading-order normalization of a germ's quit family.**

Assume some player quits with positive probability arbitrarily close to
`t = 0`.  Then there is a least order `m` and a nonnegative leading vector `a`
with positive total such that

* the total quit mass `∑ j, y_j t` is positive to the right of `0`;
* every normalized quit share `y_i t / ∑ j, y_j t` **converges** to
  `a i / ∑ j, a j` — not merely along subsequences;
* the exact discount complement `t ^ g.ramification` is negligible, comparable,
  or dominant against the total quit mass according as the ramification `q` is
  larger than, equal to, or smaller than `m`.

The last item is the point: the comparison of the vanishing discount with the
vanishing absorption is a comparison of two natural numbers. -/
theorem exists_quittingGermQuitRate_leadingOrder_normalization
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hne : ∃ i, ¬∀ᶠ t in 𝓝[>] (0 : ℝ), quittingGermQuitRate g i t = 0) :
    ∃ (m : ℕ) (a : ι → ℝ),
      Math.familyAnalyticOrder (quittingGermQuitRate g) = m ∧
      (∀ i, 0 ≤ a i) ∧
      (0 < ∑ j, a j) ∧
      (∀ i, a i ≠ 0 ↔ i ∈ Math.leadingSet (quittingGermQuitRate g)) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ∑ j, quittingGermQuitRate g j t) ∧
      (∀ i, Tendsto
        (fun t => quittingGermQuitRate g i t / ∑ j, quittingGermQuitRate g j t)
        (𝓝[>] (0 : ℝ)) (𝓝 (a i / ∑ j, a j))) ∧
      (m < g.ramification → Tendsto
        (fun t : ℝ => t ^ g.ramification / ∑ j, quittingGermQuitRate g j t)
        (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
      (g.ramification = m → Tendsto
        (fun t : ℝ => t ^ g.ramification / ∑ j, quittingGermQuitRate g j t)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 / ∑ j, a j))) ∧
      (g.ramification < m → Tendsto
        (fun t : ℝ => t ^ g.ramification / ∑ j, quittingGermQuitRate g j t)
        (𝓝[>] (0 : ℝ)) atTop) := by
  obtain ⟨m, a, horder, hnonneg, hsum, hsupport, hleading, hpos, hdiv, hsmall,
    hmatch, hbig⟩ :=
    Math.exists_leadingOrder_normalization
      (fun i => analyticAt_quittingGermQuitRate g i)
      (fun i => eventually_quittingGermQuitRate_nonneg g i) hne
  refine ⟨m, a, horder, hnonneg, hsum, hsupport, hpos, hdiv, hsmall g.ramification,
    fun hq => ?_, hbig g.ramification⟩
  rw [hq]
  exact hmatch

/-! ### Transferring the comparison to absorption -/

/-- **Transfer, negligible case.**  A scale negligible against the total quit
mass is negligible against the absorption probability. -/
theorem tendsto_pow_div_quittingGermAbsorption_nhds_zero
    (g : (quittingGame reward).AnalyticBellmanGerm) {q : ℕ}
    (hsum : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ∑ j, quittingGermQuitRate g j t)
    (h : Tendsto (fun t : ℝ => t ^ q / ∑ j, quittingGermQuitRate g j t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun t : ℝ => t ^ q / quittingGermAbsorption g t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ =>
      (Fintype.card ι : ℝ) * (t ^ q / ∑ j, quittingGermQuitRate g j t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using h.const_mul (Fintype.card ι : ℝ)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_mem_Ioo_radius g, hsum] with t ht hs
    exact div_nonneg (pow_nonneg ht.1.le q) (quittingGermAbsorption_pos g ht hs).le
  · filter_upwards [eventually_mem_Ioo_radius g, hsum] with t ht hs
    have hA : 0 < quittingGermAbsorption g t := quittingGermAbsorption_pos g ht hs
    have hbound := (quittingGermAbsorption_bounds g ht).2
    have htq : (0 : ℝ) ≤ t ^ q := pow_nonneg ht.1.le q
    rw [mul_div_assoc', div_le_div_iff₀ hA hs]
    calc t ^ q * ∑ j, quittingGermQuitRate g j t
        ≤ t ^ q * ((Fintype.card ι : ℝ) * quittingGermAbsorption g t) :=
          mul_le_mul_of_nonneg_left hbound htq
      _ = (Fintype.card ι : ℝ) * t ^ q * quittingGermAbsorption g t := by ring

/-- **Transfer, dominant case.**  A scale dominated by the total quit mass is
dominated by the absorption probability. -/
theorem tendsto_pow_div_quittingGermAbsorption_atTop
    (g : (quittingGame reward).AnalyticBellmanGerm) {q : ℕ}
    (hsum : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ∑ j, quittingGermQuitRate g j t)
    (h : Tendsto (fun t : ℝ => t ^ q / ∑ j, quittingGermQuitRate g j t)
      (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto (fun t : ℝ => t ^ q / quittingGermAbsorption g t)
      (𝓝[>] (0 : ℝ)) atTop := by
  refine tendsto_atTop_mono' _ ?_ h
  filter_upwards [eventually_mem_Ioo_radius g, hsum] with t ht hs
  have hA : 0 < quittingGermAbsorption g t := quittingGermAbsorption_pos g ht hs
  have hbound := (quittingGermAbsorption_bounds g ht).1
  have htq : (0 : ℝ) ≤ t ^ q := pow_nonneg ht.1.le q
  rw [div_le_div_iff₀ hs hA]
  exact mul_le_mul_of_nonneg_left hbound htq

end GameTheory
