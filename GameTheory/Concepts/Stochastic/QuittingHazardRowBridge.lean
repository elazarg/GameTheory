/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCyclicWeightRowDichotomy
import GameTheory.Concepts.Stochastic.QuittingRootSuccessorCertificate
import GameTheory.Concepts.Stochastic.QuittingSingletonStationaryRoot
import Math.PMFProduct.Bool
import Math.PMFProduct.Update

/-!
# Bridging the `PMF Bool` and real-hazard encodings of quitting-game rows

The main development states quitting-game roots as `ι → PMF Bool` mixtures,
with hazards surfacing through objects like `quittingStationaryContinueMass`
and the root/continuation payoffs of `QuittingRootSuccessorCertificate.lean`.
`QuittingCyclicWeightRowDichotomy.lean` states the same row-local
complementarity conditions over real-valued hazard vectors `ι → ℝ`, with
`sigmaValue`, `excludedValue`, `gammaValue`, `gainValue` and
`IsExactRowComplementary`, because the questions corpus is written over
arrays of reals. This file is the missing bridge between them.

## Contents

* `hazardOfRoot`, `rootOfHazard`: send a product root action to its
  per-coordinate quitting probability and back, with round-trip laws
  `hazardOfRoot_rootOfHazard` and `rootOfHazard_hazardOfRoot`.
* `weightOfReward`, `rewardOfWeight`: send a coalition reward (defined on
  nonempty coalitions only) to a real weight on all finsets and back, with
  round-trip laws `rewardOfWeight_weightOfReward` (exact) and
  `weightOfReward_rewardOfWeight` (exact on nonempty coalitions -- the value
  a real weight assigns to the empty coalition has no Bool-side counterpart,
  but `sigmaValue`, `excludedValue`, `gammaValue`, `gainValue` never read it).
* `expect_pmfPi_boolFamily_eq_sum_powerset`: the combinatorial heart --
  expanding the expectation of a function of a Boolean joint action, drawn
  from an independent-coordinate product with a fixed default outside a
  carrier finset, into a `Finset.prod_add`-style sum over the powerset of the
  carrier weighted by the coalition mass built from `hazardOfRoot`.
* `quittingRootQuitPayoff_eq_sigmaValue`, `quittingRootContinuePayoff_eq_gammaValue`,
  `quittingRootEndpointDifference_eq_gainValue`: the gain values agree at a
  translated row, against `weightOfReward reward` on the real side.
* `isExactRowComplementary_hazardOfRoot_iff`: `IsExactRowComplementary` at a
  translated row is exactly the zero-`ε` root endpoint Nash condition.
* `atMostOnePositive_of_isεQuittingRootEndpointNash_cyclicWeightReward`: the
  row dichotomy of `QuittingCyclicWeightRowDichotomy.lean`, restated on the
  `PMF Bool` side for `cyclicWeight`'s own root/continuation payoffs.

## Scope

The translation is exact and total in the direction Bool-to-real: every
product root action has a hazard vector in `[0,1]^ι`, and every reward on
nonempty coalitions has a real weight extending it. The reverse direction
(`rootOfHazard`) needs the hazard vector to lie in `[0,1]^ι`, matching
`QuittingCyclicWeightRowDichotomy.lean`'s own standing hypothesis `hx` on
its rows; `sigmaValue`/`gammaValue`/`gainValue` make sense for hazards
outside `[0,1]` (they are polynomial expressions with no probabilistic
content built in), but no `PMF Bool` mixture realizes such a row, so the
bridge is honestly restricted to `[0,1]`-valued rows in that direction. The
gain values agree exactly, with no sign, scope, or convention mismatch: both
sides compute Quit-payoff-minus-Continue-payoff for the same reward and the
same continuation value.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Translating rows -/

/-- The hazard vector of a product root action: each coordinate's own
one-stage quitting probability. -/
def hazardOfRoot (root : ι → PMF Bool) : ι → ℝ := fun i => (root i true).toReal

omit [Fintype ι] [DecidableEq ι] in
/-- A quitting probability is nonnegative. -/
theorem hazardOfRoot_nonneg (root : ι → PMF Bool) (i : ι) : 0 ≤ hazardOfRoot root i :=
  ENNReal.toReal_nonneg

omit [Fintype ι] [DecidableEq ι] in
/-- A quitting probability is at most one. -/
theorem hazardOfRoot_le_one (root : ι → PMF Bool) (i : ι) : hazardOfRoot root i ≤ 1 := by
  have h := pmfBool_false_toReal (root i)
  have h0 : 0 ≤ (root i false).toReal := ENNReal.toReal_nonneg
  unfold hazardOfRoot
  linarith

/-- Build a product root action out of a hazard vector known to lie in
`[0,1]`. -/
def rootOfHazard (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) : ι → PMF Bool :=
  fun i => quittingHazardCoin (x i) (hx0 i) (hx1 i)

omit [Fintype ι] [DecidableEq ι] in
/-- **Round trip, real to Bool to real.** The hazard of the coin built from
`x` is `x` itself. -/
@[simp] theorem hazardOfRoot_rootOfHazard (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i ≤ 1) :
    hazardOfRoot (rootOfHazard x hx0 hx1) = x := by
  funext i
  simp [hazardOfRoot, rootOfHazard]

omit [Fintype ι] [DecidableEq ι] in
/-- **Round trip, Bool to real to Bool.** A product root action equals the
coin built from its own hazard vector. -/
theorem rootOfHazard_hazardOfRoot (root : ι → PMF Bool) :
    rootOfHazard (hazardOfRoot root) (hazardOfRoot_nonneg root) (hazardOfRoot_le_one root) =
      root := by
  funext i
  apply PMF.ext
  intro b
  cases b with
  | true =>
      change ENNReal.ofReal (hazardOfRoot root i) = root i true
      unfold hazardOfRoot
      exact ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)
  | false =>
      change ENNReal.ofReal (1 - hazardOfRoot root i) = root i false
      have h := pmfBool_false_toReal (root i)
      unfold hazardOfRoot
      rw [← h]
      exact ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)

/-- Extend a coalition reward, defined only on nonempty coalitions, to a
weight on all finsets by returning `0` at the empty coalition -- a value
`sigmaValue`, `excludedValue`, `gammaValue` and `gainValue` never read. -/
def weightOfReward (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Finset ι → ι → ℝ :=
  fun S i => if h : S.Nonempty then reward ⟨S, h⟩ i else 0

/-- Restrict a general weight to a coalition reward on nonempty coalitions. -/
def rewardOfWeight (r : Finset ι → ι → ℝ) : {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun S i => r S.1 i

omit [Fintype ι] [DecidableEq ι] in
/-- **Round trip, real to Bool to real, on nonempty coalitions.** The value
a weight assigns to the empty coalition is not recoverable -- it has no
Bool-side counterpart -- but every coalition read by `sigmaValue`,
`excludedValue`, `gammaValue`, or `gainValue` is nonempty. -/
theorem weightOfReward_rewardOfWeight (r : Finset ι → ι → ℝ) (S : Finset ι) (h : S.Nonempty)
    (i : ι) :
    weightOfReward (rewardOfWeight r) S i = r S i := by
  simp [weightOfReward, rewardOfWeight, h]

omit [Fintype ι] [DecidableEq ι] in
/-- **Round trip, Bool to real to Bool.** A coalition reward is recovered
exactly. -/
@[simp] theorem rewardOfWeight_weightOfReward (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : {S : Finset ι // S.Nonempty}) (i : ι) :
    rewardOfWeight (weightOfReward reward) S i = reward S i := by
  obtain ⟨S, hS⟩ := S
  simp [rewardOfWeight, weightOfReward, hS]

/-! ## The combinatorial heart: Boolean product expectations as powerset sums -/

/-- **Coalition expansion of a Boolean product expectation.** Peeling
independent Bernoulli coordinates in a carrier finset `t` one at a time
turns the expectation of a function of the joint action into a
`Finset.prod_add`-style sum over the powerset of `t`, weighted by the
coalition mass built from `q`'s own quitting probabilities, holding the
coordinates outside `t` fixed at the default `rest`. -/
theorem expect_pmfPi_boolFamily_eq_sum_powerset (t : Finset ι) (q : ι → PMF Bool)
    (rest : ι → Bool) (k : (ι → Bool) → ℝ) :
    expect (pmfPi (fun i => if i ∈ t then q i else PMF.pure (rest i))) k =
      ∑ J ∈ t.powerset,
        (∏ i ∈ J, (q i true).toReal) * (∏ i ∈ t \ J, (q i false).toReal) *
          k (fun i => if i ∈ J then true else if i ∈ t then false else rest i) := by
  induction t using Finset.induction_on generalizing rest with
  | empty =>
      simp [pmfPi_pure]
  | insert a s ha ih =>
      have hσ : (fun i => if i ∈ insert a s then q i else PMF.pure (rest i)) =
          Function.update (fun i => if i ∈ s then q i else PMF.pure (rest i)) a (q a) := by
        funext i
        by_cases hia : i = a
        · subst hia; simp [ha]
        · simp [hia, Finset.mem_insert]
      rw [hσ, pmfPi_update_bind, expect_bind]
      have hσb : ∀ b : Bool,
          Function.update (fun i => if i ∈ s then q i else PMF.pure (rest i)) a (PMF.pure b) =
            fun i => if i ∈ s then q i else PMF.pure ((Function.update rest a b) i) := by
        intro b
        funext i
        by_cases hia : i = a
        · subst hia; simp [ha]
        · simp [hia]
      simp_rw [hσb, ih]
      -- `rw [add_comm]` below rewrites the *first* `_+_` it finds, which is
      -- the left-hand `f true + f false`; it becomes `f false + f true`,
      -- matching the right-hand `∑ g J + ∑ g (insert a J)` order.
      rw [expect_eq_sum, Fintype.sum_bool, Finset.sum_powerset_insert ha, add_comm]
      congr 1
      · -- the `false` branch: `a` stays out, the quitting coalition is `J`.
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [Finset.mem_powerset] at hJ
        have haJ : a ∉ J := fun h => ha (hJ h)
        have haNotSdiff : a ∉ s \ J := fun h => ha (Finset.mem_sdiff.mp h).1
        have hprodfalse : ∏ i ∈ insert a s \ J, ((q i) false).toReal =
            (q a false).toReal * ∏ i ∈ s \ J, ((q i) false).toReal := by
          have hd : insert a s \ J = insert a (s \ J) := by
            ext i
            by_cases hia : i = a
            · subst hia; simp [ha, haJ]
            · simp [hia, Finset.mem_insert, Finset.mem_sdiff]
          rw [hd, Finset.prod_insert haNotSdiff]
        have hkeq :
            (fun i => if i ∈ J then true else if i ∈ s then false else
                (Function.update rest a false) i) =
            (fun i => if i ∈ J then true else if i ∈ insert a s then false else rest i) := by
          funext i
          by_cases hia : i = a
          · subst hia; simp [haJ, ha]
          · simp [hia, Finset.mem_insert]
        rw [hprodfalse, hkeq]; ring
      · -- the `true` branch: `a` joins the quitting coalition `insert a J`.
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [Finset.mem_powerset] at hJ
        have haJ : a ∉ J := fun h => ha (hJ h)
        have hprodtrue : ∏ i ∈ insert a J, ((q i) true).toReal =
            (q a true).toReal * ∏ i ∈ J, ((q i) true).toReal :=
          Finset.prod_insert haJ
        have hd : insert a s \ insert a J = s \ J := by
          ext i
          by_cases hia : i = a
          · subst hia; simp [ha, haJ]
          · simp [hia, Finset.mem_insert, Finset.mem_sdiff]
        have hkeq :
            (fun i => if i ∈ J then true else if i ∈ s then false else
                (Function.update rest a true) i) =
            (fun i => if i ∈ insert a J then true else if i ∈ insert a s then false else
                rest i) := by
          funext i
          by_cases hia : i = a
          · subst hia; simp [haJ, ha]
          · simp [hia, Finset.mem_insert]
        rw [hprodtrue, hd, hkeq]; ring

/-- Restatement of `expect_pmfPi_boolFamily_eq_sum_powerset` with the
survival factor written as `1 - (quitting probability)`, matching the shape
of `sigmaValue`, `excludedValue`, `gammaValue`. -/
theorem expect_pmfPi_boolFamily_eq_sum_powerset' (t : Finset ι) (q : ι → PMF Bool)
    (rest : ι → Bool) (k : (ι → Bool) → ℝ) :
    expect (pmfPi (fun i => if i ∈ t then q i else PMF.pure (rest i))) k =
      ∑ J ∈ t.powerset,
        (∏ i ∈ J, (q i true).toReal) * (∏ i ∈ t \ J, (1 - (q i true).toReal)) *
          k (fun i => if i ∈ J then true else if i ∈ t then false else rest i) := by
  rw [expect_pmfPi_boolFamily_eq_sum_powerset]
  apply Finset.sum_congr rfl
  intro J _
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  rw [pmfBool_false_toReal]

/-! ## The gain values agree at a translated row -/

/-- The Bool-side pure-Quit endpoint payoff is exactly `sigmaValue`, `Σ_i`,
computed against the extended weight `weightOfReward reward` at the
translated hazard row. This is deliverable (2), the sigma half. -/
theorem quittingRootQuitPayoff_eq_sigmaValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι) (root : ι → PMF Bool)
    (who : ι) :
    quittingRootQuitPayoff reward tail root who =
      sigmaValue (weightOfReward reward) (hazardOfRoot root) who := by
  have hfamily : Function.update root who (PMF.pure true) =
      fun i => if i ∈ Finset.univ.erase who then root i else PMF.pure (true : Bool) := by
    funext i
    by_cases hi : i = who
    · subst hi; simp
    · simp [hi]
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff sigmaValue
  rw [hfamily, expect_pmfPi_boolFamily_eq_sum_powerset']
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.mem_powerset] at hJ
  have haction :
      quittingRootPayoff reward tail
          (fun i => if i ∈ J then true else if i ∈ Finset.univ.erase who then false else true)
          who =
        weightOfReward reward (insert who J) who := by
    have hqset : quittingQuitters
        (fun i => if i ∈ J then true else if i ∈ Finset.univ.erase who then false else true) =
        insert who J := by
      unfold quittingQuitters
      ext i
      by_cases hiJ : i ∈ J
      · simp [hiJ]
      · by_cases hiw : i = who
        · subst hiw; simp
        · simp [hiJ, hiw]
    have hnonempty : (insert who J).Nonempty := Finset.insert_nonempty who J
    unfold quittingRootPayoff
    rw [dif_pos (hqset ▸ hnonempty)]
    simp only [weightOfReward, dif_pos hnonempty]
    congr 1
    exact Subtype.ext hqset
  rw [haction]
  rfl

/-- The Bool-side pure-Continue endpoint payoff is exactly `gammaValue`,
`Γ_i`, computed against the extended weight `weightOfReward reward` at the
translated hazard row, with `tail who` as the next-phase value. This is
deliverable (2), the gamma half. -/
theorem quittingRootContinuePayoff_eq_gammaValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι) (root : ι → PMF Bool)
    (who : ι) :
    quittingRootContinuePayoff reward tail root who =
      gammaValue (weightOfReward reward) (hazardOfRoot root) who (tail who) := by
  have hfamily : Function.update root who (PMF.pure false) =
      fun i => if i ∈ Finset.univ.erase who then root i else PMF.pure (false : Bool) := by
    funext i
    by_cases hi : i = who
    · subst hi; simp
    · simp [hi]
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [hfamily, expect_pmfPi_boolFamily_eq_sum_powerset']
  have hmem : (∅ : Finset ι) ∈ (Finset.univ.erase who).powerset := Finset.empty_mem_powerset _
  rw [← Finset.add_sum_erase _ _ hmem]
  have e1 :
      (∏ i ∈ (∅ : Finset ι), (root i true).toReal) *
          (∏ i ∈ Finset.univ.erase who \ (∅ : Finset ι), (1 - (root i true).toReal)) *
        quittingRootPayoff reward tail
          (fun i => if i ∈ (∅ : Finset ι) then true
            else if i ∈ Finset.univ.erase who then false else false) who =
      continueMassExcl (hazardOfRoot root) who * tail who := by
    have hqempty : quittingQuitters
        (fun i => if i ∈ (∅ : Finset ι) then true
          else if i ∈ Finset.univ.erase who then false else false) = ∅ := by
      unfold quittingQuitters; ext i; simp
    unfold quittingRootPayoff continueMassExcl hazardOfRoot
    rw [dif_neg (by rw [hqempty]; exact Finset.not_nonempty_empty)]
    simp
  have e2 :
      ∑ J ∈ (Finset.univ.erase who).powerset.erase ∅,
          (∏ i ∈ J, (root i true).toReal) *
              (∏ i ∈ Finset.univ.erase who \ J, (1 - (root i true).toReal)) *
            quittingRootPayoff reward tail
              (fun i => if i ∈ J then true
                else if i ∈ Finset.univ.erase who then false else false) who =
      excludedValue (weightOfReward reward) (hazardOfRoot root) who := by
    unfold excludedValue hazardOfRoot
    apply Finset.sum_congr rfl
    intro J hJ
    rw [Finset.mem_erase, Finset.mem_powerset] at hJ
    obtain ⟨hJne, -⟩ := hJ
    have haction :
        quittingRootPayoff reward tail
            (fun i => if i ∈ J then true else if i ∈ Finset.univ.erase who then false else false)
            who =
          weightOfReward reward J who := by
      have hqset : quittingQuitters
          (fun i => if i ∈ J then true else if i ∈ Finset.univ.erase who then false else false) =
          J := by
        unfold quittingQuitters
        ext i
        by_cases hiJ : i ∈ J
        · simp [hiJ]
        · simp [hiJ]
      have hnonempty : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJne
      have hne2 : (quittingQuitters
          (fun i => if i ∈ J then true else if i ∈ Finset.univ.erase who then false else false)
          ).Nonempty := by rw [hqset]; exact hnonempty
      unfold quittingRootPayoff
      rw [dif_pos hne2]
      simp only [weightOfReward, dif_pos hnonempty]
      congr 1
      exact Subtype.ext hqset
    rw [haction]
  rw [e1, e2]
  unfold gammaValue
  ring

/-- **The gain values agree at a translated row** -- deliverable (2), the
main theorem. The real-valued `gainValue`, `g_i = Σ_i - Γ_i`, computed
against the extended weight at the translated hazard row, agrees exactly
with the Bool-side pure-Quit-minus-Continue endpoint difference. No sign,
scope, or convention mismatch: both sides compute the same quantity for the
same reward and the same continuation value. -/
theorem quittingRootEndpointDifference_eq_gainValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι) (root : ι → PMF Bool)
    (who : ι) :
    quittingRootEndpointDifference reward tail root who =
      gainValue (weightOfReward reward) (hazardOfRoot root) who (tail who) := by
  unfold quittingRootEndpointDifference gainValue
  rw [quittingRootQuitPayoff_eq_sigmaValue, quittingRootContinuePayoff_eq_gammaValue]

/-! ## Complementarity transports -/

/-- **Complementarity transport** -- deliverable (3), in both directions.
`IsExactRowComplementary` of the translated hazard row against the
translated gain vector is exactly the zero-`ε` root endpoint Nash condition
on the Bool side, which by `isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash`
is in turn exactly exact root Nash (`IsεQuittingRootNash reward tail 0 root`). -/
theorem isExactRowComplementary_hazardOfRoot_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι) (root : ι → PMF Bool) :
    IsExactRowComplementary (hazardOfRoot root)
        (fun i => gainValue (weightOfReward reward) (hazardOfRoot root) i (tail i)) ↔
      IsεQuittingRootEndpointNash reward tail 0 root := by
  have hgain : ∀ i, gainValue (weightOfReward reward) (hazardOfRoot root) i (tail i) =
      quittingRootEndpointDifference reward tail root i :=
    fun i => (quittingRootEndpointDifference_eq_gainValue reward tail root i).symm
  simp_rw [hgain]
  constructor
  · intro hexact who
    obtain ⟨hb1, hb2⟩ := hexact who
    have hxeq : hazardOfRoot root who = (root who true).toReal := rfl
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    have hx0 := hazardOfRoot_nonneg root who
    have hx1 := hazardOfRoot_le_one root who
    refine ⟨?_, ?_⟩
    · by_cases h1 : hazardOfRoot root who < 1
      · nlinarith [hb2 h1, ENNReal.toReal_nonneg (a := root who false)]
      · have heq : (root who true).toReal = 1 := hxeq ▸ le_antisymm hx1 (not_lt.mp h1)
        have hy0 : (root who false).toReal = 0 := by linarith
        simp [hy0]
    · by_cases h0 : 0 < hazardOfRoot root who
      · nlinarith [hb1 h0, ENNReal.toReal_nonneg (a := root who true)]
      · have heq : (root who true).toReal = 0 := hxeq ▸ le_antisymm (not_lt.mp h0) hx0
        simp [heq]
  · intro hnash who
    obtain ⟨hb1, hb2⟩ := hnash who
    have hb2' : 0 ≤ (root who true).toReal *
        quittingRootEndpointDifference reward tail root who := by simpa using hb2
    have hxeq : hazardOfRoot root who = (root who true).toReal := rfl
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    refine ⟨fun hpos => ?_, fun hlt1 => ?_⟩
    · rw [hxeq] at hpos
      nlinarith [hb2', hpos]
    · have hcontinue : 0 < (root who false).toReal := by rw [hxeq] at hlt1; linarith
      nlinarith [hb1, hcontinue]

/-! ## Demonstration: the row dichotomy, transported -/

/-- `sigmaValue` only ever reads a weight at nonempty coalitions
(`insert i J` is always nonempty), so it is unaffected by round-tripping a
real weight through a coalition reward. -/
theorem sigmaValue_weightOfReward_rewardOfWeight (r : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) :
    sigmaValue (weightOfReward (rewardOfWeight r)) x i = sigmaValue r x i := by
  unfold sigmaValue
  apply Finset.sum_congr rfl
  intro J _
  rw [weightOfReward_rewardOfWeight r (insert i J) (Finset.insert_nonempty i J)]

/-- `excludedValue` only ever reads a weight at nonempty coalitions (its sum
ranges over the powerset with the empty coalition erased), so it too is
unaffected. -/
theorem excludedValue_weightOfReward_rewardOfWeight (r : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) :
    excludedValue (weightOfReward (rewardOfWeight r)) x i = excludedValue r x i := by
  unfold excludedValue
  apply Finset.sum_congr rfl
  intro J hJ
  have hJne : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hJ).1
  rw [weightOfReward_rewardOfWeight r J hJne]

/-- `gammaValue`, built from `excludedValue` and a weight-independent
continuation term, is likewise unaffected. -/
theorem gammaValue_weightOfReward_rewardOfWeight
    (r : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) (next : ℝ) :
    gammaValue (weightOfReward (rewardOfWeight r)) x i next = gammaValue r x i next := by
  unfold gammaValue
  rw [excludedValue_weightOfReward_rewardOfWeight]

/-- The gain values agree too. -/
theorem gainValue_weightOfReward_rewardOfWeight
    (r : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) (next : ℝ) :
    gainValue (weightOfReward (rewardOfWeight r)) x i next = gainValue r x i next := by
  unfold gainValue
  rw [sigmaValue_weightOfReward_rewardOfWeight, gammaValue_weightOfReward_rewardOfWeight]

/-- The Bool-side coalition reward for `cyclicWeight`, restricted to
nonempty coalitions on its three cyclically ordered coordinates. -/
def cyclicWeightReward : {S : Finset CyclicIndex // S.Nonempty} → Payoff CyclicIndex :=
  rewardOfWeight cyclicWeight

/-- **The row dichotomy, transported to the `PMF Bool` side** -- deliverable
(4). This restates `atMostOnePositive_of_isExactRowComplementary` for a
product root action and a continuation payoff, through the bridge: an exact
root Nash for `cyclicWeightReward` with `tail i + 1/2` nonnegative at every
coordinate has at most one player quitting with positive probability. -/
theorem atMostOnePositive_of_isεQuittingRootEndpointNash_cyclicWeightReward
    (root : CyclicIndex → PMF Bool) (tail : Payoff CyclicIndex)
    (hz : ∀ j, 0 ≤ tail j + 1 / 2)
    (hnash : IsεQuittingRootEndpointNash cyclicWeightReward tail 0 root)
    (i j : CyclicIndex) (hi : 0 < hazardOfRoot root i) (hj : 0 < hazardOfRoot root j) :
    i = j := by
  have hcompl := (isExactRowComplementary_hazardOfRoot_iff cyclicWeightReward tail root).mpr hnash
  have hzsub : ∀ k, (tail k + 1 / 2) - 1 / 2 = tail k := fun k => by ring
  have hcompl' : IsExactRowComplementary (hazardOfRoot root)
      (fun k => gainValue cyclicWeight (hazardOfRoot root) k ((tail k + 1 / 2) - 1 / 2)) := by
    intro k
    dsimp only
    rw [hzsub k]
    have hkey := hcompl k
    unfold cyclicWeightReward at hkey
    dsimp only at hkey
    rwa [gainValue_weightOfReward_rewardOfWeight] at hkey
  exact atMostOnePositive_of_isExactRowComplementary (hazardOfRoot root)
    (fun k => tail k + 1 / 2)
    (fun k => ⟨hazardOfRoot_nonneg root k, hazardOfRoot_le_one root k⟩) hz hcompl' i j hi hj

end GameTheory
