/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.SuccessorCertificate
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanQuitEndpointLimit
import UniformEquilibrium.Quitting.Paths.OpponentActionMass

/-!
# Backward stability of root ε-complementarity (period-one base case)

Numerical analysis's central move is: an approximate solution is the exact
solution of a nearby problem.  This file asks that question of the finite
root ε-complementarity predicate `IsεQuittingRootEndpointNash` from
`UniformEquilibrium.Quitting.Root.SuccessorCertificate`: is an
ε-complementary root row *exactly* complementary for a nearby reward table,
against the same fixed tail payoff?

This is a production port of a companion development, the strongest leg of
the exact-cycle stratum frame (S1). The statements and proofs below are
unchanged from that companion development: every lemma it leaned on
(`quittingRootPayoff`,
`quittingRootQuitPayoff`, `quittingRootContinuePayoff`,
`quittingRootEndpointDifference`, `IsεQuittingRootEndpointNash`,
`quittingRoot_continueProbability_add_quitProbability`,
`action_eq_true_of_mem_support_pmfPi_update_pure_true`,
`action_eq_false_of_mem_support_pmfPi_update_pure_false`) already exists in
production with the identical name and signature, so no encoding
reconciliation was needed -- the companion development was already written
against this file's production API.

## The mechanism

`ownShiftReward reward d` raises every player `who`'s reward by `d who`
exactly on the realized quitter sets that contain `who`, and leaves every
other realized reward unchanged.  Two structural facts about
`quittingRootQuitPayoff`/`quittingRootContinuePayoff` make this shift land
entirely, and independently, on each player's own endpoint gap:

* `quittingRootQuitPayoff` is an expectation over joint actions in which
  `who` deterministically quits, so `who` belongs to *every* realized
  quitter set; the shift adds `d who` to every term, hence to the whole
  expectation (`quittingRootQuitPayoff_ownShiftReward`).
* `quittingRootContinuePayoff` is an expectation over joint actions in which
  `who` deterministically continues, so `who` belongs to *no* realized
  quitter set; the shift is a no-op there
  (`quittingRootContinuePayoff_ownShiftReward`).

Consequently the endpoint gap `quittingRootEndpointDifference` shifts by
exactly `d who`, and nothing else about the reward table needs to move
(`quittingRootEndpointDifference_ownShiftReward`).

## The theorem

`exists_exact_of_isεQuittingRootEndpointNash` packages this into a genuine
backward-error statement: given an ε-complementary root row, there is a
shift `d` making the *same* row *exactly* complementary against the shifted
table, at zero tolerance.  The shift obeys an explicit condition number:

* at a pure coordinate (`(root i true).toReal = 0` or
  `(root i false).toReal = 0`) the perturbation is at most `ε`;
* at an interior coordinate the perturbation obeys
  `|d i| * min y (1 - y) ≤ ε`, i.e. `|d i| ≤ ε / min(y, 1 - y)` -- the
  condition number `1 / min(y, 1 - y)` blows up as the mixed marginal
  approaches a pure one, so near-pure mixed rows are the ill-conditioned
  case.

`exists_exact_of_pure` records the fully pure specialization, where the
condition number collapses to `1`.

## Scope

**Fixed tail only.** `tail` is an arbitrary but fixed payoff vector, not
itself required to solve any recursive (Bellman) consistency condition
against the perturbed table. This is the period-one / fixed-tail base case;
feeding the perturbed row's value back into a tail across multiple periods
-- the natural next step toward a backward-stable cycle -- is open (S1 in
the stratum-frame ledger above).

## Nonclaims

* **Reward shifts only through own-containing sets.** `ownShiftReward` never
  touches `reward S who` for `who ∉ S`; the perturbation is exactly the one
  bilinear direction that the endpoint-difference algebra can absorb for
  free. No claim is made about perturbations that also move opponents'
  rewards on sets not containing `who`.
* **Single row against a fixed root.** The statement is about one player
  profile `root : ι → PMF Bool` and its own endpoint gaps, not about
  simultaneously repairing several candidate rows with a shared `d`.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The per-player own-set uniform reward shift: raise `who`'s reward by
`d who` exactly on the quitting sets `S` that contain `who`, leaving every
other player's reward on `S`, and every reward on sets not containing
`who`, untouched. -/
def ownShiftReward (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (d : ι → ℝ) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun S who => reward S who + (if who ∈ S.val then d who else 0)

/-- Pointwise root-stage shift: on a realized joint action, the own-set
shift adds `d who` exactly when `who` is among the quitters selected by
that action, and does nothing on the all-continue-style branch (which does
not consult `reward` at all). -/
theorem quittingRootPayoff_ownShiftReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (d : ι → ℝ) (action : ι → Bool) (who : ι) :
    quittingRootPayoff (ownShiftReward reward d) tail action who =
      quittingRootPayoff reward tail action who +
        (if action who = true then d who else 0) := by
  by_cases h : (quittingQuitters action).Nonempty
  · have hmem : who ∈ quittingQuitters action ↔ action who = true := by
      simp [quittingQuitters]
    simp only [quittingRootPayoff, ownShiftReward, dif_pos h, hmem]
  · have hnot : action who ≠ true := fun hc =>
      h ((quittingQuitters_nonempty_iff action).2 ⟨who, hc⟩)
    simp only [quittingRootPayoff, dif_neg h]
    simp [hnot]

/-- The Quit endpoint payoff shifts by exactly `d who`: every realized
quitter set in `quittingRootQuitPayoff`'s expectation contains `who` (its
own marginal is forced to pure Quit), so the own-set shift adds `d who` to
every term. -/
theorem quittingRootQuitPayoff_ownShiftReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (d : ι → ℝ) (who : ι) :
    quittingRootQuitPayoff (ownShiftReward reward d) tail root who =
      quittingRootQuitPayoff reward tail root who + d who := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  set distribution := pmfPi (Function.update root who (PMF.pure true)) with hdist
  have hpoint :
      (fun action => quittingRootPayoff (ownShiftReward reward d) tail action who) =
        fun action =>
          quittingRootPayoff reward tail action who +
            (if action who = true then d who else 0) := by
    funext action
    exact quittingRootPayoff_ownShiftReward reward tail d action who
  have hcorrection :
      expect distribution (fun action => if action who = true then d who else 0) = d who := by
    have hcongr :
        expect distribution (fun action => if action who = true then d who else 0) =
          expect distribution (fun _ => d who) := by
      apply expect_congr_on_support
      intro action haction
      rw [hdist] at haction
      have hself := action_eq_true_of_mem_support_pmfPi_update_pure_true root who action haction
      simp [hself]
    rw [hcongr, expect_const]
  calc
    expect distribution (fun action => quittingRootPayoff (ownShiftReward reward d) tail action who)
        = expect distribution (fun action =>
            quittingRootPayoff reward tail action who +
              (if action who = true then d who else 0)) := by
          rw [hpoint]
    _ = expect distribution (fun action => quittingRootPayoff reward tail action who) +
          expect distribution (fun action => if action who = true then d who else 0) :=
          expect_add distribution _ _
    _ = expect distribution (fun action => quittingRootPayoff reward tail action who) + d who := by
          rw [hcorrection]

/-- The Continue endpoint payoff is unchanged: every realized action in
`quittingRootContinuePayoff`'s expectation has `who` continuing (its own
marginal is forced to pure Continue), so `who` never belongs to a realized
quitter set and the own-set shift never fires. -/
theorem quittingRootContinuePayoff_ownShiftReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (d : ι → ℝ) (who : ι) :
    quittingRootContinuePayoff (ownShiftReward reward d) tail root who =
      quittingRootContinuePayoff reward tail root who := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  set distribution := pmfPi (Function.update root who (PMF.pure false)) with hdist
  have hpoint :
      (fun action => quittingRootPayoff (ownShiftReward reward d) tail action who) =
        fun action =>
          quittingRootPayoff reward tail action who +
            (if action who = true then d who else 0) := by
    funext action
    exact quittingRootPayoff_ownShiftReward reward tail d action who
  have hcorrection :
      expect distribution (fun action => if action who = true then d who else 0) = 0 := by
    have hcongr :
        expect distribution (fun action => if action who = true then d who else 0) =
          expect distribution (fun _ => (0 : ℝ)) := by
      apply expect_congr_on_support
      intro action haction
      rw [hdist] at haction
      have hself :=
        action_eq_false_of_mem_support_pmfPi_update_pure_false root who action haction
      simp [hself]
    rw [hcongr, expect_const]
  calc
    expect distribution (fun action => quittingRootPayoff (ownShiftReward reward d) tail action who)
        = expect distribution (fun action =>
            quittingRootPayoff reward tail action who +
              (if action who = true then d who else 0)) := by
          rw [hpoint]
    _ = expect distribution (fun action => quittingRootPayoff reward tail action who) +
          expect distribution (fun action => if action who = true then d who else 0) :=
          expect_add distribution _ _
    _ = expect distribution (fun action => quittingRootPayoff reward tail action who) := by
          rw [hcorrection, add_zero]

/-- The endpoint gap shifts by exactly `d who`, and by nothing else: Quit
moves by `d who`, Continue does not move at all. -/
theorem quittingRootEndpointDifference_ownShiftReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (d : ι → ℝ) (who : ι) :
    quittingRootEndpointDifference (ownShiftReward reward d) tail root who =
      quittingRootEndpointDifference reward tail root who + d who := by
  unfold quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_ownShiftReward, quittingRootContinuePayoff_ownShiftReward]
  ring

/-- **Backward stability of root ε-complementarity, period-one base case.**
Every ε-complementary root row is exactly complementary for an own-set
shifted reward table, against the *same* fixed tail payoff and the *same*
root. The shift is explicit and bounded coordinatewise: pure coordinates
absorb up to `ε`, interior coordinates absorb `ε / min(y, 1 - y)` where `y`
is the Continue probability -- the condition number `1 / min(y, 1 - y)`
blowing up exactly as the marginal approaches a pure endpoint. -/
theorem exists_exact_of_isεQuittingRootEndpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (ε : ℝ) (root : ι → PMF Bool) (hε : 0 ≤ ε)
    (hnash : IsεQuittingRootEndpointNash reward tail ε root) :
    ∃ d : ι → ℝ,
      IsεQuittingRootEndpointNash (ownShiftReward reward d) tail 0 root ∧
        ∀ i,
          ((root i true).toReal = 0 ∨ (root i false).toReal = 0 → |d i| ≤ ε) ∧
            ((root i true).toReal ≠ 0 → (root i false).toReal ≠ 0 →
              |d i| * min (root i true).toReal (root i false).toReal ≤ ε) := by
  classical
  set d : ι → ℝ := fun i =>
    if (root i true).toReal = 0 then
      -max (quittingRootEndpointDifference reward tail root i) 0
    else if (root i false).toReal = 0 then
      max (-(quittingRootEndpointDifference reward tail root i)) 0
    else
      -(quittingRootEndpointDifference reward tail root i) with hd
  refine ⟨d, ?_, ?_⟩
  · -- Exactness: a pure algebraic consequence of the construction of `d`,
    -- independent of `hnash`/`hε`.
    intro who
    have hshift := quittingRootEndpointDifference_ownShiftReward reward tail root d who
    have hxnn : (0 : ℝ) ≤ (root who true).toReal := ENNReal.toReal_nonneg
    have hynn : (0 : ℝ) ≤ (root who false).toReal := ENNReal.toReal_nonneg
    rw [hshift]
    by_cases hx : (root who true).toReal = 0
    · have hdWho : d who = -max (quittingRootEndpointDifference reward tail root who) 0 := by
        simp [hd, hx]
      have hdiffle :
          quittingRootEndpointDifference reward tail root who +
              d who ≤ 0 := by
        rw [hdWho]
        have := le_max_left (quittingRootEndpointDifference reward tail root who) 0
        linarith
      constructor
      · nlinarith [hynn, hdiffle]
      · simp [hx]
    · by_cases hy : (root who false).toReal = 0
      · have hdWho :
            d who = max (-(quittingRootEndpointDifference reward tail root who)) 0 := by
          simp [hd, hx, hy]
        have hdiffge :
            0 ≤ quittingRootEndpointDifference reward tail root who + d who := by
          rw [hdWho]
          have :=
            le_max_left (-(quittingRootEndpointDifference reward tail root who)) 0
          linarith
        constructor
        · simp [hy]
        · nlinarith [hxnn, hdiffge]
      · have hdWho : d who = -(quittingRootEndpointDifference reward tail root who) := by
          simp [hd, hx, hy]
        have hdiff0 :
            quittingRootEndpointDifference reward tail root who + d who = 0 := by
          rw [hdWho]; ring
        rw [hdiff0]
        constructor <;> nlinarith
  · -- Magnitude bound: uses `hnash` and `hε`.
    intro i
    have hxnn : (0 : ℝ) ≤ (root i true).toReal := ENNReal.toReal_nonneg
    have hynn : (0 : ℝ) ≤ (root i false).toReal := ENNReal.toReal_nonneg
    have hsum := quittingRoot_continueProbability_add_quitProbability root i
    constructor
    · rintro (hx | hy)
      · have hdI : d i = -max (quittingRootEndpointDifference reward tail root i) 0 := by
          simp [hd, hx]
        have hy1 : (root i false).toReal = 1 := by rw [hx] at hsum; linarith
        have hdiffle : quittingRootEndpointDifference reward tail root i ≤ ε := by
          have h1 := (hnash i).1
          rw [hy1] at h1
          linarith
        have hle : max (quittingRootEndpointDifference reward tail root i) 0 ≤ ε :=
          max_le hdiffle hε
        rw [hdI, abs_neg, abs_of_nonneg (le_max_right _ _)]
        exact hle
      · have hx0 : (root i true).toReal ≠ 0 := by
          intro hcontra
          rw [hy, hcontra] at hsum
          norm_num at hsum
        have hdI : d i = max (-(quittingRootEndpointDifference reward tail root i)) 0 := by
          simp [hd, hx0, hy]
        have hx1 : (root i true).toReal = 1 := by rw [hy] at hsum; linarith
        have hdiffge : -ε ≤ quittingRootEndpointDifference reward tail root i := by
          have h2 := (hnash i).2
          rw [hx1] at h2
          linarith
        have hle : -(quittingRootEndpointDifference reward tail root i) ≤ ε := by linarith
        have hle' : max (-(quittingRootEndpointDifference reward tail root i)) 0 ≤ ε :=
          max_le hle hε
        rw [hdI, abs_of_nonneg (le_max_right _ _)]
        exact hle'
    · intro hx hy
      have hxpos : 0 < (root i true).toReal := lt_of_le_of_ne hxnn (Ne.symm hx)
      have hypos : 0 < (root i false).toReal := lt_of_le_of_ne hynn (Ne.symm hy)
      have hdI : d i = -(quittingRootEndpointDifference reward tail root i) := by
        simp [hd, hx, hy]
      rw [hdI, abs_neg]
      have h1 := (hnash i).1
      have h2 := (hnash i).2
      rcases le_total 0 (quittingRootEndpointDifference reward tail root i) with hdpos | hdneg
      · rw [abs_of_nonneg hdpos]
        calc
          quittingRootEndpointDifference reward tail root i *
                min (root i true).toReal (root i false).toReal ≤
              quittingRootEndpointDifference reward tail root i *
                (root i false).toReal :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hdpos
          _ = (root i false).toReal *
                quittingRootEndpointDifference reward tail root i := mul_comm _ _
          _ ≤ ε := h1
      · rw [abs_of_nonpos hdneg]
        calc
          -quittingRootEndpointDifference reward tail root i *
                min (root i true).toReal (root i false).toReal ≤
              -quittingRootEndpointDifference reward tail root i *
                (root i true).toReal :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
          _ = -((root i true).toReal *
                quittingRootEndpointDifference reward tail root i) := by ring
          _ ≤ ε := by linarith

/-- **Pure specialization: condition number `1`.** If every coordinate of
`root` is pure, the own-set shift needed to make the row exactly
complementary is bounded by `ε` at every coordinate, with no `min` factor. -/
theorem exists_exact_of_pure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (ε : ℝ) (root : ι → PMF Bool) (hε : 0 ≤ ε)
    (hnash : IsεQuittingRootEndpointNash reward tail ε root)
    (hpure : ∀ i, (root i true).toReal = 0 ∨ (root i false).toReal = 0) :
    ∃ d : ι → ℝ,
      IsεQuittingRootEndpointNash (ownShiftReward reward d) tail 0 root ∧
        ∀ i, |d i| ≤ ε := by
  obtain ⟨d, hexact, hbound⟩ :=
    exists_exact_of_isεQuittingRootEndpointNash reward tail ε root hε hnash
  exact ⟨d, hexact, fun i => (hbound i).1 (hpure i)⟩

end GameTheory
