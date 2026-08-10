/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-!
# A fixed-tail support-enlargement alternative

This file isolates the exact local fact available at a fixed continuation
target.  For one player, an exact product root has the usual three-way
endpoint alternative:

* positive Quit-minus-Continue gain forces Quit with probability one;
* negative gain forces Quit with probability zero;
* an interior marginal forces equality of the two endpoints.

Consequently a strict positive Quit defect at an inactive coordinate cannot be
repaired by a small interior support enlargement while keeping the
continuation fixed.  Any exact repair must move to a sure-Quit face (or move
the continuation/reward data enough to remove the strict defect).  This is a
local collision/support alternative, not a producer theorem for a
state-matched Bellman chronology.

The quantitative lemmas below record the exact own-marginal tradeoff: changing
one player's marginal shifts that player's prescribed root payoff by the
played Quit mass times the fixed endpoint gap.  No simultaneous multi-player
root replacement is covered here.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## A generic support-local endpoint predicate -/

/-- Support-local approximate endpoint complementarity.  A played action must
be within `δ` of the other endpoint, without multiplying its defect by its
probability. -/
def IsQuittingRootSupportApproxNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (δ : ℝ) (root : ι → PMF Bool) : Prop :=
  ∀ who,
    (0 < (root who true).toReal →
      -δ ≤ quittingRootEndpointDifference reward tail root who) ∧
    (0 < (root who false).toReal →
      quittingRootEndpointDifference reward tail root who ≤ δ)

/-- The endpoint difference depends only on the opponents' marginals. -/
theorem quittingRootEndpointDifference_update_ownMarginal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (marginal : PMF Bool) :
    quittingRootEndpointDifference reward tail
        (Function.update root who marginal) who =
      quittingRootEndpointDifference reward tail root who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  simp

/-! ## Exact own-marginal shift and the approximate tradeoff -/

/-- Changing only `who`'s root marginal changes `who`'s prescribed root
payoff by the change in Quit probability times the endpoint gap. -/
theorem quittingRootExpectedPayoff_update_ownMarginal_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (marginal : PMF Bool) :
    quittingRootExpectedPayoff reward tail
        (Function.update root who marginal) who -
        quittingRootExpectedPayoff reward tail root who =
      ((marginal true).toReal - (root who true).toReal) *
        quittingRootEndpointDifference reward tail root who := by
  have hroot := quittingRootExpectedPayoff_update_eq_endpointMix
    reward tail root who (root who)
  have hroot' : quittingRootExpectedPayoff reward tail root who =
      (root who true).toReal * quittingRootQuitPayoff reward tail root who +
        (root who false).toReal * quittingRootContinuePayoff reward tail root who := by
    simpa using hroot
  rw [quittingRootExpectedPayoff_update_eq_endpointMix
    reward tail root who marginal, hroot']
  have hm : (marginal false).toReal + (marginal true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one marginal
  have hr := quittingRoot_continueProbability_add_quitProbability root who
  have hm' : (marginal false).toReal = 1 - (marginal true).toReal := by
    linarith
  have hr' : (root who false).toReal = 1 - (root who true).toReal := by
    linarith
  rw [hm', hr']
  unfold quittingRootEndpointDifference
  ring

/-- Relative to pure Continue at `who`, an own-marginal repair gains exactly
the played Quit probability times the endpoint gap. -/
theorem quittingRootExpectedPayoff_update_ownMarginal_sub_pureContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (marginal : PMF Bool) :
    quittingRootExpectedPayoff reward tail
        (Function.update root who marginal) who -
        quittingRootExpectedPayoff reward tail
          (Function.update root who (PMF.pure false)) who =
      (marginal true).toReal *
        quittingRootEndpointDifference reward tail root who := by
  rw [quittingRootExpectedPayoff_update_eq_endpointMix,
    quittingRootExpectedPayoff_update_eq_endpointMix]
  have hm : (marginal false).toReal + (marginal true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one marginal
  have hfalse : (PMF.pure false true).toReal = 0 := by simp
  have htrue : (PMF.pure false false).toReal = 1 := by simp
  rw [hfalse, htrue]
  have hm' : (marginal false).toReal = 1 - (marginal true).toReal := by
    linarith
  rw [hm']
  unfold quittingRootEndpointDifference
  ring

/-- An approximate endpoint-Nash own-marginal repair pays the endpoint gap
up to its Nash tolerance, measured relative to pure Continue. -/
theorem quittingRootExpectedPayoff_update_ownMarginal_ge_pureContinue_add_gap_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (marginal : PMF Bool) {ε : ℝ}
    (hnash : IsεQuittingRootEndpointNash reward tail ε
      (Function.update root who marginal)) :
    quittingRootExpectedPayoff reward tail
        (Function.update root who marginal) who ≥
      quittingRootExpectedPayoff reward tail
        (Function.update root who (PMF.pure false)) who +
        quittingRootEndpointDifference reward tail root who - ε := by
  have hregret := (hnash who).1
  rw [quittingRootEndpointDifference_update_ownMarginal] at hregret
  have hregret' :
      (marginal false).toReal *
          quittingRootEndpointDifference reward tail root who ≤ ε := by
    simpa using hregret
  have hsum : (marginal false).toReal + (marginal true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one marginal
  have hquitNonneg : 0 ≤ (marginal true).toReal := ENNReal.toReal_nonneg
  have hcontinueNonneg : 0 ≤ (marginal false).toReal := ENNReal.toReal_nonneg
  have hshift := quittingRootExpectedPayoff_update_ownMarginal_sub_pureContinue
    reward tail root who marginal
  have hdecomp :
      (marginal true).toReal *
          quittingRootEndpointDifference reward tail root who +
        (marginal false).toReal *
          quittingRootEndpointDifference reward tail root who =
        quittingRootEndpointDifference reward tail root who := by
    calc
      _ = ((marginal false).toReal + (marginal true).toReal) *
          quittingRootEndpointDifference reward tail root who := by ring
      _ = quittingRootEndpointDifference reward tail root who := by
        rw [hsum]
        ring
  nlinarith [hregret', hdecomp, hshift]

/-- If a support-local approximate endpoint condition has tolerance strictly
below a positive Quit-minus-Continue gap, Continue cannot remain supported.
The Boolean marginal normalization then forces sure Quit. -/
theorem quitProbability_eq_one_of_supportEndpointApproxNash_of_tolerance_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (δ : ℝ) (root : ι → PMF Bool) (who : ι)
    (hsupport : IsQuittingRootSupportApproxNash reward tail δ root)
    (htolerance : δ < quittingRootEndpointDifference reward tail root who) :
    (root who false).toReal = 0 ∧ (root who true).toReal = 1 := by
  have hcontinueNonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  have hcontinue : (root who false).toReal = 0 := by
    apply le_antisymm
    · by_contra hpositive
      have hpositive' : 0 < (root who false).toReal := lt_of_not_ge hpositive
      have hbound := (hsupport who).2 hpositive'
      linarith
    · exact hcontinueNonneg
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  constructor
  · exact hcontinue
  · nlinarith

/-- Own-coordinate-only repair form.  The endpoint gap is evaluated on the
opponents' original root, while the support-local condition may be checked on
any replacement marginal for `who`. -/
theorem ownMarginal_repair_is_sureQuit_of_supportEndpointApproxNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (δ : ℝ) (root : ι → PMF Bool) (who : ι)
    (marginal : PMF Bool)
    (hsupport : IsQuittingRootSupportApproxNash reward tail δ
      (Function.update root who marginal))
    (htolerance : δ < quittingRootEndpointDifference reward tail root who) :
    ((Function.update root who marginal) who false).toReal = 0 ∧
      ((Function.update root who marginal) who true).toReal = 1 := by
  apply quitProbability_eq_one_of_supportEndpointApproxNash_of_tolerance_lt
    reward tail δ (Function.update root who marginal) who hsupport
  simpa only [quittingRootEndpointDifference_update_ownMarginal] using htolerance

/-- A positive endpoint gain in an exact fixed-tail root forces sure Quit.

The conclusion is stronger than merely excluding an inactive coordinate: an
exact root cannot carry a positive endpoint gain at an interior marginal.
-/
theorem quitProbability_eq_one_of_positive_endpointDifference_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hpositive : 0 < quittingRootEndpointDifference reward tail root who) :
    (root who true).toReal = 1 := by
  have hendpoint := (hnash who).1
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hcontinueNonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  have hquitNonneg : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hcontinue : (root who false).toReal = 0 := by
    nlinarith
  nlinarith

/-- A negative endpoint gain in an exact fixed-tail root forces sure Continue.
-/
theorem quitProbability_eq_zero_of_negative_endpointDifference_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hnegative : quittingRootEndpointDifference reward tail root who < 0) :
    (root who true).toReal = 0 := by
  have hendpoint := (hnash who).2
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hcontinueNonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  have hquitNonneg : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hquit : (root who true).toReal = 0 := by
    nlinarith
  exact hquit

/-- The fixed-tail collision/support alternative at one coordinate.

Every exact product root either sits on the sure-Quit face or has a
nonpositive Quit-minus-Continue gain.  Thus a strict positive inactive-Quit
defect cannot be removed by activating that coordinate while retaining an
interior marginal and the same continuation target.
-/
theorem sureQuit_or_nonpositive_endpointDifference_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) :
    (root who true).toReal = 1 ∨
      quittingRootEndpointDifference reward tail root who ≤ 0 := by
  by_cases hquit : (root who true).toReal = 1
  · exact Or.inl hquit
  · right
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    have hcontinue : 0 < (root who false).toReal := by
      have hnonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
      apply lt_of_le_of_ne hnonneg
      intro hzero
      apply hquit
      nlinarith [hsum]
    have hendpoint := (hnash who).1
    nlinarith

/-- The dual alternative for a strict negative endpoint gain. -/
theorem sureContinue_or_nonnegative_endpointDifference_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) :
    (root who true).toReal = 0 ∨
      0 ≤ quittingRootEndpointDifference reward tail root who := by
  by_cases hquit : (root who true).toReal = 0
  · exact Or.inl hquit
  · right
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    have hquitpos : 0 < (root who true).toReal := by
      have hnonneg : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
      apply lt_of_le_of_ne hnonneg
      intro hzero
      apply hquit
      exact hzero.symm
    have hendpoint := (hnash who).2
    nlinarith

/-- A strict positive Quit defect at an inactive coordinate rules out exact
endpoint Nash for that same fixed continuation target.  This is the direct
support-boundary diagnostic used by the conditioned singleton-tight branch.
-/
theorem not_isZeroNash_of_inactive_strictQuitGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hzero : (root who true).toReal = 0)
    (hpositive : 0 < quittingRootEndpointDifference reward tail root who) :
    ¬ IsεQuittingRootEndpointNash reward tail 0 root := by
  intro hnash
  have hnonpos := quittingRootEndpointDifference_nonpos_of_quitProbability_eq_zero
    reward tail root who hnash hzero
  linarith

end GameTheory
