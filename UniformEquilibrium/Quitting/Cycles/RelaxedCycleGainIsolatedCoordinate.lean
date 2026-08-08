/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.RelaxedCycleGain
import UniformEquilibrium.Quitting.Cycles.CycleIsolatedCoordinate

/-!
# The signed phasewise accumulation at survival slope one

`QuittingRelaxedCycleGain.lean` builds the **signed phasewise accumulation**
`quittingRelaxedCycleGain` under a strict-contraction hypothesis
`P_who = quittingOpponentSurvivalWeight roots who 0 (m + 1) < 1`, dividing the
continuation gap by `1 - P_who`. `QuittingCycleIsolatedCoordinate.lean` treats
the complementary regime `P_who = 1` -- **isolation**, every opponent silent
-- entirely separately, iterating the companion composite from the solo-quit
anchor `Λ_who = max {0, r_who({who})}`
(`quittingCyclicContinuationBlock_mismatch_eq_of_isolated`,
`quittingCyclicContinuationBlock_isolated_mismatch_eq_negPart`), landing on
`[-r_who({who})]₊`.

A design note reports that these are "the same object": the signed
accumulation, evaluated at `P_who = 1`, should also equal `[-r_who({who})]₊`.
**This file computes what `quittingRelaxedCycleGain` actually evaluates to at
`P_who = 1`, and the two do not coincide.**

## What actually happens at `P_who = 1`

Under an isolated window, `quittingSignedStopGap` and
`quittingSignedContinueGap` both collapse to closed forms with **no** need for
absorption or periodicity:

* `quittingSignedStopGap_eq_of_isolatedWindow` --
  `stopGap k m = r_who({who}) - prescribed k`, independent of `m`;
* `quittingSignedContinueGap_eq_of_isolatedWindow` --
  `contGap k m = prescribed (k + m + 1) - prescribed k`, a telescoping sum.

`quittingRelaxedCycleGain`'s own closed form divides the continuation gap by
`1 - P_who`; at `P_who = 1` that denominator is `0`, and Lean's convention
`x / 0 = 0` erases the continuation branch outright, regardless of its value.
So `quittingRelaxedCycleGain reward roots prescribed who m` equals
`max 0 (r_who({who}) - prescribed 0)` (`quittingRelaxedCycleGain_eq_of_isolatedWindow`).
This is a genuine, fully general closed form, but it is **not**
`[-r_who({who})]₊` in general -- it equals that only when `prescribed 0 = 0`.

## The discrepancy

In exactly the regime the design note has in mind -- a cyclic continuation
block, where absorption plus the wraparound hypothesis force
`prescribed 0 = r_who({who})` (`QuittingCycleIsolatedCoordinate.lean`'s own
Step 2, `quittingCyclicContinuationBlock_value_eq_soloReward_of_isolated`) --
the formula above gives `max 0 0 = 0` **unconditionally**, whatever the sign
of `r_who({who})`
(`quittingRelaxedCycleGain_eq_zero_of_isolatedWindow_of_prescribed_eq_solo`).
The true isolated mismatch
(`quittingCyclicContinuationBlock_isolated_mismatch_eq_negPart`) is
`[-r_who({who})]₊`, strictly positive whenever `r_who({who}) < 0`
(`quittingRelaxedCycleGain_ne_soloQuitAnchor_sub_prescribed_of_isolatedWindow`).
The pre-existing machine-checked witness
`QuittingIsolatedNegativeSoloRegression` (`r_true({true}) = -1`, mismatch `1`)
realizes this unconditionally:
`quittingRelaxedCycleGain_ne_mismatch_isolatedNegativeSoloRegression` proves
`0 ≠ 1`.

## Why: which fixed point the closed form selects

`P_who = 1` is exactly the case where the one-period recursion
`W = max {A, T + P · W}` degenerates to `W = max {r_who({who}), W}`, whose
fixed points are the whole ray `W ≥ r_who({who})`, not a point.
`quittingRelaxedCycleGain_unique` (in `QuittingRelaxedCycleGain.lean`) pins
down the fixed point using the **contraction** estimate, which needs
`P_who < 1`; there is no such argument at `P_who = 1`. The closed-form
extension via `x / 0 = 0` happens to *also* land on a valid fixed point
(`prescribed 0 + gain = max {prescribed 0, r_who({who})}`, always
`≥ r_who({who})`), but it is the **wrong** member of the ray: it reproduces
whatever `prescribed 0` already says rather than the behavioral deviation
supremum. Only the **anchor-seeded** iterate -- starting the companion
composite from `Λ_who`, not from an arbitrary continuation or from
`prescribed 0` -- lands on the correct member
(`tendsto_iterate_soloQuitAnchor_of_isolated`); that is the selection
`quittingCyclicContinuationBlock_mismatch_eq_of_isolated` uses, and it is
**not** an instance of `quittingRelaxedCycleGain`'s closed form.

## What is proved

* The general isolated closed forms for `quittingSignedStopGap` and
  `quittingSignedContinueGap`, no absorption or periodicity needed.
* `quittingRelaxedCycleGain`'s own value at `P_who = 1`.
* The discrepancy with `[-r_who({who})]₊`, both as a general conditional
  statement and reproduced on the pre-existing machine-checked witness.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The isolated endpoint difference.** Under isolation the local gap
collapses to the target reward minus the supplied tail at `who`: quitting is
worth `r_who({who})` regardless of the tail (quitting is immediate), and
continuing is worth exactly the tail, since every opponent -- and now `who`
too, once continuing is forced -- never absorbs. -/
theorem quittingRootEndpointDifference_eq_of_isolated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {root : ι → PMF Bool} {who : ι} (hiso : IsQuittingIsolatedRoot root who) :
    quittingRootEndpointDifference reward tail root who =
      reward (quittingSingletonTerminal who) who - tail who := by
  obtain ⟨hazard, rfl⟩ :=
    (isQuittingIsolatedRoot_iff_exists_soloStationaryRoot root who).mp hiso
  unfold quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_soloStationaryRoot_owner, quittingSoloReward_self,
    quittingRootContinuePayoff_soloStationaryRoot_owner]

/-- **The isolated stop gap.** Under isolation on `[k, k + m]`, the finite
stopping excess collapses to `r_who({who}) - prescribed k`, independent of
`m`: the local gap at every phase is already forced by `hprescribed`, so
extending the window changes nothing. No absorption or wraparound needed. -/
theorem quittingSignedStopGap_eq_of_isolatedWindow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed) :
    ∀ m k, IsQuittingIsolatedWindow roots who (k + m + 1) →
      quittingSignedStopGap reward roots prescribed who k m =
        reward (quittingSingletonTerminal who) who - prescribed k := by
  intro m
  induction m with
  | zero =>
      intro k hiso
      have hisoK : IsQuittingIsolatedRoot (roots k) who := hiso k (by omega)
      have hp : prescribed k =
          (roots k who true).toReal * reward (quittingSingletonTerminal who) who +
            (roots k who false).toReal * prescribed (k + 1) := by
        rw [hprescribed k]
        exact quittingRootSuccessorPayoff_of_isolated reward
          (fun _ => prescribed (k + 1)) hisoK
      have hquit : (roots k who false).toReal = 1 - (roots k who true).toReal := by
        have := quittingRoot_continueProbability_add_quitProbability (roots k) who
        linarith
      rw [hquit] at hp
      change quittingSignedStopWeight reward roots prescribed who k = _
      unfold quittingSignedStopWeight
      rw [quittingRootEndpointDifference_eq_of_isolated reward _ hisoK]
      linear_combination hp
  | succ m ih =>
      intro k hiso
      have hisoK : IsQuittingIsolatedRoot (roots k) who := hiso k (by omega)
      have hisoRest : IsQuittingIsolatedWindow roots who (k + 1 + m + 1) :=
        fun t ht ↦ hiso t (by omega)
      have hrec := ih (k + 1) hisoRest
      have hp : prescribed k =
          (roots k who true).toReal * reward (quittingSingletonTerminal who) who +
            (roots k who false).toReal * prescribed (k + 1) := by
        rw [hprescribed k]
        exact quittingRootSuccessorPayoff_of_isolated reward
          (fun _ => prescribed (k + 1)) hisoK
      have hquit : (roots k who false).toReal = 1 - (roots k who true).toReal := by
        have := quittingRoot_continueProbability_add_quitProbability (roots k) who
        linarith
      rw [hquit] at hp
      change max (quittingSignedStopWeight reward roots prescribed who k)
          (quittingSignedContinueWeight reward roots prescribed who k +
            quittingRootDeletedContinueMass (roots k) who *
              quittingSignedStopGap reward roots prescribed who (k + 1) m) = _
      rw [hrec, quittingRootDeletedContinueMass_eq_one_of_isolated hisoK]
      unfold quittingSignedStopWeight quittingSignedContinueWeight
      rw [quittingRootEndpointDifference_eq_of_isolated reward _ hisoK]
      apply le_antisymm (max_le (le_of_eq ?_) (le_of_eq ?_)) ?_
      · linear_combination hp
      · linear_combination hp
      · refine le_trans (le_of_eq ?_) (le_max_left _ _)
        linear_combination -hp

/-- **The isolated continuation gap.** Under isolation on `[k, k + m]`, the
continuation excess telescopes exactly to `prescribed (k + m + 1) -
prescribed k`, no absorption or wraparound needed. Under an additional
periodic wraparound this vanishes -- matching `C_i = 0` in the design note --
but the pure telescoping identity holds regardless. -/
theorem quittingSignedContinueGap_eq_of_isolatedWindow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed) :
    ∀ m k, IsQuittingIsolatedWindow roots who (k + m + 1) →
      quittingSignedContinueGap reward roots prescribed who k m =
        prescribed (k + m + 1) - prescribed k := by
  intro m
  induction m with
  | zero =>
      intro k hiso
      have hisoK : IsQuittingIsolatedRoot (roots k) who := hiso k (by omega)
      have hp : prescribed k =
          (roots k who true).toReal * reward (quittingSingletonTerminal who) who +
            (roots k who false).toReal * prescribed (k + 1) := by
        rw [hprescribed k]
        exact quittingRootSuccessorPayoff_of_isolated reward
          (fun _ => prescribed (k + 1)) hisoK
      have hquit : (roots k who false).toReal = 1 - (roots k who true).toReal := by
        have := quittingRoot_continueProbability_add_quitProbability (roots k) who
        linarith
      rw [hquit] at hp
      change quittingSignedContinueWeight reward roots prescribed who k = _
      unfold quittingSignedContinueWeight
      rw [quittingRootEndpointDifference_eq_of_isolated reward _ hisoK]
      linear_combination hp
  | succ m ih =>
      intro k hiso
      have hisoK : IsQuittingIsolatedRoot (roots k) who := hiso k (by omega)
      have hisoRest : IsQuittingIsolatedWindow roots who (k + 1 + m + 1) :=
        fun t ht ↦ hiso t (by omega)
      have hrec := ih (k + 1) hisoRest
      have hidx : k + 1 + m + 1 = k + (m + 1) + 1 := by omega
      rw [hidx] at hrec
      have hp : prescribed k =
          (roots k who true).toReal * reward (quittingSingletonTerminal who) who +
            (roots k who false).toReal * prescribed (k + 1) := by
        rw [hprescribed k]
        exact quittingRootSuccessorPayoff_of_isolated reward
          (fun _ => prescribed (k + 1)) hisoK
      have hquit : (roots k who false).toReal = 1 - (roots k who true).toReal := by
        have := quittingRoot_continueProbability_add_quitProbability (roots k) who
        linarith
      rw [hquit] at hp
      change quittingSignedContinueWeight reward roots prescribed who k +
          quittingRootDeletedContinueMass (roots k) who *
            quittingSignedContinueGap reward roots prescribed who (k + 1) m = _
      rw [hrec, quittingRootDeletedContinueMass_eq_one_of_isolated hisoK]
      unfold quittingSignedContinueWeight
      rw [quittingRootEndpointDifference_eq_of_isolated reward _ hisoK]
      linear_combination hp

/-- **`quittingRelaxedCycleGain`'s own value at `P_who = 1`.** Isolation makes
the survival weight `1`, so the continuation branch of the defining `max` is
silently erased by Lean's `x / 0 = 0` convention; only the stop-gap closed
form survives, giving `max 0 (r_who({who}) - prescribed 0)`. This is a fully
general, provable closed form -- but see the module docstring for why it does
**not** compute `[-r_who({who})]₊` in the regime the design note has in
mind. -/
theorem quittingRelaxedCycleGain_eq_of_isolatedWindow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ) (m : ℕ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (hiso : IsQuittingIsolatedWindow roots who (m + 1)) :
    quittingRelaxedCycleGain reward roots prescribed who m =
      max 0 (reward (quittingSingletonTerminal who) who - prescribed 0) := by
  have hstop := quittingSignedStopGap_eq_of_isolatedWindow reward roots who prescribed
    hprescribed m 0 (by simpa using hiso)
  have hP : quittingOpponentSurvivalWeight roots who 0 (m + 1) = 1 :=
    (isQuittingIsolatedWindow_iff_opponentSurvivalWeight_eq_one roots who (m + 1)).mp hiso
  unfold quittingRelaxedCycleGain
  rw [hstop, hP]
  norm_num [max_comm]

/-- **The naive `P_who = 1` extension is identically zero once the prescribed
value already sits at the solo reward** -- exactly the case forced by
absorption plus wraparound in a cyclic continuation block -- regardless of
the sign of `r_who({who})`. This is the source of the discrepancy with the
true isolated mismatch `[-r_who({who})]₊`, which is nonzero whenever
`r_who({who}) < 0`. -/
theorem quittingRelaxedCycleGain_eq_zero_of_isolatedWindow_of_prescribed_eq_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ) (m : ℕ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (hiso : IsQuittingIsolatedWindow roots who (m + 1))
    (hval : prescribed 0 = reward (quittingSingletonTerminal who) who) :
    quittingRelaxedCycleGain reward roots prescribed who m = 0 := by
  rw [quittingRelaxedCycleGain_eq_of_isolatedWindow reward roots who prescribed m
    hprescribed hiso, hval, sub_self, max_self]

/-- **The discrepancy, as a general conditional.** Whenever `prescribed 0`
already equals the solo reward and that reward is negative, the signed
phasewise accumulation is `0` while the true isolated mismatch
`quittingPositiveSingletonDebtCap reward who - prescribed 0` (which is
`[-r_who({who})]₊` by `quittingCyclicContinuationBlock_isolated_mismatch_eq_negPart`)
is strictly positive. So `quittingRelaxedCycleGain`'s naive extension to
`P_who = 1` does not compute the isolated mismatch. -/
theorem quittingRelaxedCycleGain_ne_soloQuitAnchor_sub_prescribed_of_isolatedWindow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ) (m : ℕ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (hiso : IsQuittingIsolatedWindow roots who (m + 1))
    (hval : prescribed 0 = reward (quittingSingletonTerminal who) who)
    (hneg : reward (quittingSingletonTerminal who) who < 0) :
    quittingRelaxedCycleGain reward roots prescribed who m ≠
      quittingPositiveSingletonDebtCap reward who - prescribed 0 := by
  rw [quittingRelaxedCycleGain_eq_zero_of_isolatedWindow_of_prescribed_eq_solo reward roots who
    prescribed m hprescribed hiso hval, quittingSoloQuitAnchor_eq, hval, max_eq_left hneg.le]
  intro hcontra
  linarith

/-- **The discrepancy realized on a concrete witness.** The pre-existing
`QuittingIsolatedNegativeSoloRegression` regression instance
(`r_true({true}) = -1`, owner quits at rate `1/2`, opponent silent) has
`prescribed 0 = value true = r_true({true})`, so the signed phasewise
accumulation on it is `0`. -/
theorem quittingRelaxedCycleGain_eq_zero_isolatedNegativeSoloRegression :
    quittingRelaxedCycleGain QuittingIsolatedNegativeSoloRegression.reward
      (fun _ => QuittingIsolatedNegativeSoloRegression.root)
      (fun _ => QuittingIsolatedNegativeSoloRegression.value true) true 0 = 0 := by
  have hisoRoot : IsQuittingIsolatedRoot QuittingIsolatedNegativeSoloRegression.root true :=
    (isQuittingIsolatedRoot_iff_exists_soloStationaryRoot _ true).mpr
      ⟨QuittingIsolatedNegativeSoloRegression.hazard, rfl⟩
  apply quittingRelaxedCycleGain_eq_zero_of_isolatedWindow_of_prescribed_eq_solo
  · intro time
    change QuittingIsolatedNegativeSoloRegression.value true =
      quittingRootSuccessorPayoff QuittingIsolatedNegativeSoloRegression.reward
        (fun _ => QuittingIsolatedNegativeSoloRegression.value true)
        QuittingIsolatedNegativeSoloRegression.root true
    rw [quittingRootSuccessorPayoff_of_isolated _ _ hisoRoot]
    simp only [QuittingIsolatedNegativeSoloRegression.root, quittingSoloStationaryRoot_apply_owner,
      QuittingIsolatedNegativeSoloRegression.soloReward_true_true,
      QuittingIsolatedNegativeSoloRegression.hazard_true,
      QuittingIsolatedNegativeSoloRegression.hazard_false,
      QuittingIsolatedNegativeSoloRegression.value_true]
    norm_num
  · exact fun t _ ↦ hisoRoot
  · rfl

/-- **The discrepancy, unconditionally.** On the pre-existing witness `r_true
= -1`, the naive `P = 1` extension of the signed phasewise accumulation is
`0`, while the true isolated mismatch is `1`
(`QuittingIsolatedNegativeSoloRegression.mismatch_eq_one`). So `[-r_i({i})]₊`
is not literally `quittingRelaxedCycleGain` evaluated at `P_i = 1`. -/
theorem quittingRelaxedCycleGain_ne_mismatch_isolatedNegativeSoloRegression :
    quittingRelaxedCycleGain QuittingIsolatedNegativeSoloRegression.reward
        (fun _ => QuittingIsolatedNegativeSoloRegression.root)
        (fun _ => QuittingIsolatedNegativeSoloRegression.value true) true 0 ≠
      quittingPositiveSingletonDebtCap QuittingIsolatedNegativeSoloRegression.reward true -
        QuittingIsolatedNegativeSoloRegression.value true := by
  rw [quittingRelaxedCycleGain_eq_zero_isolatedNegativeSoloRegression,
    QuittingIsolatedNegativeSoloRegression.mismatch_eq_one]
  norm_num

end GameTheory
