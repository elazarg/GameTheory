/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCycleMismatchContraction
import GameTheory.Concepts.Stochastic.QuittingBellmanTelescope

/-!
# The signed phasewise accumulation is the companion-map gain of a relaxed cycle

Fix a coordinate `who` and a periodic root sequence `roots : ℕ → ι → PMF Bool` together
with a *prescribed* scalar payoff sequence `prescribed : ℕ → ℝ` that is self-consistent
(`IsQuittingLivePrescribedValue`) but is **not** assumed to be any kind of Nash
equilibrium.  `QuittingCycleMismatchContraction.lean` already treats the case where
`prescribed` is *exactly* endpoint-Nash against itself: there the companion map's own
cyclic fixed point coincides with `prescribed`, so the anchored mismatch is zero
(`quittingCyclicContinuationBlock_mismatch_eq_zero`).  This file drops that hypothesis
entirely and computes the *gap* between the companion map's cyclic fixed point and
`prescribed` in closed form.

This file formalizes the claim that the signed phasewise
accumulation of the local gaps ... equals the gain exactly.  The **local gap** at phase
`k` is `quittingRootEndpointDifference reward (fun _ => prescribed (k + 1)) (roots k) who`
(`g_k` below), and the **gain** is identified here with the amount
by which the companion map's own cyclic fixed point exceeds `prescribed 0` -- this is
exactly what "gain of a relaxed cycle" means once the companion-map machinery already
proved in `QuittingCycleMismatchContraction.lean` is applied without the exact-Nash
hypothesis.

## Re-derivation, and where it strengthens the reported claim

The claim above states the identity under a *relaxed complementarity* hypothesis
(`IsεQuittingRootEndpointNash` at some defect `ε`, matched exactly against the source's
own equations (5)-(6) once the two one-sided defect inequalities are read jointly).  The
re-derivation carried out to build this file establishes the identity **without any
complementarity hypothesis at all**: it is a statement purely about the companion-map
recursion versus the value recursion `quittingRootSuccessorPayoff`, and complementarity
is only what a *separate* argument would need to bound the local gaps by `ε` (the
`ε C₁` envelope of the reported claim, reusing `Math/CyclicMaxAffineBound.lean`, not
reproved here).  So the identity below is strictly more general than what was asked for.

The re-derivation also rechecked the reported closed form's outer `max {0, ...}` term
(reported equations (13), (18), (38)).  That "0" branch is *not* part of the abstract
max-affine recursion's solution -- solving the bare two-branch recursion
`d_k = max {α_k, β_k + q_k d_{k+1}}` around the cycle gives `max {stopGap, contGap}`
with **no** outer `0`.  The reported text calls the "0" "redundant... once one uses K2"
without pinning down why.  The reason is elementary and does not need the pure-time
reduction K2 at all: since `p_k := (roots k who true).toReal` and
`q_k := quittingRootDeletedContinueMass (roots k) who` both lie in `[0, 1]`, the two
local weights `α_k = (1 - p_k) * g_k` and `β_k = -p_k * g_k` always have `α_k * β_k ≤ 0`
(a probability weight and its complement cannot both make the same-signed local gap
strictly worse), so `max {α_k, β_k} ≥ 0` at every phase; chaining this around a cycle
with survival product `< 1` forces the whole cyclic solution to be `≥ 0`.  So the outer
`0` is true but genuinely redundant, for a reason internal to the recursion, not an
appeal to feasibility of "not deviating."  This fact is not needed for the identity
below (which only needs the base-point value, not its sign), so it is not formalized
here, but it is recorded as a checked correction to the reported proof sketch.

## What is proved

* `quittingSignedStopWeight`, `quittingSignedContinueWeight` -- the two signed local
  weights `α_k = (1 - p_k) g_k` and `β_k = -p_k g_k` of the reported equations (9)-(10).
* `quittingSignedStopGap`, `quittingSignedContinueGap` -- the finite unrolled stop and
  continuation excess over a window of `m + 1` phases (reported equations (11)-(19)).
* `quittingRelaxedCycleGain` -- the **signed phasewise accumulation**
  `max {stopGap, contGap / (1 - P)}`, the reported `Q_{i,1}` (equations (23)-(26)).
* `quittingCompanionComposite_sub_prescribed_eq` -- the exact finite identity
  expressing `quittingCompanionComposite` applied at any continuation, minus
  `prescribed`, as this signed max-affine expression.  Purely algebraic; consumes only
  the value recursion `IsQuittingLivePrescribedValue`, no complementarity.
* `quittingCompanionComposite_prescribed_add_gain_eq` -- **the main identity**: adding
  `quittingRelaxedCycleGain` to `prescribed 0` gives a fixed point of the one-period
  companion composite.
* `quittingRelaxedCycleGain_unique` -- that fixed point, and hence the gain, is unique.
* `quittingRelaxedCycleGain_eq_zero_iff` -- **necessary and sufficient**: the signed
  accumulation vanishes iff the companion composite's cyclic fixed point already equals
  `prescribed 0`, i.e. iff there is no deviation incentive to correct.

## The behavioral supremum

Identifying `quittingRelaxedCycleGain` with the literal supremum over *all* behavioral
deviations (`quittingTerminalPayoff` over `Function.update profile who deviation`) needs
two further ingredients: (1) the pure-time reduction of that supremum to pure quit-time
deviations (`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`QuittingBehaviorPureTimeExtremality.lean`), and (2) the fact that the supremum over pure
quit-time deviations of a periodic live root sequence equals the companion composite's
cyclic fixed point constructed here -- a "value of an infinite-horizon optimal-stopping
problem equals its Bellman fixed point" argument.  Both are proved in
`QuittingPeriodicPureTimeBellman.lean`
(`sSup_range_quittingRootSequencePureTimeTerminalValue_eq_of_fixed` supplies (2)); its
closing theorem `sSup_range_quittingTerminalPayoff_update_eq_prescribed_add_gain` composes
them with `quittingCompanionComposite_prescribed_add_gain_eq` below to identify the
supremum over all unilateral behavioral deviations, for a profile whose live root sequence
is periodic, with `prescribed 0 + quittingRelaxedCycleGain`.  Consequently "gain" in this
file already means exactly the literal supremum over behavioral deviations under that
periodicity hypothesis, matching what `QuittingCycleMismatchContraction.lean`'s existing
"mismatch" means in the exact-Nash case (there `prescribed` itself is the fixed point, so
the gap is `0`); this file's identity is the strict generalization of that gap to the
case where `prescribed` need not be any kind of Nash value.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The two signed local weights -/

/-- The **stopping weight** `α_k = (1 - p_k) * g_k`: the signed excess of quitting
outright at phase `k`, relative to the prescribed value `prescribed k`, where
`g_k = quittingRootEndpointDifference reward (fun _ => prescribed (k + 1)) (roots k) who`
is the local gap between quitting and continuing. -/
def quittingSignedStopWeight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ) (who : ι) (k : ℕ) : ℝ :=
  (1 - (roots k who true).toReal) *
    quittingRootEndpointDifference reward (fun _ => prescribed (k + 1)) (roots k) who

/-- The **continuation weight** `β_k = -p_k * g_k`: the signed excess charged for
continuing through phase `k` rather than matching the prescribed mixture there. -/
def quittingSignedContinueWeight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ) (who : ι) (k : ℕ) : ℝ :=
  -(roots k who true).toReal *
    quittingRootEndpointDifference reward (fun _ => prescribed (k + 1)) (roots k) who

/-! ## The finite unrolled stop and continuation excess -/

/-- The best signed excess obtainable by continuing for some `ℓ ≤ m` phases starting at
`k` and then stopping, i.e. `max_{0 ≤ ℓ ≤ m} H_{k,ℓ}` in the reported notation.  The
window has `m + 1` phases; `m` (rather than a `period` requiring `Nat` subtraction) is
the natural induction variable. -/
def quittingSignedStopGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ) (who : ι) : ℕ → ℕ → ℝ
  | k, 0 => quittingSignedStopWeight reward roots prescribed who k
  | k, m + 1 =>
      max (quittingSignedStopWeight reward roots prescribed who k)
        (quittingSignedContinueWeight reward roots prescribed who k +
          quittingRootDeletedContinueMass (roots k) who *
            quittingSignedStopGap reward roots prescribed who (k + 1) m)

/-- The signed excess of continuing through all `m + 1` phases starting at `k`, i.e.
`B_k` in the reported notation. -/
def quittingSignedContinueGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ) (who : ι) : ℕ → ℕ → ℝ
  | k, 0 => quittingSignedContinueWeight reward roots prescribed who k
  | k, m + 1 =>
      quittingSignedContinueWeight reward roots prescribed who k +
        quittingRootDeletedContinueMass (roots k) who *
          quittingSignedContinueGap reward roots prescribed who (k + 1) m

/-! ## The signed phasewise accumulation -/

/-- The **signed phasewise accumulation**, the reported `Q_{i,1}`: the larger of the best
finite stopping excess and the geometric continue-forever excess over the survival
product of a period of length `m + 1`. -/
def quittingRelaxedCycleGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ) (who : ι) (m : ℕ) : ℝ :=
  max (quittingSignedStopGap reward roots prescribed who 0 m)
    (quittingSignedContinueGap reward roots prescribed who 0 m /
      (1 - quittingOpponentSurvivalWeight roots who 0 (m + 1)))

/-! ## The per-step algebraic identity -/

/-- **One companion-map step, relative to the prescribed value.**  Purely algebraic:
consumes only the value recursion `hprescribed`, no complementarity or Nash hypothesis. -/
theorem quittingRootCompanionMap_sub_prescribed_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (k : ℕ) (c : ℝ) :
    quittingRootCompanionMap reward (roots k) who c - prescribed k =
      max (quittingSignedStopWeight reward roots prescribed who k)
        (quittingSignedContinueWeight reward roots prescribed who k +
          quittingRootDeletedContinueMass (roots k) who * (c - prescribed (k + 1))) := by
  have hp := hprescribed k
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quittingRootQuitPayoff_eq_deletedQuitValue,
    quittingRootContinuePayoff_eq_deleted] at hp
  have hsum := quittingRoot_continueProbability_add_quitProbability (roots k) who
  have hqneg : (roots k who false).toReal = 1 - (roots k who true).toReal := by linarith
  rw [hqneg] at hp
  unfold quittingRootCompanionMap quittingSignedStopWeight quittingSignedContinueWeight
    quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_eq_deletedQuitValue, quittingRootContinuePayoff_eq_deleted,
    ← max_sub_sub_right]
  congr 1
  · linear_combination -hp
  · linear_combination -hp

/-! ## The finite unrolled identity -/

/-- **The finite unrolled identity.**  By induction on the window length `m + 1`: the
one-period companion composite, applied at any real continuation `c` and compared against
the prescribed value at the window's start, equals the signed max-affine expression built
from the stop and continuation gaps.  Purely algebraic; only `hprescribed` is used, no
complementarity or Nash hypothesis anywhere. -/
theorem quittingCompanionComposite_sub_prescribed_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed) :
    ∀ (m k : ℕ) (c : ℝ),
      quittingCompanionComposite reward roots who k (m + 1) c - prescribed k =
        max (quittingSignedStopGap reward roots prescribed who k m)
          (quittingSignedContinueGap reward roots prescribed who k m +
            quittingOpponentSurvivalWeight roots who k (m + 1) *
              (c - prescribed (k + (m + 1)))) := by
  intro m
  induction m with
  | zero =>
      intro k c
      have hstep := quittingRootCompanionMap_sub_prescribed_eq reward roots who prescribed
        hprescribed k c
      rw [quittingCompanionComposite_succ, quittingCompanionComposite_zero] at *
      rw [hstep]
      have hweight : quittingOpponentSurvivalWeight roots who k 1 =
          quittingRootDeletedContinueMass (roots k) who := by
        rw [quittingRootDeletedContinueMass_eq_fixedOpponents]
        simp [quittingOpponentSurvivalWeight]
      rw [hweight]
      rfl
  | succ m ih =>
      intro k c
      rw [quittingCompanionComposite_succ]
      have hstep := quittingRootCompanionMap_sub_prescribed_eq reward roots who prescribed
        hprescribed k (quittingCompanionComposite reward roots who (k + 1) (m + 1) c)
      rw [hstep, ih (k + 1) c]
      have hweight : quittingRootDeletedContinueMass (roots k) who *
          quittingOpponentSurvivalWeight roots who (k + 1) (m + 1) =
          quittingOpponentSurvivalWeight roots who k (m + 1 + 1) := by
        rw [quittingRootDeletedContinueMass_eq_fixedOpponents]
        exact (quittingOpponentSurvivalWeight_succ_left roots who k (m + 1)).symm
      have hindex : k + 1 + (m + 1) = k + (m + 1 + 1) := by omega
      rw [show quittingSignedStopGap reward roots prescribed who k (m + 1) =
          max (quittingSignedStopWeight reward roots prescribed who k)
            (quittingSignedContinueWeight reward roots prescribed who k +
              quittingRootDeletedContinueMass (roots k) who *
                quittingSignedStopGap reward roots prescribed who (k + 1) m) from rfl,
        show quittingSignedContinueGap reward roots prescribed who k (m + 1) =
          quittingSignedContinueWeight reward roots prescribed who k +
            quittingRootDeletedContinueMass (roots k) who *
              quittingSignedContinueGap reward roots prescribed who (k + 1) m from rfl,
        mul_max_of_nonneg _ _ (quittingRootDeletedContinueMass_nonneg (roots k) who),
        add_max, ← max_assoc, mul_add, ← mul_assoc, hweight, hindex]
      congr 1
      ring

/-! ## Solving the single self-referential equation -/

/-- **The scalar self-reference solves to the reported closed form.**  This is the case
split behind `quittingRelaxedCycleGain`: `max {M, N}` with `N = B / (1 - P)` is the unique
solution of `X = max {M, B + P * X}` when `P < 1`. -/
theorem quittingSignedCycleFixedPointEq (M B P : ℝ) (hP : P < 1) :
    max M (B + P * max M (B / (1 - P))) = max M (B / (1 - P)) := by
  have hpos : (0 : ℝ) < 1 - P := by linarith
  have hne : (1 : ℝ) - P ≠ 0 := ne_of_gt hpos
  rcases le_total M (B / (1 - P)) with h | h
  · rw [max_eq_right h,
      show B + P * (B / (1 - P)) = B / (1 - P) from by field_simp; ring,
      max_eq_right h]
  · rw [max_eq_left h]
    have hB : B ≤ M * (1 - P) := by rw [div_le_iff₀ hpos] at h; exact h
    exact max_eq_left (by nlinarith [hB])

/-! ## The main identity -/

/-- **The main identity.**  Adding the signed phasewise accumulation to the prescribed
value at the start of the cycle gives a fixed point of the one-period companion
composite -- the precise sense in which the signed phasewise accumulation is the gain of
a relaxed cycle.  No
complementarity or Nash hypothesis is used: only the value recursion `hprescribed`, the
wraparound `hwrap`, and the survival bound `hP`. -/
theorem quittingCompanionComposite_prescribed_add_gain_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ) (m : ℕ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (hwrap : prescribed (m + 1) = prescribed 0)
    (hP : quittingOpponentSurvivalWeight roots who 0 (m + 1) < 1) :
    quittingCompanionComposite reward roots who 0 (m + 1)
        (prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m) =
      prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m := by
  have hkey := quittingCompanionComposite_sub_prescribed_eq reward roots who prescribed
    hprescribed m 0 (prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m)
  simp only [zero_add] at hkey
  rw [hwrap,
    show prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m -
        prescribed 0 = quittingRelaxedCycleGain reward roots prescribed who m from by ring]
    at hkey
  have hfix := quittingSignedCycleFixedPointEq
    (quittingSignedStopGap reward roots prescribed who 0 m)
    (quittingSignedContinueGap reward roots prescribed who 0 m)
    (quittingOpponentSurvivalWeight roots who 0 (m + 1)) hP
  unfold quittingRelaxedCycleGain at hkey ⊢
  rw [hfix] at hkey
  linarith [hkey]

/-! ## Uniqueness -/

/-- **The gap is unique.**  Any real number whose sum with `prescribed 0` is a fixed point
of the one-period companion composite already equals `quittingRelaxedCycleGain`. Reuses
the existing contraction estimate `abs_iterate_quittingCompanionComposite_sub_le` from
`QuittingCycleMismatchContraction.lean`, applied at a single iterate. -/
theorem quittingRelaxedCycleGain_unique
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ) (m : ℕ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (hwrap : prescribed (m + 1) = prescribed 0)
    (hP : quittingOpponentSurvivalWeight roots who 0 (m + 1) < 1)
    (gap : ℝ)
    (hgap : quittingCompanionComposite reward roots who 0 (m + 1) (prescribed 0 + gap) =
      prescribed 0 + gap) :
    gap = quittingRelaxedCycleGain reward roots prescribed who m := by
  have hfixed := quittingCompanionComposite_prescribed_add_gain_eq reward roots who prescribed
    m hprescribed hwrap hP
  have hstep := abs_iterate_quittingCompanionComposite_sub_le reward roots who (m + 1)
    hfixed (prescribed 0 + gap) 1
  rw [Function.iterate_one, hgap, pow_one] at hstep
  have hcollapse : |prescribed 0 + gap -
      (prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m)| ≤
      quittingOpponentSurvivalWeight roots who 0 (m + 1) *
        |prescribed 0 + gap - (prescribed 0 + quittingRelaxedCycleGain reward roots
          prescribed who m)| := hstep
  have hP0 : 0 ≤ quittingOpponentSurvivalWeight roots who 0 (m + 1) :=
    quittingOpponentSurvivalWeight_nonneg roots who 0 (m + 1)
  have habs : |prescribed 0 + gap -
      (prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m)| = 0 := by
    nlinarith [abs_nonneg (prescribed 0 + gap -
      (prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m)), hcollapse]
  have := abs_eq_zero.mp habs
  linarith [this]

/-! ## Necessary and sufficient -/

/-- **Necessary and sufficient.**  The signed phasewise accumulation vanishes exactly when
the one-period companion composite's cyclic fixed point already coincides with the cycle's
own prescribed value at the start -- i.e. exactly when there is no gap for the companion
map (the Bellman-optimal deviation value) to correct. -/
theorem quittingRelaxedCycleGain_eq_zero_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ) (m : ℕ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (hwrap : prescribed (m + 1) = prescribed 0)
    (hP : quittingOpponentSurvivalWeight roots who 0 (m + 1) < 1) :
    quittingRelaxedCycleGain reward roots prescribed who m = 0 ↔
      quittingCompanionComposite reward roots who 0 (m + 1) (prescribed 0) = prescribed 0 := by
  constructor
  · intro hzero
    have hfixed := quittingCompanionComposite_prescribed_add_gain_eq reward roots who
      prescribed m hprescribed hwrap hP
    rw [hzero, add_zero] at hfixed
    exact hfixed
  · intro hfixed
    have hzero := quittingRelaxedCycleGain_unique reward roots who prescribed m hprescribed
      hwrap hP 0 (by rwa [add_zero])
    linarith [hzero]

end GameTheory
