/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingRelaxedCycleGain
import GameTheory.Concepts.Stochastic.QuittingBehaviorPureTimeExtremality

/-!
# Pure quit-time extremality against a periodic root sequence

Fix a coordinate `who`, a period `m + 1`, and a root sequence
`roots : ℕ → ι → PMF Bool` that is periodic with that period
(`quittingPeriodicRoots_shift_mul`).  The one-period companion composite
`quittingCompanionComposite reward roots who 0 (m + 1)` of
`QuittingCycleMismatchContraction.lean` then has, by contraction, at most one
real fixed point whenever the deleted survival product is strictly below one.

This file identifies that fixed point with the supremum over **pure
quit-time** deviations of the infinite-horizon value
`quittingRootSequencePureTimeTerminalValue` of
`QuittingInfinitePureTimeExtremality.lean`: the standard "optimal-stopping
value equals the Bellman fixed point" argument, specialized to a periodic
one-player scalar Snell envelope.  Composed with the already-landed
behavioral pure-time reduction
(`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`QuittingBehaviorPureTimeExtremality.lean`) and with the fixed-point
construction of `QuittingRelaxedCycleGain.lean`
(`quittingCompanionComposite_prescribed_add_gain_eq`), the closing theorem of
this file expresses the supremum over **all** unilateral behavioral
deviations from a profile whose live root is periodic as the prescribed
value at the cycle's start plus `quittingRelaxedCycleGain`.

## What is proved

* `quittingCompanionComposite_mono` -- the composite is monotone in its
  continuation argument.
* `quittingCompanionComposite_comp` -- composites over adjacent windows
  concatenate.
* `quittingCompanionComposite_shift_period`,
  `quittingCompanionComposite_shift_period_mul` -- shifting a window's start
  by whole periods does not change the composite, given periodicity of
  `roots`.
* `quittingRootSequencePureTimeTerminalValue_le_companionComposite` --
  quitting at an absolute time is dominated by the composite over the
  traversed window, seeded at the quit value reached at the far end.  This
  direction needs no periodicity or fixed-point hypothesis.
* `quittingCompanionComposite_quitValue_le_of_fixed` -- within one period,
  every quit value is dominated by a fixed point of the one-period composite.
* `sSup_range_quittingRootSequencePureTimeTerminalValue_le_of_fixed` --
  **the cap dominates every pure quit-time deviation**: given periodicity and
  a fixed point `cap` of the one-period composite, the supremum of the pure
  quit-time values (including `Never`) is at most `cap`.  No reward bound is
  needed for this direction.
* `sSup_range_quittingRootSequencePureTimeTerminalValue_ge_of_fixed` --
  **the cap is attained in the limit**: `cap` is at most that same supremum,
  via convergence of the zero-terminal finite-horizon Snell recursion.
* `sSup_range_quittingRootSequencePureTimeTerminalValue_eq_of_fixed` --
  **the main identity**: the two inequalities combine to the exact value,
  proving the supremum over pure quit-time deviations of a periodic root
  sequence equals the companion map's cyclic fixed point.
* `sSup_range_quittingTerminalPayoff_update_eq_prescribed_add_gain` --
  composed with the pure-time behavioral reduction and with
  `QuittingRelaxedCycleGain.lean`'s fixed-point construction: the supremum
  over **all** unilateral behavioral deviations equals `prescribed 0 +
  quittingRelaxedCycleGain reward roots prescribed who m`, for a profile
  whose live root sequence is periodic and prescribed-value-consistent.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Structural lemmas about the companion composite -/

/-- The companion composite is monotone in its continuation argument. -/
theorem quittingCompanionComposite_mono
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) {x y : ℝ}
    (hxy : x ≤ y) :
    quittingCompanionComposite reward roots who start fuel x ≤
      quittingCompanionComposite reward roots who start fuel y := by
  induction fuel generalizing start with
  | zero => simpa using hxy
  | succ fuel ih =>
      rw [quittingCompanionComposite_succ, quittingCompanionComposite_succ]
      unfold quittingRootCompanionMap
      have hscaled :
          quittingRootDeletedContinueMass (roots start) who *
              quittingCompanionComposite reward roots who (start + 1) fuel x ≤
            quittingRootDeletedContinueMass (roots start) who *
              quittingCompanionComposite reward roots who (start + 1) fuel y :=
        mul_le_mul_of_nonneg_left (ih (start + 1))
          (quittingRootDeletedContinueMass_nonneg (roots start) who)
      exact max_le_max le_rfl (by linarith)

/-- Composing the composite over a first window then a second window equals
the composite over their concatenation. -/
theorem quittingCompanionComposite_comp
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start a b : ℕ) (c : ℝ) :
    quittingCompanionComposite reward roots who start (a + b) c =
      quittingCompanionComposite reward roots who start a
        (quittingCompanionComposite reward roots who (start + a) b c) := by
  induction a generalizing start with
  | zero => simp
  | succ a ih =>
      have hlhs : a + 1 + b = (a + b) + 1 := by omega
      rw [hlhs, quittingCompanionComposite_succ, ih (start + 1),
        quittingCompanionComposite_succ]
      have hidx : start + 1 + a = start + (a + 1) := by omega
      rw [hidx]

/-- Shifting a window's start by one full period does not change the
composite, when `roots` is periodic with that period. -/
theorem quittingCompanionComposite_shift_period
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ)
    (hperiodic : ∀ k, roots (k + (m + 1)) = roots k)
    (start fuel : ℕ) (c : ℝ) :
    quittingCompanionComposite reward roots who (start + (m + 1)) fuel c =
      quittingCompanionComposite reward roots who start fuel c := by
  induction fuel generalizing start with
  | zero => simp
  | succ fuel ih =>
      rw [quittingCompanionComposite_succ, quittingCompanionComposite_succ,
        hperiodic start]
      have hidx : start + (m + 1) + 1 = start + 1 + (m + 1) := by omega
      rw [hidx, ih (start + 1)]

/-- Shifting a window's start by whole periods does not change the
composite. -/
theorem quittingCompanionComposite_shift_period_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ)
    (hperiodic : ∀ k, roots (k + (m + 1)) = roots k)
    (turns start fuel : ℕ) (c : ℝ) :
    quittingCompanionComposite reward roots who
        (start + turns * (m + 1)) fuel c =
      quittingCompanionComposite reward roots who start fuel c := by
  induction turns generalizing start with
  | zero => simp
  | succ turns ih =>
      have hidx : start + (turns + 1) * (m + 1) =
          (start + (m + 1)) + turns * (m + 1) := by ring
      rw [hidx, ih (start + (m + 1)),
        quittingCompanionComposite_shift_period reward roots who m hperiodic]

/-- A one-period fixed point stays fixed after any whole number of extra
periods. -/
theorem quittingCompanionComposite_period_mul_fixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ)
    (hperiodic : ∀ k, roots (k + (m + 1)) = roots k)
    {cap : ℝ} (hfixed : quittingCompanionComposite reward roots who 0
      (m + 1) cap = cap) (turns : ℕ) :
    quittingCompanionComposite reward roots who 0 (turns * (m + 1)) cap =
      cap := by
  induction turns with
  | zero => simp
  | succ turns ih =>
      have hsplit : (turns + 1) * (m + 1) = (m + 1) + turns * (m + 1) := by
        ring
      have hshift := quittingCompanionComposite_shift_period reward roots who
        m hperiodic 0 (turns * (m + 1)) cap
      rw [zero_add] at hshift
      rw [hsplit, quittingCompanionComposite_comp, zero_add, hshift, ih,
        hfixed]

omit [Fintype ι] [DecidableEq ι] in
/-- A periodic root sequence agrees at indices differing by whole
periods. -/
theorem quittingPeriodicRoots_shift_mul
    (roots : ℕ → ι → PMF Bool) (m : ℕ)
    (hperiodic : ∀ k, roots (k + (m + 1)) = roots k)
    (turns k : ℕ) :
    roots (k + turns * (m + 1)) = roots k := by
  induction turns generalizing k with
  | zero => simp
  | succ turns ih =>
      have hidx : k + (turns + 1) * (m + 1) =
          (k + (m + 1)) + turns * (m + 1) := by ring
      rw [hidx, ih (k + (m + 1)), hperiodic k]

/-! ## Pure-time values against the companion composite -/

/-- Quitting exactly now has terminal value the immediate deleted quit
value. -/
theorem quittingRootSequencePureTimeTerminalValue_some_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some start) start =
      quittingRootDeletedQuitValue reward (roots start) who := by
  unfold quittingRootSequencePureTimeTerminalValue
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
    quittingRootDeletedQuitValue_eq_fixedOpponents]
  simp

/-- **Pure-time domination by the companion composite.**  Quitting at the
absolute time `start + fuel`, evaluated from `start`, is dominated by the
`fuel`-window composite seeded at the quit value reached at the far end.  No
periodicity or fixed-point hypothesis is used. -/
theorem quittingRootSequencePureTimeTerminalValue_le_companionComposite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some (start + fuel)) start ≤
      quittingCompanionComposite reward roots who start fuel
        (quittingRootDeletedQuitValue reward (roots (start + fuel)) who) := by
  induction fuel generalizing start with
  | zero =>
      simpa using
        le_of_eq (quittingRootSequencePureTimeTerminalValue_some_self
          reward roots who start)
  | succ fuel ih =>
      have hstep := ih (start + 1)
      rw [show start + 1 + fuel = start + (fuel + 1) by omega] at hstep
      have hgoal : quittingRootSequencePureTimeTerminalValue reward roots who
          (some (start + (fuel + 1))) start =
        quittingRootDeletedContinueReward reward (roots start) who +
          quittingRootDeletedContinueMass (roots start) who *
            quittingRootSequencePureTimeTerminalValue reward roots who
              (some (start + (fuel + 1))) (start + 1) := by
        unfold quittingRootSequencePureTimeTerminalValue
        rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
          quittingRootDeletedContinueReward_eq_fixedOpponents,
          quittingRootDeletedContinueMass_eq_fixedOpponents]
        have hne : start ≠ start + (fuel + 1) := by omega
        rw [quittingPureTimeHazard_some_of_ne hne]
        simp
      rw [hgoal, quittingCompanionComposite_succ]
      have hmass := quittingRootDeletedContinueMass_nonneg (roots start) who
      have hscaled := mul_le_mul_of_nonneg_left hstep hmass
      unfold quittingRootCompanionMap
      exact le_trans (by linarith) (le_max_right _ _)

/-! ## The cap dominates every pure quit-time deviation -/

/-- Within one period, every quit value is dominated by a fixed point of
the one-period composite. -/
theorem quittingCompanionComposite_quitValue_le_of_fixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ) {cap : ℝ}
    (hfixed : quittingCompanionComposite reward roots who 0 (m + 1) cap = cap)
    {r : ℕ} (hr : r ≤ m) :
    quittingCompanionComposite reward roots who 0 r
        (quittingRootDeletedQuitValue reward (roots r) who) ≤ cap := by
  have hqle : quittingRootDeletedQuitValue reward (roots r) who ≤
      quittingCompanionComposite reward roots who r (m + 1 - r) cap := by
    have hpos : m + 1 - r = (m - r) + 1 := by omega
    rw [hpos, quittingCompanionComposite_succ]
    unfold quittingRootCompanionMap
    exact le_max_left _ _
  have hmono := quittingCompanionComposite_mono reward roots who 0 r hqle
  have hcomp := quittingCompanionComposite_comp reward roots who 0 r
    (m + 1 - r) cap
  rw [zero_add] at hcomp
  rw [← hcomp, show r + (m + 1 - r) = m + 1 by omega, hfixed] at hmono
  exact hmono

/-- **Every finite quit-time value is dominated by a fixed point.**  No
attainment or boundedness hypothesis is used: this is purely the "no policy
beats the Bellman value" half of optimal-stopping extremality. -/
theorem quittingRootSequencePureTimeTerminalValue_some_le_of_fixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ)
    (hperiodic : ∀ k, roots (k + (m + 1)) = roots k)
    {cap : ℝ} (hfixed : quittingCompanionComposite reward roots who 0
      (m + 1) cap = cap) (N : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some N) 0 ≤ cap := by
  have hle := quittingRootSequencePureTimeTerminalValue_le_companionComposite
    reward roots who 0 N
  rw [zero_add] at hle
  refine hle.trans ?_
  obtain ⟨j, r, hrle, hN⟩ : ∃ j r, r ≤ m ∧ j * (m + 1) + r = N := by
    refine ⟨N / (m + 1), N % (m + 1), ?_, ?_⟩
    · have hlt := Nat.mod_lt N (show 0 < m + 1 by omega)
      omega
    · rw [mul_comm]
      exact Nat.div_add_mod N (m + 1)
  have hQeq : roots N = roots r := by
    have hshift := quittingPeriodicRoots_shift_mul roots m hperiodic j r
    rw [show r + j * (m + 1) = N by omega] at hshift
    exact hshift
  rw [hQeq, ← hN]
  have hcomp := quittingCompanionComposite_comp reward roots who 0
    (j * (m + 1)) r (quittingRootDeletedQuitValue reward (roots r) who)
  rw [zero_add] at hcomp
  have hshiftComp := quittingCompanionComposite_shift_period_mul reward roots
    who m hperiodic j 0 r (quittingRootDeletedQuitValue reward (roots r) who)
  rw [zero_add] at hshiftComp
  rw [hcomp, hshiftComp]
  have hHle := quittingCompanionComposite_quitValue_le_of_fixed reward roots
    who m hfixed hrle
  have hmono := quittingCompanionComposite_mono reward roots who 0
    (j * (m + 1)) hHle
  have hperiod := quittingCompanionComposite_period_mul_fixed reward roots
    who m hperiodic hfixed j
  rw [hperiod] at hmono
  exact hmono

/-! ## The never-quitting value -/

omit [DecidableEq ι] in
/-- The terminal value of a root-sequence profile is invariant under
shifting the start by one full period, given periodicity of `roots`. -/
theorem quittingRootSequenceTerminalValue_shift_period
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ)
    (hperiodic : ∀ k, roots (k + (m + 1)) = roots k) (start : ℕ) :
    quittingRootSequenceTerminalValue reward roots who (start + (m + 1)) =
      quittingRootSequenceTerminalValue reward roots who start := by
  have hprofile : quittingRootSequenceProfile reward roots (start + (m + 1)) =
      quittingRootSequenceProfile reward roots start := by
    funext player time _
    unfold quittingRootSequenceProfile
    have hidx : start + (m + 1) + time = start + time + (m + 1) := by omega
    rw [hidx, hperiodic (start + time)]
  unfold quittingRootSequenceTerminalValue
  rw [hprofile]

omit [Fintype ι] in
/-- The never-quit update sequence is periodic whenever `roots` is,
since the never-quit hazard is a constant coordinate. -/
theorem quittingRootSequenceUpdate_none_periodic
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ)
    (hperiodic : ∀ k, roots (k + (m + 1)) = roots k) (k : ℕ) :
    quittingRootSequenceUpdate roots who (quittingPureTimeHazard none)
        (k + (m + 1)) =
      quittingRootSequenceUpdate roots who (quittingPureTimeHazard none)
        k := by
  unfold quittingRootSequenceUpdate
  rw [hperiodic k, quittingPureTimeHazard_none, quittingPureTimeHazard_none]

/-- The never-quit terminal value is invariant under shifting the start by
one full period. -/
theorem quittingRootSequencePureTimeTerminalValue_none_shift_period
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ)
    (hperiodic : ∀ k, roots (k + (m + 1)) = roots k) (start : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who none
        (start + (m + 1)) =
      quittingRootSequencePureTimeTerminalValue reward roots who none
        start := by
  unfold quittingRootSequencePureTimeTerminalValue
    quittingRootSequenceHazardTerminalValue
  rw [quittingRootSequenceTerminalValue_shift_period reward
    (quittingRootSequenceUpdate roots who (quittingPureTimeHazard none)) who m
    (quittingRootSequenceUpdate_none_periodic roots who m hperiodic) start]

/-- The never-quit value satisfies the exact (no-choice) continuation
recursion at every time. -/
theorem quittingRootSequencePureTimeTerminalValue_none_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (t : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who none t =
      quittingRootDeletedContinueReward reward (roots t) who +
        quittingRootDeletedContinueMass (roots t) who *
          quittingRootSequencePureTimeTerminalValue reward roots who none
            (t + 1) := by
  unfold quittingRootSequencePureTimeTerminalValue
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
    quittingRootDeletedContinueReward_eq_fixedOpponents,
    quittingRootDeletedContinueMass_eq_fixedOpponents]
  simp

/-- Within one period, the companion composite seeded at `cap` at least
matches one companion-map step forward. -/
theorem le_quittingCompanionComposite_of_le_m
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ) (cap : ℝ) {t : ℕ}
    (ht : t ≤ m) :
    quittingRootDeletedContinueReward reward (roots t) who +
        quittingRootDeletedContinueMass (roots t) who *
          quittingCompanionComposite reward roots who (t + 1) (m - t) cap ≤
      quittingCompanionComposite reward roots who t (m + 1 - t) cap := by
  have hpos : m + 1 - t = (m - t) + 1 := by omega
  rw [hpos, quittingCompanionComposite_succ]
  unfold quittingRootCompanionMap
  exact le_max_right _ _

/-- **The finite chain bounding the never-quit gap.**  Survival-weighted, the
gap between the windowed composite (seeded at `cap`) and the never-quit value
never grows across a phase, for every offset up to the period boundary. -/
theorem quittingCompanionComposite_never_survival_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ) {cap : ℝ}
    (hfixed : quittingCompanionComposite reward roots who 0 (m + 1) cap =
      cap) :
    ∀ t, t ≤ m + 1 →
      quittingOpponentSurvivalWeight roots who 0 t *
          (quittingCompanionComposite reward roots who t (m + 1 - t) cap -
            quittingRootSequencePureTimeTerminalValue reward roots who
              none t) ≤
        cap - quittingRootSequencePureTimeTerminalValue reward roots who
          none 0 := by
  intro t
  induction t with
  | zero =>
      intro _
      have h0 : m + 1 - 0 = m + 1 := by omega
      rw [h0, hfixed]
      simp [quittingOpponentSurvivalWeight]
  | succ t ih =>
      intro ht
      have htm : t ≤ m := by omega
      have hprev := ih (by omega)
      have hstepIneq := le_quittingCompanionComposite_of_le_m reward roots who
        m cap htm
      have hrec := quittingRootSequencePureTimeTerminalValue_none_succ reward
        roots who t
      have hmt : m - t = m + 1 - (t + 1) := by omega
      rw [hmt] at hstepIneq
      have hAC :
          quittingRootDeletedContinueMass (roots t) who *
              (quittingCompanionComposite reward roots who (t + 1)
                  (m + 1 - (t + 1)) cap -
                quittingRootSequencePureTimeTerminalValue reward roots who
                  none (t + 1)) ≤
            quittingCompanionComposite reward roots who t (m + 1 - t) cap -
              quittingRootSequencePureTimeTerminalValue reward roots who
                none t := by nlinarith [hstepIneq, hrec]
      have hW0 := quittingOpponentSurvivalWeight_nonneg roots who 0 t
      have hscaled : quittingOpponentSurvivalWeight roots who 0 t *
          (quittingRootDeletedContinueMass (roots t) who *
              (quittingCompanionComposite reward roots who (t + 1)
                  (m + 1 - (t + 1)) cap -
                quittingRootSequencePureTimeTerminalValue reward roots who
                  none (t + 1))) ≤
          quittingOpponentSurvivalWeight roots who 0 t *
            (quittingCompanionComposite reward roots who t (m + 1 - t) cap -
              quittingRootSequencePureTimeTerminalValue reward roots who
                none t) :=
        mul_le_mul_of_nonneg_left hAC hW0
      have hWsucc : quittingOpponentSurvivalWeight roots who 0 (t + 1) =
          quittingOpponentSurvivalWeight roots who 0 t *
            quittingRootDeletedContinueMass (roots t) who := by
        rw [quittingOpponentSurvivalWeight_succ, zero_add,
          quittingRootDeletedContinueMass_eq_fixedOpponents]
      rw [hWsucc, mul_assoc]
      exact le_trans hscaled hprev

/-- **The never-quit value is dominated by a fixed point.**  Together with
`quittingRootSequencePureTimeTerminalValue_some_le_of_fixed`, this completes
the "cap dominates every pure quit-time deviation" half of optimal-stopping
extremality. -/
theorem quittingRootSequencePureTimeTerminalValue_none_le_of_fixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ)
    (hperiodic : ∀ k, roots (k + (m + 1)) = roots k)
    {cap : ℝ} (hfixed : quittingCompanionComposite reward roots who 0
      (m + 1) cap = cap)
    (hP : quittingOpponentSurvivalWeight roots who 0 (m + 1) < 1) :
    quittingRootSequencePureTimeTerminalValue reward roots who none 0 ≤
      cap := by
  have hchain := quittingCompanionComposite_never_survival_le reward roots
    who m hfixed (m + 1) le_rfl
  rw [show m + 1 - (m + 1) = 0 from by omega,
    quittingCompanionComposite_zero] at hchain
  have hshift := quittingRootSequencePureTimeTerminalValue_none_shift_period
    reward roots who m hperiodic 0
  rw [zero_add] at hshift
  rw [hshift] at hchain
  nlinarith [hchain, hP]

/-- **The cap dominates every pure quit-time deviation.**  Assembled from
the genuine finite quit times and the never-quit alternative: whenever
`roots` is periodic and `cap` is a fixed point of the one-period companion
composite, `cap` is an upper bound for the whole pure-time value set. -/
theorem sSup_range_quittingRootSequencePureTimeTerminalValue_le_of_fixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ)
    (hperiodic : ∀ k, roots (k + (m + 1)) = roots k)
    {cap : ℝ} (hfixed : quittingCompanionComposite reward roots who 0
      (m + 1) cap = cap)
    (hP : quittingOpponentSurvivalWeight roots who 0 (m + 1) < 1) :
    sSup (Set.range fun quitTime : Option ℕ =>
      quittingRootSequencePureTimeTerminalValue reward roots who
        quitTime 0) ≤ cap := by
  apply csSup_le
  · exact ⟨quittingRootSequencePureTimeTerminalValue reward roots who none 0,
      ⟨none, rfl⟩⟩
  · rintro _ ⟨quitTime, rfl⟩
    cases quitTime with
    | none =>
        exact quittingRootSequencePureTimeTerminalValue_none_le_of_fixed
          reward roots who m hperiodic hfixed hP
    | some N =>
        exact quittingRootSequencePureTimeTerminalValue_some_le_of_fixed
          reward roots who m hperiodic hfixed N

/-! ## The cap is attained in the limit -/

/-- Iterating the one-period companion composite `j` times agrees with the
composite over `j` whole periods, given periodicity of `roots`. -/
theorem quittingCompanionComposite_iterate_eq_period_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ)
    (hperiodic : ∀ k, roots (k + (m + 1)) = roots k) (j : ℕ) (c : ℝ) :
    (quittingCompanionComposite reward roots who 0 (m + 1))^[j] c =
      quittingCompanionComposite reward roots who 0 (j * (m + 1)) c := by
  induction j generalizing c with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      have hshift := quittingCompanionComposite_shift_period reward roots
        who m hperiodic 0 (j * (m + 1)) c
      rw [zero_add] at hshift
      have hcomp := quittingCompanionComposite_comp reward roots who 0
        (m + 1) (j * (m + 1)) c
      rw [zero_add, hshift] at hcomp
      rw [show (j + 1) * (m + 1) = (m + 1) + j * (m + 1) by ring, hcomp]

/-- **Every zero-terminal composite value is attained by some finite
pure-time choice.**  Constructive: the induction produces the maximizing
choice directly, never invoking a generic finite-maximum principle. -/
theorem exists_quittingFinitePureTimePayoff_ge_companionComposite_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    ∃ choice : Fin (fuel + 1),
      quittingCompanionComposite reward roots who start fuel 0 ≤
        quittingFinitePureTimePayoff reward roots who start fuel choice := by
  induction fuel generalizing start with
  | zero => exact ⟨0, le_refl _⟩
  | succ fuel ih =>
      obtain ⟨choice', hchoice'⟩ := ih (start + 1)
      have hQ : quittingRootDeletedQuitValue reward (roots start) who =
          quittingFinitePureTimePayoff reward roots who start (fuel + 1)
            0 := by
        rw [quittingRootDeletedQuitValue_eq_fixedOpponents]
        rfl
      have hCeq :
          quittingRootDeletedContinueReward reward (roots start) who +
            quittingRootDeletedContinueMass (roots start) who *
              quittingFinitePureTimePayoff reward roots who (start + 1) fuel
                choice' =
          quittingFinitePureTimePayoff reward roots who start (fuel + 1)
            choice'.succ := by
        rw [quittingRootDeletedContinueReward_eq_fixedOpponents,
          quittingRootDeletedContinueMass_eq_fixedOpponents]
        rfl
      have hmass := quittingRootDeletedContinueMass_nonneg (roots start) who
      have hC :
          quittingRootDeletedContinueReward reward (roots start) who +
            quittingRootDeletedContinueMass (roots start) who *
              quittingCompanionComposite reward roots who (start + 1) fuel
                0 ≤
          quittingFinitePureTimePayoff reward roots who start (fuel + 1)
            choice'.succ := by
        rw [← hCeq]
        nlinarith [mul_le_mul_of_nonneg_left hchoice' hmass]
      have hle : quittingCompanionComposite reward roots who start
          (fuel + 1) 0 ≤
        max (quittingFinitePureTimePayoff reward roots who start (fuel + 1)
              0)
          (quittingFinitePureTimePayoff reward roots who start (fuel + 1)
            choice'.succ) := by
        rw [quittingCompanionComposite_succ]
        unfold quittingRootCompanionMap
        rw [hQ]
        exact max_le_max le_rfl hC
      rcases le_total
          (quittingFinitePureTimePayoff reward roots who start (fuel + 1) 0)
          (quittingFinitePureTimePayoff reward roots who start (fuel + 1)
            choice'.succ) with hcmp | hcmp
      · exact ⟨choice'.succ, by rwa [max_eq_right hcmp] at hle⟩
      · exact ⟨0, by rwa [max_eq_left hcmp] at hle⟩

/-- The zero-boundary continue-throughout finite payoff converges to the
never-quit infinite value. -/
theorem tendsto_quittingFiniteRootPayoff_none_pureTimeTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    Tendsto (fun fuel => quittingFiniteRootPayoff reward roots who
        (quittingPureTimeHazard none) 0 fuel)
      atTop (nhds (quittingRootSequencePureTimeTerminalValue reward roots
        who none 0)) := by
  simpa [quittingRootSequencePureTimeTerminalValue,
    quittingRootSequenceHazardTerminalValue, quittingRootSequenceTerminalValue]
    using tendsto_quittingFiniteRootPayoff_terminal reward roots who
      (quittingPureTimeHazard none) 0

/-- **The cap is attained in the limit.**  Zero-terminal finite-horizon
Snell recursions over whole periods converge to `cap`; each is dominated by
some finite pure-time choice, whose value is within `ε` of the supremum. -/
theorem sSup_range_quittingRootSequencePureTimeTerminalValue_ge_of_fixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ)
    (hperiodic : ∀ k, roots (k + (m + 1)) = roots k)
    {cap : ℝ} (hfixed : quittingCompanionComposite reward roots who 0
      (m + 1) cap = cap)
    (hP : quittingOpponentSurvivalWeight roots who 0 (m + 1) < 1)
    {M : ℝ} (hM : 0 ≤ M) (hreward : ∀ S player, |reward S player| ≤ M) :
    cap ≤ sSup (Set.range fun quitTime : Option ℕ =>
      quittingRootSequencePureTimeTerminalValue reward roots who
        quitTime 0) := by
  have hbdd : BddAbove (Set.range fun quitTime : Option ℕ =>
      quittingRootSequencePureTimeTerminalValue reward roots who
        quitTime 0) :=
    bddAbove_range_quittingRootSequencePureTimeTerminalValue reward roots who
      hM hreward
  apply le_of_forall_pos_le_add
  intro ε hε
  have hneverTendsto :=
    tendsto_quittingFiniteRootPayoff_none_pureTimeTerminalValue reward roots
      who
  obtain ⟨fuelThreshold, hfuelThreshold⟩ :=
    (Metric.tendsto_atTop.mp hneverTendsto) ε hε
  have hneverBound : ∀ fuel, fuelThreshold ≤ fuel →
      quittingFiniteRootPayoff reward roots who
        (quittingPureTimeHazard none) 0 fuel ≤
        quittingRootSequencePureTimeTerminalValue reward roots who none 0 +
          ε := by
    intro fuel hfuel
    have hbound := hfuelThreshold fuel hfuel
    rw [Real.dist_eq] at hbound
    have := (abs_lt.mp hbound).2
    linarith
  have hboundedComposite : ∀ fuel, fuelThreshold ≤ fuel →
      quittingCompanionComposite reward roots who 0 fuel 0 ≤
        sSup (Set.range fun quitTime : Option ℕ =>
          quittingRootSequencePureTimeTerminalValue reward roots who
            quitTime 0) + ε := by
    intro fuel hfuel
    obtain ⟨choice, hchoice⟩ :=
      exists_quittingFinitePureTimePayoff_ge_companionComposite_zero reward
        roots who 0 fuel
    refine hchoice.trans ?_
    refine Fin.lastCases ?_ (fun offset => ?_) choice
    · rw [quittingFinitePureTimePayoff_last_eq_neverFinite]
      calc
        quittingFiniteRootPayoff reward roots who
            (quittingPureTimeHazard none) 0 fuel ≤
          quittingRootSequencePureTimeTerminalValue reward roots who none
            0 + ε := hneverBound fuel hfuel
        _ ≤ sSup (Set.range fun quitTime : Option ℕ =>
              quittingRootSequencePureTimeTerminalValue reward roots who
                quitTime 0) + ε := by
          linarith [le_csSup hbdd (⟨none, rfl⟩ :
            quittingRootSequencePureTimeTerminalValue reward roots who none
                0 ∈ Set.range fun quitTime : Option ℕ =>
              quittingRootSequencePureTimeTerminalValue reward roots who
                quitTime 0)]
    · rw [quittingFinitePureTimePayoff_castSucc_eq_terminal]
      simp only [Nat.zero_add]
      calc
        quittingRootSequencePureTimeTerminalValue reward roots who
            (some offset.val) 0 ≤
          sSup (Set.range fun quitTime : Option ℕ =>
              quittingRootSequencePureTimeTerminalValue reward roots who
                quitTime 0) :=
          le_csSup hbdd ⟨some offset.val, rfl⟩
        _ ≤ sSup (Set.range fun quitTime : Option ℕ =>
              quittingRootSequencePureTimeTerminalValue reward roots who
                quitTime 0) + ε := by linarith
  have htendstoIter := tendsto_iterate_quittingCompanionComposite reward roots
    who (m + 1) hfixed hP 0
  have htendstoPeriod : Tendsto (fun j : ℕ =>
      quittingCompanionComposite reward roots who 0 (j * (m + 1)) 0)
      atTop (nhds cap) := by
    have heq : (fun j : ℕ =>
        quittingCompanionComposite reward roots who 0 (j * (m + 1)) 0) =
      (fun j : ℕ =>
        (quittingCompanionComposite reward roots who 0 (m + 1))^[j] 0) := by
      funext j
      exact (quittingCompanionComposite_iterate_eq_period_mul reward roots
        who m hperiodic j 0).symm
    rw [heq]
    exact htendstoIter
  have hjThreshold : ∀ᶠ j : ℕ in atTop, fuelThreshold ≤ j * (m + 1) := by
    have hdiv : Tendsto (fun j : ℕ => j * (m + 1)) atTop atTop :=
      Filter.tendsto_atTop_mono
        (fun j => Nat.le_mul_of_pos_right j (Nat.succ_pos m)) tendsto_id
    exact hdiv.eventually_ge_atTop fuelThreshold
  have hcapLe : cap ≤ sSup (Set.range fun quitTime : Option ℕ =>
      quittingRootSequencePureTimeTerminalValue reward roots who
        quitTime 0) + ε := by
    apply le_of_tendsto htendstoPeriod
    filter_upwards [hjThreshold] with j hj
    exact hboundedComposite (j * (m + 1)) hj
  linarith [hcapLe]

/-! ## The main identity, and the behavioral consequence -/

/-- **The main identity.**  The supremum over pure quit-time deviations of a
periodic root sequence equals the companion map's cyclic fixed point: the
standard "optimal-stopping value equals the Bellman fixed point" argument. -/
theorem sSup_range_quittingRootSequencePureTimeTerminalValue_eq_of_fixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (m : ℕ)
    (hperiodic : ∀ k, roots (k + (m + 1)) = roots k)
    {cap : ℝ} (hfixed : quittingCompanionComposite reward roots who 0
      (m + 1) cap = cap)
    (hP : quittingOpponentSurvivalWeight roots who 0 (m + 1) < 1)
    {M : ℝ} (hM : 0 ≤ M) (hreward : ∀ S player, |reward S player| ≤ M) :
    sSup (Set.range fun quitTime : Option ℕ =>
      quittingRootSequencePureTimeTerminalValue reward roots who
        quitTime 0) = cap :=
  le_antisymm
    (sSup_range_quittingRootSequencePureTimeTerminalValue_le_of_fixed
      reward roots who m hperiodic hfixed hP)
    (sSup_range_quittingRootSequencePureTimeTerminalValue_ge_of_fixed
      reward roots who m hperiodic hfixed hP hM hreward)

/-- **The behavioral consequence.**  Composed with the pure-time reduction of
`QuittingBehaviorPureTimeExtremality.lean` and the fixed-point construction
of `QuittingRelaxedCycleGain.lean`: for a profile whose live root sequence is
periodic and prescribed-value-consistent, the supremum over **all**
unilateral behavioral deviations equals the prescribed value at the cycle's
start plus the signed phasewise accumulation `quittingRelaxedCycleGain`. -/
theorem sSup_range_quittingTerminalPayoff_update_eq_prescribed_add_gain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (prescribed : ℕ → ℝ) (m : ℕ)
    (hprescribed : IsQuittingLivePrescribedValue reward
      (quittingProfileLiveRoot reward profile) who prescribed)
    (hwrap : prescribed (m + 1) = prescribed 0)
    (hperiodic : ∀ k, quittingProfileLiveRoot reward profile (k + (m + 1)) =
      quittingProfileLiveRoot reward profile k)
    (hP : quittingOpponentSurvivalWeight
      (quittingProfileLiveRoot reward profile) who 0 (m + 1) < 1)
    {M : ℝ} (hM : 0 ≤ M) (hreward : ∀ S player, |reward S player| ≤ M) :
    sSup (Set.range fun deviation :
        (quittingGame reward).BehaviorStrategy who =>
      quittingTerminalPayoff reward
        (Function.update profile who deviation) who) =
      prescribed 0 + quittingRelaxedCycleGain reward
        (quittingProfileLiveRoot reward profile) prescribed who m := by
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime reward profile who
    hM hreward]
  have hpureEq : (fun quitTime : Option ℕ => quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who quitTime)) who) =
      (fun quitTime : Option ℕ =>
        quittingRootSequencePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward profile) who quitTime 0) := by
    funext quitTime
    exact quittingTerminalPayoff_update_pureTimeBehaviorStrategy reward
      profile who quitTime
  rw [hpureEq]
  have hcap := quittingCompanionComposite_prescribed_add_gain_eq reward
    (quittingProfileLiveRoot reward profile) who prescribed m hprescribed
    hwrap hP
  exact sSup_range_quittingRootSequencePureTimeTerminalValue_eq_of_fixed
    reward (quittingProfileLiveRoot reward profile) who m hperiodic hcap hP
    hM hreward

end GameTheory
