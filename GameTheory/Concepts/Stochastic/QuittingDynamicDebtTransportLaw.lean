/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteDynamicDebt

/-!
# The exact transport law for the finite dynamic debt

`quittingFiniteDynamicDebt` is defined by a raw Bellman maximum, and
`QuittingFiniteDynamicDebtChains.lean` records only the coarse upper bound
`debt ≤ opponentSurvivalWeight * terminalDebt` obtained by discarding local
strictness.  This file records the exact backward recursion and its
unrolled closed form, valid under the same one-step residual-zero
hypothesis used by that bound.

At a live stage, define the *stage gap* `quittingStageGap` as how much the
fixed-opponents quit value exceeds the fixed-opponents continue value under
the prescribed tail.  Under residual-zero the raw Bellman maximum recursion
collapses to

`debt start (fuel + 1) = max 0 (continueMass * debt (start + 1) fuel -
  max 0 (stageGap start))`,

which is `quittingFiniteDynamicDebt_succ_eq_max_zero_stageGap`.  Unrolling
this from the terminal boundary gives the closed form

`debt start fuel = max 0 (survivalWeight * terminalDebt -
  Σ survivalWeight * max 0 stageGap)`,

which is `quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps`.
Since the subtracted sum is nonnegative, this closed form immediately
implies the coarse survival-weighted bound; that implication is recorded as
a consistency check on the closed form, not as a replacement for the
existing theorem.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The stage gap: how much the fixed-opponents quit value at a live stage
exceeds the fixed-opponents continue value evaluated at the prescribed next
value.  This is the quantity whose positive part is annihilated from the
transported debt at each step. -/
def quittingStageGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) : ℝ :=
  quittingFixedOpponentsQuitValue reward roots who time -
    (quittingFixedOpponentsContinueReward reward roots who time +
      quittingFixedOpponentsContinueMass roots who time * prescribed (time + 1))

/-- Shifting a common summand `Γ` out of a difference of two maxima. -/
theorem max_sub_max_eq_of_add_eq (Q Γ y : ℝ) :
    max Q (Γ + y) - max Q Γ = max (Q - Γ) y - max (Q - Γ) 0 := by
  have heq : Γ + (Q - Γ) = Q := by ring
  have e1 : max Q (Γ + y) = Γ + max (Q - Γ) y := by
    have hshift := add_max Γ (Q - Γ) y
    rw [heq] at hshift
    exact hshift.symm
  have e2 : max Q Γ = Γ + max (Q - Γ) 0 := by
    have hshift := add_max Γ (Q - Γ) 0
    rw [heq, add_zero] at hshift
    exact hshift.symm
  rw [e1, e2]
  ring

/-- For a nonnegative `x`, subtracting `max h 0` from `max h x` agrees with
flooring `x - max h 0` at zero.  This is the elementary real-number fact
underlying the one-step transport law; it fails without `0 ≤ x`. -/
theorem max_sub_max_zero_eq_max_zero_sub_of_nonneg {h x : ℝ} (hx : 0 ≤ x) :
    max h x - max h 0 = max 0 (x - max 0 h) := by
  rcases le_total h 0 with hh | hh
  · rw [max_eq_right (hh.trans hx), max_eq_right hh, max_eq_left hh, sub_zero,
      max_eq_right hx]
  · rw [max_eq_left hh, max_eq_right hh]
    rcases le_total h x with hhx | hhx
    · rw [max_eq_right hhx, max_eq_right (show (0 : ℝ) ≤ x - h by linarith)]
    · rw [max_eq_left hhx, sub_self, max_eq_left (show x - h ≤ 0 by linarith)]

/-- Flooring at zero absorbs a nested flooring: subtracting a nonnegative
`z` from `max 0 Y` and flooring again agrees with subtracting `z` from `Y`
directly and flooring once. -/
theorem max_zero_sub_of_nonneg {Y z : ℝ} (hz : 0 ≤ z) :
    max 0 (max 0 Y - z) = max 0 (Y - z) := by
  rcases le_total 0 Y with hY | hY
  · rw [max_eq_right hY]
  · rw [max_eq_left hY, max_eq_left (show (0 : ℝ) - z ≤ 0 by linarith),
      max_eq_left (show Y - z ≤ 0 by linarith)]

/-- The defining one-step exact dynamic-debt recursion, collapsed under
residual-zero to the positive-part stage-gap form: transported next debt
minus the positive part of the current stage gap, floored at zero. -/
theorem quittingFiniteDynamicDebt_succ_eq_max_zero_stageGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (start fuel : ℕ)
    (hresidual :
      quittingPrescribedOneStepResidual reward roots who prescribed start = 0) :
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start (fuel + 1) =
      max 0
        (quittingFixedOpponentsContinueMass roots who start *
            quittingFiniteDynamicDebt reward roots who prescribed
              terminalDebt (start + 1) fuel -
          max 0 (quittingStageGap reward roots who prescribed start)) := by
  set q := quittingFixedOpponentsContinueMass roots who start with hqdef
  set d' := quittingFiniteDynamicDebt reward roots who prescribed
    terminalDebt (start + 1) fuel with hd'def
  set Q := quittingFixedOpponentsQuitValue reward roots who start with hQdef
  set Γ := quittingFixedOpponentsContinueReward reward roots who start +
    q * prescribed (start + 1) with hΓdef
  have hgap : quittingStageGap reward roots who prescribed start = Q - Γ := by
    unfold quittingStageGap
    rw [← hQdef, ← hqdef, ← hΓdef]
  have hpres : prescribed start = max Q Γ := by
    have hres' := hresidual
    unfold quittingPrescribedOneStepResidual quittingLiveBellmanValue at hres'
    rw [← hQdef, ← hqdef] at hres'
    linarith
  have hd'_nonneg : 0 ≤ d' := by
    rw [hd'def]
    exact quittingFiniteDynamicDebt_nonneg reward roots who prescribed
      hprescribed hterminalDebt (start + 1) fuel
  have hq_nonneg : 0 ≤ q := by
    rw [hqdef]
    exact quittingStationaryContinueMass_nonneg
      (Function.update (roots start) who (PMF.pure false))
  have hx_nonneg : 0 ≤ q * d' := mul_nonneg hq_nonneg hd'_nonneg
  have hstep : quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
      start (fuel + 1) = max Q (Γ + q * d') - max Q Γ := by
    rw [quittingFiniteDynamicDebt_succ, hpres]
    congr 2
    rw [hΓdef]
    ring
  calc
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start (fuel + 1) = max Q (Γ + q * d') - max Q Γ := hstep
    _ = max (Q - Γ) (q * d') - max (Q - Γ) 0 :=
        max_sub_max_eq_of_add_eq Q Γ (q * d')
    _ = max 0 (q * d' - max 0 (Q - Γ)) :=
        max_sub_max_zero_eq_max_zero_sub_of_nonneg hx_nonneg
    _ = max 0 (q * d' - max 0 (quittingStageGap reward roots who prescribed start)) := by
        rw [hgap]

/-- The unrolled exact dynamic-debt law: the transported terminal debt
minus the accumulated survival-weighted positive stage gaps, floored at
zero.  Only residual-zero on the traversed window `[start, start + fuel)`
is used, matching the localized hypothesis of the coarse survival-weighted
bound. -/
theorem quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel =
        max 0
          (quittingOpponentSurvivalWeight roots who start fuel * terminalDebt -
            ∑ offset ∈ Finset.range fuel,
              quittingOpponentSurvivalWeight roots who start offset *
                max 0 (quittingStageGap reward roots who prescribed
                  (start + offset))) := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro _
      simp only [quittingFiniteDynamicDebt_zero, quittingOpponentSurvivalWeight,
        Finset.range_zero, Finset.prod_empty, Finset.sum_empty, one_mul, sub_zero]
      exact (max_eq_right hterminalDebt).symm
  | succ fuel ih =>
      intro hwindow
      have hstart : start < bound := by omega
      have htailWindow : start + 1 + fuel ≤ bound := by omega
      have hres_start := hresidual start hstart
      have hstep := quittingFiniteDynamicDebt_succ_eq_max_zero_stageGap
        reward roots who prescribed hprescribed hterminalDebt start fuel hres_start
      rw [hstep, ih (start + 1) htailWindow]
      have hq_nonneg : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      -- Move the nonnegative continue mass inside the inner floor, then
      -- absorb the nested floor using `max_zero_sub_of_nonneg`.
      rw [mul_max_of_nonneg _ _ hq_nonneg, mul_zero,
        max_zero_sub_of_nonneg (le_max_left 0
          (quittingStageGap reward roots who prescribed start))]
      congr 1
      have hW : quittingOpponentSurvivalWeight roots who start (fuel + 1) =
          quittingFixedOpponentsContinueMass roots who start *
            quittingOpponentSurvivalWeight roots who (start + 1) fuel := by
        rw [show fuel + 1 = 1 + fuel by omega, quittingOpponentSurvivalWeight_add]
        have hone : quittingOpponentSurvivalWeight roots who start 1 =
            quittingFixedOpponentsContinueMass roots who start := by
          simp [quittingOpponentSurvivalWeight]
        rw [hone]
      have hS : (∑ offset ∈ Finset.range (fuel + 1),
            quittingOpponentSurvivalWeight roots who start offset *
              max 0 (quittingStageGap reward roots who prescribed (start + offset))) =
          max 0 (quittingStageGap reward roots who prescribed start) +
            quittingFixedOpponentsContinueMass roots who start *
              ∑ offset ∈ Finset.range fuel,
                quittingOpponentSurvivalWeight roots who (start + 1) offset *
                  max 0 (quittingStageGap reward roots who prescribed
                    (start + 1 + offset)) := by
        rw [Finset.sum_range_succ' (fun offset =>
          quittingOpponentSurvivalWeight roots who start offset *
            max 0 (quittingStageGap reward roots who prescribed (start + offset)))]
        have hzero : quittingOpponentSurvivalWeight roots who start 0 = 1 := by
          simp [quittingOpponentSurvivalWeight]
        rw [hzero, one_mul, add_comm]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset _
        have hshift : quittingOpponentSurvivalWeight roots who start (offset + 1) =
            quittingFixedOpponentsContinueMass roots who start *
              quittingOpponentSurvivalWeight roots who (start + 1) offset := by
          rw [show offset + 1 = 1 + offset by omega, quittingOpponentSurvivalWeight_add]
          have hone : quittingOpponentSurvivalWeight roots who start 1 =
              quittingFixedOpponentsContinueMass roots who start := by
            simp [quittingOpponentSurvivalWeight]
          rw [hone]
        rw [hshift, show start + (offset + 1) = start + 1 + offset by omega]
        ring
      rw [hW, hS]
      ring

/-- **Consistency check.**  The unrolled closed form implies the coarse
survival-weighted bound of `quittingFiniteDynamicDebt_le_survival_mul_terminalDebt_on`,
since the accumulated stage-gap sum being subtracted is nonnegative.  This
is not a restatement of that theorem: it is proved independently from the
closed form above, and its agreement with the earlier one-sided theorem is
the intended faithfulness check on the closed form. -/
theorem quittingFiniteDynamicDebt_le_survival_mul_terminalDebt_on_of_transportLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel ≤
        quittingOpponentSurvivalWeight roots who start fuel * terminalDebt := by
  intro start fuel hwindow
  rw [quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps
    reward roots who prescribed hprescribed hterminalDebt bound hresidual
    start fuel hwindow]
  have hsum_nonneg :
      0 ≤ ∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          max 0 (quittingStageGap reward roots who prescribed (start + offset)) := by
    apply Finset.sum_nonneg
    intro offset _
    exact mul_nonneg (quittingOpponentSurvivalWeight_nonneg roots who start offset)
      (le_max_left 0 _)
  have hweight_nonneg : 0 ≤ quittingOpponentSurvivalWeight roots who start fuel :=
    quittingOpponentSurvivalWeight_nonneg roots who start fuel
  apply max_le
  · exact mul_nonneg hweight_nonneg hterminalDebt
  · linarith

/-! ## Corollaries of the transport law -/

/-- **Fence-free equality.**  If every stage gap on the traversed window is
nonpositive, the positive-part floor in the transport law never activates,
and the exact dynamic debt equals the plain transported terminal debt.
This strengthens the general `≤` bound to an equality. -/
theorem quittingFiniteDynamicDebt_eq_survivalWeight_mul_terminalDebt_of_stageGap_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0)
    (hgap : ∀ time, time < bound →
      quittingStageGap reward roots who prescribed time ≤ 0) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel =
        quittingOpponentSurvivalWeight roots who start fuel * terminalDebt := by
  intro start fuel hwindow
  rw [quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps
    reward roots who prescribed hprescribed hterminalDebt bound hresidual
    start fuel hwindow]
  have hsum_zero :
      (∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          max 0 (quittingStageGap reward roots who prescribed (start + offset))) = 0 := by
    apply Finset.sum_eq_zero
    intro offset hoffset
    have hle : quittingStageGap reward roots who prescribed (start + offset) ≤ 0 :=
      hgap (start + offset) (by
        have := Finset.mem_range.mp hoffset
        omega)
    rw [max_eq_left hle, mul_zero]
  rw [hsum_zero, sub_zero]
  exact max_eq_right (mul_nonneg
    (quittingOpponentSurvivalWeight_nonneg roots who start fuel) hterminalDebt)

/-- **Monotone in the terminal debt.**  Raising the terminal debt (while
keeping it nonnegative) never decreases the exact dynamic debt: the
subtracted stage-gap sum does not depend on the terminal debt, and the
transported term scales monotonically with it. -/
theorem quittingFiniteDynamicDebt_mono_terminalDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt terminalDebt' : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (hle : terminalDebt ≤ terminalDebt')
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel ≤
        quittingFiniteDynamicDebt reward roots who prescribed terminalDebt'
          start fuel := by
  intro start fuel hwindow
  rw [quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps
        reward roots who prescribed hprescribed hterminalDebt bound hresidual
        start fuel hwindow,
      quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps
        reward roots who prescribed hprescribed (hterminalDebt.trans hle) bound hresidual
        start fuel hwindow]
  exact max_le_max le_rfl (sub_le_sub_right
    (mul_le_mul_of_nonneg_left hle
      (quittingOpponentSurvivalWeight_nonneg roots who start fuel)) _)

/-- **Zero terminal debt gives zero debt.**  With no terminal debt to
transport, the transported term vanishes and the subtracted stage-gap sum
is nonnegative, so the outer floor collapses the whole expression to
zero. -/
theorem quittingFiniteDynamicDebt_eq_zero_of_terminalDebt_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingFiniteDynamicDebt reward roots who prescribed 0 start fuel = 0 := by
  intro start fuel hwindow
  rw [quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps
    reward roots who prescribed hprescribed le_rfl bound hresidual start fuel hwindow]
  have hsum_nonneg :
      0 ≤ ∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          max 0 (quittingStageGap reward roots who prescribed (start + offset)) :=
    Finset.sum_nonneg fun offset _ => mul_nonneg
      (quittingOpponentSurvivalWeight_nonneg roots who start offset) (le_max_left 0 _)
  rw [mul_zero, zero_sub]
  exact max_eq_left (by linarith)

/-- **The stage gap ignores its own coordinate.**  `quittingStageGap` at
`time` reads `roots time` only through `Function.update (roots time) who _`,
which overwrites the `who` marginal before it is ever read.  Consequently
replacing `roots time who` by an arbitrary `ρ` leaves the stage gap at
`time` unchanged. -/
theorem quittingStageGap_update_own_marginal_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) (ρ : PMF Bool) :
    quittingStageGap reward
        (Function.update roots time (Function.update (roots time) who ρ))
        who prescribed time =
      quittingStageGap reward roots who prescribed time := by
  simp [quittingStageGap, quittingFixedOpponentsQuitValue,
    quittingFixedOpponentsContinueReward, quittingFixedOpponentsContinueMass,
    Function.update_idem]

end GameTheory
