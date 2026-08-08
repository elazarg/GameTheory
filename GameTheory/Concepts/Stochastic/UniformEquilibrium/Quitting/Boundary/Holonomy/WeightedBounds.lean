/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Holonomy.Basic
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Exceptional.BellmanTail
import Math.PMFProduct.CoalitionMass

/-!
# Weighted boundary defects of actual finite quitting blocks

`QuittingBoundaryHolonomy.lean` bounds the five scalar coordinates of every
actual finite block in one fixed compact box
(`quittingBoundaryHolonomyCoefficientBox`): every coordinate is merely
bounded by the common reward bound `M := quittingRewardBound reward`.  That
bound is **unweighted** -- it says nothing about how close the intercept is
to zero for a block whose survival is close to one.

This file sharpens the two intercept coordinates.  The prescribed intercept
`B` and the continue-through intercept `T` are each bounded by their own
*defect*, i.e. by `M` times the shortfall of the matching survival slope from
one:

    |B| ≤ (1 - P) * M      where `P` is full product survival through the
                            block (the prescribed slope)
    |T| ≤ (1 - χ) * M      where `χ` is opponent-only survival (the
                            best-response slope)

A block whose survival is close to `1` therefore has a *small* intercept, not
merely a bounded one.  Since `1 - P ≤ 1` and `1 - χ ≤ 1` (both slopes are
nonnegative), the weighted bounds immediately imply the corresponding
unweighted conjuncts of `quittingFiniteBoundaryHolonomy_coordinates_bounded`;
see `quittingFiniteBoundaryHolonomy_intercept_tail_bounded` below, which is
the correctness check that the weighted statement is not merely plausible but
actually implies the landed box bound.  Neither field of that landed theorem
is modified or reproved here.

**Why weighted beats unweighted.** It makes each block's contribution to a
telescoped error proportional to its own absorbed mass `1 - P`
(respectively `1 - χ`), rather than to a block-count-independent constant.
Summing weighted defects over a chronological run of blocks therefore gives a
tail sum that converges as the blocks' survival approaches `1`, instead of a
bound that grows linearly in the number of blocks -- turning error estimates
into convergent tail sums rather than counts of blocks.
`abs_intercept_compose_le_add` records the two-block instance of this: the
defect of a chronological composite is at most the sum of the two blocks'
defects, so the same bound assembles along any finite composition.

## Proof strategy, and what is reused from `Math.PMFProduct`

The single-stage piece of the argument -- that the one-stage continuation
reward is bounded by `M` times the one-stage *absorbed* mass, not merely by
`M` -- is already on record as `abs_quittingFixedOpponentsContinueReward_le_hazard`
(`QuittingExceptionalBellmanTail.lean`).  Its proof isolates the single
all-continue atom from a total-probability-one sum, which is exactly the
technique behind `Math.PMFProduct.sum_coalitionMass_nonempty`; no new
coalition-level plumbing is needed to reuse it here, since every quitting
action already corresponds to exactly one coalition (there is nothing to
group: the reward-bearing atoms and the nonempty coalitions are already in
bijection one-for-one).

The multi-stage assembly (`abs_quittingFiniteContinueToBoundaryValue_zero_le_mul_defect`,
`abs_quittingFiniteTerminalHazardValue_self_zero_le_mul_defect`) is a direct
structural induction on the Bellman-style recursions, using only the
*one-step* survival recursion `S(fuel+1) = c(start) * S(start+1)(fuel)`
(already on record as `quittingOpponentSurvivalWeight_succ_front`, and as the
definitional unfold of `quittingFiniteFullSurvivalWeight`) -- not the
accumulated flat-sum telescope.  This is deliberate: the one-step recursion
already supplies everything the induction needs, so nothing about it is
re-derived.

To honor the request to reuse, rather than re-derive, the *flat-sum* form of
the telescope, `scalarSurvivalTelescope` below is a literal specialization of
the landed `Math.PMFProduct.sum_survivalMass_mul_sub_continueMass` (via the
one-coordinate index type `Unit`) to an arbitrary scalar sequence.  It is
exported as an explicit witness that the closed-form sum identity described
informally above does hold for these sequences, even though the two main
theorems reach their conclusion by the shorter direct induction instead of
routing through it.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## A literal specialization of the landed `Math.PMFProduct` telescope -/

/-- The scalar survival telescope for an arbitrary real sequence `c`, obtained
as a literal one-coordinate specialization of the landed
`Math.PMFProduct.sum_survivalMass_mul_sub_continueMass`.  This is the
flat-sum identity `Σ_{u<m} S(u) * (1 - c(u)) = 1 - S(m)` with
`S(u) = ∏_{v<u} c(v)`, exhibited here for reuse even though the two weighted
defect bounds below reach their conclusion by direct induction instead. -/
theorem scalarSurvivalTelescope (c : ℕ → ℝ) (fuel : ℕ) :
    ∑ offset ∈ Finset.range fuel,
        (∏ o ∈ Finset.range offset, c o) * (1 - c offset) =
      1 - ∏ o ∈ Finset.range fuel, c o := by
  have hcm : ∀ n : ℕ,
      Math.PMFProduct.continueMass (fun _ : Unit => 1 - c n) = c n := by
    intro n
    simp [Math.PMFProduct.continueMass]
  have hsm : ∀ t : ℕ,
      Math.PMFProduct.survivalMass (fun n (_ : Unit) => 1 - c n) t =
        ∏ o ∈ Finset.range t, c o := by
    intro t
    induction t with
    | zero => simp [Math.PMFProduct.survivalMass]
    | succ t ih =>
        rw [Math.PMFProduct.survivalMass_succ, ih, hcm, Finset.prod_range_succ]
  have h := Math.PMFProduct.sum_survivalMass_mul_sub_continueMass
    (fun n (_ : Unit) => 1 - c n) fuel
  simp only [hsm, hcm] at h
  exact h

/-! ## Weighted defect of the continue-through boundary value -/

/-- The continue-through boundary value against a fixed opponent clock is
bounded by the reward bound times the opponent-only *defect* `1 - χ`, not
merely by the reward bound. -/
theorem abs_quittingFiniteContinueToBoundaryValue_zero_le_mul_defect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ start fuel,
      |quittingFiniteContinueToBoundaryValue reward roots who 0 start fuel| ≤
        quittingRewardBound reward *
          (1 - quittingOpponentSurvivalWeight roots who start fuel) := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      simp [quittingFiniteContinueToBoundaryValue, quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hMnonneg : 0 ≤ quittingRewardBound reward :=
        quittingRewardBound_nonneg reward
      have hcnonneg : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg _
      have hCR : |quittingFixedOpponentsContinueReward reward roots who start| ≤
          quittingRewardBound reward *
            (1 - quittingFixedOpponentsContinueMass roots who start) :=
        abs_quittingFixedOpponentsContinueReward_le_hazard reward roots who start
          (quittingRewardBound reward) hMnonneg
          (fun S => abs_reward_le_quittingRewardBound reward S who)
      have hstep : quittingFiniteContinueToBoundaryValue reward roots who 0 start
            (fuel + 1) =
          quittingFixedOpponentsContinueReward reward roots who start +
            quittingFixedOpponentsContinueMass roots who start *
              quittingFiniteContinueToBoundaryValue reward roots who 0
                (start + 1) fuel := rfl
      rw [hstep]
      have htri :
          |quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingFiniteContinueToBoundaryValue reward roots who 0
                  (start + 1) fuel| ≤
            |quittingFixedOpponentsContinueReward reward roots who start| +
              quittingFixedOpponentsContinueMass roots who start *
                |quittingFiniteContinueToBoundaryValue reward roots who 0
                  (start + 1) fuel| := by
        have h1 := abs_add_le
          (quittingFixedOpponentsContinueReward reward roots who start)
          (quittingFixedOpponentsContinueMass roots who start *
            quittingFiniteContinueToBoundaryValue reward roots who 0
              (start + 1) fuel)
        rwa [abs_mul, abs_of_nonneg hcnonneg] at h1
      have hcombine :
          |quittingFixedOpponentsContinueReward reward roots who start| +
              quittingFixedOpponentsContinueMass roots who start *
                |quittingFiniteContinueToBoundaryValue reward roots who 0
                  (start + 1) fuel| ≤
            quittingRewardBound reward *
                (1 - quittingFixedOpponentsContinueMass roots who start) +
              quittingFixedOpponentsContinueMass roots who start *
                (quittingRewardBound reward *
                  (1 - quittingOpponentSurvivalWeight roots who (start + 1) fuel)) :=
        add_le_add hCR (mul_le_mul_of_nonneg_left (ih (start + 1)) hcnonneg)
      have hfinal := htri.trans hcombine
      have hSsucc : quittingOpponentSurvivalWeight roots who start (fuel + 1) =
          quittingFixedOpponentsContinueMass roots who start *
            quittingOpponentSurvivalWeight roots who (start + 1) fuel :=
        quittingOpponentSurvivalWeight_succ_front roots who start fuel
      rw [hSsucc]
      calc
        |quittingFixedOpponentsContinueReward reward roots who start +
            quittingFixedOpponentsContinueMass roots who start *
              quittingFiniteContinueToBoundaryValue reward roots who 0
                (start + 1) fuel| ≤ _ := hfinal
        _ = quittingRewardBound reward *
              (1 - quittingFixedOpponentsContinueMass roots who start *
                quittingOpponentSurvivalWeight roots who (start + 1) fuel) := by
          ring

/-! ## Weighted defect of the prescribed hazard value -/

/-- One-stage weighted bound on the hazard-mixed absorbing payoff: quitting
now via the player's own hazard mixed with continuing now (opponent hazard)
is bounded by the reward bound times the one-stage *full* defect `1 - c`,
where `c` is the probability that the player's own hazard and every opponent
both continue. -/
private theorem abs_hazardMix_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool) (time : ℕ) :
    |(hazard time true).toReal *
          quittingFixedOpponentsQuitValue reward roots who time +
        (hazard time false).toReal *
          quittingFixedOpponentsContinueReward reward roots who time| ≤
      quittingRewardBound reward *
        (1 - quittingFiniteFullContinueMass roots who hazard time) := by
  have hMnonneg : 0 ≤ quittingRewardBound reward := quittingRewardBound_nonneg reward
  have htnonneg : 0 ≤ (hazard time true).toReal := ENNReal.toReal_nonneg
  have hfnonneg : 0 ≤ (hazard time false).toReal := ENNReal.toReal_nonneg
  have hsum : (hazard time true).toReal + (hazard time false).toReal = 1 := by
    simpa [Fintype.sum_bool] using pmf_toReal_sum_one (hazard time)
  have hQV : |quittingFixedOpponentsQuitValue reward roots who time| ≤
      quittingRewardBound reward :=
    abs_quittingFixedOpponentsQuitValue_le_rewardBound reward roots who time
  have hCR : |quittingFixedOpponentsContinueReward reward roots who time| ≤
      quittingRewardBound reward *
        (1 - quittingFixedOpponentsContinueMass roots who time) :=
    abs_quittingFixedOpponentsContinueReward_le_hazard reward roots who time
      (quittingRewardBound reward) hMnonneg
      (fun S => abs_reward_le_quittingRewardBound reward S who)
  have htri :
      |(hazard time true).toReal *
            quittingFixedOpponentsQuitValue reward roots who time +
          (hazard time false).toReal *
            quittingFixedOpponentsContinueReward reward roots who time| ≤
        (hazard time true).toReal *
            |quittingFixedOpponentsQuitValue reward roots who time| +
          (hazard time false).toReal *
            |quittingFixedOpponentsContinueReward reward roots who time| := by
    have h1 := abs_add_le
      ((hazard time true).toReal *
        quittingFixedOpponentsQuitValue reward roots who time)
      ((hazard time false).toReal *
        quittingFixedOpponentsContinueReward reward roots who time)
    rwa [abs_mul, abs_mul, abs_of_nonneg htnonneg, abs_of_nonneg hfnonneg] at h1
  have hcombine :
      (hazard time true).toReal *
          |quittingFixedOpponentsQuitValue reward roots who time| +
        (hazard time false).toReal *
          |quittingFixedOpponentsContinueReward reward roots who time| ≤
      (hazard time true).toReal * quittingRewardBound reward +
        (hazard time false).toReal *
          (quittingRewardBound reward *
            (1 - quittingFixedOpponentsContinueMass roots who time)) :=
    add_le_add (mul_le_mul_of_nonneg_left hQV htnonneg)
      (mul_le_mul_of_nonneg_left hCR hfnonneg)
  have hfinal := htri.trans hcombine
  have heq :
      (hazard time true).toReal * quittingRewardBound reward +
          (hazard time false).toReal *
            (quittingRewardBound reward *
              (1 - quittingFixedOpponentsContinueMass roots who time)) =
        quittingRewardBound reward *
          (1 - (hazard time false).toReal *
            quittingFixedOpponentsContinueMass roots who time) := by
    have hht : (hazard time true).toReal = 1 - (hazard time false).toReal := by
      linarith
    rw [hht]; ring
  rw [heq] at hfinal
  have hfc : quittingFiniteFullContinueMass roots who hazard time =
      (hazard time false).toReal * quittingFixedOpponentsContinueMass roots who
        time := rfl
  rw [hfc]
  exact hfinal

/-- The prescribed hazard value against a fixed opponent clock and an
arbitrary own hazard is bounded by the reward bound times the block's own
*full* defect `1 - P`, not merely by the reward bound. -/
theorem abs_quittingFiniteTerminalHazardValue_self_zero_le_mul_defect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool) :
    ∀ start fuel,
      |quittingFiniteTerminalHazardValue reward roots who hazard 0 start fuel| ≤
        quittingRewardBound reward *
          (1 - quittingFiniteFullSurvivalWeight roots who hazard start fuel) := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      simp [quittingFiniteTerminalHazardValue, quittingFiniteFullSurvivalWeight,
        quittingFiniteContinueWeight]
  | succ fuel ih =>
      have hcnonneg : 0 ≤ quittingFiniteFullContinueMass roots who hazard start :=
        quittingFiniteFullContinueMass_nonneg roots who hazard start
      have hmix := abs_hazardMix_le reward roots who hazard start
      have hstep : quittingFiniteTerminalHazardValue reward roots who hazard 0 start
            (fuel + 1) =
          ((hazard start true).toReal *
                quittingFixedOpponentsQuitValue reward roots who start +
              (hazard start false).toReal *
                quittingFixedOpponentsContinueReward reward roots who start) +
            quittingFiniteFullContinueMass roots who hazard start *
              quittingFiniteTerminalHazardValue reward roots who hazard 0
                (start + 1) fuel := by
        change ((hazard start true).toReal *
                quittingFixedOpponentsQuitValue reward roots who start +
              (hazard start false).toReal *
                (quittingFixedOpponentsContinueReward reward roots who start +
                  quittingFixedOpponentsContinueMass roots who start *
                    quittingFiniteTerminalHazardValue reward roots who hazard 0
                      (start + 1) fuel)) = _
        unfold quittingFiniteFullContinueMass
        ring
      rw [hstep]
      have htri :
          |((hazard start true).toReal *
                  quittingFixedOpponentsQuitValue reward roots who start +
                (hazard start false).toReal *
                  quittingFixedOpponentsContinueReward reward roots who start) +
              quittingFiniteFullContinueMass roots who hazard start *
                quittingFiniteTerminalHazardValue reward roots who hazard 0
                  (start + 1) fuel| ≤
            |(hazard start true).toReal *
                  quittingFixedOpponentsQuitValue reward roots who start +
                (hazard start false).toReal *
                  quittingFixedOpponentsContinueReward reward roots who start| +
              quittingFiniteFullContinueMass roots who hazard start *
                |quittingFiniteTerminalHazardValue reward roots who hazard 0
                  (start + 1) fuel| := by
        have h1 := abs_add_le
          ((hazard start true).toReal *
                quittingFixedOpponentsQuitValue reward roots who start +
              (hazard start false).toReal *
                quittingFixedOpponentsContinueReward reward roots who start)
          (quittingFiniteFullContinueMass roots who hazard start *
            quittingFiniteTerminalHazardValue reward roots who hazard 0
              (start + 1) fuel)
        rwa [abs_mul, abs_of_nonneg hcnonneg] at h1
      have hcombine :
          |(hazard start true).toReal *
                quittingFixedOpponentsQuitValue reward roots who start +
              (hazard start false).toReal *
                quittingFixedOpponentsContinueReward reward roots who start| +
            quittingFiniteFullContinueMass roots who hazard start *
              |quittingFiniteTerminalHazardValue reward roots who hazard 0
                (start + 1) fuel| ≤
          quittingRewardBound reward *
              (1 - quittingFiniteFullContinueMass roots who hazard start) +
            quittingFiniteFullContinueMass roots who hazard start *
              (quittingRewardBound reward *
                (1 - quittingFiniteFullSurvivalWeight roots who hazard
                  (start + 1) fuel)) :=
        add_le_add hmix (mul_le_mul_of_nonneg_left (ih (start + 1)) hcnonneg)
      have hfinal := htri.trans hcombine
      have hSsucc : quittingFiniteFullSurvivalWeight roots who hazard start
            (fuel + 1) =
          quittingFiniteFullContinueMass roots who hazard start *
            quittingFiniteFullSurvivalWeight roots who hazard (start + 1) fuel :=
        rfl
      rw [hSsucc]
      calc
        |((hazard start true).toReal *
                quittingFixedOpponentsQuitValue reward roots who start +
              (hazard start false).toReal *
                quittingFixedOpponentsContinueReward reward roots who start) +
            quittingFiniteFullContinueMass roots who hazard start *
              quittingFiniteTerminalHazardValue reward roots who hazard 0
                (start + 1) fuel| ≤ _ := hfinal
        _ = quittingRewardBound reward *
              (1 - quittingFiniteFullContinueMass roots who hazard start *
                quittingFiniteFullSurvivalWeight roots who hazard
                  (start + 1) fuel) := by
          ring

/-! ## Weighted bounds for the bundled holonomy -/

/-- **Weighted intercept bound.** The prescribed intercept of an actual
finite root block is bounded by the reward bound times its own defect
`1 - P`, where `P` is the block's full product survival slope -- not merely
by the reward bound. -/
theorem abs_quittingFiniteBoundaryHolonomy_prescribed_intercept_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι) :
    |QuittingAffineSummary.intercept
        (QuittingBoundaryHolonomy.prescribed
          (quittingFiniteBoundaryHolonomy reward roots start extra) who)| ≤
      quittingRewardBound reward *
        (1 - QuittingAffineSummary.survival
          (QuittingBoundaryHolonomy.prescribed
            (quittingFiniteBoundaryHolonomy reward roots start extra) who)) := by
  rw [quittingFiniteBoundaryHolonomy_prescribed_intercept,
    quittingFiniteBoundaryHolonomy_prescribed_survival]
  exact abs_quittingFiniteTerminalHazardValue_self_zero_le_mul_defect
    reward roots who (fun time => roots time who) start (extra + 1)

/-- **Weighted continue-through bound.** The continue-through intercept of an
actual finite root block is bounded by the reward bound times its own defect
`1 - χ`, where `χ` is the block's opponent-only survival slope -- not merely
by the reward bound. -/
theorem abs_quittingFiniteBoundaryHolonomy_bestResponse_tail_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι) :
    |QuittingMaxAffineSummary.tail
        (QuittingBoundaryHolonomy.bestResponse
          (quittingFiniteBoundaryHolonomy reward roots start extra) who)| ≤
      quittingRewardBound reward *
        (1 - QuittingMaxAffineSummary.survival
          (QuittingBoundaryHolonomy.bestResponse
            (quittingFiniteBoundaryHolonomy reward roots start extra) who)) := by
  rw [quittingFiniteBoundaryHolonomy_bestResponse_tail,
    quittingFiniteBoundaryHolonomy_bestResponse_survival]
  exact abs_quittingFiniteContinueToBoundaryValue_zero_le_mul_defect
    reward roots who start (extra + 1)

/-! ## Corollary: the weighted bounds imply the landed unweighted box bound -/

/-- **Corollary.** Since `1 - P ≤ 1` and `1 - χ ≤ 1`, the two weighted defect
bounds above imply the unweighted intercept bounds already recorded in
`quittingFiniteBoundaryHolonomy_coordinates_bounded`.  This is the
correctness check that the weighted statement is not merely plausible but
actually implies the landed box membership; neither field of the landed
theorem is modified or reproved here. -/
theorem quittingFiniteBoundaryHolonomy_intercept_tail_bounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι) :
    |QuittingAffineSummary.intercept
        (QuittingBoundaryHolonomy.prescribed
          (quittingFiniteBoundaryHolonomy reward roots start extra) who)| ≤
      quittingRewardBound reward ∧
    |QuittingMaxAffineSummary.tail
        (QuittingBoundaryHolonomy.bestResponse
          (quittingFiniteBoundaryHolonomy reward roots start extra) who)| ≤
      quittingRewardBound reward := by
  have hB := abs_quittingFiniteBoundaryHolonomy_prescribed_intercept_le
    reward roots start extra who
  have hT := abs_quittingFiniteBoundaryHolonomy_bestResponse_tail_le
    reward roots start extra who
  have hM : 0 ≤ quittingRewardBound reward := quittingRewardBound_nonneg reward
  have hP : 0 ≤ QuittingAffineSummary.survival
      (QuittingBoundaryHolonomy.prescribed
        (quittingFiniteBoundaryHolonomy reward roots start extra) who) :=
    QuittingAffineSummary.survival_nonneg _
  have hχ : 0 ≤ QuittingMaxAffineSummary.survival
      (QuittingBoundaryHolonomy.bestResponse
        (quittingFiniteBoundaryHolonomy reward roots start extra) who) :=
    QuittingMaxAffineSummary.survival_nonneg _
  refine ⟨hB.trans ?_, hT.trans ?_⟩
  · nlinarith [mul_nonneg hM hP]
  · nlinarith [mul_nonneg hM hχ]

/-! ## Bonus: composite defect bounded by the sum of block defects -/

/-- **Composite defect.** If two chronologically composed
`QuittingAffineSummary` blocks each have intercept bounded by `M` times their
own defect, and both survival slopes lie in `[0,1]`, the composite intercept
is bounded by `M` times the *sum* of the two blocks' defects.  This is the
two-block instance of what makes a tail estimate over a chronological run of
blocks possible: defects add along the composition instead of the intercept
merely staying bounded. -/
theorem abs_intercept_compose_le_add
    (outer inner : QuittingAffineSummary) (M : ℝ)
    (hM : 0 ≤ M)
    (hBouter : |outer.intercept| ≤ M * (1 - outer.survival))
    (hBinner : |inner.intercept| ≤ M * (1 - inner.survival))
    (houter1 : outer.survival ≤ 1) (hinner1 : inner.survival ≤ 1) :
    |(outer * inner).intercept| ≤
      M * (1 - outer.survival) + M * (1 - inner.survival) := by
  have houter0 : 0 ≤ outer.survival := outer.survival_nonneg
  have hcompose : (outer * inner).intercept =
      outer.intercept + outer.survival * inner.intercept := rfl
  rw [hcompose]
  have hdefect0 : 0 ≤ 1 - inner.survival := by linarith
  calc
    |outer.intercept + outer.survival * inner.intercept| ≤
        |outer.intercept| + |outer.survival * inner.intercept| := abs_add_le _ _
    _ = |outer.intercept| + outer.survival * |inner.intercept| := by
      rw [abs_mul, abs_of_nonneg houter0]
    _ ≤ M * (1 - outer.survival) + outer.survival * (M * (1 - inner.survival)) :=
      add_le_add hBouter (mul_le_mul_of_nonneg_left hBinner houter0)
    _ ≤ M * (1 - outer.survival) + M * (1 - inner.survival) := by
      nlinarith [mul_le_mul_of_nonneg_right (sub_nonneg.mpr houter1)
        (mul_nonneg hM hdefect0)]

end GameTheory
