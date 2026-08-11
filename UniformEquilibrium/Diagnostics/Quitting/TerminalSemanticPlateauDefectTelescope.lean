/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge

/-!
# A finite stopping-time telescope for semantic defect charge

The one-row arbitrary-root estimate can be summed along one actual profile,
but the resulting right hand side must not be called the regret of one
deviation.  This module records the exact stopped Abel decomposition.  It
leaves visible the three honest obstructions: endpoint excess debt,
absorption-weighted shifted-tail excess debt, and the occupation sum of the
local Nash defects.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem sum_mul_forwardDiff_eq_endpoint_add_drop
    (live excess : ℕ → ℝ) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
        live time * (excess (time + 1) - excess time)) =
      live cutoff * excess cutoff - live 0 * excess 0 +
        ∑ time ∈ Finset.range cutoff,
          (live time - live (time + 1)) * excess (time + 1) := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ring

private theorem sum_forwardDrop_eq_start_sub_endpoint
    (live : ℕ → ℝ) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
        (live time - live (time + 1))) = live 0 - live cutoff := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- The total opponent-absorption debt charge at one live row. -/
def quittingSpineOpponentAbsorptionDebtCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) : ℝ :=
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  let root := quittingProfileLiveRoot reward profile time
  ∑ who, quittingRootOpponentAbsorptionMass root who *
    quittingTerminalSemanticDebt tail who

/-- The total local Nash defect at one actual live row. -/
def quittingSpineTotalNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) : ℝ :=
  quittingRootTotalNashDefect reward
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    (quittingProfileLiveRoot reward profile time)

/-- Excess total debt of a shifted live tail above a displayed reference
level.  In the minimum-plateau application the reference is the global
minimum total debt. -/
def quittingSpineDebtExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (reference : ℝ) (time : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile time)) -
    reference

/-- A collision stage atom is bounded by the aggregate opponent-absorption
debt charge on the same actual row.  Every debt coordinate sees at least one
quitting opponent in a coalition with two or more members. -/
theorem quittingStageCoalitionMass_mul_tailDebtSum_le_liveMass_mul_charge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcollision : 1 < terminal.val.card) :
    quittingStageCoalitionMass reward profile time terminal *
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1))) ≤
      quittingLiveMass reward profile time *
        quittingSpineOpponentAbsorptionDebtCharge reward profile time := by
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  let root := quittingProfileLiveRoot reward profile time
  have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have htailDebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward htailCarrier
  have hcoordinate : ∀ who,
      quittingRootCoalitionMass root terminal.val *
          quittingTerminalSemanticDebt tail who ≤
        quittingRootOpponentAbsorptionMass root who *
          quittingTerminalSemanticDebt tail who := by
    intro who
    obtain ⟨other, hother, hne⟩ := terminal.val.exists_mem_ne hcollision who
    exact mul_le_mul_of_nonneg_right
      (quittingRootCoalitionMass_le_opponentAbsorptionMass_of_other_mem
        root terminal.val who other hother hne)
      (htailDebt who)
  have hsum := Finset.sum_le_sum fun who (_hwho : who ∈ Finset.univ) =>
    hcoordinate who
  have hliveNonneg := quittingLiveMass_nonneg reward profile time
  have hweighted := mul_le_mul_of_nonneg_left hsum hliveNonneg
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  unfold quittingTerminalSemanticDebtSum
  simpa [quittingSpineOpponentAbsorptionDebtCharge, tail, root, Finset.mul_sum,
    mul_assoc] using hweighted

/-- **Finite stopped defect/excess telescope.**  Along one actual profile,
the survival-weighted opponent-absorption debt charge is bounded by exactly
three terms:

* excess debt still alive at the cutoff;
* excess debt exposed on rows where joint survival is lost;
* the survival-weighted occupation sum of the actual local Nash defects.

The initial excess appears with a favorable minus sign.  In particular, the
last sum is retained as a local-defect occupation measure; the theorem does
not identify it with the gain of one unilateral deviation. -/
theorem sum_liveMass_mul_spineOpponentAbsorptionDebtCharge_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (reference : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineOpponentAbsorptionDebtCharge reward profile time) ≤
      quittingLiveMass reward profile cutoff *
          quittingSpineDebtExcess reward profile reference cutoff -
        quittingSpineDebtExcess reward profile reference 0 +
      (∑ time ∈ Finset.range cutoff,
        (quittingLiveMass reward profile time -
            quittingLiveMass reward profile (time + 1)) *
          quittingSpineDebtExcess reward profile reference (time + 1)) +
      ∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineTotalNashDefect reward profile time := by
  have hrow : ∀ time,
      quittingSpineOpponentAbsorptionDebtCharge reward profile time ≤
        quittingSpineDebtExcess reward profile reference (time + 1) -
          quittingSpineDebtExcess reward profile reference time +
        quittingSpineTotalNashDefect reward profile time := by
    intro time
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))
    let current := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile time)
    let root := quittingProfileLiveRoot reward profile time
    have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
      quittingTerminalSemanticPair_mem_carrier reward _
    have htailDebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt tail who :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hM hreward htailCarrier
    have hcharge :=
      sum_opponentAbsorptionMass_mul_debt_le_sumDebt_drift_add_totalNashDefect
        reward tail root htailDebt
    have hprefix : current = quittingTerminalSemanticPrefix reward root tail := by
      dsimp only [current, root, tail]
      exact quittingTerminalSemanticPair_spine_eq_prefix
        reward profile time hM hreward
    rw [← hprefix] at hcharge
    simpa [quittingSpineOpponentAbsorptionDebtCharge,
      quittingSpineDebtExcess, quittingSpineTotalNashDefect,
      tail, current, root] using hcharge
  have hweighted : ∀ time,
      quittingLiveMass reward profile time *
          quittingSpineOpponentAbsorptionDebtCharge reward profile time ≤
        quittingLiveMass reward profile time *
          (quittingSpineDebtExcess reward profile reference (time + 1) -
            quittingSpineDebtExcess reward profile reference time +
            quittingSpineTotalNashDefect reward profile time) := by
    intro time
    exact mul_le_mul_of_nonneg_left (hrow time)
      (quittingLiveMass_nonneg reward profile time)
  have hsum := Finset.sum_le_sum fun time (_htime : time ∈ Finset.range cutoff) =>
    hweighted time
  have habel := sum_mul_forwardDiff_eq_endpoint_add_drop
    (quittingLiveMass reward profile)
    (quittingSpineDebtExcess reward profile reference) cutoff
  rw [quittingLiveMass_zero] at habel
  calc
    (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineOpponentAbsorptionDebtCharge reward profile time) ≤
      (∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            (quittingSpineDebtExcess reward profile reference (time + 1) -
              quittingSpineDebtExcess reward profile reference time)) +
        ∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingSpineTotalNashDefect reward profile time := by
      simpa [mul_add, Finset.sum_add_distrib] using hsum
    _ = _ := by rw [habel]; ring

/-- Collision-marked specialization of the stopped telescope.  This is the
profile-owned form used by the plateau trichotomy: no marked root is replaced
by a separately selected Nash root. -/
theorem sum_stageCollisionMass_mul_tailDebtSum_le_stoppedDefectExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (reference : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcollision : 1 < terminal.val.card) :
    (∑ time ∈ Finset.range cutoff,
      quittingStageCoalitionMass reward profile time terminal *
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1)))) ≤
      quittingLiveMass reward profile cutoff *
          quittingSpineDebtExcess reward profile reference cutoff -
        quittingSpineDebtExcess reward profile reference 0 +
      (∑ time ∈ Finset.range cutoff,
        (quittingLiveMass reward profile time -
            quittingLiveMass reward profile (time + 1)) *
          quittingSpineDebtExcess reward profile reference (time + 1)) +
      ∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineTotalNashDefect reward profile time := by
  have hmarked := Finset.sum_le_sum fun time (_htime : time ∈ Finset.range cutoff) =>
    quittingStageCoalitionMass_mul_tailDebtSum_le_liveMass_mul_charge
      reward profile time terminal hM hreward hcollision
  exact hmarked.trans
    (sum_liveMass_mul_spineOpponentAbsorptionDebtCharge_le
      reward profile reference cutoff hM hreward)

/-- Minimum-carrier specialization.  All shifted-tail excesses are
nonnegative; this makes explicit that the Abel telescope has no hidden
negative boundary charge. -/
theorem quittingSpineDebtExcess_nonneg_of_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (time : ℕ) :
    0 ≤ quittingSpineDebtExcess reward profile
      (quittingTerminalSemanticDebtSum minimum) time := by
  unfold quittingSpineDebtExcess
  exact sub_nonneg.mpr (hminimum _
    (quittingTerminalSemanticPair_mem_carrier reward _))

/-- **Near-minimum-spine consumer.**  If every shifted tail through a stopped
horizon lies within `epsilon` of the reference debt level, all excess-debt
terms in the stopped telescope cost at most `epsilon` in total (not one
`epsilon` per row).  What remains is precisely the occupation sum of local
Nash defects.

This is a useful sharp fence: near-minimum tail attachment eliminates the
excess part of the seam, but a separate stopping-time argument is still
needed to consume the displayed defect occupation sum. -/
theorem sum_liveMass_mul_spineOpponentAbsorptionDebtCharge_le_epsilon_add_defect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (reference epsilon : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinitial : 0 ≤ quittingSpineDebtExcess reward profile reference 0)
    (hnear : ∀ time ≤ cutoff,
      quittingSpineDebtExcess reward profile reference time ≤ epsilon) :
    (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineOpponentAbsorptionDebtCharge reward profile time) ≤
      epsilon +
        ∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingSpineTotalNashDefect reward profile time := by
  have htelescope :=
    sum_liveMass_mul_spineOpponentAbsorptionDebtCharge_le
      reward profile reference cutoff hM hreward
  have hliveEndpointNonneg := quittingLiveMass_nonneg reward profile cutoff
  have hliveEndpointLe := quittingLiveMass_le_one reward profile cutoff
  have hendpoint : quittingLiveMass reward profile cutoff *
      quittingSpineDebtExcess reward profile reference cutoff ≤
        quittingLiveMass reward profile cutoff * epsilon :=
    mul_le_mul_of_nonneg_left (hnear cutoff le_rfl) hliveEndpointNonneg
  have hdropNonneg : ∀ time,
      0 ≤ quittingLiveMass reward profile time -
        quittingLiveMass reward profile (time + 1) := by
    intro time
    exact sub_nonneg.mpr (quittingLiveMass_succ_le reward profile time)
  have hdrop : (∑ time ∈ Finset.range cutoff,
      (quittingLiveMass reward profile time -
          quittingLiveMass reward profile (time + 1)) *
        quittingSpineDebtExcess reward profile reference (time + 1)) ≤
      ∑ time ∈ Finset.range cutoff,
        (quittingLiveMass reward profile time -
          quittingLiveMass reward profile (time + 1)) * epsilon := by
    exact Finset.sum_le_sum fun time htime =>
      mul_le_mul_of_nonneg_left
        (hnear (time + 1) (by
          have := Finset.mem_range.mp htime
          omega))
        (hdropNonneg time)
  have hdropSum := sum_forwardDrop_eq_start_sub_endpoint
    (quittingLiveMass reward profile) cutoff
  rw [quittingLiveMass_zero] at hdropSum
  have hbudget :
      quittingLiveMass reward profile cutoff *
            quittingSpineDebtExcess reward profile reference cutoff -
          quittingSpineDebtExcess reward profile reference 0 +
        (∑ time ∈ Finset.range cutoff,
          (quittingLiveMass reward profile time -
              quittingLiveMass reward profile (time + 1)) *
            quittingSpineDebtExcess reward profile reference (time + 1)) ≤
        epsilon := by
    calc
      _ ≤ quittingLiveMass reward profile cutoff * epsilon +
          (∑ time ∈ Finset.range cutoff,
            (quittingLiveMass reward profile time -
              quittingLiveMass reward profile (time + 1)) * epsilon) := by
        linarith
      _ = epsilon := by
        rw [← Finset.sum_mul, hdropSum]
        ring
  linarith

end GameTheory
