/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtSourceDynamicAlternative
import UniformEquilibrium.Quitting.AbsorptionPath.MetrizableMarkedAbsorptionDecoder
import UniformEquilibrium.Quitting.Debt.Dynamic.TwoEndedDynamicDebtCompactification
import UniformEquilibrium.Quitting.Boundary.Holonomy.QuantitativeAggregateTerminalAnchor

/-!
# Boundary provenance and the asymptotic mismatch alternative

The zero-boundary finite minimizers have two complementary compactness
interfaces.  Ordinary projective extraction retains every fixed distance
from the initial state and loses the moving terminal end.  The two-ended
compactification retains a separate reverse ray, but supplies no bridge
survival between the two rays.  A small scalar regression below records why
fixed-coordinate convergence alone cannot recover a moving zero boundary.

The metrizable marked-absorption decoder has the opposite strength: for any
sequence of finite coherent cylinders it jointly retains both exact-D
anchors, holonomy, absorption law, and repair state.  The strengthened
subsequence theorem below exposes the two anchor limits explicitly.  Its
semantic target does not, however, contain the canonical charged-path
capacity potential, so this compactness statement does not compare the
capacity boundary with the exact-D boundary.  Quantitative aggregate
terminal anchors likewise control a terminal packet and a one-sided repair
value; they do not identify the independently selected min--max projective
tail's capacity boundary.

The strongest unconditional conclusion currently available is therefore
asymptotic rather than exact.  The capacity account is antitone, its raw
killed dissipations are summable, and the one-step survival-scaled boundary
mismatch exceeds the initial mismatch by exactly that dissipation.  The
excess tends to zero along the full tail.  Nothing here makes a finite
dissipation vanish, so the zero-face recurrence theorem still needs its
displayed boundary-mismatch nonexpansion premise.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

/-! ## A formal regression for the moving terminal end -/

/-- Scalar finite-prefix debt equal to one strictly before its cutoff and
zero at and after the moving terminal end. -/
def projectiveTerminalEscapeDebt (cutoff time : ℕ) : ℝ :=
  if time < cutoff then 1 else 0

/-- The single source atom immediately before the moving terminal end. -/
def projectiveTerminalEscapeSource (cutoff time : ℕ) : ℝ :=
  if time + 1 = cutoff then 1 else 0

/-- Every finite regression prefix satisfies an exact survival-one killed
recursion. -/
theorem projectiveTerminalEscapeDebt_step (cutoff time : ℕ) :
    projectiveTerminalEscapeDebt cutoff time =
      projectiveTerminalEscapeSource cutoff time +
        projectiveTerminalEscapeDebt cutoff (time + 1) := by
  unfold projectiveTerminalEscapeDebt projectiveTerminalEscapeSource
  split_ifs <;> norm_num at * <;> omega

/-- Every finite approximant has literal zero debt at its own terminal end. -/
@[simp]
theorem projectiveTerminalEscapeDebt_diagonal (cutoff : ℕ) :
    projectiveTerminalEscapeDebt cutoff cutoff = 0 := by
  simp [projectiveTerminalEscapeDebt]

/-- Nevertheless, every fixed initial coordinate converges to one as the
moving cutoff escapes. -/
theorem projectiveTerminalEscapeDebt_tendsto_one (time : ℕ) :
    Tendsto (fun cutoff ↦ projectiveTerminalEscapeDebt cutoff time)
      atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (time + 1)] with cutoff hcutoff
  simp [projectiveTerminalEscapeDebt, lt_of_lt_of_le (Nat.lt_succ_self time) hcutoff]

/-- The moving terminal source disappears from every fixed coordinate. -/
theorem projectiveTerminalEscapeSource_tendsto_zero (time : ℕ) :
    Tendsto (fun cutoff ↦ projectiveTerminalEscapeSource cutoff time)
      atTop (nhds 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (time + 2)] with cutoff hcutoff
  have hne : time + 1 ≠ cutoff := by omega
  simp [projectiveTerminalEscapeSource, hne]

/-- The fixed-coordinate limit is the positive harmonic solution of the
source-free survival-one recursion.  Thus exact finite recursion and a
moving zero boundary do not determine the projective terminal boundary. -/
theorem projectiveTerminalEscape_limit_harmonic :
    (1 : ℝ) = 0 + 1 * 1 := by norm_num

/-! ## What the metrizable decoder does retain -/

namespace MetrizableMarkedAbsorptionCompletion

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Every finite coherent-cylinder sequence has one subsequence on which
the completed path, both exact-D anchors, and the decoder-facing repair state
converge jointly.  This makes the decoder's two-ended strength explicit,
without adding a capacity-potential coordinate that it does not contain. -/
theorem exists_finite_subsequence_with_anchor_repairState_limit
    (finite : ℕ → FiniteMarkedAbsorptionPath reward) :
    ∃ (limit : MetrizableMarkedAbsorptionPath reward) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
      Tendsto (fun index ↦ completeMetrizable (finite (subseq index)))
        atTop (nhds limit) ∧
      Tendsto (fun index ↦ finiteEntryAnchor (finite (subseq index)))
        atTop (nhds (metrizableEntryAnchor limit)) ∧
      Tendsto (fun index ↦ finiteExitAnchor (finite (subseq index)))
        atTop (nhds (metrizableExitAnchor limit)) ∧
      Tendsto
        (fun index ↦ metrizableRepairState
          (completeMetrizable (finite (subseq index))))
        atTop (nhds (metrizableRepairState limit)) := by
  obtain ⟨limit, subseq, hsubseq, hpath, hrepair⟩ :=
    exists_finite_subsequence_with_repairState_limit finite
  refine ⟨limit, subseq, hsubseq, hpath, ?_, ?_, hrepair⟩
  · have hentry :=
      continuous_metrizableEntryAnchor.continuousAt.tendsto.comp hpath
    simpa [Function.comp_def] using hentry
  · have hexit :=
      continuous_metrizableExitAnchor.continuousAt.tendsto.comp hpath
    simpa [Function.comp_def] using hexit

end MetrizableMarkedAbsorptionCompletion

/-! ## Summable capacity dissipation on the canonical tail -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

/-- Raw chronological decrease of the capacity-derived debt account. -/
def killedCapacityDebtAccountDrop (who : ι) (time : ℕ) : ℝ :=
  seam.killedCapacityDebtAccount who time -
    seam.killedCapacityDebtAccount who (time + 1)

/-- The part of a carried next capacity account killed by current joint
absorption. -/
def killedCapacityAbsorptionCarryLoss (who : ι) (time : ℕ) : ℝ :=
  (1 - seam.killedDebtSurvival time) *
    seam.killedCapacityDebtAccount who (time + 1)

/-- The capacity-derived debt account is antitone along chronological time. -/
theorem antitone_killedCapacityDebtAccount (who : ι) :
    Antitone (seam.killedCapacityDebtAccount who) := by
  apply antitone_nat_of_succ_le
  intro time
  have hpay :=
    seam.killedDebtSource_add_capacityDebtAccount_succ_le who time
  have hsource : 0 ≤ seam.killedDebtSource who time :=
    quittingDynamicDebtSeam_nonneg
      (seam.tail time) (seam.tail_mem time) who
  linarith

/-- Capacity-account drops are nonnegative. -/
theorem killedCapacityDebtAccountDrop_nonneg (who : ι) (time : ℕ) :
    0 ≤ seam.killedCapacityDebtAccountDrop who time := by
  unfold killedCapacityDebtAccountDrop
  exact sub_nonneg.mpr
    (seam.antitone_killedCapacityDebtAccount who (Nat.le_succ time))

/-- Raw capacity-account drops form a summable telescoping series. -/
theorem summable_killedCapacityDebtAccountDrop (who : ι) :
    Summable (seam.killedCapacityDebtAccountDrop who) := by
  refine summable_of_sum_range_le
    (c := seam.killedCapacityDebtAccount who 0)
    (seam.killedCapacityDebtAccountDrop_nonneg who) ?_
  intro fuel
  rw [show (∑ time ∈ Finset.range fuel,
      seam.killedCapacityDebtAccountDrop who time) =
        seam.killedCapacityDebtAccount who 0 -
          seam.killedCapacityDebtAccount who fuel by
      exact Finset.sum_range_sub'
        (seam.killedCapacityDebtAccount who) fuel]
  exact sub_le_self _
    (seam.killedCapacityDebtAccount_nonneg who fuel)

/-- Absorption carry losses are nonnegative. -/
theorem killedCapacityAbsorptionCarryLoss_nonneg
    (who : ι) (time : ℕ) :
    0 ≤ seam.killedCapacityAbsorptionCarryLoss who time := by
  exact mul_nonneg
    (sub_nonneg.mpr (quittingStationaryContinueMass_le_one _))
    (seam.killedCapacityDebtAccount_nonneg who (time + 1))

/-- Carry losses are summable because the capacity account is bounded by its
initial value and joint absorption is summable. -/
theorem summable_killedCapacityAbsorptionCarryLoss (who : ι) :
    Summable (seam.killedCapacityAbsorptionCarryLoss who) := by
  apply Summable.of_nonneg_of_le
    (seam.killedCapacityAbsorptionCarryLoss_nonneg who)
  · intro time
    have haccount := seam.antitone_killedCapacityDebtAccount who
      (Nat.zero_le (time + 1))
    have habsorption : 0 ≤ 1 - seam.killedDebtSurvival time :=
      sub_nonneg.mpr (quittingStationaryContinueMass_le_one _)
    exact mul_le_mul_of_nonneg_left haccount habsorption
  · have habsorption : Summable
        (fun time ↦ 1 - seam.killedDebtSurvival time) := by
      change Summable (quittingDynamicDebtTailAbsorptionCharge seam.tail)
      exact seam.jointAbsorption_summable
    exact habsorption.mul_right
      (seam.killedCapacityDebtAccount who 0)

/-- Killed capacity dissipation is bounded by raw account drop plus the
absorption carry loss. -/
theorem killedCapacityDissipation_le_drop_add_carryLoss
    (who : ι) (time : ℕ) :
    killedDissipation seam.killedDebtSurvival
        (seam.killedDebtSource who)
        (seam.killedCapacityDebtAccount who) time ≤
      seam.killedCapacityDebtAccountDrop who time +
        seam.killedCapacityAbsorptionCarryLoss who time := by
  have hsource : 0 ≤ seam.killedDebtSource who time :=
    quittingDynamicDebtSeam_nonneg
      (seam.tail time) (seam.tail_mem time) who
  unfold killedDissipation killedCapacityDebtAccountDrop
    killedCapacityAbsorptionCarryLoss
  linarith

/-- The raw killed dissipations of the canonical capacity account are
summable.  This is stronger than pointwise convergence to zero but still does
not imply that any finite dissipation vanishes. -/
theorem summable_killedCapacityDissipation (who : ι) :
    Summable (fun time ↦
      killedDissipation seam.killedDebtSurvival
        (seam.killedDebtSource who)
        (seam.killedCapacityDebtAccount who) time) := by
  apply Summable.of_nonneg_of_le
  · exact (isKilledExcessive_iff_dissipation_nonneg _ _ _).mp
      (seam.killedCapacityDebtAccount_isKilledExcessive who)
  · exact seam.killedCapacityDissipation_le_drop_add_carryLoss who
  · exact (seam.summable_killedCapacityDebtAccountDrop who).add
      (seam.summable_killedCapacityAbsorptionCarryLoss who)

/-- Capacity dissipation tends to zero along the full canonical tail. -/
theorem killedCapacityDissipation_tendsto_zero (who : ι) :
    Tendsto (fun time ↦
      killedDissipation seam.killedDebtSurvival
        (seam.killedDebtSource who)
        (seam.killedCapacityDebtAccount who) time)
      atTop (nhds 0) :=
  (seam.summable_killedCapacityDissipation who).tendsto_atTop_zero

/-- A one-step boundary mismatch is literally the survival-scaled endpoint
mismatch. -/
theorem killedCapacityBoundaryMismatch_one
    (who : ι) (time : ℕ) :
    seam.killedCapacityBoundaryMismatch who time 1 =
      seam.killedDebtSurvival time *
        (seam.killedDebtReference who (time + 1) -
          seam.killedCapacityDebtAccount who (time + 1)) := by
  simp [killedCapacityBoundaryMismatch, killedBoundaryRemainder,
    killedPrefixWeight, Math.survivalProduct]
  ring

/-- **Best unconditional late-boundary alternative.**  The excess of the
one-step survival-scaled boundary mismatch over the initial mismatch is
exactly current capacity dissipation and tends to zero.  This is asymptotic
equality, not the finite nonexpansion needed for zero-face entry. -/
theorem boundaryMismatch_one_sub_initialMismatch_tendsto_zero
    (who : ι) :
    Tendsto (fun time ↦
      seam.killedCapacityBoundaryMismatch who time 1 -
        seam.killedCapacityInitialMismatch who time)
      atTop (nhds 0) := by
  have heq : (fun time ↦
      seam.killedCapacityBoundaryMismatch who time 1 -
        seam.killedCapacityInitialMismatch who time) =
      (fun time ↦ killedDissipation seam.killedDebtSurvival
        (seam.killedDebtSource who)
        (seam.killedCapacityDebtAccount who) time) := by
    funext time
    have hidentity :=
      seam.killedCapacityBoundaryMismatch_eq_initial_add_dissipation
        who time 1
    simp [killedSourceSum] at hidentity
    linarith
  rw [heq]
  exact seam.killedCapacityDissipation_tendsto_zero who

end QuittingCounterexampleSeamWitness

end GameTheory
