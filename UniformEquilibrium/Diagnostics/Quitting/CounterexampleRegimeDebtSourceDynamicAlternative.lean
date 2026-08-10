/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtSourceObstructionCarrier
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeKilledCapacityPotential

/-!
# Dynamic alternative for the debt-source exposed face

The playerwise debt-source coordinate turns the diagonal dynamic-debt seam
into a literal grade-one price.  Along the canonical optimized tail its
finite and infinite chronological prices are exactly the killed source terms
in dynamic-debt conservation.  This is the correct survival scale: the raw
source tends to zero, but that does not imply that any finite source is zero.

There is nevertheless an exact local alternative.  For a selected player,
either the current tail edge lies in the zero-source exposed face, the next
edge does, or the capacity-derived excessive account has strictly positive
killed dissipation at the current edge.  The last branch is priced exactly
by growth of the survival-scaled boundary mismatch between exact debt and
the capacity account.

Consequently, nonexpansion of that boundary mismatch forces zero-face entry
at the current or next edge, and the same premise at arbitrarily late starts
forces recurrence.  This boundary/return premise is not derived here: the
counterexample seam and the canonical capacity bounds do not compare their
surviving boundaries.  No absorption-normal argument, strategic repair, or
boundary realization is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.LinearProgramming.FlowCostateDuality Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

/-! ## Canonical tail flows and exact survival pricing -/

/-- The enriched raw obstruction of the canonical one-stage tail edge. -/
def tailDebtSourceObstructionFlow (time : ℕ) :
    RawGradedFlow QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι) :=
  quittingDebtSourceObstructionFlow
    (seam.tail time, seam.tail (time + 1))

/-- Every canonical enriched tail flow belongs to the exact compact source
carrier. -/
theorem tailDebtSourceObstructionFlow_mem (time : ℕ) :
    seam.tailDebtSourceObstructionFlow time ∈
      quittingDebtSourceOneStageObstructionCarrier reward :=
  seam.debtSourceTailEdgeFlow_mem time

/-- The selected coordinate co-state prices exactly the canonical diagonal
debt source at one date. -/
@[simp]
theorem pair_tailDebtSourceObstructionFlow
    (who : ι) (time : ℕ) :
    pair (quittingDebtSourceCostate who)
        (seam.tailDebtSourceObstructionFlow time) =
      seam.killedDebtSource who time := by
  rw [tailDebtSourceObstructionFlow,
    pair_quittingDebtSourceCostate_edge]
  rfl

/-- A canonical tail flow lies in the selected zero-source exposed face
exactly when its literal diagonal debt source vanishes. -/
theorem tailDebtSourceObstructionFlow_mem_zeroFace_iff
    (who : ι) (time : ℕ) :
    seam.tailDebtSourceObstructionFlow time ∈
        exposedFace (quittingDebtSourceZeroFaceCostate who)
          (quittingDebtSourceOneStageObstructionCarrier reward) ↔
      seam.killedDebtSource who time = 0 := by
  rw [seam.mem_exposedFace_quittingDebtSourceZeroFaceCostate_iff who]
  constructor
  · rintro ⟨_, hzero⟩
    exact hzero
  · intro hzero
    exact ⟨seam.tailDebtSourceObstructionFlow_mem time, hzero⟩

/-- Exact finite survival pricing of the canonical debt-source co-state.
The terminal debt boundary remains visible. -/
theorem debt_eq_surviving_add_sum_pair_tailDebtSource
    (who : ι) (start fuel : ℕ) :
    seam.killedDebtReference who start =
      quittingJointSurvivalWeight
          (quittingDynamicDebtTailRoots seam.tail) start fuel *
          seam.killedDebtReference who (start + fuel) +
        ∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight
              (quittingDynamicDebtTailRoots seam.tail) start offset *
            pair (quittingDebtSourceCostate who)
              (seam.tailDebtSourceObstructionFlow (start + offset)) := by
  simpa only [killedDebtReference, pair_tailDebtSourceObstructionFlow,
    killedDebtSource] using seam.debt_conservation who start fuel

/-- Exact infinite survival pricing.  Persistent positive finite-date
prices are compatible with the displayed positive harmonic boundary. -/
theorem debt_eq_survivalLimit_mul_limit_add_tsum_pair_tailDebtSource
    (who : ι) (start : ℕ) :
    seam.killedDebtReference who start =
      quittingJointSurvivalLimit
          (quittingDynamicDebtTailRoots seam.tail) start *
          seam.limit.debt who +
        ∑' offset : ℕ,
          quittingJointSurvivalWeight
              (quittingDynamicDebtTailRoots seam.tail) start offset *
            pair (quittingDebtSourceCostate who)
              (seam.tailDebtSourceObstructionFlow (start + offset)) := by
  simpa only [killedDebtReference, pair_tailDebtSourceObstructionFlow,
    killedDebtSource] using
      seam.debt_eq_survivalLimit_mul_limit_add_tsum_weightedSeam who start

/-! ## The exact capacity/debt boundary mismatch -/

/-- Difference between the surviving exact-debt boundary and the surviving
capacity-account boundary over a finite window. -/
def killedCapacityBoundaryMismatch
    (who : ι) (start fuel : ℕ) : ℝ :=
  killedBoundaryRemainder seam.killedDebtSurvival
      (seam.killedDebtReference who) start fuel -
    killedBoundaryRemainder seam.killedDebtSurvival
      (seam.killedCapacityDebtAccount who) start fuel

/-- **Exact mismatch transport.**  Boundary mismatch equals initial
mismatch plus every survival-priced dissipation of the capacity account. -/
theorem killedCapacityBoundaryMismatch_eq_initial_add_dissipation
    (who : ι) (start fuel : ℕ) :
    seam.killedCapacityBoundaryMismatch who start fuel =
      seam.killedCapacityInitialMismatch who start +
        killedSourceSum seam.killedDebtSurvival
          (killedDissipation seam.killedDebtSurvival
            (seam.killedDebtSource who)
            (seam.killedCapacityDebtAccount who)) start fuel := by
  have href := seam.killedDebtReference_eq_killedTailAccount who start fuel
  have hcapacity := potential_eq_source_add_dissipationSum_add_boundary
    seam.killedDebtSurvival (seam.killedDebtSource who)
      (seam.killedCapacityDebtAccount who) start fuel
  unfold killedTailAccount at href
  unfold killedCapacityBoundaryMismatch killedCapacityInitialMismatch
  linarith

/-- Boundary mismatch can only increase beyond the initial mismatch.  This
is the exact survival-scaled monotonicity supplied by excessivity. -/
theorem killedCapacityInitialMismatch_le_boundaryMismatch
    (who : ι) (start fuel : ℕ) :
    seam.killedCapacityInitialMismatch who start ≤
      seam.killedCapacityBoundaryMismatch who start fuel := by
  rw [seam.killedCapacityBoundaryMismatch_eq_initial_add_dissipation]
  exact le_add_of_nonneg_right
    (killedSourceSum_nonneg seam.killedDebtSurvival
      (killedDissipation seam.killedDebtSurvival
        (seam.killedDebtSource who)
        (seam.killedCapacityDebtAccount who))
      seam.killedDebtSurvival_nonneg
      ((isKilledExcessive_iff_dissipation_nonneg _ _ _).mp
        (seam.killedCapacityDebtAccount_isKilledExcessive who))
      start fuel)

/-! ## Local zero-face/dissipation alternative -/

/-- If two consecutive playerwise debt sources are positive, the canonical
capacity account has strict killed dissipation at the first date.  The
reason is exact: positive current source makes absorption positive, while
positive next source makes the next capacity account positive, so replacing
its full carry by survival-discounted carry loses a strictly positive term. -/
theorem killedCapacityDissipation_pos_of_source_pos_succ
    (who : ι) (time : ℕ)
    (hcurrent : 0 < seam.killedDebtSource who time)
    (hnext : 0 < seam.killedDebtSource who (time + 1)) :
    0 < killedDissipation seam.killedDebtSurvival
      (seam.killedDebtSource who)
      (seam.killedCapacityDebtAccount who) time := by
  have hsourceLe := quittingDynamicDebtSeam_le_cap_mul_absorptionMass
    (state := seam.tail time) (seam.tail_mem time) who
  have habsorptionNonneg :
      0 ≤ quittingDynamicDebtTailAbsorptionCharge seam.tail time :=
    quittingDynamicDebtTailAbsorptionCharge_nonneg seam.tail time
  have hcapNonneg :
      0 ≤ quittingPositiveSingletonDebtCap reward who := le_max_left _ _
  have hsourceLe' : seam.killedDebtSource who time ≤
      quittingPositiveSingletonDebtCap reward who *
        quittingDynamicDebtTailAbsorptionCharge seam.tail time := by
    simpa [killedDebtSource, quittingDynamicDebtTailAbsorptionCharge] using
      hsourceLe
  have habsorptionPos :
      0 < quittingDynamicDebtTailAbsorptionCharge seam.tail time := by
    by_contra hnot
    have hzero : quittingDynamicDebtTailAbsorptionCharge seam.tail time = 0 :=
      le_antisymm (le_of_not_gt hnot) habsorptionNonneg
    rw [hzero, mul_zero] at hsourceLe'
    linarith
  have hsurvivalLt : seam.killedDebtSurvival time < 1 := by
    change quittingStationaryContinueMass
      (quittingRootOfSimplex (seam.tail time).1.2) < 1
    change 0 < 1 - quittingStationaryContinueMass
      (quittingRootOfSimplex (seam.tail time).1.2) at habsorptionPos
    linarith
  have hnextAccountPos :
      0 < seam.killedCapacityDebtAccount who (time + 1) := by
    have hpayNext :=
      seam.killedDebtSource_add_capacityDebtAccount_succ_le who (time + 1)
    have hfarNonneg :=
      seam.killedCapacityDebtAccount_nonneg who (time + 1 + 1)
    linarith
  have hpayCurrent :=
    seam.killedDebtSource_add_capacityDebtAccount_succ_le who time
  unfold killedDissipation
  nlinarith [mul_pos (sub_pos.mpr hsurvivalLt) hnextAccountPos]

/-- **Unconditional local alternative.**  At every date, the canonical tail
is in the selected zero-source face now, is in it next, or produces strict
killed-capacity dissipation now. -/
theorem zeroFace_or_succ_zeroFace_or_capacityDissipation_pos
    (who : ι) (time : ℕ) :
    seam.tailDebtSourceObstructionFlow time ∈
        exposedFace (quittingDebtSourceZeroFaceCostate who)
          (quittingDebtSourceOneStageObstructionCarrier reward) ∨
      seam.tailDebtSourceObstructionFlow (time + 1) ∈
        exposedFace (quittingDebtSourceZeroFaceCostate who)
          (quittingDebtSourceOneStageObstructionCarrier reward) ∨
      0 < killedDissipation seam.killedDebtSurvival
        (seam.killedDebtSource who)
        (seam.killedCapacityDebtAccount who) time := by
  by_cases hcurrent : seam.killedDebtSource who time = 0
  · exact Or.inl
      ((seam.tailDebtSourceObstructionFlow_mem_zeroFace_iff who time).2
        hcurrent)
  by_cases hnext : seam.killedDebtSource who (time + 1) = 0
  · exact Or.inr (Or.inl
      ((seam.tailDebtSourceObstructionFlow_mem_zeroFace_iff who (time + 1)).2
        hnext))
  · apply Or.inr (Or.inr _)
    exact seam.killedCapacityDissipation_pos_of_source_pos_succ who time
      (lt_of_le_of_ne
        (quittingDynamicDebtSeam_nonneg
          (seam.tail time) (seam.tail_mem time) who)
        (Ne.symm hcurrent))
      (lt_of_le_of_ne
        (quittingDynamicDebtSeam_nonneg
          (seam.tail (time + 1)) (seam.tail_mem (time + 1)) who)
        (Ne.symm hnext))

/-- If neither of two consecutive canonical flows is in the zero-source
face, every positive-length window starting there has boundary mismatch
strictly larger than its initial mismatch. -/
theorem initialMismatch_lt_boundaryMismatch_of_not_zeroFace_and_succ
    (who : ι) (start fuel : ℕ) (hfuel : 0 < fuel)
    (hcurrent : seam.tailDebtSourceObstructionFlow start ∉
      exposedFace (quittingDebtSourceZeroFaceCostate who)
        (quittingDebtSourceOneStageObstructionCarrier reward))
    (hnext : seam.tailDebtSourceObstructionFlow (start + 1) ∉
      exposedFace (quittingDebtSourceZeroFaceCostate who)
        (quittingDebtSourceOneStageObstructionCarrier reward)) :
    seam.killedCapacityInitialMismatch who start <
      seam.killedCapacityBoundaryMismatch who start fuel := by
  have hsourceCurrent : 0 < seam.killedDebtSource who start :=
    lt_of_le_of_ne
      (quittingDynamicDebtSeam_nonneg
        (seam.tail start) (seam.tail_mem start) who)
      (Ne.symm (fun hzero ↦ hcurrent
        ((seam.tailDebtSourceObstructionFlow_mem_zeroFace_iff who start).2
          hzero)))
  have hsourceNext : 0 < seam.killedDebtSource who (start + 1) :=
    lt_of_le_of_ne
      (quittingDynamicDebtSeam_nonneg
        (seam.tail (start + 1)) (seam.tail_mem (start + 1)) who)
      (Ne.symm (fun hzero ↦ hnext
        ((seam.tailDebtSourceObstructionFlow_mem_zeroFace_iff who
          (start + 1)).2 hzero)))
  have hlocal := seam.killedCapacityDissipation_pos_of_source_pos_succ
    who start hsourceCurrent hsourceNext
  have hsumPos : 0 < killedSourceSum seam.killedDebtSurvival
      (killedDissipation seam.killedDebtSurvival
        (seam.killedDebtSource who)
        (seam.killedCapacityDebtAccount who)) start fuel := by
    unfold killedSourceSum
    apply Finset.sum_pos'
    · intro offset _
      exact mul_nonneg
        (killedPrefixWeight_nonneg seam.killedDebtSurvival
          seam.killedDebtSurvival_nonneg start offset)
        (((isKilledExcessive_iff_dissipation_nonneg _ _ _).mp
          (seam.killedCapacityDebtAccount_isKilledExcessive who))
            (start + offset))
    · refine ⟨0, by simp [hfuel], ?_⟩
      simpa using hlocal
  rw [seam.killedCapacityBoundaryMismatch_eq_initial_add_dissipation]
  linarith

/-- **Sharp conditional entry criterion.**  If the survival-scaled boundary
mismatch does not grow beyond the initial mismatch on one positive-length
window, the canonical tail is in the selected zero-source face at the start
or at the next edge. -/
theorem zeroFace_or_succ_zeroFace_of_boundaryMismatch_le
    (who : ι) (start fuel : ℕ) (hfuel : 0 < fuel)
    (hmismatch : seam.killedCapacityBoundaryMismatch who start fuel ≤
      seam.killedCapacityInitialMismatch who start) :
    seam.tailDebtSourceObstructionFlow start ∈
        exposedFace (quittingDebtSourceZeroFaceCostate who)
          (quittingDebtSourceOneStageObstructionCarrier reward) ∨
      seam.tailDebtSourceObstructionFlow (start + 1) ∈
        exposedFace (quittingDebtSourceZeroFaceCostate who)
          (quittingDebtSourceOneStageObstructionCarrier reward) := by
  by_contra hneither
  push Not at hneither
  have hstrict :=
    seam.initialMismatch_lt_boundaryMismatch_of_not_zeroFace_and_succ
      who start fuel hfuel hneither.1 hneither.2
  exact (not_lt_of_ge hmismatch) hstrict

/-- Boundary-mismatch nonexpansion at arbitrarily late starts forces
playerwise zero-source face recurrence.  This isolates the precise
boundary/return premise not supplied by the current counterexample data. -/
theorem zeroFace_recurrence_of_eventual_boundaryMismatch_le
    (who : ι)
    (hreturn : ∀ cutoff, ∃ fuel, 0 < fuel ∧
      seam.killedCapacityBoundaryMismatch who cutoff fuel ≤
        seam.killedCapacityInitialMismatch who cutoff) :
    ∀ cutoff, ∃ time, cutoff ≤ time ∧
      seam.tailDebtSourceObstructionFlow time ∈
        exposedFace (quittingDebtSourceZeroFaceCostate who)
          (quittingDebtSourceOneStageObstructionCarrier reward) := by
  intro cutoff
  obtain ⟨fuel, hfuel, hmismatch⟩ := hreturn cutoff
  rcases seam.zeroFace_or_succ_zeroFace_of_boundaryMismatch_le
      who cutoff fuel hfuel hmismatch with hcurrent | hnext
  · exact ⟨cutoff, le_rfl, hcurrent⟩
  · exact ⟨cutoff + 1, Nat.le_add_right cutoff 1, hnext⟩

end QuittingCounterexampleSeamWitness

end GameTheory
