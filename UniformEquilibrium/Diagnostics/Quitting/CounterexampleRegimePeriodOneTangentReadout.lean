/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacket
import UniformEquilibrium.Quitting.Cycles.PeriodOneTangentAtlas

/-!
# Period-one readout of a quitting counterexample tangent

The charge-tangent extractor uses literal one-stage windows.  This file keeps
that fact in the output and reads each selected edge through the period-one
mass and evaluator atlas.

The repeated root below is only a diagnostic deviation attached to the
selected edge.  The source tail is not claimed to be periodic, and its later
annotations are not claimed to solve the repeated-root recursion.  Every
evaluator identity uses only the actual Nash--Bellman recurrence from
`tail t` to `tail (t + 1)`.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

/-- The operational product root on a selected one-stage edge. -/
def periodOneReadoutRoot (start : ℕ → ℕ) (index : ℕ) : ι → PMF Bool :=
  quittingDynamicDebtTailRoots seam.tail (start index)

/-- The root's conditional singleton-owner share. -/
def periodOneReadoutMass
    (start : ℕ → ℕ) (index : ℕ) (owner : ι) : ℝ :=
  quittingRootNormalizedSingletonMass (seam.periodOneReadoutRoot start index)
    owner

/-- The semantic endpoint tangent of periodically repeating the selected
root, measured from the actual far endpoint of the source edge. -/
def periodOneReadoutTangent
    (start : ℕ → ℕ) (index : ℕ) (who : ι) : ℝ :=
  quittingWindowRestartDelivery reward
      (quittingPeriodOneRootSequence (seam.periodOneReadoutRoot start index))
      who 0 1 -
    (seam.tail (start index + 1)).1.1 who

/-- The source edge at a selected start supplies exactly the one affine
recurrence required by the local period-one atlas. -/
theorem periodOneReadout_step
    (start : ℕ → ℕ) (index : ℕ) (who : ι) :
    (seam.tail (start index)).1.1 who =
      quittingRootAbsorbingContribution reward
          (seam.periodOneReadoutRoot start index) who +
        quittingStationaryContinueMass
            (seam.periodOneReadoutRoot start index) *
          (seam.tail (start index + 1)).1.1 who := by
  have hstep := congrFun (seam.tail_edge (start index)).1.1 who
  simpa [periodOneReadoutRoot, quittingDynamicDebtTailRoots,
    quittingRootSuccessorPayoff_apply_eq_affine] using hstep

private theorem oneStageWindow_absorptionMass_eq
    (window : QuittingFiniteRootWindow
      (quittingDynamicDebtTailRoots seam.tail))
    (hfuel : window.fuel = 1) :
    window.absorptionMass =
      quittingRootAbsorptionMass
        (quittingDynamicDebtTailRoots seam.tail window.start) := by
  rcases window with ⟨start, fuel⟩
  dsimp at hfuel ⊢
  subst fuel
  simp [QuittingFiniteRootWindow.absorptionMass,
    QuittingFiniteRootWindow.survivalWeight,
    QuittingFiniteRootWindow.rootAt]

private theorem oneStageWindow_normalizedSingletonOccupation_eq
    (window : QuittingFiniteRootWindow
      (quittingDynamicDebtTailRoots seam.tail))
    (hfuel : window.fuel = 1) (owner : ι) :
    window.normalizedSingletonOccupation owner =
      quittingRootNormalizedSingletonMass
        (quittingDynamicDebtTailRoots seam.tail window.start) owner := by
  rcases window with ⟨start, fuel⟩
  dsimp at hfuel ⊢
  subst fuel
  simp [QuittingFiniteRootWindow.normalizedSingletonOccupation,
    QuittingFiniteRootWindow.singletonMass,
    QuittingFiniteRootWindow.absorptionMass,
    QuittingFiniteRootWindow.survivalWeight,
    QuittingFiniteRootWindow.rootAt,
    quittingRootNormalizedSingletonMass]

/-- Subsequence data on which the actual one-stage roots have convergent
owner shares and semantic endpoint tangents. -/
structure CounterexampleRegimePeriodOneTangentReadout where
  packet : QuittingChargeTangentPacket reward
  start : ℕ → ℕ
  start_tendsto : Tendsto start atTop atTop
  absorption_pos : ∀ index,
    0 < quittingRootAbsorptionMass (seam.periodOneReadoutRoot start index)
  mass_tendsto : ∀ owner,
    Tendsto (fun index ↦ seam.periodOneReadoutMass start index owner)
      atTop (nhds (packet.mass owner))
  tangent_tendsto : ∀ who,
    Tendsto (fun index ↦ seam.periodOneReadoutTangent start index who)
      atTop (nhds (packet.tangent who))
  signed_coordinate :
    (∃ who, packet.tangent who < 0 ∧
      ∀ᶠ index in atTop,
        seam.periodOneReadoutTangent start index who < 0) ∨
    ∃ owner, 0 < packet.mass owner ∧ 0 < packet.tangent owner ∧
      ∀ᶠ index in atTop,
        0 < seam.periodOneReadoutMass start index owner ∧
          0 < seam.periodOneReadoutTangent start index owner

namespace CounterexampleRegimePeriodOneTangentReadout

variable (readout : CounterexampleRegimePeriodOneTangentReadout seam)

/-- The selected root's owner coefficient is exactly its normalized mass
coordinate. -/
theorem opponentContinue_sub_continue_eq_absorption_mul_mass
    (index : ℕ) (owner : ι) :
    quittingStationaryContinueMass
          (Function.update (seam.periodOneReadoutRoot readout.start index)
            owner (PMF.pure false)) -
        quittingStationaryContinueMass
          (seam.periodOneReadoutRoot readout.start index) =
      quittingRootAbsorptionMass
          (seam.periodOneReadoutRoot readout.start index) *
        seam.periodOneReadoutMass readout.start index owner := by
  exact quittingRootOpponentContinue_sub_continue_eq_absorption_mul_share
    (seam.periodOneReadoutRoot readout.start index) owner
    (readout.absorption_pos index)

/-- The complementary coefficient is the non-owner normalized mass. -/
theorem one_sub_opponentContinue_eq_absorption_mul_one_sub_mass
    (index : ℕ) (owner : ι) :
    1 - quittingStationaryContinueMass
          (Function.update (seam.periodOneReadoutRoot readout.start index)
            owner (PMF.pure false)) =
      quittingRootAbsorptionMass
          (seam.periodOneReadoutRoot readout.start index) *
        (1 - seam.periodOneReadoutMass readout.start index owner) := by
  exact
    one_sub_quittingRootOpponentContinue_eq_absorption_mul_one_sub_share
      (seam.periodOneReadoutRoot readout.start index) owner
      (readout.absorption_pos index)

/-- Both displayed evaluator slacks are nonnegative on every selected edge.
This is the strategic content of that one exact Nash--Bellman edge. -/
theorem slacks_nonneg (index : ℕ) (who : ι) :
    0 ≤ quittingPeriodicWindowPhaseSlack reward
        (quittingPeriodOneRootSequence
          (seam.periodOneReadoutRoot readout.start index)) who 1
        ((seam.tail (readout.start index)).1.1 who) ∧
      0 ≤ quittingPeriodicWindowRefusalSlack reward
        (quittingPeriodOneRootSequence
          (seam.periodOneReadoutRoot readout.start index)) who 1
        ((seam.tail (readout.start index)).1.1 who)
        ((seam.tail (readout.start index + 1)).1.1 who) := by
  have hedge := (seam.tail_edge (readout.start index)).1
  have hstep := congrFun hedge.1 who
  have hnash :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (seam.tail (readout.start index + 1)).1.1
      (seam.periodOneReadoutRoot readout.start index)).1 (by
        simpa [periodOneReadoutRoot, quittingDynamicDebtTailRoots] using
          hedge.2)
  exact quittingPeriodOne_slacks_nonneg_of_step_nash reward
    (seam.periodOneReadoutRoot readout.start index) who
    ((seam.tail (readout.start index)).1.1 who)
    (seam.tail (readout.start index + 1)).1.1
    (by
      simpa [periodOneReadoutRoot, quittingDynamicDebtTailRoots] using hstep)
    hnash

/-- Positive prescribed Quit probability makes the selected edge's phase
slack vanish by exact root complementarity. -/
theorem phaseSlack_eq_zero_of_quitProbability_pos
    (index : ℕ) (who : ι)
    (hquit : 0 <
      (seam.periodOneReadoutRoot readout.start index who true).toReal) :
    quittingPeriodicWindowPhaseSlack reward
        (quittingPeriodOneRootSequence
          (seam.periodOneReadoutRoot readout.start index)) who 1
        ((seam.tail (readout.start index)).1.1 who) = 0 := by
  have hedge := (seam.tail_edge (readout.start index)).1
  have hstep := congrFun hedge.1 who
  have hnash :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (seam.tail (readout.start index + 1)).1.1
      (seam.periodOneReadoutRoot readout.start index)).1 (by
        simpa [periodOneReadoutRoot, quittingDynamicDebtTailRoots] using
          hedge.2)
  exact quittingPeriodOne_phaseSlack_eq_zero_of_quitProbability_pos reward
    (seam.periodOneReadoutRoot readout.start index) who
    ((seam.tail (readout.start index)).1.1 who)
    (seam.tail (readout.start index + 1)).1.1
    (by
      simpa [periodOneReadoutRoot, quittingDynamicDebtTailRoots] using hstep)
    hnash hquit

/-- Positive prescribed Continue probability makes the selected edge's
refusal slack vanish by exact root complementarity. -/
theorem refusalSlack_eq_zero_of_continueProbability_pos
    (index : ℕ) (who : ι)
    (hcontinue : 0 <
      (seam.periodOneReadoutRoot readout.start index who false).toReal) :
    quittingPeriodicWindowRefusalSlack reward
        (quittingPeriodOneRootSequence
          (seam.periodOneReadoutRoot readout.start index)) who 1
        ((seam.tail (readout.start index)).1.1 who)
        ((seam.tail (readout.start index + 1)).1.1 who) = 0 := by
  have hedge := (seam.tail_edge (readout.start index)).1
  have hstep := congrFun hedge.1 who
  have hnash :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (seam.tail (readout.start index + 1)).1.1
      (seam.periodOneReadoutRoot readout.start index)).1 (by
        simpa [periodOneReadoutRoot, quittingDynamicDebtTailRoots] using
          hedge.2)
  exact quittingPeriodOne_refusalSlack_eq_zero_of_continueProbability_pos
    reward (seam.periodOneReadoutRoot readout.start index) who
    ((seam.tail (readout.start index)).1.1 who)
    (seam.tail (readout.start index + 1)).1.1
    (by
      simpa [periodOneReadoutRoot, quittingDynamicDebtTailRoots] using hstep)
    hnash hcontinue

/-- Exact phase readout on an actual selected edge.  The slack is retained;
no optimality beyond the source Nash--Bellman edge is asserted. -/
theorem bestPhaseStop_sub_restartDelivery_eq
    (index : ℕ) (who : ι) :
    quittingPeriodicWindowBestPhaseStop reward
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index)) who 1 -
        quittingWindowRestartDelivery reward
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index)) who 0 1 =
      -quittingStationaryContinueMass
          (seam.periodOneReadoutRoot readout.start index) *
          seam.periodOneReadoutTangent readout.start index who -
        quittingPeriodicWindowPhaseSlack reward
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index)) who 1
          ((seam.tail (readout.start index)).1.1 who) := by
  simpa [periodOneReadoutTangent] using
    quittingPeriodOneBestPhaseStop_sub_restartDelivery_eq_tangent_of_step
      reward (seam.periodOneReadoutRoot readout.start index) who
      ((seam.tail (readout.start index)).1.1 who)
      ((seam.tail (readout.start index + 1)).1.1 who)
      (seam.periodOneReadout_step readout.start index who)
      (readout.absorption_pos index)

/-- Exact refusal readout on the proper-mass branch. -/
theorem refusalValue_sub_restartDelivery_eq
    (index : ℕ) (who : ι)
    (hproper : seam.periodOneReadoutMass readout.start index who < 1) :
    quittingPeriodicWindowRefusalValue reward
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index)) who -
        quittingWindowRestartDelivery reward
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index)) who 0 1 =
      (seam.periodOneReadoutMass readout.start index who /
          (1 - seam.periodOneReadoutMass readout.start index who)) *
          seam.periodOneReadoutTangent readout.start index who -
        quittingPeriodicWindowRefusalSlack reward
            (quittingPeriodOneRootSequence
              (seam.periodOneReadoutRoot readout.start index)) who 1
            ((seam.tail (readout.start index)).1.1 who)
            ((seam.tail (readout.start index + 1)).1.1 who) /
          (quittingRootAbsorptionMass
              (seam.periodOneReadoutRoot readout.start index) *
            (1 - seam.periodOneReadoutMass readout.start index who)) := by
  simpa [periodOneReadoutMass, periodOneReadoutTangent] using
    quittingPeriodOneRefusalValue_sub_restartDelivery_eq_tangent_of_step
      reward (seam.periodOneReadoutRoot readout.start index) who
      ((seam.tail (readout.start index)).1.1 who)
      ((seam.tail (readout.start index + 1)).1.1 who)
      (seam.periodOneReadout_step readout.start index who)
      (readout.absorption_pos index) hproper

/-- Full normalized mass is the isolated-player boundary; the refusal
formula is deliberately not divided by its zero opponent gap. -/
theorem fullMass_boundary
    (index : ℕ) (who : ι)
    (hfull : seam.periodOneReadoutMass readout.start index who = 1) :
    quittingOpponentSurvivalWeight
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index)) who 0 1 = 1 ∧
      1 - quittingOpponentSurvivalWeight
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index)) who 0 1 = 0 ∧
      ∀ other, other ≠ who →
        seam.periodOneReadoutRoot readout.start index other =
          PMF.pure false := by
  exact quittingPeriodOne_fullSingletonMass_boundary
    (seam.periodOneReadoutRoot readout.start index) who
    (readout.absorption_pos index) hfull

/-- A packet coordinate cannot simultaneously have full mass and a positive
tangent: positive mass pins the boundary to the singleton payoff, while full
mass makes the singleton mixture that same payoff. -/
theorem packet_mass_lt_one_of_pos_mass_pos_tangent
    (owner : ι) (hmass : 0 < readout.packet.mass owner)
    (htangent : 0 < readout.packet.tangent owner) :
    readout.packet.mass owner < 1 := by
  have hmassLe : readout.packet.mass owner ≤ 1 := by
    calc
      readout.packet.mass owner ≤
          ∑ player : ι, readout.packet.mass player :=
        Finset.single_le_sum
          (fun player _ ↦ readout.packet.mass_nonneg player)
          (Finset.mem_univ owner)
      _ = 1 := readout.packet.mass_sum
  apply lt_of_le_of_ne hmassLe
  intro hmassEq
  have hone : readout.packet.mass owner = 1 := hmassEq
  have herase :
      ∑ other ∈ (Finset.univ.erase owner : Finset ι),
          readout.packet.mass other = 0 := by
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset ι))
      (f := readout.packet.mass) (a := owner) (Finset.mem_univ owner)
    rw [readout.packet.mass_sum, hone] at hsplit
    linarith
  have hzero : ∀ other ∈ (Finset.univ.erase owner : Finset ι),
      readout.packet.mass other = 0 := by
    intro other hother
    apply le_antisymm
    · calc
        readout.packet.mass other ≤
            ∑ player ∈ (Finset.univ.erase owner : Finset ι),
              readout.packet.mass player :=
          Finset.single_le_sum
            (fun player _ ↦ readout.packet.mass_nonneg player) hother
        _ = 0 := herase
    · exact readout.packet.mass_nonneg other
  have hweighted :
      ∑ other ∈ (Finset.univ.erase owner : Finset ι),
          readout.packet.mass other *
            reward (quittingSingletonTerminal other) owner = 0 := by
    apply Finset.sum_eq_zero
    intro other hother
    rw [hzero other hother, zero_mul]
  have hmixture :
      quittingSingletonMixture reward readout.packet.mass owner =
        reward (quittingSingletonTerminal owner) owner := by
    unfold quittingSingletonMixture
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ owner), hone,
      one_mul, hweighted, zero_add]
  have htangentEq := readout.packet.tangent_eq owner
  rw [hmixture,
    readout.packet.positive_mass_pins_boundary owner hmass] at htangentEq
  linarith

/-- The active-positive packet branch has an honest proper-mass refusal
readout.  Eventually the selected root gives the owner positive probability
to Continue, exact complementarity kills refusal slack, and the repeated-root
refusal evaluator is strictly above restart.  This evaluates a diagnostic
repetition of the selected root; it does not attach that repetition to the
source tail. -/
theorem activePositive_refusalGain
    (owner : ι) (hmass : 0 < readout.packet.mass owner)
    (htangent : 0 < readout.packet.tangent owner) :
    readout.packet.mass owner < 1 ∧
      Tendsto (fun index ↦
        quittingPeriodicWindowRefusalValue reward
            (quittingPeriodOneRootSequence
              (seam.periodOneReadoutRoot readout.start index)) owner -
          quittingWindowRestartDelivery reward
            (quittingPeriodOneRootSequence
              (seam.periodOneReadoutRoot readout.start index)) owner 0 1)
        atTop (nhds ((readout.packet.mass owner /
          (1 - readout.packet.mass owner)) * readout.packet.tangent owner)) ∧
      ∀ᶠ index in atTop,
        0 < seam.periodOneReadoutMass readout.start index owner ∧
          seam.periodOneReadoutMass readout.start index owner < 1 ∧
          0 < seam.periodOneReadoutTangent readout.start index owner ∧
          0 < (seam.periodOneReadoutRoot readout.start index owner false).toReal ∧
          quittingPeriodicWindowRefusalSlack reward
              (quittingPeriodOneRootSequence
                (seam.periodOneReadoutRoot readout.start index)) owner 1
              ((seam.tail (readout.start index)).1.1 owner)
              ((seam.tail (readout.start index + 1)).1.1 owner) = 0 ∧
          0 < quittingPeriodicWindowRefusalValue reward
                (quittingPeriodOneRootSequence
                  (seam.periodOneReadoutRoot readout.start index)) owner -
              quittingWindowRestartDelivery reward
                (quittingPeriodOneRootSequence
                  (seam.periodOneReadoutRoot readout.start index)) owner 0 1 := by
  have hmassLt :=
    packet_mass_lt_one_of_pos_mass_pos_tangent seam readout owner
      hmass htangent
  have hcontinueTendsto :
      Tendsto (fun index ↦
        (seam.periodOneReadoutRoot readout.start index owner false).toReal)
        atTop (nhds 1) := by
    simpa [periodOneReadoutRoot, Function.comp_def] using
      (seam.continueProbability_tendsto_one owner).comp readout.start_tendsto
  have hbase : ∀ᶠ index in atTop,
      0 < seam.periodOneReadoutMass readout.start index owner ∧
        seam.periodOneReadoutMass readout.start index owner < 1 ∧
        0 < seam.periodOneReadoutTangent readout.start index owner ∧
        0 < (seam.periodOneReadoutRoot readout.start index owner false).toReal := by
    filter_upwards
      [(readout.mass_tendsto owner).eventually_const_lt hmass,
        (readout.mass_tendsto owner).eventually_lt_const hmassLt,
        (readout.tangent_tendsto owner).eventually_const_lt htangent,
        hcontinueTendsto.eventually_const_lt zero_lt_one] with
        index hmassPos hmassProper htangentPos hcontinuePos
    exact ⟨hmassPos, hmassProper, htangentPos, hcontinuePos⟩
  have hgainEq : ∀ᶠ index in atTop,
      quittingPeriodicWindowRefusalValue reward
            (quittingPeriodOneRootSequence
              (seam.periodOneReadoutRoot readout.start index)) owner -
          quittingWindowRestartDelivery reward
            (quittingPeriodOneRootSequence
              (seam.periodOneReadoutRoot readout.start index)) owner 0 1 =
        (seam.periodOneReadoutMass readout.start index owner /
          (1 - seam.periodOneReadoutMass readout.start index owner)) *
            seam.periodOneReadoutTangent readout.start index owner := by
    filter_upwards [hbase] with index hindex
    have hslack := refusalSlack_eq_zero_of_continueProbability_pos
      seam readout index owner hindex.2.2.2
    rw [refusalValue_sub_restartDelivery_eq seam readout
      index owner hindex.2.1, hslack]
    simp
  have halgebra :
      Tendsto (fun index ↦
        (seam.periodOneReadoutMass readout.start index owner /
          (1 - seam.periodOneReadoutMass readout.start index owner)) *
            seam.periodOneReadoutTangent readout.start index owner)
        atTop (nhds ((readout.packet.mass owner /
          (1 - readout.packet.mass owner)) * readout.packet.tangent owner)) := by
    have hdenominator : Tendsto (fun index : ℕ ↦
        (1 : ℝ) - seam.periodOneReadoutMass readout.start index owner)
        atTop (nhds (1 - readout.packet.mass owner)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
        atTop (nhds 1)).sub (readout.mass_tendsto owner)
    exact ((readout.mass_tendsto owner).div hdenominator
      (by linarith : 1 - readout.packet.mass owner ≠ 0)).mul
        (readout.tangent_tendsto owner)
  have hgainTendsto := halgebra.congr' (hgainEq.mono fun _ h ↦ h.symm)
  refine ⟨hmassLt, hgainTendsto, ?_⟩
  filter_upwards [hbase, hgainEq] with index hindex hgain
  have hslack := refusalSlack_eq_zero_of_continueProbability_pos
    seam readout index owner hindex.2.2.2
  refine ⟨hindex.1, hindex.2.1, hindex.2.2.1, hindex.2.2.2,
    hslack, ?_⟩
  rw [hgain]
  exact mul_pos (div_pos hindex.1 (sub_pos.mpr hindex.2.1))
    hindex.2.2.1

end CounterexampleRegimePeriodOneTangentReadout

/-- Either the optimized tail is eventually all-Continue, or its literal
one-stage extraction supplies a period-one tangent readout. -/
theorem eventually_allContinue_or_exists_periodOneTangentReadout :
    (∃ threshold, ∀ time, threshold ≤ time →
      quittingDynamicDebtTailRoots seam.tail time =
        (quittingAllContinueRoot : ι → PMF Bool)) ∨
      Nonempty (CounterexampleRegimePeriodOneTangentReadout seam) := by
  rcases seam.eventually_allContinue_or_exists_oneStage_chargeTangentPacket with
    hplateau | ⟨packet, window, hstart, hfuel, habsorption,
      hmass, htangent⟩
  · exact Or.inl hplateau
  · right
    let start : ℕ → ℕ := fun index ↦ (window index).start
    have habsorptionRoot : ∀ index,
        0 < quittingRootAbsorptionMass
          (seam.periodOneReadoutRoot start index) := by
      intro index
      have hmassEq := seam.oneStageWindow_absorptionMass_eq
        (window index) (hfuel index)
      have hpositive := habsorption index
      rw [hmassEq] at hpositive
      simpa [periodOneReadoutRoot, start] using hpositive
    have hmassRoot : ∀ owner,
        Tendsto (fun index ↦ seam.periodOneReadoutMass start index owner)
          atTop (nhds (packet.mass owner)) := by
      intro owner
      apply (hmass owner).congr'
      filter_upwards [] with index
      simpa [periodOneReadoutMass, periodOneReadoutRoot, start] using
        seam.oneStageWindow_normalizedSingletonOccupation_eq
          (window index) (hfuel index) owner
    have htangentRoot : ∀ who,
        Tendsto (fun index ↦ seam.periodOneReadoutTangent start index who)
          atTop (nhds (packet.tangent who)) := by
      intro who
      apply (htangent who).congr'
      filter_upwards [] with index
      let root := seam.periodOneReadoutRoot start index
      let initial := (seam.tail (start index)).1.1 who
      let terminal := (seam.tail (start index + 1)).1.1 who
      have hstepFull := congrFun (seam.tail_edge (start index)).1.1 who
      have hstep : initial =
          quittingRootAbsorbingContribution reward root who +
            quittingStationaryContinueMass root * terminal := by
        simpa [root, initial, terminal, periodOneReadoutRoot,
          quittingDynamicDebtTailRoots,
          quittingRootSuccessorPayoff_apply_eq_affine] using hstepFull
      have hsemantic :=
        quittingPeriodOne_absorption_mul_restartDelivery_sub_terminal_of_step
          reward root who initial terminal hstep (habsorptionRoot index)
      have hwindowMass := seam.oneStageWindow_absorptionMass_eq
        (window index) (hfuel index)
      rw [normalizedEndpointTangent, periodOneReadoutTangent,
        hfuel index, Nat.add_one, hwindowMass]
      change (initial - terminal) /
          quittingRootAbsorptionMass root =
        quittingWindowRestartDelivery reward
            (quittingPeriodOneRootSequence root) who 0 1 - terminal
      apply (div_eq_iff (habsorptionRoot index).ne').2
      rw [← hsemantic]
      ring
    have hsigned :
        (∃ who, packet.tangent who < 0 ∧
          ∀ᶠ index in atTop,
            seam.periodOneReadoutTangent start index who < 0) ∨
        ∃ owner, 0 < packet.mass owner ∧ 0 < packet.tangent owner ∧
          ∀ᶠ index in atTop,
            0 < seam.periodOneReadoutMass start index owner ∧
              0 < seam.periodOneReadoutTangent start index owner := by
      rcases regime.chargeTangentPacket_underfunded_or_active_funded packet with
        ⟨who, hnegative⟩ | ⟨owner, hmassPos, htangentPos⟩
      · exact Or.inl
          ⟨who, hnegative,
            (htangentRoot who).eventually_lt_const hnegative⟩
      · exact Or.inr ⟨owner, hmassPos, htangentPos, by
          filter_upwards
            [(hmassRoot owner).eventually_const_lt hmassPos,
              (htangentRoot owner).eventually_const_lt htangentPos] with
              index hmassIndex htangentIndex
          exact ⟨hmassIndex, htangentIndex⟩⟩
    exact ⟨{
      packet := packet
      start := start
      start_tendsto := hstart
      absorption_pos := habsorptionRoot
      mass_tendsto := hmassRoot
      tangent_tendsto := htangentRoot
      signed_coordinate := hsigned
    }⟩

end QuittingCounterexampleSeamWitness

end GameTheory
