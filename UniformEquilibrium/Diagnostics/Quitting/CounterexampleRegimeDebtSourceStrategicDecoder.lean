/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtSourceDynamicAlternative
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacketEnergy
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodOneTangentReadout
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeExactCycleStrata

/-!
# Strategic boundary of the debt-source exposed face

The playerwise debt-source face has an exact game-facing decoder once the
missing chronological datum is supplied.  A finite word of exact boxed debt
edges which lies in every playerwise zero-source face transports the augmented
cap at every phase.  If that word closes, absorbs, and is punishment
admissible, its displayed roots and augmented caps form a solved exact
quitting cycle.  Thus the required "common word" is recorded below as one
literal proof-carrying type rather than hidden in a recurrence or separation
hypothesis.

The canonical tail supplies less.  At each selected player and date it gives
zero-face entry now, zero-face entry next, or strict priced capacity
dissipation.  Independently, a non-plateau one-stage tangent readout gives one
of two exact strategic diagnostics:

* a negative tangent coordinate is eventually either absent from the current
  product-root support or yields a strictly profitable phase-stop evaluator;
* after all negative coordinates are excluded, an active positive coordinate
  yields a strictly profitable repeated-root refusal evaluator and a supported
  positive reciprocal singleton pair.

Neither diagnostic is a repair.  The phase or refusal evaluator still has to
be realized by one common chronological word, and the reciprocal pair still
needs the full collision/floor inequalities of a product-root lift.  The final
theorem therefore exposes exactly the strongest unconditional current
decoder together with the counterexample's necessarily absent common
zero-face return word.  It does not claim support enlargement, punishment
realization, or boundary exhaustion.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.LinearProgramming.FlowCostateDuality
open scoped Topology

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

/-! ## A literal common zero-face return word -/

/-- A finite chronological word in the simultaneous debt-source zero face.

The source field retains literal exact boxed dynamic-debt edges.  `zeroFaces`
is the all-player exposed-face condition, not an averaged or limiting
condition.  The final two fields are exactly the absorption and punishment
gates required by the solved-cycle compiler. -/
structure QuittingDebtSourceFaceReturnWord
    (seam : QuittingCounterexampleSeamWitness regime) (K : ℕ) where
  phase : Fin K
  state : Fin K → QuittingDebtPoint ι
  source : ∀ current,
    (state current, state (finRotate K current)) ∈
      quittingFloorDynamicDebtEdgeGraph reward
  zeroFaces : ∀ current selected,
    quittingDebtSourceObstructionFlow
          (state current, state (finRotate K current)) ∈
      exposedFace (quittingDebtSourceZeroFaceCostate selected)
        (quittingDebtSourceOneStageObstructionCarrier reward)
  absorbs :
    (∏ current : Fin K,
      quittingStationaryContinueMass
        (quittingRootOfSimplex (state current).1.2)) < 1
  punishmentAdmissible :
    IsQuittingCyclePunishmentAdmissible reward
      (fun current ↦ quittingRootOfSimplex (state current).1.2)

namespace QuittingDebtSourceFaceReturnWord

variable {seam : QuittingCounterexampleSeamWitness regime}
variable (word : QuittingDebtSourceFaceReturnWord
  (regime := regime) (reward := reward) seam K)

/-- The literal product-root cycle carried by the return word. -/
def cycle : Fin K → ι → PMF Bool :=
  fun current ↦ quittingRootOfSimplex (word.state current).1.2

/-- The augmented-cap value cycle carried by the return word. -/
def value : Fin K → Payoff ι :=
  fun current ↦ quittingDynamicDebtCap (word.state current)

/-- Every zero-face source edge lifts to an exact Nash--Bellman edge between
the corresponding augmented-cap states. -/
theorem capEdge (current : Fin K) :
    IsQuittingNashBellmanEdge reward
      (quittingDynamicDebtCapPoint (word.state current))
      (quittingDynamicDebtCapPoint (word.state (finRotate K current))) := by
  have hsource := word.source current
  have htransport :=
    (seam.debtSourceFlow_mem_all_zeroFaces_iff_cap_transport
      (word.state current, word.state (finRotate K current))
      hsource).1 (word.zeroFaces current)
  have hseam :=
    (quittingDynamicDebtCap_transport_iff_capSeam_eq_zero reward
      (word.state current) (word.state (finRotate K current))
      hsource.1.2.2 hsource.1.2.1.2.1).1 htransport
  exact isQuittingNashBellmanEdge_dynamicDebtCapPoint_of_capSeam_eq_zero
    reward (word.state current) (word.state (finRotate K current))
      hsource.1.2.2 hsource.1.2.1.2.1 hseam

/-- A literal common zero-face return word is a solved exact quitting cycle. -/
theorem isSolvedExactQuittingCycle :
    IsSolvedExactQuittingCycle reward word.cycle word.value := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro current
    exact (word.capEdge current).1
  · intro current
    exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (word.value (finRotate K current))
        (word.cycle current)).1 (word.capEdge current).2
  · exact word.absorbs
  · exact word.punishmentAdmissible

end QuittingDebtSourceFaceReturnWord

/-- Existence of one literal finite common return word in all playerwise
zero-source faces. -/
def HasQuittingDebtSourceFaceReturnWord
    (seam : QuittingCounterexampleSeamWitness regime) : Prop :=
  ∃ K, Nonempty (QuittingDebtSourceFaceReturnWord seam K)

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

/-- A common zero-face return word lands directly in the solved exact-cycle
stratum. -/
theorem hasSolvedExactQuittingCycle_of_hasDebtSourceFaceReturnWord
    (hword : HasQuittingDebtSourceFaceReturnWord seam) :
    HasSolvedExactQuittingCycle reward := by
  obtain ⟨K, ⟨word⟩⟩ := hword
  exact ⟨K, ⟨word.phase⟩, word.cycle, word.value,
    word.isSolvedExactQuittingCycle⟩

/-- A counterexample cannot possess the missing common zero-face return word,
because that word would compile to a uniform-equilibrium payoff. -/
theorem not_hasQuittingDebtSourceFaceReturnWord :
    ¬ HasQuittingDebtSourceFaceReturnWord seam := by
  intro hword
  exact regime.not_hasSolvedExactQuittingCycle
    (seam.hasSolvedExactQuittingCycle_of_hasDebtSourceFaceReturnWord hword)

/-! ## Exact signed one-stage diagnostics -/

/-- Proof-carrying negative-coordinate output of the one-stage tangent
readout.  The phase evaluator is game-facing, while the zero-probability
branch records that this coordinate is absent from the selected root support. -/
structure DebtSourceNegativePhaseDiagnostic where
  readout : CounterexampleRegimePeriodOneTangentReadout seam
  player : ι
  tangent_neg : readout.packet.tangent player < 0
  eventually_offSupport_or_phaseGain : ∀ᶠ index in atTop,
    (seam.periodOneReadoutRoot readout.start index player true).toReal = 0 ∨
      0 < quittingPeriodicWindowBestPhaseStop reward
            (quittingPeriodOneRootSequence
              (seam.periodOneReadoutRoot readout.start index)) player 1 -
          quittingWindowRestartDelivery reward
            (quittingPeriodOneRootSequence
              (seam.periodOneReadoutRoot readout.start index)) player 0 1

/-- Proof-carrying active-positive output.  Besides the exact repeated-root
refusal gain, it retains the finite reciprocal singleton pair selected by
packet energy.  This is the support-enlargement input, not the enlargement. -/
structure DebtSourceActiveSupportDiagnostic where
  readout : CounterexampleRegimePeriodOneTangentReadout seam
  active : ι
  tangent_nonneg : ∀ who, 0 ≤ readout.packet.tangent who
  active_mass_pos : 0 < readout.packet.mass active
  active_tangent_pos : 0 < readout.packet.tangent active
  reciprocalPair : ∃ first second,
    0 < readout.packet.mass first ∧
      0 < readout.packet.mass second ∧ first ≠ second ∧
      0 < quittingSingletonSoloEffect reward first second +
        quittingSingletonSoloEffect reward second first
  eventually_refusalGain : ∀ᶠ index in atTop,
    0 < quittingPeriodicWindowRefusalValue reward
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index)) active -
        quittingWindowRestartDelivery reward
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index)) active 0 1

namespace CounterexampleRegimePeriodOneTangentReadout

variable (readout : CounterexampleRegimePeriodOneTangentReadout seam)

/-- A negative tangent coordinate has a sharp one-stage alternative: once
joint survival is positive, either that player has zero prescribed Quit
probability, or root complementarity kills the phase slack and the exact
phase-stop evaluator is strictly profitable. -/
theorem eventually_offSupport_or_phaseGain_of_tangent_neg
    (player : ι) (hnegative : readout.packet.tangent player < 0) :
    ∀ᶠ index in atTop,
      (seam.periodOneReadoutRoot readout.start index player true).toReal = 0 ∨
        0 < quittingPeriodicWindowBestPhaseStop reward
              (quittingPeriodOneRootSequence
                (seam.periodOneReadoutRoot readout.start index)) player 1 -
            quittingWindowRestartDelivery reward
              (quittingPeriodOneRootSequence
                (seam.periodOneReadoutRoot readout.start index)) player 0 1 := by
  have htangent : ∀ᶠ index in atTop,
      seam.periodOneReadoutTangent readout.start index player < 0 :=
    (readout.tangent_tendsto player).eventually_lt_const hnegative
  have habsorption :=
    seam.rootAbsorptionMass_tendsto_zero.comp readout.start_tendsto
  have hcontinue : Tendsto (fun index ↦
      quittingStationaryContinueMass
        (seam.periodOneReadoutRoot readout.start index)) atTop (nhds 1) := by
    have honeSub :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub
        habsorption
    simpa [quittingRootAbsorptionMass, periodOneReadoutRoot,
      quittingDynamicDebtTailRoots] using honeSub
  have hcontinuePos : ∀ᶠ index in atTop,
      0 < quittingStationaryContinueMass
        (seam.periodOneReadoutRoot readout.start index) :=
    hcontinue.eventually_const_lt zero_lt_one
  filter_upwards [htangent, hcontinuePos] with index htangentIndex hcontinueIndex
  by_cases hquit :
      (seam.periodOneReadoutRoot readout.start index player true).toReal = 0
  · exact Or.inl hquit
  · right
    have hquitPos : 0 <
        (seam.periodOneReadoutRoot readout.start index player true).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hquit)
    have hslack := phaseSlack_eq_zero_of_quitProbability_pos
      seam readout index player hquitPos
    rw [bestPhaseStop_sub_restartDelivery_eq seam readout index player,
      hslack]
    simp only [sub_zero]
    have hproduct :
        quittingStationaryContinueMass
            (seam.periodOneReadoutRoot readout.start index) *
          seam.periodOneReadoutTangent readout.start index player < 0 :=
      mul_neg_of_pos_of_neg hcontinueIndex htangentIndex
    simpa only [neg_mul] using (neg_pos.mpr hproduct)

end CounterexampleRegimePeriodOneTangentReadout

open CounterexampleRegimePeriodOneTangentReadout

/-! ## The literal priced-current alternative -/

/-- Avoiding the selected zero face on two consecutive canonical edges keeps
both literal debt-source co-state prices positive and forces strict
killed-capacity dissipation at the first date. -/
theorem zeroFace_or_succ_zeroFace_or_pricedSource_dissipation
    (selected : ι) (time : ℕ) :
    seam.tailDebtSourceObstructionFlow time ∈
        exposedFace (quittingDebtSourceZeroFaceCostate selected)
          (quittingDebtSourceOneStageObstructionCarrier reward) ∨
      seam.tailDebtSourceObstructionFlow (time + 1) ∈
        exposedFace (quittingDebtSourceZeroFaceCostate selected)
          (quittingDebtSourceOneStageObstructionCarrier reward) ∨
      (0 < pair (quittingDebtSourceCostate selected)
          (seam.tailDebtSourceObstructionFlow time) ∧
        0 < pair (quittingDebtSourceCostate selected)
          (seam.tailDebtSourceObstructionFlow (time + 1)) ∧
        0 < killedDissipation seam.killedDebtSurvival
          (seam.killedDebtSource selected)
          (seam.killedCapacityDebtAccount selected) time) := by
  by_cases hcurrent : seam.tailDebtSourceObstructionFlow time ∈
      exposedFace (quittingDebtSourceZeroFaceCostate selected)
        (quittingDebtSourceOneStageObstructionCarrier reward)
  · exact Or.inl hcurrent
  by_cases hnext : seam.tailDebtSourceObstructionFlow (time + 1) ∈
      exposedFace (quittingDebtSourceZeroFaceCostate selected)
        (quittingDebtSourceOneStageObstructionCarrier reward)
  · exact Or.inr (Or.inl hnext)
  · right
    right
    have hcurrentSource : 0 < seam.killedDebtSource selected time :=
      lt_of_le_of_ne
        (quittingDynamicDebtSeam_nonneg
          (seam.tail time) (seam.tail_mem time) selected)
        (Ne.symm fun hzero ↦ hcurrent
          ((seam.tailDebtSourceObstructionFlow_mem_zeroFace_iff
            selected time).2 hzero))
    have hnextSource : 0 < seam.killedDebtSource selected (time + 1) :=
      lt_of_le_of_ne
        (quittingDynamicDebtSeam_nonneg
          (seam.tail (time + 1)) (seam.tail_mem (time + 1)) selected)
        (Ne.symm fun hzero ↦ hnext
          ((seam.tailDebtSourceObstructionFlow_mem_zeroFace_iff
            selected (time + 1)).2 hzero))
    refine ⟨?_, ?_, seam.killedCapacityDissipation_pos_of_source_pos_succ
      selected time hcurrentSource hnextSource⟩
    · rw [pair_tailDebtSourceObstructionFlow seam selected time]
      exact hcurrentSource
    · rw [pair_tailDebtSourceObstructionFlow seam selected (time + 1)]
      exact hnextSource

/-- **Signed tangent diagnostic.**  Unless the canonical tail is eventually
all-Continue, its literal one-stage readout yields either the negative phase
alternative above, or an active-positive refusal diagnostic together with a
supported positive reciprocal pair.

The theorem deliberately stops at evaluators and finite pair data.  Turning
either branch into a repair requires a common strategically realized word. -/
theorem eventually_allContinue_or_debtSource_signedDiagnostic :
    (∃ threshold, ∀ time, threshold ≤ time →
      quittingDynamicDebtTailRoots seam.tail time =
        (quittingAllContinueRoot : ι → PMF Bool)) ∨
      Nonempty (DebtSourceNegativePhaseDiagnostic seam) ∨
      Nonempty (DebtSourceActiveSupportDiagnostic seam) := by
  rcases seam.eventually_allContinue_or_exists_periodOneTangentReadout with
    hplateau | hreadout
  · exact Or.inl hplateau
  · right
    obtain ⟨readout⟩ := hreadout
    by_cases hnegative : ∃ player, readout.packet.tangent player < 0
    · obtain ⟨player, hplayer⟩ := hnegative
      have hphase :=
        eventually_offSupport_or_phaseGain_of_tangent_neg
          (seam := seam) readout player hplayer
      exact Or.inl ⟨{
        readout := readout
        player := player
        tangent_neg := hplayer
        eventually_offSupport_or_phaseGain := hphase }⟩
    · have htangentNonneg : ∀ who, 0 ≤ readout.packet.tangent who := by
        intro who
        exact le_of_not_gt (fun hwho ↦ hnegative ⟨who, hwho⟩)
      obtain ⟨active, hmass, htangent⟩ :=
        (regime.chargeTangentPacket_underfunded_or_active_funded
          readout.packet).resolve_left hnegative
      have hpair := readout.packet.exists_supported_pair_pos_reciprocalSoloEffect
        htangentNonneg active hmass htangent
      have hrefusal :=
        (activePositive_refusalGain seam readout active hmass htangent).2.2
      exact Or.inr ⟨{
        readout := readout
        active := active
        tangent_nonneg := htangentNonneg
        active_mass_pos := hmass
        active_tangent_pos := htangent
        reciprocalPair := hpair
        eventually_refusalGain := hrefusal.mono fun _ h ↦ h.2.2.2.2.2 }⟩

/-! ## The maximal unconditional current decoder -/

/-- **Debt-source strategic decoder boundary.**  At every player and date:

1. the exact source current enters the selected zero face now or next, or the
   two consecutive literal co-state prices are positive and force strict
   killed-capacity dissipation;
2. the non-plateau tangent lane emits an exact negative phase diagnostic or
   an active support/refusal diagnostic; and
3. no finite simultaneous-zero-face return word satisfying the actual cycle
   gates exists in a counterexample.

The third conjunct is the precisely typed remaining realization obstruction.
Playerwise face recurrence alone cannot replace it: the word requires one
common finite chronology, all playerwise faces simultaneously, an absorbing
return, and punishment admissibility. -/
theorem debtSource_strategicDecoderBoundary (selected : ι) (time : ℕ) :
    (seam.tailDebtSourceObstructionFlow time ∈
        exposedFace (quittingDebtSourceZeroFaceCostate selected)
          (quittingDebtSourceOneStageObstructionCarrier reward) ∨
      seam.tailDebtSourceObstructionFlow (time + 1) ∈
        exposedFace (quittingDebtSourceZeroFaceCostate selected)
          (quittingDebtSourceOneStageObstructionCarrier reward) ∨
      (0 < pair (quittingDebtSourceCostate selected)
          (seam.tailDebtSourceObstructionFlow time) ∧
        0 < pair (quittingDebtSourceCostate selected)
          (seam.tailDebtSourceObstructionFlow (time + 1)) ∧
        0 < killedDissipation seam.killedDebtSurvival
          (seam.killedDebtSource selected)
          (seam.killedCapacityDebtAccount selected) time)) ∧
    ((∃ threshold, ∀ date, threshold ≤ date →
        quittingDynamicDebtTailRoots seam.tail date =
          (quittingAllContinueRoot : ι → PMF Bool)) ∨
      Nonempty (DebtSourceNegativePhaseDiagnostic seam) ∨
      Nonempty (DebtSourceActiveSupportDiagnostic seam)) ∧
    ¬ HasQuittingDebtSourceFaceReturnWord seam := by
  exact ⟨zeroFace_or_succ_zeroFace_or_pricedSource_dissipation
      seam selected time,
    seam.eventually_allContinue_or_debtSource_signedDiagnostic,
    seam.not_hasQuittingDebtSourceFaceReturnWord⟩

end QuittingCounterexampleSeamWitness

end GameTheory
