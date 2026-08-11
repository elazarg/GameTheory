/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionTemporalSplit
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectStratification

/-!
# Consuming the concentrated reset-reprojection branch

A concentrated reprojection packet has one fixed coalition cylinder with a
uniformly positive stage mass.  This upgrades the survival-weighted owner
defect to an unweighted local defect.  Compactifying the same marked shifted
tails then gives the exact strategic alternative:

* the marked coalition is a singleton;
* the shifted tails escape strictly above the minimum-debt fiber; or
* on the minimum fiber, a uniformly positive local Nash defect remains on
  players other than the reset owner.

The last defect is attached to the same reached row and the same positive
coalition cylinder, so `quittingTerminalPayoff_stageBestEndpointDeviation_markedRouting`
turns any positive coordinate selected from it into a legal unilateral gain
with literal four-way coalition routing.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- Positive concentration removes the survival weight from the marked
owner's local defect. -/
theorem QuittingReprojectionConcentratedPacket.ownerDefect_tendsto_zero
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (hscale : ∀ n, 0 < scale n)
    (hscaleTendsto : Tendsto scale atTop (nhds 0)) :
    Tendsto (fun rank ↦
      quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (profiles (packet.subseq rank)) (packet.mark rank + 1))).1
        (quittingProfileLiveRoot reward
          (profiles (packet.subseq rank)) (packet.mark rank)) owner)
      atTop (nhds 0) := by
  let defect : ℕ → ℝ := fun rank ↦
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (profiles (packet.subseq rank)) (packet.mark rank + 1))).1
      (quittingProfileLiveRoot reward
        (profiles (packet.subseq rank)) (packet.mark rank)) owner
  let weighted : ℕ → ℝ := fun rank ↦
    quittingLiveMass reward (profiles (packet.subseq rank))
      (packet.mark rank) * defect rank
  have hweighted : Tendsto weighted atTop (nhds 0) := by
    have hscaleSub : Tendsto (fun rank ↦ scale (packet.subseq rank))
        atTop (nhds 0) :=
      hscaleTendsto.comp packet.subseq_strictMono.tendsto_atTop
    have hproduct := packet.defect_tendsto.mul hscaleSub
    convert hproduct using 1
    · funext rank
      dsimp only [weighted, defect]
      field_simp [(hscale (packet.subseq rank)).ne']
    · simp
  have hbound : ∀ rank,
      packet.resolution * defect rank ≤ weighted rank := by
    intro rank
    have hstageLe := quittingStageCoalitionMass_le_liveMass reward
      (profiles (packet.subseq rank)) (packet.mark rank) terminal
    have hlive : packet.resolution ≤
        quittingLiveMass reward (profiles (packet.subseq rank))
          (packet.mark rank) :=
      (packet.stageMass rank).trans hstageLe
    exact mul_le_mul_of_nonneg_right hlive
      (quittingRootCoordinateNashDefect_nonneg reward _ _ owner)
  have hupper : Tendsto (fun rank ↦ weighted rank / packet.resolution)
      atTop (nhds 0) := by
    simpa using hweighted.div_const packet.resolution
  have hzero : Tendsto defect atTop (nhds 0) := by
    apply squeeze_zero
    · intro rank
      exact quittingRootCoordinateNashDefect_nonneg reward _ _ owner
    · intro rank
      exact (le_div_iff₀ packet.resolution_pos).2 (by
        simpa [mul_comm] using hbound rank)
    · exact hupper
  simpa only [defect] using hzero

/-- A positive other-coordinate defect sum at one concentrated row selects a
legal unilateral best-endpoint deviation on that same profile and routes the
same positive coalition cylinder without loss. -/
theorem exists_other_stageBestEndpointDeviation_markedRouting_of_sum_defect_pos
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : iota) (stage : ℕ) (terminal : {S : Finset iota // S.Nonempty})
    (hstage : 0 < quittingStageCoalitionMass reward profile stage terminal)
    (hdefect : 0 < ∑ other ∈ Finset.univ.erase owner,
      quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (stage + 1))).1
        (quittingProfileLiveRoot reward profile stage) other) :
    ∃ other, other ≠ owner ∧
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))
      let root := quittingProfileLiveRoot reward profile stage
      let action := quittingRootBestEndpointAction reward tail.1 root other
      let routed := quittingPureEndpointRoutedCoalition terminal.val other action
      quittingTerminalPayoff reward
            (Function.update profile other
              (quittingStagePureEndpointBehaviorDeviation
                reward profile other stage action)) other -
          quittingTerminalPayoff reward profile other =
            quittingLiveMass reward profile stage *
              quittingRootCoordinateNashDefect reward tail.1 root other ∧
        0 < quittingTerminalPayoff reward
            (Function.update profile other
              (quittingStagePureEndpointBehaviorDeviation
                reward profile other stage action)) other -
          quittingTerminalPayoff reward profile other ∧
        0 < quittingRootCoalitionMass
          (Function.update root other (PMF.pure action)) routed ∧
        quittingRootCoalitionMass root terminal.val ≤
          quittingRootCoalitionMass
            (Function.update root other (PMF.pure action)) routed ∧
        ((other ∈ terminal.val ∧ action = true ∧ routed = terminal.val) ∨
          (other ∈ terminal.val ∧ action = false ∧
            routed = terminal.val.erase other) ∨
          (other ∉ terminal.val ∧ action = true ∧
            routed = insert other terminal.val) ∨
          (other ∉ terminal.val ∧ action = false ∧ routed = terminal.val)) := by
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  have hnonneg : ∀ other ∈ Finset.univ.erase owner,
      0 ≤ quittingRootCoordinateNashDefect reward tail.1 root other := by
    intro other _
    exact quittingRootCoordinateNashDefect_nonneg reward _ _ other
  obtain ⟨other, hotherMem, hotherDefect⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonneg).mp hdefect
  have hotherNe : other ≠ owner := (Finset.mem_erase.mp hotherMem).1
  have hlive : 0 < quittingLiveMass reward profile stage :=
    hstage.trans_le (quittingStageCoalitionMass_le_liveMass
      reward profile stage terminal)
  have hrootMass : 0 < quittingRootCoalitionMass root terminal.val := by
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
      at hstage
    exact (mul_pos_iff.mp hstage).resolve_right (by
      intro hnegative
      exact (not_lt_of_ge (quittingLiveMass_nonneg reward profile stage))
        hnegative.1) |>.2
  refine ⟨other, hotherNe, ?_⟩
  exact quittingTerminalPayoff_stageBestEndpointDeviation_markedRouting
    reward profile other stage terminal.val hlive hrootMass hotherDefect

/-- **Concentrated-row minimum-fiber consumer.**

For a positive minimum semantic debt, a concentrated same-profile row either
already lies on a singleton cylinder, has a marked-tail cluster strictly above
the minimum fiber, or retains a uniform positive sum of local Nash defects on
coordinates other than the reset owner.  The owner defect itself tends to
zero along the displayed cluster subsequence. -/
theorem exists_concentrated_singleton_or_tailEscape_or_otherDefect
    (minimum : QuittingTerminalSemanticPair iota)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hscale : ∀ n, 0 < scale n)
    (hscaleTendsto : Tendsto scale atTop (nhds 0)) :
    terminal.val.card = 1 ∨
      ∃ cluster : QuittingTerminalSemanticPair iota,
        ∃ subseq : ℕ → ℕ,
        cluster ∈ quittingTerminalSemanticCarrier reward ∧
        StrictMono subseq ∧
        Tendsto (fun rank ↦
          quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (profiles (packet.subseq (subseq rank)))
              (packet.mark (subseq rank) + 1)))
          atTop (nhds cluster) ∧
        Tendsto (fun rank ↦
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward
                (profiles (packet.subseq (subseq rank)))
                (packet.mark (subseq rank) + 1))).1
            (quittingProfileLiveRoot reward
              (profiles (packet.subseq (subseq rank)))
              (packet.mark (subseq rank))) owner)
          atTop (nhds 0) ∧
        (quittingTerminalSemanticDebtSum minimum <
            quittingTerminalSemanticDebtSum cluster ∨
          quittingTerminalSemanticDebtSum cluster =
              quittingTerminalSemanticDebtSum minimum ∧
            ∀ᶠ rank in atTop,
              packet.resolution *
                    quittingTerminalSemanticDebtSum minimum / 2 ≤
                ∑ other ∈ Finset.univ.erase owner,
                  quittingRootCoordinateNashDefect reward
                    (quittingTerminalSemanticPair reward
                      (quittingAllContinueProfileSpine reward
                        (profiles (packet.subseq (subseq rank)))
                        (packet.mark (subseq rank) + 1))).1
                    (quittingProfileLiveRoot reward
                      (profiles (packet.subseq (subseq rank)))
                      (packet.mark (subseq rank))) other) := by
  by_cases hcollision : 2 ≤ terminal.val.card
  · right
    let tail : ℕ → QuittingTerminalSemanticPair iota := fun rank ↦
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (profiles (packet.subseq rank)) (packet.mark rank + 1))
    have htailMem : ∀ rank,
        tail rank ∈ quittingTerminalSemanticCarrier reward := fun rank ↦
      quittingTerminalSemanticPair_mem_carrier reward _
    obtain ⟨cluster, hcluster, subseq, hsubseq, htailLimit⟩ :=
      (quittingTerminalSemanticCarrier_isCompact reward hM hreward).tendsto_subseq
        htailMem
    have howner := packet.ownerDefect_tendsto_zero hscale hscaleTendsto
    have hownerSub := howner.comp hsubseq.tendsto_atTop
    refine ⟨cluster, subseq, hcluster, hsubseq, ?_, ?_, ?_⟩
    · change Tendsto (tail ∘ subseq) atTop (nhds cluster)
      exact htailLimit
    · change Tendsto ((fun rank ↦
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward
                (profiles (packet.subseq rank)) (packet.mark rank + 1))).1
            (quittingProfileLiveRoot reward
              (profiles (packet.subseq rank)) (packet.mark rank)) owner) ∘
        subseq) atTop (nhds 0)
      exact hownerSub
    have hclusterMin := hminimum cluster hcluster
    rcases hclusterMin.lt_or_eq with hescape | hfiber
    · exact Or.inl hescape
    · refine Or.inr ⟨hfiber.symm, ?_⟩
      let excess : ℕ → ℝ := fun rank ↦
        quittingTerminalSemanticDebtSum (tail (subseq rank)) -
          quittingTerminalSemanticDebtSum minimum
      let ownerDefect : ℕ → ℝ := fun rank ↦
        quittingRootCoordinateNashDefect reward
          (tail (subseq rank)).1
          (quittingProfileLiveRoot reward
            (profiles (packet.subseq (subseq rank)))
            (packet.mark (subseq rank))) owner
      let otherDefect : ℕ → ℝ := fun rank ↦
        ∑ other ∈ Finset.univ.erase owner,
          quittingRootCoordinateNashDefect reward
            (tail (subseq rank)).1
            (quittingProfileLiveRoot reward
              (profiles (packet.subseq (subseq rank)))
              (packet.mark (subseq rank))) other
      have hdebtLimit : Tendsto (fun rank ↦
          quittingTerminalSemanticDebtSum (tail (subseq rank)))
          atTop (nhds (quittingTerminalSemanticDebtSum cluster)) :=
        continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
          htailLimit
      have hexcess : Tendsto excess atTop (nhds 0) := by
        have hsub := hdebtLimit.sub_const
          (quittingTerminalSemanticDebtSum minimum)
        have hzero : quittingTerminalSemanticDebtSum cluster -
            quittingTerminalSemanticDebtSum minimum = 0 := by
          linarith
        rw [hzero] at hsub
        simpa only [excess] using hsub
      have hownerZero : Tendsto ownerDefect atTop (nhds 0) := by
        change Tendsto ((fun rank ↦
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward
                (profiles (packet.subseq rank)) (packet.mark rank + 1))).1
            (quittingProfileLiveRoot reward
              (profiles (packet.subseq rank)) (packet.mark rank)) owner) ∘
          subseq) atTop (nhds 0)
        exact hownerSub
      have hchargePositive : 0 < packet.resolution *
          quittingTerminalSemanticDebtSum minimum :=
        mul_pos packet.resolution_pos hminimumPositive
      have hexcessSmall : ∀ᶠ rank in atTop,
          excess rank < packet.resolution *
              quittingTerminalSemanticDebtSum minimum / 4 :=
        hexcess.eventually (Iio_mem_nhds (by linarith))
      have hownerSmall : ∀ᶠ rank in atTop,
          ownerDefect rank < packet.resolution *
              quittingTerminalSemanticDebtSum minimum / 4 :=
        hownerZero.eventually (Iio_mem_nhds (by linarith))
      have hother : ∀ᶠ rank in atTop,
          packet.resolution * quittingTerminalSemanticDebtSum minimum / 2 ≤
            otherDefect rank := by
        filter_upwards [hexcessSmall, hownerSmall] with rank
            hexcessBound hownerBound
        have hrow :=
          quittingStageCollisionMass_mul_minimumDebt_le_tailExcess_add_totalNashDefect
            reward minimum
              (profiles (packet.subseq (subseq rank)))
              (packet.mark (subseq rank)) terminal hM hreward
                hminimumCarrier hminimum hcollision
        have hscaled : packet.resolution *
              quittingTerminalSemanticDebtSum minimum ≤
            quittingStageCoalitionMass reward
                (profiles (packet.subseq (subseq rank)))
                (packet.mark (subseq rank)) terminal *
              quittingTerminalSemanticDebtSum minimum :=
          mul_le_mul_of_nonneg_right (packet.stageMass (subseq rank))
            hminimumPositive.le
        have hbudget : packet.resolution *
              quittingTerminalSemanticDebtSum minimum ≤
            excess rank +
              quittingRootTotalNashDefect reward
                (tail (subseq rank)).1
                (quittingProfileLiveRoot reward
                  (profiles (packet.subseq (subseq rank)))
                  (packet.mark (subseq rank))) :=
          hscaled.trans (by
            simpa only [excess, tail, quittingSpineDebtExcess,
              quittingSpineTotalNashDefect] using hrow)
        have hsplit : quittingRootTotalNashDefect reward
              (tail (subseq rank)).1
              (quittingProfileLiveRoot reward
                (profiles (packet.subseq (subseq rank)))
                (packet.mark (subseq rank))) =
            otherDefect rank + ownerDefect rank := by
          unfold quittingRootTotalNashDefect
          rw [Finset.sum_erase_add _ _ (Finset.mem_univ owner)]
        rw [hsplit] at hbudget
        linarith
      simpa only [otherDefect, tail] using hother
  · left
    have hcardPos : 0 < terminal.val.card := Finset.card_pos.mpr terminal.property
    omega

end GameTheory
