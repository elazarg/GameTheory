/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionConcentratedConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNegativeVertexGerm
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNashDefectMobiusIncidence

/-!
# Consuming a concentrated opponent singleton

When the concentrated reprojection cylinder is a singleton different from
the reset owner, its positive stage mass gives a uniform lower bound on the
owner's Continue probability at the same reached roots.  The vanishing owner
defect therefore forces the positive part of the owner's expected pure-Quit
advantage to vanish at those exact rows.

In a counterexample, the singleton owner's table has the standard strict
joiner-or-punishment-moat alternative.  Keeping the reset owner distinguished
sharpens it to three branches:

* a third player strictly gains by joining the singleton;
* the reset owner itself strictly gains on the singleton table edge, while
  its expected rowwise Quit advantage is asymptotically suppressed by other
  coalition states;
* the singleton owner has a fixed positive punishment moat.

Thus the branch feeds the singleton compiler whenever the reset owner is not
a strict table joiner.  In the remaining branch the exact residual is a
coalition-cancellation problem; positive singleton mass and vanishing local
defect alone do not produce a legal profitable deviation or a stationary
singleton germ.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The mass of an exact coalition is bounded by any displayed nonmember's
Continue probability. -/
theorem quittingRootCoalitionMass_le_continueProbability_of_not_mem
    (root : ι → PMF Bool) (coalition : Finset ι) (marked : ι)
    (hmarked : marked ∉ coalition) :
    quittingRootCoalitionMass root coalition ≤
      (root marked false).toReal := by
  let rate : ι → ℝ := fun who => (root who true).toReal
  have hrateNonneg : ∀ who, 0 ≤ rate who :=
    fun who => ENNReal.toReal_nonneg
  have hrateLeOne : ∀ who, rate who ≤ 1 := fun who =>
    ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one true)
  have hinsideLeOne : (∏ who ∈ coalition, rate who) ≤ 1 :=
    Finset.prod_le_one
      (fun who _ => hrateNonneg who)
      (fun who _ => hrateLeOne who)
  have hmarkedComplement : marked ∈ coalitionᶜ := by
    simpa using hmarked
  have hrestNonneg :
      0 ≤ ∏ who ∈ coalitionᶜ.erase marked, (1 - rate who) :=
    Finset.prod_nonneg fun who _ => sub_nonneg.mpr (hrateLeOne who)
  have hrestLeOne :
      (∏ who ∈ coalitionᶜ.erase marked, (1 - rate who)) ≤ 1 :=
    Finset.prod_le_one
      (fun who _ => sub_nonneg.mpr (hrateLeOne who))
      (fun who _ => by linarith [hrateNonneg who])
  have houtside : (∏ who ∈ coalitionᶜ, (1 - rate who)) =
      (∏ who ∈ coalitionᶜ.erase marked, (1 - rate who)) *
        (1 - rate marked) := by
    simpa using (Finset.prod_erase_mul coalitionᶜ
      (fun who => 1 - rate who) hmarkedComplement).symm
  have hcontinue : 1 - rate marked = (root marked false).toReal := by
    have hsum := quittingRoot_continueProbability_add_quitProbability
      root marked
    dsimp only [rate]
    linarith
  unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
    quittingRootQuitRates
  change (∏ who ∈ coalition, rate who) *
      (∏ who ∈ coalitionᶜ, (1 - rate who)) ≤ _
  rw [houtside, hcontinue, ← mul_assoc]
  exact mul_le_of_le_one_left ENNReal.toReal_nonneg
    (mul_le_one₀ hinsideLeOne hrestNonneg hrestLeOne)

/-- Uniform mass on a coalition not containing the reset owner removes the
played-Continue weight from the positive endpoint advantage. -/
theorem QuittingReprojectionConcentratedPacket.ownerQuitAdvantage_posPart_tendsto_zero
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : ι} {terminal : {S : Finset ι // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (howner : owner ∉ terminal.val)
    (hscale : ∀ n, 0 < scale n)
    (hscaleTendsto : Tendsto scale atTop (nhds 0)) :
    Tendsto (fun rank =>
      max (quittingRootEndpointDifference reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (profiles (packet.subseq rank)) (packet.mark rank + 1))).1
        (quittingProfileLiveRoot reward
          (profiles (packet.subseq rank)) (packet.mark rank)) owner) 0)
      atTop (nhds 0) := by
  let tail : ℕ → Payoff ι := fun rank =>
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward
        (profiles (packet.subseq rank)) (packet.mark rank + 1))).1
  let root : ℕ → ι → PMF Bool := fun rank =>
    quittingProfileLiveRoot reward
      (profiles (packet.subseq rank)) (packet.mark rank)
  let defect : ℕ → ℝ := fun rank =>
    quittingRootCoordinateNashDefect reward (tail rank) (root rank) owner
  let advantage : ℕ → ℝ := fun rank =>
    max (quittingRootEndpointDifference reward
      (tail rank) (root rank) owner) 0
  have hdefect : Tendsto defect atTop (nhds 0) := by
    simpa only [defect, tail, root] using
      packet.ownerDefect_tendsto_zero hscale hscaleTendsto
  have hcontinueLower : ∀ rank,
      packet.resolution ≤ ((root rank) owner false).toReal := by
    intro rank
    have hrootMass : packet.resolution ≤
        quittingRootCoalitionMass (root rank) terminal.val := by
      calc
        packet.resolution ≤ quittingStageCoalitionMass reward
            (profiles (packet.subseq rank)) (packet.mark rank) terminal :=
          packet.stageMass rank
        _ = quittingLiveMass reward (profiles (packet.subseq rank))
              (packet.mark rank) *
            quittingRootCoalitionMass (root rank) terminal.val :=
          quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass
            reward (profiles (packet.subseq rank)) (packet.mark rank) terminal
        _ ≤ quittingRootCoalitionMass (root rank) terminal.val := by
          exact mul_le_of_le_one_left
            (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
              (root rank) terminal.val)
            (quittingLiveMass_le_one reward
              (profiles (packet.subseq rank)) (packet.mark rank))
    exact hrootMass.trans
      (quittingRootCoalitionMass_le_continueProbability_of_not_mem
        (root rank) terminal.val owner howner)
  have hadvantageBound : ∀ rank,
      advantage rank ≤ defect rank / packet.resolution := by
    intro rank
    have hformula :=
      quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart
        (reward := reward) (tail rank) (root rank) owner
    have hpositiveNonneg : 0 ≤ advantage rank := le_max_right _ _
    have hnegativeNonneg : 0 ≤
        ((root rank) owner true).toReal *
          max (-quittingRootEndpointDifference reward
            (tail rank) (root rank) owner) 0 :=
      mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _)
    have hscaled : packet.resolution * advantage rank ≤ defect rank := by
      calc
        packet.resolution * advantage rank ≤
            ((root rank) owner false).toReal * advantage rank :=
          mul_le_mul_of_nonneg_right (hcontinueLower rank) hpositiveNonneg
        _ ≤ defect rank := by
          change ((root rank) owner false).toReal *
              max (quittingRootEndpointDifference reward
                (tail rank) (root rank) owner) 0 ≤
            quittingRootCoordinateNashDefect reward
              (tail rank) (root rank) owner
          rw [hformula]
          exact le_add_of_nonneg_right hnegativeNonneg
    exact (le_div_iff₀ packet.resolution_pos).2 (by
      simpa [mul_comm] using hscaled)
  have hupper : Tendsto (fun rank => defect rank / packet.resolution)
      atTop (nhds 0) := by
    simpa using hdefect.div_const packet.resolution
  apply squeeze_zero
  · intro rank
    exact le_max_right _ _
  · exact hadvantageBound
  · exact hupper

namespace QuittingCounterexampleRegime

/-- **Concentrated opponent-singleton trichotomy.**  The singleton has either
a strict third-player joiner, the reset owner is itself a strict joiner whose
expected rowwise advantage is asymptotically canceled, or the singleton owner
has a fixed punishment moat. -/
theorem exists_thirdJoiner_or_ownerCancellation_or_punishmentMoat_of_concentratedSingleton
    (regime : QuittingCounterexampleRegime reward)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : ι} {terminal : {S : Finset ι // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (hcard : terminal.val.card = 1)
    (other : ι) (hotherNe : other ≠ owner)
    (hotherMem : other ∈ terminal.val)
    (hscale : ∀ n, 0 < scale n)
    (hscaleTendsto : Tendsto scale atTop (nhds 0)) :
    terminal.val = {other} ∧
      Tendsto (fun rank =>
        max (quittingRootEndpointDifference reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (profiles (packet.subseq rank)) (packet.mark rank + 1))).1
          (quittingProfileLiveRoot reward
            (profiles (packet.subseq rank)) (packet.mark rank)) owner) 0)
        atTop (nhds 0) ∧
      ((∃ joiner, joiner ≠ other ∧ joiner ≠ owner ∧
          quittingSoloReward reward other joiner <
            quittingSingletonCollisionReward reward other joiner) ∨
        quittingSoloReward reward other owner <
          quittingSingletonCollisionReward reward other owner ∨
        quittingSoloReward reward other other <
          quittingPunishmentValue reward other) := by
  obtain ⟨blocker, hterminal⟩ := Finset.card_eq_one.mp hcard
  have hotherEq : other = blocker := by
    rw [hterminal] at hotherMem
    simpa using hotherMem
  subst blocker
  have hownerNotMem : owner ∉ terminal.val := by
    rw [hterminal]
    simpa using hotherNe.symm
  refine ⟨hterminal, packet.ownerQuitAdvantage_posPart_tendsto_zero
    hownerNotMem hscale hscaleTendsto, ?_⟩
  rcases regime.strictJoiner_or_soloReward_lt_punishmentValue other with
    hjoin | hmoat
  · obtain ⟨joiner, hjoinerNe, hstrict⟩ := hjoin
    by_cases hjoinerOwner : joiner = owner
    · subst joiner
      exact Or.inr (Or.inl hstrict)
    · exact Or.inl ⟨joiner, hjoinerNe, hjoinerOwner, hstrict⟩
  · exact Or.inr (Or.inr hmoat)

/-- If the reset owner is not a strict table joiner of the recurrent
singleton, the cancellation branch is absent: a fixed third-player strict
joiner or a fixed punishment moat remains. -/
theorem exists_thirdJoiner_or_punishmentMoat_of_concentratedSingleton
    (regime : QuittingCounterexampleRegime reward)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : ι} {terminal : {S : Finset ι // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (hcard : terminal.val.card = 1)
    (other : ι) (hotherNe : other ≠ owner)
    (hotherMem : other ∈ terminal.val)
    (hownerNoJoin : quittingSingletonCollisionReward reward other owner ≤
      quittingSoloReward reward other owner)
    (hscale : ∀ n, 0 < scale n)
    (hscaleTendsto : Tendsto scale atTop (nhds 0)) :
    (∃ joiner, joiner ≠ other ∧ joiner ≠ owner ∧
        quittingSoloReward reward other joiner <
          quittingSingletonCollisionReward reward other joiner) ∨
      quittingSoloReward reward other other <
        quittingPunishmentValue reward other := by
  obtain ⟨_hterminal, _hadvantage, hstrategic⟩ :=
    regime.exists_thirdJoiner_or_ownerCancellation_or_punishmentMoat_of_concentratedSingleton
      packet hcard other hotherNe hotherMem hscale hscaleTendsto
  rcases hstrategic with hthird | howner | hmoat
  · exact Or.inl hthird
  · exact False.elim (not_lt_of_ge hownerNoJoin howner)
  · exact Or.inr hmoat

end QuittingCounterexampleRegime

end GameTheory
