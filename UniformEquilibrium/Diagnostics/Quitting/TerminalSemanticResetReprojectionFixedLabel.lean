/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionConcentratedConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauNashMoat
import UniformEquilibrium.Quitting.Debt.Marked.FencePacket

/-!
# A fixed strategic label in the concentrated reprojection branch

The minimum-fiber other-defect alternative can be frozen without losing its
game provenance.  One fixed non-owner player and one fixed Boolean best
endpoint recur on a strict subsequence; the same marked tails and actual roots
converge jointly.  Their limit retains both positive marked-coalition mass and
positive defect in that fixed coordinate.

This also identifies the exact obstruction to the existing reset and cycle
interfaces: the limiting root is quantitatively not an exact Nash root at the
limiting tail.  It therefore cannot be inserted as a cap--Nash reset or an
exact Nash--Bellman cycle row without an additional Nashification step.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- The fixed player/action/root/tail package extracted from a concentrated
minimum-fiber defect occupation. -/
structure QuittingReprojectionFixedLabelLimit
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : iota) (terminal : {S : Finset iota // S.Nonempty})
    (packetSubseq markedSubseq : ℕ → ℕ) (mark : ℕ → ℕ)
    (cluster : QuittingTerminalSemanticPair iota) (charge : ℝ) where
  player : iota
  player_ne_owner : player ≠ owner
  action : Bool
  rootLimit : QuittingRootSimplex iota
  selector : ℕ → ℕ
  selector_strictMono : StrictMono selector
  tail_tendsto : Tendsto (fun rank ↦
    quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward
        (profiles (packetSubseq (markedSubseq (selector rank))))
        (mark (markedSubseq (selector rank)) + 1)))
    atTop (nhds cluster)
  root_tendsto : Tendsto (fun rank ↦
    quittingSimplexOfRoot
      (quittingProfileLiveRoot reward
        (profiles (packetSubseq (markedSubseq (selector rank))))
        (mark (markedSubseq (selector rank)))))
    atTop (nhds rootLimit)
  action_eq : ∀ rank,
    quittingRootBestEndpointAction reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (profiles (packetSubseq (markedSubseq (selector rank))))
          (mark (markedSubseq (selector rank)) + 1))).1
      (quittingProfileLiveRoot reward
        (profiles (packetSubseq (markedSubseq (selector rank))))
        (mark (markedSubseq (selector rank)))) player = action
  defect_lower : ∀ rank,
    charge ≤ ((Finset.univ.erase owner).card : ℝ) *
      quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (profiles (packetSubseq (markedSubseq (selector rank))))
            (mark (markedSubseq (selector rank)) + 1))).1
        (quittingProfileLiveRoot reward
          (profiles (packetSubseq (markedSubseq (selector rank))))
          (mark (markedSubseq (selector rank)))) player
  coalition_lower : ∀ rank, charge ≤
    quittingRootCoalitionMass
      (quittingProfileLiveRoot reward
        (profiles (packetSubseq (markedSubseq (selector rank))))
        (mark (markedSubseq (selector rank)))) terminal.val
  limit_defect_lower : charge ≤ ((Finset.univ.erase owner).card : ℝ) *
    quittingRootCoordinateNashDefect reward cluster.1
      (quittingRootOfSimplex rootLimit) player
  limit_coalition_lower : charge ≤
    quittingRootCoalitionMass (quittingRootOfSimplex rootLimit) terminal.val

set_option maxHeartbeats 1000000 in
-- The joint compactness extraction elaborates deeply nested profile selectors.
/-- **Fixed-label extraction.**  A uniform other-defect sum on a convergent
marked-tail subsequence freezes one non-owner player, its best action, and a
joint root limit.  `charge` is used both as a defect-sum floor and as the root
coalition floor; callers may pass their smaller positive common lower bound. -/
theorem exists_fixedLabelLimit_of_concentrated_otherDefect
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (cluster : QuittingTerminalSemanticPair iota)
    (markedSubseq : ℕ → ℕ) (_hmarkedSubseq : StrictMono markedSubseq)
    (htail : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (profiles (packet.subseq (markedSubseq rank)))
          (packet.mark (markedSubseq rank) + 1)))
      atTop (nhds cluster))
    (howner : Tendsto (fun rank ↦
      quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (profiles (packet.subseq (markedSubseq rank)))
            (packet.mark (markedSubseq rank) + 1))).1
        (quittingProfileLiveRoot reward
          (profiles (packet.subseq (markedSubseq rank)))
          (packet.mark (markedSubseq rank))) owner)
      atTop (nhds 0))
    {charge : ℝ} (hcharge : 0 < charge)
    (hother : ∀ᶠ rank in atTop, charge ≤
      ∑ other ∈ Finset.univ.erase owner,
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (profiles (packet.subseq (markedSubseq rank)))
              (packet.mark (markedSubseq rank) + 1))).1
          (quittingProfileLiveRoot reward
            (profiles (packet.subseq (markedSubseq rank)))
            (packet.mark (markedSubseq rank))) other)
    (hcoalition : charge ≤ packet.resolution) :
    Nonempty (QuittingReprojectionFixedLabelLimit reward profiles owner terminal
      packet.subseq markedSubseq packet.mark cluster charge) := by
  classical
  obtain ⟨start, hstart⟩ := Filter.eventually_atTop.1 hother
  let shifted : ℕ → ℕ := fun n ↦ start + n
  have hshifted : StrictMono shifted := fun a b hab => Nat.add_lt_add_left hab start
  let tail : ℕ → QuittingTerminalSemanticPair iota := fun n ↦
    quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward
        (profiles (packet.subseq (markedSubseq (shifted n))))
        (packet.mark (markedSubseq (shifted n)) + 1))
  let root : ℕ → iota → PMF Bool := fun n ↦
    quittingProfileLiveRoot reward
      (profiles (packet.subseq (markedSubseq (shifted n))))
      (packet.mark (markedSubseq (shifted n)))
  let defect : ℕ → iota → ℝ := fun n who ↦
    quittingRootCoordinateNashDefect reward (tail n).1 (root n) who
  let players := Finset.univ.erase owner
  have hsum : ∀ n, charge ≤ ∑ other ∈ players, defect n other := by
    intro n
    exact hstart (shifted n) (Nat.le_add_right start n)
  have hplayers : players.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hsum
    simpa using (not_lt_of_ge (hsum 0) hcharge)
  have hwitness : ∀ n, ∃ who,
      charge ≤ (players.card : ℝ) * defect n who := by
    intro n
    obtain ⟨who, hwho, havg⟩ :=
      QuittingMarkedFencePacket.exists_sum_le_card_mul
        players hplayers (defect n)
    exact ⟨who, (hsum n).trans havg⟩
  have hownerScaled : Tendsto (fun n ↦
      (players.card : ℝ) * defect n owner) atTop (nhds 0) := by
    have hownerShift := howner.comp hshifted.tendsto_atTop
    have hconst : Tendsto (fun _ : ℕ ↦ (players.card : ℝ)) atTop
        (nhds (players.card : ℝ)) := tendsto_const_nhds
    have hmul := hconst.mul hownerShift
    simpa only [defect, tail, root, Function.comp_apply, mul_zero] using hmul
  obtain ⟨player, hplayerNe, hplayerFrequent⟩ :=
    exists_frequently_other_of_coordinate_tendsto_zero_of_uniform_witness
      (fun n who ↦ (players.card : ℝ) * defect n who)
      owner charge hcharge hownerScaled hwitness
  obtain ⟨playerSubseq, hplayerSubseq, hplayerLower⟩ :=
    extraction_of_frequently_atTop hplayerFrequent
  let bestAction : ℕ → Bool := fun n ↦
    quittingRootBestEndpointAction reward
      (tail (playerSubseq n)).1 (root (playerSubseq n)) player
  have hactionFrequent : ∃ action : Bool,
      ∃ᶠ n in atTop, bestAction n = action := by
    by_contra hnot
    push Not at hnot
    have hall : ∀ᶠ n in atTop, ∀ action : Bool,
        bestAction n ≠ action := by
      rw [eventually_all]
      exact hnot
    obtain ⟨n, hn⟩ := hall.exists
    exact hn (bestAction n) rfl
  obtain ⟨action, hactionFrequent⟩ := hactionFrequent
  obtain ⟨actionSubseq, hactionSubseq, hactionEq⟩ :=
    extraction_of_frequently_atTop hactionFrequent
  let simplexRoot : ℕ → QuittingRootSimplex iota := fun n ↦
    quittingSimplexOfRoot
      (root (playerSubseq (actionSubseq n)))
  obtain ⟨rootLimit, _hrootLimit, rootSubseq, hrootSubseq, hrootLimit⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (QuittingRootSimplex iota))).tendsto_subseq
      (fun n ↦ Set.mem_univ (simplexRoot n))
  let selector : ℕ → ℕ := fun rank ↦
    shifted (playerSubseq (actionSubseq (rootSubseq rank)))
  have hselector : StrictMono selector :=
    hshifted.comp (hplayerSubseq.comp (hactionSubseq.comp hrootSubseq))
  have htailFinal : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (profiles (packet.subseq (markedSubseq (selector rank))))
          (packet.mark (markedSubseq (selector rank)) + 1)))
      atTop (nhds cluster) :=
    htail.comp hselector.tendsto_atTop
  have hrootFinal : Tendsto (fun rank ↦
      quittingSimplexOfRoot
        (quittingProfileLiveRoot reward
          (profiles (packet.subseq (markedSubseq (selector rank))))
          (packet.mark (markedSubseq (selector rank)))))
      atTop (nhds rootLimit) := by
    change Tendsto (simplexRoot ∘ rootSubseq) atTop (nhds rootLimit)
    exact hrootLimit
  have hdefectFinal : ∀ rank, charge ≤ (players.card : ℝ) *
      quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (profiles (packet.subseq (markedSubseq (selector rank))))
            (packet.mark (markedSubseq (selector rank)) + 1))).1
        (quittingProfileLiveRoot reward
          (profiles (packet.subseq (markedSubseq (selector rank))))
          (packet.mark (markedSubseq (selector rank)))) player := by
    intro rank
    exact hplayerLower (actionSubseq (rootSubseq rank))
  have hcoalitionFinal : ∀ rank, charge ≤
      quittingRootCoalitionMass
        (quittingProfileLiveRoot reward
          (profiles (packet.subseq (markedSubseq (selector rank))))
          (packet.mark (markedSubseq (selector rank)))) terminal.val := by
    intro rank
    let profile := profiles (packet.subseq (markedSubseq (selector rank)))
    let time := packet.mark (markedSubseq (selector rank))
    let live := quittingLiveMass reward profile time
    let mass := quittingRootCoalitionMass
      (quittingProfileLiveRoot reward profile time) terminal.val
    have hstage := packet.stageMass (markedSubseq (selector rank))
    have hlive := quittingLiveMass_le_one reward profile time
    have hmassNonneg := MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
      (quittingProfileLiveRoot reward profile time) terminal.val
    have hproduct : packet.resolution ≤ live * mass := by
      simpa only [profile, time, live, mass,
        quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass] using hstage
    exact hcoalition.trans (hproduct.trans (by nlinarith))
  have hlimitDefect : charge ≤ (players.card : ℝ) *
      quittingRootCoordinateNashDefect reward cluster.1
        (quittingRootOfSimplex rootLimit) player := by
    let selectedTail : ℕ → Payoff iota := fun rank ↦
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (profiles (packet.subseq (markedSubseq (selector rank))))
          (packet.mark (markedSubseq (selector rank)) + 1))).1
    let selectedRoot : ℕ → QuittingRootSimplex iota := fun rank ↦
      quittingSimplexOfRoot
        (quittingProfileLiveRoot reward
          (profiles (packet.subseq (markedSubseq (selector rank))))
          (packet.mark (markedSubseq (selector rank))))
    let good : Set (Payoff iota × QuittingRootSimplex iota) :=
      {point | charge ≤ (players.card : ℝ) *
        quittingRootCoordinateNashDefect reward point.1
          (quittingRootOfSimplex point.2) player}
    have hgoodClosed : IsClosed good := by
      exact isClosed_le continuous_const
        (continuous_const.mul
          (continuous_quittingRootCoordinateNashDefect_simplex reward player))
    have htailValue : Tendsto selectedTail atTop (nhds cluster.1) := by
      change Tendsto (fun rank ↦
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (profiles (packet.subseq (markedSubseq (selector rank))))
            (packet.mark (markedSubseq (selector rank)) + 1))).1)
        atTop (nhds cluster.1)
      exact
      (continuous_fst.tendsto cluster).comp htailFinal
    have hselectedRoot : Tendsto selectedRoot atTop (nhds rootLimit) := by
      exact hrootFinal
    have hpair : Tendsto (fun rank ↦
        (selectedTail rank, selectedRoot rank)) atTop
        (nhds (cluster.1, rootLimit)) :=
      htailValue.prodMk_nhds hselectedRoot
    have hgoodEventually : ∀ᶠ rank in atTop,
        (selectedTail rank, selectedRoot rank) ∈ good := by
      filter_upwards with rank
      simpa only [good, selectedTail, selectedRoot, Set.mem_setOf_eq,
        quittingRootOfSimplex_simplexOfRoot] using
        hdefectFinal rank
    have hmem : (cluster.1, rootLimit) ∈ good :=
      hgoodClosed.mem_of_tendsto hpair hgoodEventually
    simpa only [good, Set.mem_setOf_eq] using hmem
  have hlimitCoalition : charge ≤
      quittingRootCoalitionMass (quittingRootOfSimplex rootLimit) terminal.val := by
    let good : Set (QuittingRootSimplex iota) := {root | charge ≤
      quittingRootCoalitionMass (quittingRootOfSimplex root) terminal.val}
    have hgoodClosed : IsClosed good :=
      isClosed_le continuous_const
        (continuous_quittingRootCoalitionMass_simplex terminal.val)
    have hgoodEventually : ∀ᶠ rank in atTop,
        quittingSimplexOfRoot
          (quittingProfileLiveRoot reward
            (profiles (packet.subseq (markedSubseq (selector rank))))
            (packet.mark (markedSubseq (selector rank)))) ∈ good := by
      filter_upwards with rank
      simpa only [good, Set.mem_setOf_eq,
        quittingRootOfSimplex_simplexOfRoot] using hcoalitionFinal rank
    have hmem : rootLimit ∈ good := hgoodClosed.mem_of_tendsto hrootFinal
      hgoodEventually
    simpa only [good, Set.mem_setOf_eq] using hmem
  refine ⟨{
    player := player
    player_ne_owner := hplayerNe
    action := action
    rootLimit := rootLimit
    selector := selector
    selector_strictMono := hselector
    tail_tendsto := htailFinal
    root_tendsto := hrootFinal
    action_eq := ?_
    defect_lower := ?_
    coalition_lower := hcoalitionFinal
    limit_defect_lower := ?_
    limit_coalition_lower := hlimitCoalition }⟩
  · intro rank
    exact hactionEq (rootSubseq rank)
  · simpa only [players] using hdefectFinal
  · simpa only [players] using hlimitDefect

/-- The fixed local limit is quantitatively outside the exact cap--Nash
correspondence.  This is the sharp obstruction to feeding it directly to the
existing reset-return and exact-cycle compilers. -/
theorem QuittingReprojectionFixedLabelLimit.not_isZeroQuittingRootNash
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {packetSubseq markedSubseq : ℕ → ℕ} {mark : ℕ → ℕ}
    {cluster : QuittingTerminalSemanticPair iota} {charge : ℝ}
    (limit : QuittingReprojectionFixedLabelLimit reward profiles owner terminal
      packetSubseq markedSubseq mark cluster charge)
    (hcharge : 0 < charge) :
    ¬ IsεQuittingRootNash reward cluster.1 0
      (quittingRootOfSimplex limit.rootLimit) := by
  intro hnash
  have hzero := (isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
    reward cluster.1 (quittingRootOfSimplex limit.rootLimit)).mp hnash
      limit.player
  have hlower := limit.limit_defect_lower
  rw [hzero, mul_zero] at hlower
  linarith

end GameTheory
