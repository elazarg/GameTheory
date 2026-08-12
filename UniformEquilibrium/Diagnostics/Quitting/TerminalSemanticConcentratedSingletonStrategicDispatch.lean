/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetFaceLawTemporalSplit
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticConcentratedSingletonCancellation
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOffDiagonalStaticOrientationDispatch

/-!
# Strategic dispatch for a relabeled concentrated singleton

A positive nonsingleton law on a reset face may produce a concentrated atom
with a different label, and that label may be a singleton.  This file keeps
the literal concentrated packet and resolves that singleton through the
existing counterexample table and cancellation theorems.

The exact outputs are an atomic-toggle handoff, positive punishment value,
exact player deletion, a recurrent owner-payoff tail escape, or a fixed
played coalition on which owner insertion is quantitatively harmful.  The
last two are the remaining chronological singleton residuals.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- A fixed fraction of the recurrent singleton-join gap reappears as a
strict lower bound on the reset owner's actual shifted-tail payoff. -/
def HasQuittingConcentratedSingletonOwnerTailEscape
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (other : iota) : Prop :=
  let gap := quittingSingletonCollisionReward reward other owner -
    quittingSoloReward reward other owner
  let charge := packet.resolution * gap / 4
  0 < gap ∧ 0 < charge ∧
    ∃ᶠ rank in atTop,
      quittingSoloReward reward owner owner + charge <
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (profiles (packet.subseq rank)) (packet.mark rank + 1))).1 owner

/-- A fixed realized opponent coalition recurrently carries a quantitative
Continue-versus-join loss for the reset owner. -/
def HasQuittingConcentratedSingletonFixedOwnerJoinLoss
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (other : iota) : Prop :=
  let gap := quittingSingletonCollisionReward reward other owner -
    quittingSoloReward reward other owner
  0 < gap ∧
    ∃ action : iota → Bool,
      action owner = false ∧
      (quittingQuitters action).Nonempty ∧
      0 < quittingTerminalOpponentAdvantage reward owner action ∧
      ∃ᶠ rank in atTop,
        packet.resolution * gap / 2 ≤
          (Fintype.card (iota → Bool) : ℝ) *
            quittingPlayedOwnerJoinLossTerm reward
              (quittingProfileLiveRoot reward
                (profiles (packet.subseq rank)) (packet.mark rank))
              owner action

/-- Exhaustive strategic output attached to one recurrent opponent
singleton.  The singleton identity and vanishing positive owner-Quit
advantage are retained as common packet provenance. -/
def HasQuittingConcentratedSingletonStrategicDispatch
    (regime : QuittingCounterexampleRegime reward)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (other : iota) : Prop :=
  terminal.val = {other} ∧
    Tendsto (fun rank ↦
      max (quittingRootEndpointDifference reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (profiles (packet.subseq rank)) (packet.mark rank + 1))).1
      (quittingProfileLiveRoot reward
          (profiles (packet.subseq rank)) (packet.mark rank)) owner) 0)
      atTop (nhds 0) ∧
    HasQuittingSingletonStaticStrategicDispatch reward other
      regime.terminalGap ∧
    (HasQuittingStaticAtomicToggleHandoff reward ∨
      0 < quittingPunishmentValue reward other ∨
      HasQuittingExactPlayerDeletionAtGap reward other regime.terminalGap ∨
      HasQuittingConcentratedSingletonOwnerTailEscape packet other ∨
      HasQuittingConcentratedSingletonFixedOwnerJoinLoss packet other)

namespace QuittingCounterexampleRegime

/-- A strict joiner of a singleton supplies the existing literal atomic
toggle handoff, with the pure pair row as its unstable atom. -/
theorem hasStaticAtomicToggleHandoff_of_strictSingletonJoiner
    (regime : QuittingCounterexampleRegime reward)
    (owner joiner : iota) (hne : joiner ≠ owner)
    (hstrict : quittingSoloReward reward owner joiner <
      quittingSingletonCollisionReward reward owner joiner) :
    HasQuittingStaticAtomicToggleHandoff reward := by
  classical
  let quitters : Finset iota := {owner}
  have hquitters : quitters.Nonempty := by
    simp [quitters]
  have hjoiner : joiner ∉ quitters := by
    simp [quitters, hne]
  have htoggle : reward ⟨quitters, hquitters⟩ joiner <
      reward
        ⟨insert joiner quitters,
          Finset.insert_nonempty joiner quitters⟩ joiner := by
    simpa [quitters, quittingSoloReward,
      quittingSingletonCollisionReward, Finset.pair_comm] using hstrict
  exact ⟨joiner, quitters, hquitters, hjoiner, htoggle,
    exists_outsider_atomicDeviation_of_strict_ownerToggle reward
      regime.terminalGap_pos regime.terminalExploitability joiner quitters
      hquitters hjoiner htoggle⟩

/-- **Relabeled concentrated-singleton strategic dispatch.**

The third-joiner branch becomes a literal atomic-toggle handoff.  The
punishment-moat branch enters the universal singleton static dispatcher and
therefore yields atomic instability, positive punishment, or exact deletion.
If the reset owner is the strict singleton joiner, the same concentrated rows
instead yield a recurrent owner-tail escape or a fixed played owner-insertion
loss. -/
theorem concentratedSingletonStrategicDispatch
    (regime : QuittingCounterexampleRegime reward)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (hcard : terminal.val.card = 1)
    (other : iota) (hotherNe : other ≠ owner)
    (hotherMem : other ∈ terminal.val)
    (hscale : ∀ n, 0 < scale n)
    (hscaleTendsto : Tendsto scale atTop (nhds 0)) :
    HasQuittingConcentratedSingletonStrategicDispatch
      regime packet other := by
  obtain ⟨hterminal, hadvantage, hstrategic⟩ :=
    regime.exists_thirdJoiner_or_ownerCancellation_or_punishmentMoat_of_concentratedSingleton
      packet hcard other hotherNe hotherMem hscale hscaleTendsto
  refine ⟨hterminal, hadvantage,
    regime.singletonStaticStrategicDispatch other, ?_⟩
  rcases hstrategic with hthird | howner | hmoat
  · obtain ⟨joiner, hjoinerNe, _hjoinerOwner, hstrict⟩ := hthird
    exact Or.inl
      (regime.hasStaticAtomicToggleHandoff_of_strictSingletonJoiner
        other joiner hjoinerNe hstrict)
  · have hcancel := packet.frequent_ownerTailEscape_or_fixedJoinLoss
      other hotherNe hterminal hscale hscaleTendsto howner
    rcases hcancel with htail | hloss
    · right; right; right; left
      let gap := quittingSingletonCollisionReward reward other owner -
        quittingSoloReward reward other owner
      let charge := packet.resolution * gap / 4
      have hgap : 0 < gap := by
        dsimp only [gap]
        linarith
      have hcharge : 0 < charge := by
        dsimp only [charge]
        exact div_pos (mul_pos packet.resolution_pos hgap) (by norm_num)
      exact ⟨hgap, hcharge, by simpa only [gap, charge] using htail⟩
    · right; right; right; right
      let gap := quittingSingletonCollisionReward reward other owner -
        quittingSoloReward reward other owner
      have hgap : 0 < gap := by
        dsimp only [gap]
        linarith
      exact ⟨hgap, by simpa only [gap] using hloss⟩
  · rcases regime.singletonStaticStrategicDispatch other with
      hatomic | hpunishment | hdeletion
    · exact Or.inl hatomic
    · exact Or.inr (Or.inl hpunishment)
    · exact Or.inr (Or.inr (Or.inl hdeletion))

end QuittingCounterexampleRegime

/-- The exact non-singleton output of the concentrated minimum-fiber
consumer, bundled so a regime wrapper can expose the singleton branch without
duplicating its collision data. -/
structure QuittingConcentratedCollisionMinimumResidual
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    (owner : iota) (terminal : {S : Finset iota // S.Nonempty})
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale) where
  cluster : QuittingTerminalSemanticPair iota
  subseq : ℕ → ℕ
  cluster_mem : cluster ∈ quittingTerminalSemanticCarrier reward
  subseq_strictMono : StrictMono subseq
  tail_tendsto : Tendsto (fun rank ↦
    quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward
        (profiles (packet.subseq (subseq rank)))
        (packet.mark (subseq rank) + 1)))
    atTop (nhds cluster)
  ownerDefect_tendsto : Tendsto (fun rank ↦
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (profiles (packet.subseq (subseq rank)))
          (packet.mark (subseq rank) + 1))).1
      (quittingProfileLiveRoot reward
        (profiles (packet.subseq (subseq rank)))
        (packet.mark (subseq rank))) owner)
    atTop (nhds 0)
  escape_or_otherDefect :
    quittingTerminalSemanticDebtSum minimum <
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
                  (packet.mark (subseq rank))) other

namespace QuittingCounterexampleRegime

/-- **Concentrated packet capstone.**  A packet carrying a fixed opponent
label is either a fully classified relabeled singleton, or it retains the
existing collision minimum-fiber residual with the same literal rows. -/
theorem concentratedPacket_singletonStrategic_or_collisionMinimumResidual
    (regime : QuittingCounterexampleRegime reward)
    (minimum : QuittingTerminalSemanticPair iota)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (other : iota) (hotherNe : other ≠ owner)
    (hotherMem : other ∈ terminal.val)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hscale : ∀ n, 0 < scale n)
    (hscaleTendsto : Tendsto scale atTop (nhds 0)) :
    HasQuittingConcentratedSingletonStrategicDispatch
        regime packet other ∨
      Nonempty (QuittingConcentratedCollisionMinimumResidual
        reward minimum owner terminal packet) := by
  rcases exists_concentrated_singleton_or_tailEscape_or_otherDefect
      (reward := reward) minimum packet hM hreward hminimumCarrier hminimum
        hminimumPositive hscale hscaleTendsto with hsingleton | hcollision
  · exact Or.inl (regime.concentratedSingletonStrategicDispatch
      packet hsingleton other hotherNe hotherMem hscale hscaleTendsto)
  · right
    obtain ⟨cluster, subseq, hcluster, hsubseq, htail, howner,
        hresidual⟩ := hcollision
    exact ⟨{
      cluster := cluster
      subseq := subseq
      cluster_mem := hcluster
      subseq_strictMono := hsubseq
      tail_tendsto := htail
      ownerDefect_tendsto := howner
      escape_or_otherDefect := hresidual }⟩

/-- **Reset-face law capstone with the relabeled singleton exposed.**

A positive nonsingleton law coordinate at a global positive minimum first
produces the existing concentrated packet, whose label may differ from the
original terminal.  The returned label is then dispatched without a hidden
cardinality assumption: it is either a strategically classified opponent
singleton, or the existing collision minimum-fiber residual on the same
literal packet. -/
theorem exists_resetFaceLaw_singletonStrategic_or_collisionMinimumResidual
    (regime : QuittingCounterexampleRegime reward)
    (point : QuittingTerminalSemanticLawPoint iota)
    (owner : iota)
    (terminal : {S : Finset iota // S.Nonempty})
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hface : quittingTerminalSemanticDebt point.1 owner = 0)
    (hmass : 0 < point.2 (some terminal))
    (hcollision : 1 < terminal.val.card)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum point.1) :
    ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      ∃ cutoff : ℕ → ℕ, ∃ scale : ℕ → ℝ,
      ∃ fixedOther : iota,
      ∃ exact : {S : Finset iota // S.Nonempty},
      ∃ packet : QuittingReprojectionConcentratedPacket
        reward profiles owner exact cutoff scale,
        Tendsto (fun n ↦
          (quittingTerminalSemanticPair reward (profiles n),
            quittingTerminalOutcomeMass reward (profiles n)))
          atTop (nhds point) ∧
        (∀ n, 0 < scale n) ∧
        Tendsto scale atTop (nhds 0) ∧
        fixedOther ≠ owner ∧ fixedOther ∈ exact.val ∧
        (HasQuittingConcentratedSingletonStrategicDispatch
            regime packet fixedOther ∨
          Nonempty (QuittingConcentratedCollisionMinimumResidual
            reward point.1 owner exact packet)) := by
  obtain ⟨profiles, cutoff, scale, fixedOther, exact, hprofiles,
      hscale, hscaleTendsto, hfixedOther, hfixedOtherMem, hpacket⟩ :=
    exists_resetFaceLaw_concentratedPacket_of_collision
      reward point owner terminal hM hreward hpoint hface hmass hcollision
  let packet := Classical.choice hpacket
  have hpointCarrier : point.1 ∈
      quittingTerminalSemanticCarrier reward := by
    rw [quittingTerminalSemanticCarrier]
    apply map_mem_closure continuous_fst hpoint
    rintro _ ⟨profile, rfl⟩
    exact ⟨profile, rfl⟩
  have hdispatch :=
    regime.concentratedPacket_singletonStrategic_or_collisionMinimumResidual
      point.1 packet fixedOther hfixedOther hfixedOtherMem hM hreward
        hpointCarrier hminimum hminimumPositive hscale hscaleTendsto
  exact ⟨profiles, cutoff, scale, fixedOther, exact, packet, hprofiles,
    hscale, hscaleTendsto, hfixedOther, hfixedOtherMem, hdispatch⟩

end QuittingCounterexampleRegime

end GameTheory
