/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOffDiagonalAtomSequenceDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio

/-!
# Reset-face return for the off-diagonal rectangle endpoint

The fixed-label rectangle sequence already supplies literal double endpoints:
first replace the active mover, then install the observer's selected pure-time
response.  The observer debt of these executable profiles tends to zero.

Compactifying the complete semantic/law points therefore gives an exact
observer-reset cluster.  The existing reset-face minimizer then produces a
point no higher than that cluster.  It either lies on the global minimum
fiber, or it is an off-minimum reset point whose only exact cap--Nash root is
all-Continue.  This removes any additional endpoint-return hypothesis from
the rectangle branch.

The original fixed atom, player labels, terminal label, and literal profiles
remain exact along the selected subsequence.  The final reset-face minimizer
is only a semantic consumer: it need not preserve the cluster's terminal law,
the signed atom, or the original chronology.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal double endpoint: the mover replacement followed by the selected
observer pure-time response. -/
def quittingStoppingLawRectangleDoubleEndpointProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update (quittingStoppingLawRectangleTargetProfile packet n)
    packet.observer
    (quittingPureTimeBehaviorStrategy reward packet.observer
      (packet.quitTime n))

/-- The comparison endpoint in which the mover keeps its prescribed
strategy and the same observer response is installed. -/
def quittingStoppingLawRectangleSourceResponseProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update (frontier.profiles (frontier.subseq (packet.rank n)))
    packet.observer
    (quittingPureTimeBehaviorStrategy reward packet.observer
      (packet.quitTime n))

/-- Complete endpoint-return packet for a fixed rectangle sequence.  The
cluster retains the limiting terminal law of the literal double endpoints.
The returned point records the separate semantic reset-face minimization. -/
structure QuittingStoppingLawRectangleResetFaceDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) where
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  rank_strictMono : StrictMono (packet.rank ∘ subseq)
  cluster : QuittingTerminalSemanticLawPoint ι
  cluster_mem : cluster ∈ quittingTerminalSemanticLawCarrier reward
  doubleEndpoint_tendsto : Tendsto (fun n =>
    (quittingTerminalSemanticPair reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet (subseq n)),
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet (subseq n))))
    atTop (nhds cluster)
  cluster_observer_reset :
    quittingTerminalSemanticDebt cluster.1 packet.observer = 0
  cluster_fiber_or_separated :
    quittingTerminalSemanticDebtSum cluster.1 =
        quittingTerminalSemanticDebtSum frontier.base ∨
      quittingTerminalSemanticDebtSum frontier.base <
        quittingTerminalSemanticDebtSum cluster.1
  returned : QuittingTerminalSemanticPair ι
  returned_mem : returned ∈ quittingTerminalSemanticCarrier reward
  returned_observer_reset :
    quittingTerminalSemanticDebt returned packet.observer = 0
  base_le_returned : quittingTerminalSemanticDebtSum frontier.base ≤
    quittingTerminalSemanticDebtSum returned
  returned_le_cluster : quittingTerminalSemanticDebtSum returned ≤
    quittingTerminalSemanticDebtSum cluster.1
  opponent_transfer_identity :
    (∑ other ∈ Finset.univ.erase packet.observer,
        quittingTerminalSemanticDebtChange frontier.base returned other) =
      (quittingTerminalSemanticDebtSum returned -
          quittingTerminalSemanticDebtSum frontier.base) +
        quittingTerminalSemanticDebt frontier.base packet.observer
  opponent_transfer : quittingTerminalSemanticDebt frontier.base
      packet.observer ≤
    ∑ other ∈ Finset.univ.erase packet.observer,
      quittingTerminalSemanticDebtChange frontier.base returned other
  returned_fiber_or_separated :
    quittingTerminalSemanticDebtSum returned =
        quittingTerminalSemanticDebtSum frontier.base ∨
      quittingTerminalSemanticDebtSum frontier.base <
        quittingTerminalSemanticDebtSum returned
  allContinue_nash : IsεQuittingRootNash reward returned.2 0
    (quittingAllContinueRoot : ι → PMF Bool)
  allContinue_fixed :
    quittingTerminalSemanticPrefix reward quittingAllContinueRoot returned =
      returned
  unique_capNash : ∀ root : ι → PMF Bool,
    IsεQuittingRootNash reward returned.2 0 root →
      root = (quittingAllContinueRoot : ι → PMF Bool)

/-- The fixed signed rectangle atom remains literally true on every selected
rank.  This concerns the original double endpoints, not the semantic point
`dispatch.returned`. -/
theorem QuittingStoppingLawRectangleResetFaceDispatch.atom_bound
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    (dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet)
    (n : ℕ) :
    packet.charge / 4 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (quittingStoppingLawRectangleDoubleEndpointProfile packet
            (dispatch.subseq n))
          (quittingStoppingLawRectangleSourceResponseProfile packet
            (dispatch.subseq n))
          packet.observer (some packet.terminal) := by
  simpa only [quittingStoppingLawRectangleDoubleEndpointProfile,
    quittingStoppingLawRectangleTargetProfile,
    quittingStoppingLawRectangleSourceResponseProfile,
    Function.update_eq_self] using packet.atom_bound (dispatch.subseq n)

/-- **Unconditional rectangle endpoint return/separation.**  No metric-return
or near-minimality assumption on the double endpoints is needed. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.nonempty_resetFaceDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) :
    Nonempty (QuittingStoppingLawRectangleResetFaceDispatch packet) := by
  let endpoint : ℕ → QuittingTerminalSemanticLawPoint ι := fun n =>
    (quittingTerminalSemanticPair reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet n),
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet n))
  have hendpointMem : ∀ n,
      endpoint n ∈ quittingTerminalSemanticLawCarrier reward := by
    intro n
    exact quittingTerminalSemanticLawPoint_mem_carrier reward _
  obtain ⟨cluster, hcluster, subseq, hsubseq, hendpoint⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)).tendsto_subseq hendpointMem
  have hdebtCluster :=
    ((continuous_quittingTerminalSemanticDebt packet.observer).comp
      continuous_fst).tendsto cluster |>.comp hendpoint
  have hdebtZero := packet.observer_debt_tendsto_zero.comp
    hsubseq.tendsto_atTop
  change Tendsto (fun n => quittingTerminalSemanticDebt
      (endpoint (subseq n)).1 packet.observer) atTop (nhds 0) at hdebtZero
  have hclusterReset : quittingTerminalSemanticDebt cluster.1
      packet.observer = 0 := by
    change Tendsto (fun n => quittingTerminalSemanticDebt
      (endpoint (subseq n)).1 packet.observer) atTop
      (nhds (quittingTerminalSemanticDebt cluster.1 packet.observer)) at hdebtCluster
    exact tendsto_nhds_unique hdebtCluster hdebtZero
  have hclusterCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier cluster hcluster
  have hclusterFloor := frontier.base_minimum cluster.1 hclusterCarrier
  have hclusterFiber := hclusterFloor.eq_or_lt.imp Eq.symm id
  obtain ⟨returned, hreturned, hreturnedReset, hbaseLe, hreturnedLe,
      htransferIdentity, htransfer, hreturnedFiber, hnash, hfixed,
      hunique⟩ :=
    exists_resetFace_minimizer_with_unique_allContinue_capNash
      (reward := reward) frontier.base cluster.1 packet.observer
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) frontier.base_minimum
      frontier.base_positive hclusterCarrier hclusterReset
  refine ⟨⟨subseq, hsubseq, packet.rank_strictMono.comp hsubseq,
    cluster, hcluster, ?_, hclusterReset, hclusterFiber, returned, hreturned,
    hreturnedReset, hbaseLe, hreturnedLe, htransferIdentity, htransfer,
    hreturnedFiber, hnash, hfixed, hunique⟩⟩
  change Tendsto (fun n =>
    (quittingTerminalSemanticPair reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet (subseq n)),
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet (subseq n))))
    atTop (nhds cluster) at hendpoint
  exact hendpoint

/-- Regime-facing dispatch: the prescribed atom branch remains open, while
every rectangle branch now reaches the semantic reset-face return/separation
consumer without an extra endpoint-return hypothesis. -/
theorem QuittingCounterexampleStoppingLawFrontier.exists_prescribedAtomSequence_or_rectangleResetFaceDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    Nonempty (QuittingStoppingLawPrescribedAtomSequence frontier) ∨
      ∃ packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier,
        Nonempty (QuittingStoppingLawRectangleResetFaceDispatch packet) := by
  rcases frontier.exists_prescribedAtomSequence_or_vanishingDebtRectangleSequence
      with hprescribed | hrectangle
  · exact Or.inl hprescribed
  · obtain ⟨packet⟩ := hrectangle
    exact Or.inr ⟨packet, packet.nonempty_resetFaceDispatch⟩

end GameTheory
