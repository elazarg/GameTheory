/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Endpoint.AnalyticPrescribedEndpointTailRecurrentChildBridge
import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.FiniteBiasCanonicalTransportCirculationAlternative

/-!
# Atlas leaf for the tail recurrent-child frontier

This two-leaf atlas consumes the concrete endpoint-transport circulation
evidence.  A proper class inside the positive circulation active support
exposes strict local cardinal descent; actual entry, whole-vector target,
legal interface, and identification with the global node rank remain named
exactly.  A class covering the full active support is retained positively
through regeneration, equal local support rank, the positive tail-law seed
path, and aggregate oriented charge.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.OnlineLearning Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Typed support frontier for one concrete tail-reachable endpoint
circulation.  Neither constructor is by itself a terminal recursive leaf. -/
inductive TailRecurrentChildAtlasLeaf
    {germ : G.AnalyticBellmanGerm}
    {who : ι} {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (evidence :
      TailReachableEndpointTransportCirculationEvidence
        germ who entry startEpoch valid)
    (candidate :
      TailReachableRecurrentClassCandidate evidence) : Type _
  | properSupport
      (proper :
        candidate.HasProperTailSupportRankDescent)
  | fullTailSupport
      (boundary :
        candidate.FullTailSupportBoundary)

namespace TailRecurrentChildAtlasLeaf

variable
    {germ : G.AnalyticBellmanGerm}
    {who : ι} {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    {evidence :
      TailReachableEndpointTransportCirculationEvidence
        germ who entry startEpoch valid}
    {candidate :
      TailReachableRecurrentClassCandidate evidence}

/-- Every concrete tail endpoint circulation is consumed by exactly the
two-way active-support frontier. -/
theorem exists_of_candidate :
    Nonempty
      (TailRecurrentChildAtlasLeaf evidence candidate) := by
  rcases
      candidate.properTailSupportRankDescent_or_fullTailSupport with
    proper | full
  · exact ⟨.properSupport proper⟩
  · obtain ⟨boundary⟩ :=
      candidate.exists_fullTailSupportBoundary full
    exact ⟨.fullTailSupport boundary⟩

/-- The endpoint evidence itself canonically reaches the atlas, retaining
its positive-mass tail-law seed and aggregate-charge class in both leaves. -/
theorem exists_of_evidence :
    ∃ candidate :
        TailReachableRecurrentClassCandidate evidence,
      Nonempty
        (TailRecurrentChildAtlasLeaf evidence candidate) := by
  obtain ⟨candidate⟩ :=
    TailReachableRecurrentClassCandidate.exists_of_evidence
      (evidence := evidence)
  exact ⟨candidate, exists_of_candidate⟩

/-- Consuming a proper-support leaf with its explicitly named
entry/target/global-rank/legal obligations produces a recurrent child.  The
other leaf remains the positive full-active-support regeneration boundary.
-/
theorem recurrentChild_or_fullTailSupportBoundary
    (leaf : TailRecurrentChildAtlasLeaf evidence candidate)
    {Player Node : Type*}
    (nodeEntry : Node → TailTransportActiveState evidence)
    (nodeTarget : Node → Player → ℝ)
    (nodeRank : Node → ℕ)
    (LegalEntryInterface : Node → Prop)
    (parent : Node)
    (resolveProper :
      ∀ proper :
          candidate.HasProperTailSupportRankDescent,
        Nonempty
          (candidate.ProperSupportChildObligations proper
            nodeEntry nodeTarget nodeRank
            LegalEntryInterface parent)) :
    Nonempty
        (PublicRecurrentClassChild
          (tailTransportActiveKernel evidence)
          nodeEntry nodeTarget nodeRank (· < ·)
          LegalEntryInterface parent) ∨
      Nonempty candidate.FullTailSupportBoundary := by
  cases leaf with
  | properSupport proper =>
      obtain ⟨obligations⟩ := resolveProper proper
      exact Or.inl ⟨
        candidate.toPublicRecurrentClassChild_of_properSupport
          proper nodeEntry nodeTarget nodeRank
          LegalEntryInterface parent obligations⟩
  | fullTailSupport boundary =>
      exact Or.inr ⟨boundary⟩

end TailRecurrentChildAtlasLeaf

namespace FiniteBiasSeed.CanonicalPrescribedTransportCirculationBranch

variable
    {germ : G.AnalyticBellmanGerm}
    {seed : germ.FiniteBiasSeed}
    {entry : G.State}

/-- The canonical failed-transport branch is connected directly to the
active-support recurrent-class frontier. -/
theorem exists_tailRecurrentChildAtlas
    (branch :
      CanonicalPrescribedTransportCirculationBranch germ seed entry) :
    ∃ candidate :
        TailReachableRecurrentClassCandidate
          branch.transportCirculation,
      Nonempty
        (TailRecurrentChildAtlasLeaf
          branch.transportCirculation candidate) :=
  TailRecurrentChildAtlasLeaf.exists_of_evidence

end FiniteBiasSeed.CanonicalPrescribedTransportCirculationBranch

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
