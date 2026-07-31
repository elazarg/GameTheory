/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticPrescribedEndpointTailAlternative
import GameTheory.Concepts.Stochastic.PublicRecurrentClassSupportRank
import Math.Probability.FiniteKernelRegeneration

/-!
# Recurrent-child frontier of a tail-reachable endpoint circulation

The tail endpoint alternative selects more than an abstract circulation:
it retains an actual positive-mass state of the stabilized tail law, a
support path from that state to the selected class, and positive aggregate
oriented endpoint charge on the entire selected communicating class.

This file turns that data into the strongest unconditional recurrent-class
candidate.  The class support is compared with the positive circulation
active support inside the stabilized tail family.  A proper class has
strict active-support-cardinality descent.  If the class covers that whole
active support, it instead has fixed-kernel regeneration at the
positive-charge representative and equal active-support rank.

Neither branch silently constructs a public recursive child.  The semantic
tail path uses the row kernel on ambient states, whereas a recursive child
uses the induced active-state kernel and an application-specific legal
entry interface.  The exact parent-entry, child-entry, whole-vector target,
rank, and legal-entry obligations are therefore exposed below.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.OnlineLearning Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- The active state type of the concrete punctured circulation retained by
the tail endpoint evidence. -/
abbrev TailTransportActiveState
    {germ : G.AnalyticBellmanGerm}
    {who : ι} {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (evidence :
      TailReachableEndpointTransportCirculationEvidence
        germ who entry startEpoch valid) :=
  occupationActiveStates
    (fun state : PrescribedFinkTailState evidence.tail => state.1)
    evidence.chargedClass.positiveClass.mass

/-- The induced stationary operational kernel on the positive source
support of the punctured circulation. -/
abbrev tailTransportActiveKernel
    {germ : G.AnalyticBellmanGerm}
    {who : ι} {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (evidence :
      TailReachableEndpointTransportCirculationEvidence
        germ who entry startEpoch valid) :
    TailTransportActiveState evidence →
      PMF (TailTransportActiveState evidence) :=
  occupationActiveKernel
    evidence.chargedClass.semantic.kernel
    (fun state : PrescribedFinkTailState evidence.tail => state.1)
    evidence.chargedClass.positiveClass.mass
    evidence.chargedClass.positiveClass.mass_nonneg
    (actualOccupationBalance_explicit
      evidence.chargedClass.semantic.kernel
      (fun state : PrescribedFinkTailState evidence.tail => state.1)
      evidence.chargedClass.positiveClass.mass
      evidence.chargedClass.positiveClass.balance)

/-- The exact tail-law, graph-entry, and aggregate-charge data carried by
the selected recurrent-class candidate. -/
structure TailReachableRecurrentClassCandidate
    {germ : G.AnalyticBellmanGerm}
    {who : ι} {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (evidence :
      TailReachableEndpointTransportCirculationEvidence
        germ who entry startEpoch valid) where
  seed : G.State
  seed_mass :
    evidence.tail.tailLaw seed ≠ 0
  seed_reaches_representative :
    AvailableReachable
      evidence.chargedClass.semantic.kernel
      (fun state : PrescribedFinkTailState evidence.tail => state.1)
      seed
      evidence.chargedClass.positiveClass.representative.1
  aggregate_oriented_charge_pos :
    0 <
      occupationCommunicationClassOriginalCharge
        evidence.chargedClass.semantic.kernel
        (fun state : PrescribedFinkTailState evidence.tail => state.1)
        (tailRestrictedEndpointTransportCharge
          evidence.tail who evidence.forward
          evidence.chargedClass.parameter)
        evidence.chargedClass.positiveClass.mass
        evidence.chargedClass.positiveClass.mass_nonneg
        evidence.chargedClass.positiveClass.balance
        evidence.chargedClass.positiveClass.representative

namespace TailReachableRecurrentClassCandidate

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

/-- The tail endpoint evidence canonically supplies the graph-theoretic
recurrent-class candidate. -/
theorem exists_of_evidence :
    Nonempty (TailReachableRecurrentClassCandidate evidence) := by
  obtain ⟨seed, seed_mass, reachable⟩ :=
    evidence.chargedClass.exists_tailLaw_seed_reaching_representative
  exact ⟨{
    seed := seed
    seed_mass := seed_mass
    seed_reaches_representative := reachable
    aggregate_oriented_charge_pos :=
      evidence.chargedClass.positiveClass.original_class_charge_pos
  }⟩

/-- Cardinality of the positive occupation support inside the stabilized
tail source family.  The analytic evidence does not assert that every state
of the stabilized tail family receives positive circulation mass. -/
def tailSupportRank
    (_candidate : TailReachableRecurrentClassCandidate evidence) : ℕ :=
  Fintype.card (TailTransportActiveState evidence)

/-- Cardinality of the selected communicating class. -/
def classSupportRank
    (_candidate : TailReachableRecurrentClassCandidate evidence) : ℕ :=
  evidence.chargedClass.positiveClass.closedClass.states.card

/-- The class is a proper recurrent support inside the positive circulation
active support and hence has strict finite support rank. -/
def HasProperTailSupportRankDescent
    (candidate : TailReachableRecurrentClassCandidate evidence) : Prop :=
  evidence.chargedClass.positiveClass.closedClass.states ⊂
      (Finset.univ : Finset (TailTransportActiveState evidence)) ∧
    candidate.classSupportRank < candidate.tailSupportRank

/-- Positive same-rank boundary: the selected positive-charge class covers
the entire positive circulation support of the tail-restricted family. -/
def IsFullTailSupportClass
    (_candidate : TailReachableRecurrentClassCandidate evidence) : Prop :=
  evidence.chargedClass.positiveClass.closedClass.states =
    (Finset.univ : Finset (TailTransportActiveState evidence))

/-- Proper inclusion gives the advertised strict tail-support rank. -/
theorem hasProperTailSupportRankDescent_of_ssubset
    (candidate : TailReachableRecurrentClassCandidate evidence)
    (proper :
      evidence.chargedClass.positiveClass.closedClass.states ⊂
        (Finset.univ : Finset (TailTransportActiveState evidence))) :
    candidate.HasProperTailSupportRankDescent := by
  exact ⟨proper, Finset.card_lt_card proper⟩

/-- Exact positive support frontier: a class is either a strict
support-rank child or it covers the whole stabilized tail support. -/
theorem properTailSupportRankDescent_or_fullTailSupport
    (candidate : TailReachableRecurrentClassCandidate evidence) :
    candidate.HasProperTailSupportRankDescent ∨
      candidate.IsFullTailSupportClass := by
  by_cases full :
      evidence.chargedClass.positiveClass.closedClass.states =
        (Finset.univ : Finset (TailTransportActiveState evidence))
  · exact Or.inr full
  · exact Or.inl <|
      candidate.hasProperTailSupportRankDescent_of_ssubset <|
        Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.subset_univ _, full⟩

/-- Full active support gives support reachability to the positive-charge
representative from every active state. -/
theorem reaches_representative_of_fullTailSupport
    (candidate : TailReachableRecurrentClassCandidate evidence)
    (full : candidate.IsFullTailSupportClass)
    (source : TailTransportActiveState evidence) :
    PMFReachable
      (tailTransportActiveKernel evidence) source
      evidence.chargedClass.positiveClass.representative := by
  apply evidence.chargedClass.positiveClass.closedClass.communicates
  · rw [full]
    exact Finset.mem_univ source
  · simpa only
      [evidence.chargedClass.positiveClass.closedClass_entry] using
        evidence.chargedClass.positiveClass.closedClass.entry_mem

/-- The constructive same-rank boundary retained when the class covers the
whole positive circulation active support. -/
structure FullTailSupportBoundary
    (candidate : TailReachableRecurrentClassCandidate evidence) where
  full : candidate.IsFullTailSupportClass
  regeneration :
    FiniteKernelRegeneration
      (tailTransportActiveKernel evidence)
      evidence.chargedClass.positiveClass.representative
  hittingMinorization :
    FiniteHittingMinorization
      (tailTransportActiveKernel evidence)
      evidence.chargedClass.positiveClass.representative
  same_support_rank :
    candidate.classSupportRank = candidate.tailSupportRank

/-- Full active support has a positive fixed-kernel bounded-step
regeneration package; it is retained as a boundary, not discarded as
failure of rank descent. -/
theorem exists_fullTailSupportBoundary
    (candidate : TailReachableRecurrentClassCandidate evidence)
    (full : candidate.IsFullTailSupportClass) :
    Nonempty (FullTailSupportBoundary candidate) := by
  obtain ⟨regeneration⟩ :=
    exists_finiteKernelRegeneration
      (tailTransportActiveKernel evidence)
      evidence.chargedClass.positiveClass.representative
      (candidate.reaches_representative_of_fullTailSupport full)
  obtain ⟨hittingMinorization⟩ :=
    exists_finiteHittingMinorization
      (tailTransportActiveKernel evidence)
      evidence.chargedClass.positiveClass.representative
      (candidate.reaches_representative_of_fullTailSupport full)
  exact ⟨{
    full := full
    regeneration := regeneration
    hittingMinorization := hittingMinorization
    same_support_rank := by
      rw [classSupportRank, tailSupportRank, full]
      exact Finset.card_univ
  }⟩

/-- Exact obligations needed to turn the graph-theoretic class into a
`PublicRecurrentClassChild`.  In particular, target preservation is
equality of the complete player-indexed vector. -/
structure ChildObligations
    (candidate : TailReachableRecurrentClassCandidate evidence)
    {Player Rank Node : Type*}
    (nodeEntry : Node → TailTransportActiveState evidence)
    (nodeTarget : Node → Player → ℝ)
    (nodeRank : Node → Rank)
    (rankLt : Rank → Rank → Prop)
    (LegalEntryInterface : Node → Prop)
    (parent : Node) where
  child : Node
  parent_entry :
    nodeEntry parent =
      evidence.chargedClass.positiveClass.representative
  child_entry :
    nodeEntry child =
      evidence.chargedClass.positiveClass.representative
  whole_vector_target :
    nodeTarget child = nodeTarget parent
  rank_decreases :
    rankLt (nodeRank child) (nodeRank parent)
  legal_entry_interface :
    LegalEntryInterface parent

/-- Once the five explicit recursive obligations are supplied, the
candidate becomes a public recurrent child. -/
def toPublicRecurrentClassChild
    (candidate : TailReachableRecurrentClassCandidate evidence)
    {Player Rank Node : Type*}
    (nodeEntry : Node → TailTransportActiveState evidence)
    (nodeTarget : Node → Player → ℝ)
    (nodeRank : Node → Rank)
    (rankLt : Rank → Rank → Prop)
    (LegalEntryInterface : Node → Prop)
    (parent : Node)
    (obligations :
      candidate.ChildObligations
        nodeEntry nodeTarget nodeRank rankLt
        LegalEntryInterface parent) :
    PublicRecurrentClassChild
      (tailTransportActiveKernel evidence)
      nodeEntry nodeTarget nodeRank rankLt
      LegalEntryInterface parent := by
  let selectedCore :=
    evidence.chargedClass.positiveClass.closedClass
  let core :
      ReachableClosedClass
        (tailTransportActiveKernel evidence)
        (nodeEntry parent) := {
    states := selectedCore.states
    states_nonempty := selectedCore.states_nonempty
    closed := selectedCore.closed
    communicates := selectedCore.communicates
    entry := evidence.chargedClass.positiveClass.representative
    entry_mem := by
      change
        evidence.chargedClass.positiveClass.representative ∈
          evidence.chargedClass.positiveClass.closedClass.states
      rw [
        evidence.chargedClass.positiveClass.closedClass.states_eq_communicationClass,
        evidence.chargedClass.positiveClass.closedClass_entry]
      exact
        self_mem_pmfCommunicationClass
          (tailTransportActiveKernel evidence)
          evidence.chargedClass.positiveClass.representative
    reachable_entry := by
      rw [obligations.parent_entry]
      exact Relation.ReflTransGen.refl
  }
  refine {
    core := core
    child := obligations.child
    child_entry := ?_
    target_preserved := obligations.whole_vector_target
    rank_decreases := obligations.rank_decreases
    legal_entry_interface := obligations.legal_entry_interface
  }
  exact obligations.child_entry

/-- On the proper-support branch, identifying node ranks with the active
and class support cardinalities discharges the strict-rank obligation.
Entry, whole-vector target, and legal implementation remain explicit. -/
structure ProperSupportChildObligations
    (candidate : TailReachableRecurrentClassCandidate evidence)
    (proper : candidate.HasProperTailSupportRankDescent)
    {Player Node : Type*}
    (nodeEntry : Node → TailTransportActiveState evidence)
    (nodeTarget : Node → Player → ℝ)
    (nodeRank : Node → ℕ)
    (LegalEntryInterface : Node → Prop)
    (parent : Node) where
  child : Node
  parent_entry :
    nodeEntry parent =
      evidence.chargedClass.positiveClass.representative
  child_entry :
    nodeEntry child =
      evidence.chargedClass.positiveClass.representative
  whole_vector_target :
    nodeTarget child = nodeTarget parent
  parent_rank :
    nodeRank parent = candidate.tailSupportRank
  child_rank :
    nodeRank child = candidate.classSupportRank
  legal_entry_interface :
    LegalEntryInterface parent

/-- Proper tail support supplies exactly the strict natural-number rank
field of a recurrent child. -/
def toPublicRecurrentClassChild_of_properSupport
    (candidate : TailReachableRecurrentClassCandidate evidence)
    (proper : candidate.HasProperTailSupportRankDescent)
    {Player Node : Type*}
    (nodeEntry : Node → TailTransportActiveState evidence)
    (nodeTarget : Node → Player → ℝ)
    (nodeRank : Node → ℕ)
    (LegalEntryInterface : Node → Prop)
    (parent : Node)
    (obligations :
      candidate.ProperSupportChildObligations proper
        nodeEntry nodeTarget nodeRank LegalEntryInterface parent) :
    PublicRecurrentClassChild
      (tailTransportActiveKernel evidence)
      nodeEntry nodeTarget nodeRank (· < ·)
      LegalEntryInterface parent := by
  apply candidate.toPublicRecurrentClassChild
  exact {
    child := obligations.child
    parent_entry := obligations.parent_entry
    child_entry := obligations.child_entry
    whole_vector_target := obligations.whole_vector_target
    rank_decreases := by
      rw [obligations.child_rank, obligations.parent_rank]
      exact proper.2
    legal_entry_interface := obligations.legal_entry_interface
  }

end TailReachableRecurrentClassCandidate

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
