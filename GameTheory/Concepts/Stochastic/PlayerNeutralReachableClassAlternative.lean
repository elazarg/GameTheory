/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerNeutralZeroDriftRestriction
import GameTheory.Concepts.Stochastic.PublicRecurrentClassTarget
import Math.Probability.ChargedClassSupportRank

/-!
# Reachable charged classes after player-neutral deflation

Strict leading-drift deflation preserves a normalized positive circulation
on the residual zero-drift operational family.  To turn that circulation
into a recurrent class at a public entry, its positive-mass sources must be
reachable from that entry in the union of the residual operational supports.

Under exactly that support hypothesis, the generic occupation realization
selects a reachable closed communicating class with positive aggregate
owner charge.  The selected class either has strictly smaller source-support
rank or is the whole active support.

This does not transport the complete payoff-vector target and does not
identify source-support cardinality with a public-recursion rank.  Those
remain separate strategic obligations.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm
namespace PlayerNeutralStrictLeadingDrift

variable
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}

/-- An entry-reachable charged circulation and one of its positive
communicating classes, together with the exact support-rank dichotomy. -/
structure ReachablePositiveClassData
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (entry : G.State) where
  circulation :
    EntryReachablePositiveChargedCirculation
      C.zeroDriftKernel C.zeroDriftSource
      C.zeroDriftCharge entry
  positiveClass : circulation.PositiveCommunicatingClass
  rankAlternative :
    positiveClass.HasProperSupportRankDescent ∨
      positiveClass.IsFullActiveSupportClass

namespace ReachablePositiveClassData

variable
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {entry : G.State}

/-- Convert a selected residual positive class into recurrent-child data on
the original game state space.

The occupation construction supplies the class and its operational owner.
The arguments below deliberately expose the three strategic seams it does
not supply:

* `core` and `legal_entry_interface` realize a legal public kernel and entry;
* `continuation`, `harmonic`, and the target equalities transport the whole
  payoff vector;
* `rank_decreases` identifies a genuine decrease in the chosen recursion
  rank.

`core_states` is the precise identification between the ambient public class
and the subtype class selected by the occupation realization. -/
def toPublicRecurrentClassChild
    {Rank Node : Type*}
    (D : ReachablePositiveClassData
      (germ := germ) (B := B) (who := who) C entry)
    (legalKernel : G.State → PMF G.State)
    (nodeEntry : Node → G.State)
    (nodeTarget : Node → Payoff ι)
    (nodeRank : Node → Rank)
    (rankLt : Rank → Rank → Prop)
    (LegalEntryInterface : Node → Prop)
    (parent : Node)
    (core :
      ReachableClosedClass legalKernel (nodeEntry parent))
    (core_states :
      core.states =
        D.positiveClass.closedClass.states.image
          (fun state => state.1))
    (core_entry :
      core.entry = D.positiveClass.representative.1)
    (continuation : G.State → Payoff ι)
    (harmonic :
      ∀ state, state ∈ core.states →
        ∀ player,
          continuation state player =
            expect (legalKernel state)
              (fun next => continuation next player))
    (parent_target :
      nodeTarget parent =
        continuation D.positiveClass.representative.1)
    (child : Node)
    (childState : D.circulation.ActiveState)
    (childState_mem :
      childState ∈ D.positiveClass.closedClass.states)
    (child_entry : nodeEntry child = childState.1)
    (child_target :
      nodeTarget child = continuation childState.1)
    (rank_decreases :
      rankLt (nodeRank child) (nodeRank parent))
    (legal_entry_interface : LegalEntryInterface parent) :
    PublicRecurrentClassChild
      legalKernel nodeEntry nodeTarget nodeRank rankLt
      LegalEntryInterface parent := by
  have childState_mem_core : childState.1 ∈ core.states := by
    rw [core_states]
    exact Finset.mem_image.mpr
      ⟨childState, childState_mem, rfl⟩
  have parent_target_core :
      nodeTarget parent = continuation core.entry := by
    rw [parent_target, core_entry]
  exact PublicRecurrentClassChild.of_harmonicClassTarget
    core continuation harmonic parent_target_core
    child childState.1 childState_mem_core child_entry
    child_target rank_decreases legal_entry_interface

/-- Proper source-support inclusion derives the rank field when the public
recursion uses the corresponding support cardinalities as natural-number
ranks.  Every other public-child obligation remains explicit. -/
def toPublicRecurrentClassChild_of_properSupportRank
    {Node : Type*}
    (D : ReachablePositiveClassData
      (germ := germ) (B := B) (who := who) C entry)
    (proper :
      D.positiveClass.HasProperSupportRankDescent)
    (legalKernel : G.State → PMF G.State)
    (nodeEntry : Node → G.State)
    (nodeTarget : Node → Payoff ι)
    (nodeRank : Node → ℕ)
    (LegalEntryInterface : Node → Prop)
    (parent : Node)
    (core :
      ReachableClosedClass legalKernel (nodeEntry parent))
    (core_states :
      core.states =
        D.positiveClass.closedClass.states.image
          (fun state => state.1))
    (core_entry :
      core.entry = D.positiveClass.representative.1)
    (continuation : G.State → Payoff ι)
    (harmonic :
      ∀ state, state ∈ core.states →
        ∀ player,
          continuation state player =
            expect (legalKernel state)
              (fun next => continuation next player))
    (parent_target :
      nodeTarget parent =
        continuation D.positiveClass.representative.1)
    (child : Node)
    (childState : D.circulation.ActiveState)
    (childState_mem :
      childState ∈ D.positiveClass.closedClass.states)
    (child_entry : nodeEntry child = childState.1)
    (child_target :
      nodeTarget child = continuation childState.1)
    (parent_rank :
      nodeRank parent = D.circulation.activeSupportRank)
    (child_rank :
      nodeRank child = D.positiveClass.supportRank)
    (legal_entry_interface : LegalEntryInterface parent) :
    PublicRecurrentClassChild
      legalKernel nodeEntry nodeTarget nodeRank (· < ·)
      LegalEntryInterface parent := by
  apply D.toPublicRecurrentClassChild
    legalKernel nodeEntry nodeTarget nodeRank (· < ·)
    LegalEntryInterface parent core core_states core_entry
    continuation harmonic parent_target child childState
    childState_mem child_entry child_target
  · rw [child_rank, parent_rank]
    exact proper.2
  · exact legal_entry_interface

end ReachablePositiveClassData

/-- At every public entry, the residual operational family has the exact
entry-aware alternative: a reachable positive charged class with its
support-rank dichotomy, or a bounded potential controlling every reachable
residual charge.  An unrestricted residual circulation does not exclude
the potential branch because it may live in an unreachable component. -/
theorem reachablePositiveClassData_or_boundedPotential
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (entry : G.State) :
    Nonempty (C.ReachablePositiveClassData entry) ∨
      Nonempty
        (EntryReachableBoundedChargePotential
          C.zeroDriftKernel C.zeroDriftSource
          C.zeroDriftCharge entry) := by
  rcases entryReachablePositiveChargedCirculation_or_boundedPotential
      C.zeroDriftKernel C.zeroDriftSource C.zeroDriftCharge entry with
    reachable | bounded
  · left
    obtain ⟨reachableCirculation⟩ := reachable
    obtain ⟨positiveClass⟩ :=
      reachableCirculation.exists_positiveCommunicatingClass
    exact ⟨{
      circulation := reachableCirculation
      positiveClass := positiveClass
      rankAlternative :=
        positiveClass.properSupportRankDescent_or_fullActiveSupport
          reachableCirculation
    }⟩
  · exact Or.inr bounded

/-- A concrete residual circulation whose positive-mass sources are
reachable from `entry` yields a reachable positive charged class.

The source-support assumption is exact for restricting this particular
circulation; no reachability of zero-mass residual columns is required. -/
theorem exists_reachablePositiveClassData_of_massSupport
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (entry : G.State)
    (mass : C.ZeroDriftIndex → ℝ)
    (mass_nonneg : ∀ index, 0 ≤ mass index)
    (balance :
      ∀ destination,
        ∑ index, mass index *
          actualOccupationColumn
            C.zeroDriftKernel C.zeroDriftSource
            index destination = 0)
    (charge_eq_one :
      ∑ index, mass index * C.zeroDriftCharge index = 1)
    (massSupport_reachable :
      ∀ index, 0 < mass index →
        AvailableReachable
          C.zeroDriftKernel C.zeroDriftSource entry
          (C.zeroDriftSource index)) :
    Nonempty (C.ReachablePositiveClassData entry) := by
  have restricted :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (fun index :
              ReachableOccupationIndex
                C.zeroDriftKernel C.zeroDriftSource entry =>
            C.zeroDriftKernel index.1)
          (fun index :
              ReachableOccupationIndex
                C.zeroDriftKernel C.zeroDriftSource entry =>
            C.zeroDriftSource index.1))
        (fun index :
            ReachableOccupationIndex
              C.zeroDriftKernel C.zeroDriftSource entry =>
          C.zeroDriftCharge index.1) :=
    restrict_positiveChargedCirculation_of_mass_support
      C.zeroDriftKernel C.zeroDriftSource C.zeroDriftCharge
      entry mass mass_nonneg balance charge_eq_one
      massSupport_reachable
  obtain ⟨reachableCirculation⟩ :=
    EntryReachablePositiveChargedCirculation.of_hasNormalizedPositiveChargedCirculation
      restricted
  obtain ⟨positiveClass⟩ :=
    reachableCirculation.exists_positiveCommunicatingClass
  exact ⟨{
    circulation := reachableCirculation
    positiveClass := positiveClass
    rankAlternative :=
      positiveClass.properSupportRankDescent_or_fullActiveSupport
        reachableCirculation
  }⟩

/-- If every residual source is operationally reachable from `entry`, the
circulation preserved by strict deflation supplies a reachable positive
class.  This checkable graph hypothesis is stronger than the exact
positive-mass support condition above. -/
theorem exists_reachablePositiveClassData_of_allSourcesReachable
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (entry : G.State)
    (allSources_reachable :
      ∀ index : C.ZeroDriftIndex,
        AvailableReachable
          C.zeroDriftKernel C.zeroDriftSource entry
          (C.zeroDriftSource index)) :
    Nonempty (C.ReachablePositiveClassData entry) := by
  obtain ⟨mass, mass_nonneg, balance, charge_eq_one⟩ :=
    C.exists_zeroDrift_normalizedPositiveChargedCirculation circulation
  exact C.exists_reachablePositiveClassData_of_massSupport
    entry mass mass_nonneg balance charge_eq_one
    (fun index _ => allSources_reachable index)

end PlayerNeutralStrictLeadingDrift
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
