/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicRecurrentClassTarget
import Math.Probability.ChargedClassSupportRank

/-!
# Support-rank recurrent public children

The proper-support branch of a positive communicating class supplies a
strict natural-number rank decrease.  This file feeds that one conclusion
into the harmonic target constructor.  Entry identification, harmonic
target transport, child selection, and the legal entry interface remain
explicit inputs.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

namespace PublicRecurrentClassChild

variable
    {State Index Player Node : Type*}
    [Fintype State] [Fintype Index] [DecidableEq State]
    {kernel : Index → PMF State}
    {source : Index → State}
    {charge : Index → ℝ}
    {externalEntry : State}
    {C :
      EntryReachablePositiveChargedCirculation
        kernel source charge externalEntry}
    {P : C.PositiveCommunicatingClass}
    {nodeEntry : Node → C.ActiveState}
    {nodeTarget : Node → Player → ℝ}
    {nodeRank : Node → ℕ}
    {LegalEntryInterface : Node → Prop}
    {parent : Node}

/-- The proper-support class produces a recurrent public child when all
non-rank obligations of `of_harmonicClassTarget` are supplied explicitly.

The node ranks must be identified with the ambient and class support
cardinalities; only then is strict descent inferred from proper inclusion. -/
def of_harmonicClassTarget_of_properSupportRank
    (proper : P.HasProperSupportRankDescent)
    (core :
      ReachableClosedClass C.activeKernel (nodeEntry parent))
    (core_states : core.states = P.closedClass.states)
    (core_entry : core.entry = P.representative)
    (continuation : C.ActiveState → Player → ℝ)
    (harmonic :
      ∀ state, state ∈ P.closedClass.states →
        ∀ player,
          continuation state player =
            expect (C.activeKernel state)
              (fun next => continuation next player))
    (parent_target :
      nodeTarget parent = continuation P.representative)
    (child : Node) (childState : C.ActiveState)
    (childState_mem : childState ∈ P.closedClass.states)
    (child_entry : nodeEntry child = childState)
    (child_target :
      nodeTarget child = continuation childState)
    (parent_rank : nodeRank parent = C.activeSupportRank)
    (child_rank : nodeRank child = P.supportRank)
    (legal_entry_interface : LegalEntryInterface parent) :
    PublicRecurrentClassChild
      C.activeKernel nodeEntry nodeTarget nodeRank (· < ·)
      LegalEntryInterface parent := by
  have rank_decreases :
      nodeRank child < nodeRank parent := by
    rw [child_rank, parent_rank]
    exact proper.2
  have core_harmonic :
      ∀ state, state ∈ core.states →
        ∀ player,
          continuation state player =
            expect (C.activeKernel state)
              (fun next => continuation next player) := by
    intro state hstate player
    exact harmonic state (by rwa [← core_states]) player
  have core_parent_target :
      nodeTarget parent =
        continuation core.entry := by
    rw [parent_target, core_entry]
  have core_child_mem : childState ∈ core.states := by
    rwa [core_states]
  exact PublicRecurrentClassChild.of_harmonicClassTarget
    core continuation core_harmonic core_parent_target
    child childState core_child_mem child_entry child_target
    rank_decreases legal_entry_interface

end PublicRecurrentClassChild

end StochasticGame
end GameTheory
