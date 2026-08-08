/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Public.RecurrentClassChild
import Math.Probability.HarmonicClosedClass

/-!
# Harmonic target transport for recurrent public children

Harmonicity transports an entire payoff vector within a finite closed
communicating class.  The constructor below uses that fact to discharge the
target field of `PublicRecurrentClassChild`.

The child entry, the identification of the parent and child targets with a
common harmonic continuation vector, the strict rank decrease, and the
legal entry interface all remain explicit hypotheses.  Positive occupation
charge alone supplies none of them.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

namespace PublicRecurrentClassChild

variable
    {State Player Rank Node : Type*}
    [Fintype State] [DecidableEq State]
    {legalKernel : State → PMF State}
    {entry : Node → State}
    {target : Node → Player → ℝ}
    {rank : Node → Rank}
    {rankLt : Rank → Rank → Prop}
    {LegalEntryInterface : Node → Prop}
    {parent : Node}

/-- Build a recurrent child by transporting a coordinatewise harmonic
continuation vector inside a selected closed communicating class.

No rank conclusion is inferred: `rank_decreases` is an explicit input. -/
def of_harmonicClassTarget
    (core : ReachableClosedClass legalKernel (entry parent))
    (continuation : State → Player → ℝ)
    (harmonic :
      ∀ state, state ∈ core.states →
        ∀ player,
          continuation state player =
            expect (legalKernel state)
              (fun next => continuation next player))
    (parent_target :
      target parent = continuation core.entry)
    (child : Node) (childState : State)
    (childState_mem : childState ∈ core.states)
    (child_entry : entry child = childState)
    (child_target : target child = continuation childState)
    (rank_decreases : rankLt (rank child) (rank parent))
    (legal_entry_interface : LegalEntryInterface parent) :
    PublicRecurrentClassChild
      legalKernel entry target rank rankLt
      LegalEntryInterface parent where
  core := core.repoint childState childState_mem
  child := child
  child_entry := child_entry
  target_preserved := by
    rw [child_target, parent_target]
    exact core.harmonicVector_eq_entry
      continuation harmonic childState_mem
  rank_decreases := rank_decreases
  legal_entry_interface := legal_entry_interface

end PublicRecurrentClassChild

namespace PositiveClassChargeDoesNotTransportTarget

/-!
The two-state deterministic cycle is one closed communicating class.  Its
balanced occupation has positive total charge, but an arbitrary vector may
take different values at the two states.  The missing hypothesis is exactly
harmonicity (or an equivalent target-identification condition).
-/

abbrev State := Bool
abbrev Index := Bool
abbrev Player := Unit

def kernel (state : State) : PMF State :=
  PMF.pure (!state)

def source (index : Index) : State :=
  index

def charge (index : Index) : ℝ :=
  if index then 0 else 1

def target (state : State) (_ : Player) : ℝ :=
  if state then 1 else 0

/-- Unit mass on both directed edges is balanced and has total charge one. -/
theorem positiveChargedCirculation :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn kernel source) charge := by
  refine ⟨fun _ => 1, fun _ => by norm_num, ?_, ?_⟩
  · intro destination
    cases destination <;>
      norm_num [actualOccupationColumn, kernel, source]
  · norm_num [charge]

/-- The two states form one closed communicating class. -/
def closedClass :
    ReachableClosedClass kernel false where
  states := Finset.univ
  states_nonempty := ⟨false, Finset.mem_univ false⟩
  closed := by
    intro state _ destination _
    exact Finset.mem_univ destination
  communicates := by
    intro left _ right _
    cases left <;> cases right
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by simp [PMFSupportStep, kernel])
    · exact Relation.ReflTransGen.single (by simp [PMFSupportStep, kernel])
    · exact Relation.ReflTransGen.refl
  entry := false
  entry_mem := Finset.mem_univ false
  reachable_entry := Relation.ReflTransGen.refl

/-- The arbitrary target differs across the positively charged class. -/
theorem target_not_constant :
    target false ≠ target true := by
  intro h
  have hcoordinate := congrFun h ()
  norm_num [target] at hcoordinate

/-- The same target is not harmonic for the class kernel. -/
theorem target_not_harmonic :
    target false () ≠
      expect (kernel false) (fun next => target next ()) := by
  norm_num [target, kernel]

/-- Positive charge on one closed communicating class therefore does not
transport an arbitrary payoff-vector target. -/
theorem positiveClassCharge_and_targetFailure :
    HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn kernel source) charge ∧
      target false ≠ target true :=
  ⟨positiveChargedCirculation, target_not_constant⟩

end PositiveClassChargeDoesNotTransportTarget

end StochasticGame
end GameTheory
