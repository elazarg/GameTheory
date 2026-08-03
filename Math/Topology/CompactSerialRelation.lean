/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Infinite chains in compact serial relations

This file isolates a small inverse-limit principle.  A closed relation on a
nonempty compact box which has a predecessor at every point admits an
infinite backward chain.  Finite chains are produced by choosing one
predecessor at a time from a terminal anchor; compactness then closes all
finite compatibility conditions simultaneously.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Topology

/-- A closed predecessor-serial relation on one compact box. -/
structure CompactSerialRelation (Point : Type*) [TopologicalSpace Point] where
  box : Set Point
  relation : Point → Point → Prop
  box_nonempty : box.Nonempty
  box_compact : IsCompact box
  relationGraph_closed : IsClosed
    {pair : Point × Point |
      pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2}
  predecessor_exists : ∀ tail, tail ∈ box →
    ∃ current, current ∈ box ∧ relation current tail

variable {Point : Type*} [TopologicalSpace Point]

/-- The chosen terminal anchor, packaged as a point of the compact box. -/
def CompactSerialRelation.center
    (system : CompactSerialRelation Point) : system.box :=
  ⟨Classical.choose system.box_nonempty,
    Classical.choose_spec system.box_nonempty⟩

/-- An arbitrary chosen predecessor of a point in the compact box. -/
def CompactSerialRelation.predecessor
    (system : CompactSerialRelation Point) (tail : system.box) : system.box :=
  ⟨Classical.choose (system.predecessor_exists tail tail.property),
    (Classical.choose_spec
      (system.predecessor_exists tail tail.property)).1⟩

/-- The chosen predecessor is related to its tail. -/
theorem CompactSerialRelation.predecessor_related
    (system : CompactSerialRelation Point) (tail : system.box) :
    system.relation (system.predecessor tail) tail :=
  (Classical.choose_spec
    (system.predecessor_exists tail tail.property)).2

/-- Apply the chosen predecessor operation a finite number of times. -/
def compactSerialIteratedPredecessor
    (system : CompactSerialRelation Point) : ℕ → system.box → system.box
  | 0, point => point
  | fuel + 1, point =>
      system.predecessor
        (compactSerialIteratedPredecessor system fuel point)

@[simp] theorem compactSerialIteratedPredecessor_zero
    (system : CompactSerialRelation Point) (point : system.box) :
    compactSerialIteratedPredecessor system 0 point = point := by
  rfl

@[simp] theorem compactSerialIteratedPredecessor_succ
    (system : CompactSerialRelation Point) (fuel : ℕ)
    (point : system.box) :
    compactSerialIteratedPredecessor system (fuel + 1) point =
      system.predecessor
        (compactSerialIteratedPredecessor system fuel point) := by
  rfl

/-- A finite chain pulled backward from the fixed terminal anchor.  Past the
terminal index we fill coordinates with the same harmless box point. -/
def compactSerialPrefixPath
    (system : CompactSerialRelation Point)
    (horizon time : ℕ) : Point :=
  if time ≤ horizon then
    compactSerialIteratedPredecessor system (horizon - time) system.center
  else
    system.center

/-- Every coordinate of the chosen finite chain lies in the compact box. -/
theorem compactSerialPrefixPath_mem
    (system : CompactSerialRelation Point) (horizon time : ℕ) :
    compactSerialPrefixPath system horizon time ∈ system.box := by
  classical
  unfold compactSerialPrefixPath
  split_ifs
  · exact (compactSerialIteratedPredecessor system
      (horizon - time) system.center).property
  · exact system.center.property

/-- The chosen finite chain satisfies the relation before its terminal
anchor. -/
theorem compactSerialPrefixPath_related
    (system : CompactSerialRelation Point)
    (horizon time : ℕ) (htime : time < horizon) :
    system.relation
      (compactSerialPrefixPath system horizon time)
      (compactSerialPrefixPath system horizon (time + 1)) := by
  classical
  have htime0 : time ≤ horizon := htime.le
  have htime1 : time + 1 ≤ horizon := by omega
  unfold compactSerialPrefixPath
  rw [if_pos htime0, if_pos htime1]
  have hsub : horizon - time = (horizon - (time + 1)) + 1 := by omega
  rw [hsub, compactSerialIteratedPredecessor_succ]
  exact system.predecessor_related _

/-- Box-valued paths satisfying the first `horizon` relation constraints. -/
def compactSerialPrefixSolutionSet
    (system : CompactSerialRelation Point) (horizon : ℕ) :
    Set (ℕ → Point) :=
  {value |
    (∀ time, value time ∈ system.box) ∧
      ∀ time : Fin horizon,
        system.relation (value time) (value (time + 1))}

/-- Every finite-prefix solution set is inhabited. -/
theorem compactSerialPrefixSolutionSet_nonempty
    (system : CompactSerialRelation Point) (horizon : ℕ) :
    (compactSerialPrefixSolutionSet system horizon).Nonempty := by
  refine ⟨compactSerialPrefixPath system horizon, ?_, ?_⟩
  · exact compactSerialPrefixPath_mem system horizon
  · intro time
    exact compactSerialPrefixPath_related system horizon time time.isLt

/-- Adding one more relation constraint shrinks the prefix solution set. -/
theorem compactSerialPrefixSolutionSet_succ_subset
    (system : CompactSerialRelation Point) (horizon : ℕ) :
    compactSerialPrefixSolutionSet system (horizon + 1) ⊆
      compactSerialPrefixSolutionSet system horizon := by
  intro value hvalue
  refine ⟨hvalue.1, fun time ↦ ?_⟩
  exact hvalue.2 ⟨time, lt_trans time.isLt (Nat.lt_succ_self horizon)⟩

variable [T2Space Point]

/-- Every finite-prefix solution set is closed in the sequence space. -/
theorem compactSerialPrefixSolutionSet_isClosed
    (system : CompactSerialRelation Point) (horizon : ℕ) :
    IsClosed (compactSerialPrefixSolutionSet system horizon) := by
  let ambient : Set (ℕ → Point) :=
    {value | ∀ time, value time ∈ system.box}
  have hambientCompact : IsCompact ambient := by
    dsimp only [ambient]
    exact isCompact_pi_infinite fun _ ↦ system.box_compact
  have hambientClosed : IsClosed ambient := hambientCompact.isClosed
  let relationGraph : Set (Point × Point) :=
    {pair |
      pair.1 ∈ system.box ∧ pair.2 ∈ system.box ∧
        system.relation pair.1 pair.2}
  have hconstraint : ∀ time : Fin horizon,
      IsClosed {value : ℕ → Point |
        (value time, value (time + 1)) ∈ relationGraph} := by
    intro time
    have hpair : Continuous (fun value : ℕ → Point ↦
        (value time, value ((time : ℕ) + 1))) :=
      (continuous_apply (time : ℕ)).prodMk
        (continuous_apply ((time : ℕ) + 1))
    exact (by
      apply IsClosed.preimage hpair
      simpa only [relationGraph] using system.relationGraph_closed)
  have hclosed : IsClosed
      (ambient ∩ ⋂ time : Fin horizon,
        {value : ℕ → Point |
          (value time, value (time + 1)) ∈ relationGraph}) :=
    hambientClosed.inter (isClosed_iInter hconstraint)
  have heq : compactSerialPrefixSolutionSet system horizon =
      ambient ∩ ⋂ time : Fin horizon,
        {value : ℕ → Point |
          (value time, value (time + 1)) ∈ relationGraph} := by
    ext value
    simp only [compactSerialPrefixSolutionSet, ambient, relationGraph,
      Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro hvalue
      exact ⟨hvalue.1, fun time ↦
        ⟨hvalue.1 time, hvalue.1 ((time : ℕ) + 1), hvalue.2 time⟩⟩
    · intro hvalue
      exact ⟨hvalue.1, fun time ↦ (hvalue.2 time).2.2⟩
  rw [heq]
  exact hclosed

/-- Every finite-prefix solution set is compact. -/
theorem compactSerialPrefixSolutionSet_isCompact
    (system : CompactSerialRelation Point) (horizon : ℕ) :
    IsCompact (compactSerialPrefixSolutionSet system horizon) := by
  have hambient : IsCompact
      {value : ℕ → Point | ∀ time, value time ∈ system.box} :=
    isCompact_pi_infinite fun _ ↦ system.box_compact
  exact hambient.of_isClosed_subset
    (compactSerialPrefixSolutionSet_isClosed system horizon)
    (fun _ hvalue ↦ hvalue.1)

/-- Compact inverse-limit existence for a closed predecessor-serial relation. -/
theorem CompactSerialRelation.exists_infiniteChain
    (system : CompactSerialRelation Point) :
    ∃ value : ℕ → Point,
      (∀ time, value time ∈ system.box) ∧
        ∀ time, system.relation (value time) (value (time + 1)) := by
  let prefixSet : ℕ → Set (ℕ → Point) :=
    fun horizon ↦ compactSerialPrefixSolutionSet system horizon
  have hnested : ∀ horizon,
      prefixSet (horizon + 1) ⊆ prefixSet horizon :=
    compactSerialPrefixSolutionSet_succ_subset system
  have hnonempty : ∀ horizon, (prefixSet horizon).Nonempty :=
    compactSerialPrefixSolutionSet_nonempty system
  have hcompact0 : IsCompact (prefixSet 0) :=
    compactSerialPrefixSolutionSet_isCompact system 0
  have hclosed : ∀ horizon, IsClosed (prefixSet horizon) :=
    compactSerialPrefixSolutionSet_isClosed system
  obtain ⟨value, hvalue⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      prefixSet hnested hnonempty hcompact0 hclosed
  have hprefix : ∀ horizon, value ∈ prefixSet horizon :=
    Set.mem_iInter.mp hvalue
  exact ⟨value, (hprefix 0).1, fun time ↦
    (hprefix (time + 1)).2 ⟨time, Nat.lt_succ_self time⟩⟩

end Topology
end Math
