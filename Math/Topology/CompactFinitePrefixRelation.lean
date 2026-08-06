/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Infinite chains from arbitrarily long finite chains

A closed relation on a compact box need not be predecessor-serial at every
point.  For inverse-limit constructions it is often enough that compatible
chains exist at every finite horizon.  This file records that weaker compactness
principle.

The proof uses the nested compact sets of box-valued sequences satisfying the
first `horizon` relation constraints.  Finite-prefix realizability makes every
set nonempty; compactness closes all constraints simultaneously.
-/

noncomputable section

namespace Math
namespace Topology

variable {Point : Type*} [TopologicalSpace Point]

/-- Box-valued paths satisfying the first `horizon` relation constraints. -/
def compactFinitePrefixSolutionSet
    (box : Set Point) (relation : Point → Point → Prop) (horizon : ℕ) :
    Set (ℕ → Point) :=
  {value |
    (∀ time, value time ∈ box) ∧
      ∀ time : Fin horizon,
        relation (value time) (value (time + 1))}

omit [TopologicalSpace Point] in
/-- Adding one relation constraint shrinks the finite-prefix solution set. -/
theorem compactFinitePrefixSolutionSet_succ_subset
    (box : Set Point) (relation : Point → Point → Prop) (horizon : ℕ) :
    compactFinitePrefixSolutionSet box relation (horizon + 1) ⊆
      compactFinitePrefixSolutionSet box relation horizon := by
  intro value hvalue
  refine ⟨hvalue.1, fun time ↦ ?_⟩
  exact hvalue.2 ⟨time, lt_trans time.isLt (Nat.lt_succ_self horizon)⟩

variable [T2Space Point]

/-- Closed relation graph and compact box make every finite-prefix solution
set closed in the sequence space. -/
theorem compactFinitePrefixSolutionSet_isClosed
    (box : Set Point) (relation : Point → Point → Prop)
    (hbox : IsCompact box)
    (hgraph : IsClosed
      {pair : Point × Point |
        pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2})
    (horizon : ℕ) :
    IsClosed (compactFinitePrefixSolutionSet box relation horizon) := by
  let ambient : Set (ℕ → Point) :=
    {value | ∀ time, value time ∈ box}
  have hambientCompact : IsCompact ambient := by
    dsimp only [ambient]
    exact isCompact_pi_infinite fun _ ↦ hbox
  have hambientClosed : IsClosed ambient := hambientCompact.isClosed
  let relationGraph : Set (Point × Point) :=
    {pair |
      pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2}
  have hconstraint : ∀ time : Fin horizon,
      IsClosed {value : ℕ → Point |
        (value time, value (time + 1)) ∈ relationGraph} := by
    intro time
    have hpair : Continuous (fun value : ℕ → Point ↦
        (value time, value ((time : ℕ) + 1))) :=
      (continuous_apply (time : ℕ)).prodMk
        (continuous_apply ((time : ℕ) + 1))
    apply IsClosed.preimage hpair
    simpa only [relationGraph] using hgraph
  have hclosed : IsClosed
      (ambient ∩ ⋂ time : Fin horizon,
        {value : ℕ → Point |
          (value time, value (time + 1)) ∈ relationGraph}) :=
    hambientClosed.inter (isClosed_iInter hconstraint)
  have heq : compactFinitePrefixSolutionSet box relation horizon =
      ambient ∩ ⋂ time : Fin horizon,
        {value : ℕ → Point |
          (value time, value (time + 1)) ∈ relationGraph} := by
    ext value
    simp only [compactFinitePrefixSolutionSet, ambient, relationGraph,
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
theorem compactFinitePrefixSolutionSet_isCompact
    (box : Set Point) (relation : Point → Point → Prop)
    (hbox : IsCompact box)
    (hgraph : IsClosed
      {pair : Point × Point |
        pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2})
    (horizon : ℕ) :
    IsCompact (compactFinitePrefixSolutionSet box relation horizon) := by
  have hambient : IsCompact
      {value : ℕ → Point | ∀ time, value time ∈ box} :=
    isCompact_pi_infinite fun _ ↦ hbox
  exact hambient.of_isClosed_subset
    (compactFinitePrefixSolutionSet_isClosed box relation hbox hgraph horizon)
    (fun _ hvalue ↦ hvalue.1)

/-- **Compact finite-prefix inverse limit.**  If every finite number of
relation constraints is realizable by a path in a compact box, and the
box-restricted relation graph is closed, then one infinite compatible chain
exists.  No seriality hypothesis at arbitrary box points is required. -/
theorem exists_infiniteChain_of_finitePrefixes
    (box : Set Point) (relation : Point → Point → Prop)
    (hbox : IsCompact box)
    (hgraph : IsClosed
      {pair : Point × Point |
        pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2})
    (hprefix : ∀ horizon,
      (compactFinitePrefixSolutionSet box relation horizon).Nonempty) :
    ∃ value : ℕ → Point,
      (∀ time, value time ∈ box) ∧
        ∀ time, relation (value time) (value (time + 1)) := by
  let prefixSet : ℕ → Set (ℕ → Point) :=
    fun horizon ↦ compactFinitePrefixSolutionSet box relation horizon
  have hnested : ∀ horizon,
      prefixSet (horizon + 1) ⊆ prefixSet horizon :=
    compactFinitePrefixSolutionSet_succ_subset box relation
  have hnonempty : ∀ horizon, (prefixSet horizon).Nonempty := hprefix
  have hcompact0 : IsCompact (prefixSet 0) :=
    compactFinitePrefixSolutionSet_isCompact box relation hbox hgraph 0
  have hclosed : ∀ horizon, IsClosed (prefixSet horizon) :=
    compactFinitePrefixSolutionSet_isClosed box relation hbox hgraph
  obtain ⟨value, hvalue⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      prefixSet hnested hnonempty hcompact0 hclosed
  have hprefixValue : ∀ horizon, value ∈ prefixSet horizon :=
    Set.mem_iInter.mp hvalue
  exact ⟨value, (hprefixValue 0).1, fun time ↦
    (hprefixValue (time + 1)).2 ⟨time, Nat.lt_succ_self time⟩⟩

end Topology
end Math
