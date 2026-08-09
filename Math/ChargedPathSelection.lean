/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ChargedPathBudget
import Mathlib.Tactic

/-!
# Selection of divergent charged paths

This module separates two properties of a nonnegatively charged relation.
Finite paths from a state may have arbitrarily large charge, while no single
infinite path need accumulate unbounded charge.  The missing compatibility is
expressed by `ChargeRenewal`: after collecting one unit of charge, one can end
at a state from which finite charge is still unbounded.

Infinite paths are represented in nonempty finite blocks.  Each block is a
literal `ChargedRelation.Path`, so no edge or charge is omitted, and
`prefixPath` flattens every finite block prefix back to one ordinary finite
path.  This representation makes concatenation and renewal choice exact while
avoiding an irrelevant encoding of a stream position inside a variable-length
block.

The main theorem states, for arbitrary charged relations, that charge renewal
is equivalent to the implication from unbounded finite charge to existence of
one divergent infinite path.  No compactness, finite branching, or application
to game theory is asserted.
-/

noncomputable section

universe u v

namespace Math
namespace ChargedPathBudget
namespace ChargedRelation

variable {State : Type u} {Edge : Type v}
variable (R : ChargedRelation State Edge)

/-! ## Infinite blocked paths and their exact finite prefixes -/

/-- An infinite path from `start`, represented by consecutive nonempty finite
blocks.  Requiring positive block length rules out stuttering by empty paths.
The blocks may have arbitrary finite lengths. -/
structure InfinitePathFrom (start : State) where
  state : ℕ → State
  state_zero : state 0 = start
  segment : ∀ n, R.Path (state n) (state (n + 1))
  segment_length_pos : ∀ n, 0 < (segment n).length

namespace InfinitePathFrom

variable {R} {start : State}

/-- Flatten the first `n` blocks into one ordinary finite admissible path. -/
def prefixPath (path : R.InfinitePathFrom start) :
    ∀ n, R.Path start (path.state n)
  | 0 => (Path.nil start).castTgt path.state_zero.symm
  | n + 1 => (prefixPath path n).append (path.segment n)

/-- Charge accumulated by the first `n` blocks. -/
def partialCharge (path : R.InfinitePathFrom start) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (path.segment k).chargeSum

@[simp] theorem partialCharge_zero (path : R.InfinitePathFrom start) :
    path.partialCharge 0 = 0 := by
  simp [partialCharge]

theorem partialCharge_succ (path : R.InfinitePathFrom start) (n : ℕ) :
    path.partialCharge (n + 1) =
      path.partialCharge n + (path.segment n).chargeSum := by
  simp [partialCharge, Finset.sum_range_succ]

/-- Flattening preserves accumulated charge exactly. -/
@[simp] theorem chargeSum_prefixPath (path : R.InfinitePathFrom start) (n : ℕ) :
    (path.prefixPath n).chargeSum = path.partialCharge n := by
  induction n with
  | zero => simp [prefixPath]
  | succ n ih =>
      rw [prefixPath, Path.chargeSum_append, ih, partialCharge_succ]

/-- A finite path between two block boundaries. -/
def betweenPath (path : R.InfinitePathFrom start) (first : ℕ) :
    ∀ fuel, R.Path (path.state first) (path.state (first + fuel))
  | 0 => Path.nil _
  | fuel + 1 => (betweenPath path first fuel).append
      (path.segment (first + fuel))

@[simp] theorem chargeSum_betweenPath_zero
    (path : R.InfinitePathFrom start) (first : ℕ) :
    (path.betweenPath first 0).chargeSum = 0 := by
  rfl

/-- Partial charge splits exactly at every block boundary. -/
theorem partialCharge_add (path : R.InfinitePathFrom start)
    (first fuel : ℕ) :
    path.partialCharge (first + fuel) =
      path.partialCharge first + (path.betweenPath first fuel).chargeSum := by
  induction fuel with
  | zero => simp [betweenPath]
  | succ fuel ih =>
      change path.partialCharge ((first + fuel) + 1) =
        path.partialCharge first +
          ((path.betweenPath first fuel).append
            (path.segment (first + fuel))).chargeSum
      rw [partialCharge_succ, Path.chargeSum_append, ih]
      ring

/-- Partial charge is nondecreasing because every edge charge is
nonnegative. -/
theorem partialCharge_mono (path : R.InfinitePathFrom start) :
    Monotone path.partialCharge := by
  apply monotone_nat_of_le_succ
  intro n
  rw [partialCharge_succ]
  exact le_add_of_nonneg_right (path.segment n).chargeSum_nonneg

/-- Discard the first `first` blocks of an infinite path. -/
def drop (path : R.InfinitePathFrom start) (first : ℕ) :
    R.InfinitePathFrom (path.state first) where
  state fuel := path.state (first + fuel)
  state_zero := rfl
  segment fuel := path.segment (first + fuel)
  segment_length_pos fuel := path.segment_length_pos (first + fuel)

/-- The partial charge of a dropped path is exactly the charge between the
corresponding block boundaries of the original path. -/
theorem partialCharge_drop (path : R.InfinitePathFrom start)
    (first fuel : ℕ) :
    (path.drop first).partialCharge fuel =
      (path.betweenPath first fuel).chargeSum := by
  induction fuel with
  | zero => simp [drop]
  | succ fuel ih =>
      rw [partialCharge_succ]
      change (path.drop first).partialCharge fuel +
          (path.segment (first + fuel)).chargeSum = _
      rw [ih]
      change (path.betweenPath first fuel).chargeSum +
          (path.segment (first + fuel)).chargeSum =
        ((path.betweenPath first fuel).append
          (path.segment (first + fuel))).chargeSum
      rw [Path.chargeSum_append]

/-- One infinite path has unbounded charge when its block-prefix charges are
unbounded above. -/
def HasUnboundedCharge (path : R.InfinitePathFrom start) : Prop :=
  ∀ bound : ℝ, ∃ n : ℕ, bound ≤ path.partialCharge n

/-- Every block-boundary tail of an unbounded-charge path remains
unbounded-charge. -/
theorem HasUnboundedCharge.drop {path : R.InfinitePathFrom start}
    (hpath : path.HasUnboundedCharge) (first : ℕ) :
    (path.drop first).HasUnboundedCharge := by
  intro bound
  let positiveBound := max bound 1
  obtain ⟨later, hlater⟩ :=
    hpath (path.partialCharge first + positiveBound)
  have hpositive : 0 < positiveBound :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hfirstLater : first < later := by
    by_contra hnot
    have hlaterFirst : later ≤ first := Nat.le_of_not_gt hnot
    have hmono := path.partialCharge_mono hlaterFirst
    linarith
  let fuel := later - first
  have hindex : first + fuel = later :=
    Nat.add_sub_of_le hfirstLater.le
  refine ⟨fuel, ?_⟩
  rw [path.partialCharge_drop first fuel]
  have hlater' : path.partialCharge first + positiveBound ≤
      path.partialCharge (first + fuel) := by
    simpa only [hindex] using hlater
  rw [path.partialCharge_add first fuel] at hlater'
  exact (le_max_left bound 1).trans (by linarith)

/-- Unit charge in every block forces unbounded partial charge. -/
theorem hasUnboundedCharge_of_one_le_segmentCharge
    (path : R.InfinitePathFrom start)
    (hunit : ∀ n, 1 ≤ (path.segment n).chargeSum) :
    path.HasUnboundedCharge := by
  have hnat : ∀ n : ℕ, (n : ℝ) ≤ path.partialCharge n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [partialCharge_succ]
        push_cast
        linarith [hunit n]
  intro bound
  obtain ⟨n, hn⟩ := exists_nat_gt bound
  exact ⟨n, (le_of_lt hn).trans (hnat n)⟩

end InfinitePathFrom

/-! ## Unbounded finite charge and divergence -/

/-- Finite admissible paths starting at `start` have arbitrarily large
charge. -/
def HasUnboundedFiniteCharge (start : State) : Prop :=
  ∀ bound : ℝ, ∃ target : State, ∃ path : R.Path start target,
    bound ≤ path.chargeSum

/-- Existence of one infinite path from `start` with unbounded partial
charge. -/
def CanDiverge (start : State) : Prop :=
  ∃ path : R.InfinitePathFrom start, path.HasUnboundedCharge

/-- The explicit finite-path quantifier is exactly unboundedness of the
existing `chargesFrom` set. -/
theorem hasUnboundedFiniteCharge_iff_not_bddAbove_chargesFrom
    (start : State) :
    R.HasUnboundedFiniteCharge start ↔ ¬ BddAbove (R.chargesFrom start) := by
  classical
  constructor
  · intro hunbounded hbounded
    obtain ⟨bound, hbound⟩ := hbounded
    obtain ⟨target, path, hlarge⟩ := hunbounded (bound + 1)
    have hupper := hbound (R.mem_chargesFrom path)
    linarith
  · intro hnotBounded bound
    by_contra hnot
    push Not at hnot
    apply hnotBounded
    refine ⟨bound, ?_⟩
    rintro charge ⟨target, path, rfl⟩
    exact (hnot target path).le

/-- Every divergent infinite path supplies arbitrarily charged finite
prefixes. -/
theorem CanDiverge.hasUnboundedFiniteCharge {start : State}
    (h : R.CanDiverge start) : R.HasUnboundedFiniteCharge start := by
  obtain ⟨path, hpath⟩ := h
  intro bound
  obtain ⟨n, hn⟩ := hpath bound
  exact ⟨path.state n, path.prefixPath n, by simpa using hn⟩

/-- Every block-boundary tail of a divergent path still has unbounded finite
charge. -/
theorem InfinitePathFrom.hasUnboundedFiniteCharge_state
    {start : State} (path : R.InfinitePathFrom start)
    (hpath : path.HasUnboundedCharge) (first : ℕ) :
    R.HasUnboundedFiniteCharge (path.state first) := by
  intro bound
  let positiveBound := max bound 1
  obtain ⟨later, hlater⟩ :=
    hpath (path.partialCharge first + positiveBound)
  have hpositive : 0 < positiveBound :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hfirstLater : first < later := by
    by_contra hnot
    have hlaterFirst : later ≤ first := Nat.le_of_not_gt hnot
    have hmono := path.partialCharge_mono hlaterFirst
    linarith
  let fuel := later - first
  have hindex : first + fuel = later := by
    exact Nat.add_sub_of_le hfirstLater.le
  refine ⟨path.state (first + fuel), path.betweenPath first fuel, ?_⟩
  have hlater' : path.partialCharge first + positiveBound ≤
      path.partialCharge (first + fuel) := by
    simpa only [hindex] using hlater
  rw [path.partialCharge_add first fuel] at hlater'
  have hboundPositive : bound ≤ positiveBound := le_max_left _ _
  linarith

/-! ## Viable charged blocks and renewal -/

/-- A unit-charge finite block which ends where finite charge remains
unbounded. -/
structure ViableUnitBlock (start : State) where
  target : State
  path : R.Path start target
  unit_le : 1 ≤ path.chargeSum
  target_unbounded : R.HasUnboundedFiniteCharge target

namespace ViableUnitBlock

variable {R} {start : State}

private theorem chargeSum_eq_zero_of_length_eq_zero {source target : State}
    (path : R.Path source target) (hzero : path.length = 0) :
    path.chargeSum = 0 := by
  cases path with
  | nil => rfl
  | cons edge rest => simp at hzero

/-- A viable unit block is necessarily nonempty. -/
theorem path_length_pos (block : R.ViableUnitBlock start) :
    0 < block.path.length := by
  by_contra hnot
  have hzero : block.path.length = 0 := Nat.eq_zero_of_not_pos hnot
  have hcharge : block.path.chargeSum = 0 :=
    chargeSum_eq_zero_of_length_eq_zero block.path hzero
  linarith [block.unit_le]

end ViableUnitBlock

/-- Some viable unit block exists from `start`. -/
def HasViableUnitBlock (start : State) : Prop :=
  Nonempty (R.ViableUnitBlock start)

/-- Witness that the set of viable-block lengths is nonempty. -/
private theorem exists_viableBlock_length {start : State}
    (h : R.HasViableUnitBlock start) :
    ∃ length : ℕ, ∃ block : R.ViableUnitBlock start,
      block.path.length = length := by
  let block := Classical.choice h
  exact ⟨block.path.length, block, rfl⟩

/-- Minimal length among viable unit blocks from `start`. -/
noncomputable def minimalViableBlockLength {start : State}
    (h : R.HasViableUnitBlock start) : ℕ :=
  by
    classical
    exact Nat.find (exists_viableBlock_length (R := R) h)

/-- A viable unit block selected with minimal path length. -/
noncomputable def minimalViableBlock {start : State}
    (h : R.HasViableUnitBlock start) : R.ViableUnitBlock start :=
  by
    classical
    exact Classical.choose
      (Nat.find_spec (exists_viableBlock_length (R := R) h))

@[simp] theorem minimalViableBlock_length {start : State}
    (h : R.HasViableUnitBlock start) :
    (R.minimalViableBlock h).path.length = R.minimalViableBlockLength h :=
  by
    classical
    exact Classical.choose_spec
      (Nat.find_spec (exists_viableBlock_length (R := R) h))

/-- The selected block has no longer path than any other viable unit block. -/
theorem minimalViableBlock_length_le {start : State}
    (h : R.HasViableUnitBlock start) (block : R.ViableUnitBlock start) :
    (R.minimalViableBlock h).path.length ≤ block.path.length := by
  classical
  rw [R.minimalViableBlock_length h]
  exact Nat.find_min'
    (exists_viableBlock_length (R := R) h) ⟨block, rfl⟩

/-! ## Canonical unit-block selection from an already divergent path -/

/-- A unit-charge finite block ending at a state which itself still admits a
divergent infinite path. -/
structure DivergentUnitBlock (start : State) where
  target : State
  path : R.Path start target
  unit_le : 1 ≤ path.chargeSum
  target_canDiverge : R.CanDiverge target

namespace DivergentUnitBlock

variable {R} {start : State}

private theorem chargeSum_eq_zero_of_length_eq_zero {source target : State}
    (path : R.Path source target) (hzero : path.length = 0) :
    path.chargeSum = 0 := by
  cases path with
  | nil => rfl
  | cons edge rest => simp at hzero

/-- A divergent unit block is nonempty. -/
theorem path_length_pos (block : R.DivergentUnitBlock start) :
    0 < block.path.length := by
  by_contra hnot
  have hzero : block.path.length = 0 := Nat.eq_zero_of_not_pos hnot
  have hcharge : block.path.chargeSum = 0 :=
    chargeSum_eq_zero_of_length_eq_zero block.path hzero
  linarith [block.unit_le]

end DivergentUnitBlock

/-- Some divergence-preserving unit block exists from `start`. -/
def HasDivergentUnitBlock (start : State) : Prop :=
  Nonempty (R.DivergentUnitBlock start)

/-- Every actually divergent path has a unit-charge prefix after which its tail
is still actually divergent. -/
theorem CanDiverge.hasDivergentUnitBlock {start : State}
    (h : R.CanDiverge start) : R.HasDivergentUnitBlock start := by
  obtain ⟨path, hpath⟩ := h
  obtain ⟨blocks, hunit⟩ := hpath 1
  exact ⟨{
    target := path.state blocks
    path := path.prefixPath blocks
    unit_le := by simpa using hunit
    target_canDiverge := ⟨path.drop blocks, hpath.drop blocks⟩ }⟩

private theorem exists_divergentUnitBlock_length {start : State}
    (h : R.HasDivergentUnitBlock start) :
    ∃ length : ℕ, ∃ block : R.DivergentUnitBlock start,
      block.path.length = length := by
  let block := Classical.choice h
  exact ⟨block.path.length, block, rfl⟩

/-- Minimal length among divergence-preserving unit blocks. -/
noncomputable def minimalDivergentUnitBlockLength {start : State}
    (h : R.HasDivergentUnitBlock start) : ℕ := by
  classical
  exact Nat.find (exists_divergentUnitBlock_length (R := R) h)

/-- The canonical minimal-length divergence-preserving unit block. -/
noncomputable def minimalDivergentUnitBlock {start : State}
    (h : R.HasDivergentUnitBlock start) : R.DivergentUnitBlock start := by
  classical
  exact Classical.choose
    (Nat.find_spec (exists_divergentUnitBlock_length (R := R) h))

@[simp] theorem minimalDivergentUnitBlock_length {start : State}
    (h : R.HasDivergentUnitBlock start) :
    (R.minimalDivergentUnitBlock h).path.length =
      R.minimalDivergentUnitBlockLength h := by
  classical
  exact Classical.choose_spec
    (Nat.find_spec (exists_divergentUnitBlock_length (R := R) h))

/-- No divergence-preserving unit block is shorter than the selected one. -/
theorem minimalDivergentUnitBlock_length_le {start : State}
    (h : R.HasDivergentUnitBlock start)
    (block : R.DivergentUnitBlock start) :
    (R.minimalDivergentUnitBlock h).path.length ≤ block.path.length := by
  classical
  rw [R.minimalDivergentUnitBlock_length h]
  exact Nat.find_min'
    (exists_divergentUnitBlock_length (R := R) h) ⟨block, rfl⟩

namespace DivergentSelection

variable {R}

/-- The canonical minimal block at an actually divergent state. -/
noncomputable def selectedBlock
    (state : { state : State // R.CanDiverge state }) :
    R.DivergentUnitBlock state.1 :=
  R.minimalDivergentUnitBlock state.2.hasDivergentUnitBlock

/-- Advance to the divergence-preserving endpoint of the selected block. -/
noncomputable def nextState
    (state : { state : State // R.CanDiverge state }) :
    { state : State // R.CanDiverge state } :=
  ⟨(selectedBlock state).target, (selectedBlock state).target_canDiverge⟩

/-- Iterate the minimal divergence-preserving selector. -/
noncomputable def orbit
    (initial : { state : State // R.CanDiverge state }) :
    ℕ → { state : State // R.CanDiverge state }
  | 0 => initial
  | n + 1 => nextState (orbit initial n)

/-- Reblock an actually divergent path canonically so that every block carries
at least one unit of charge and every boundary remains actually divergent. -/
noncomputable def normalizedPath {start : State}
    (hstart : R.CanDiverge start) : R.InfinitePathFrom start where
  state n := (orbit ⟨start, hstart⟩ n).1
  state_zero := rfl
  segment n := (selectedBlock (orbit ⟨start, hstart⟩ n)).path
  segment_length_pos n :=
    (selectedBlock (orbit ⟨start, hstart⟩ n)).path_length_pos

theorem normalizedPath_segment_unit {start : State}
    (hstart : R.CanDiverge start) (n : ℕ) :
    1 ≤ ((normalizedPath hstart).segment n).chargeSum :=
  (selectedBlock (orbit ⟨start, hstart⟩ n)).unit_le

theorem normalizedPath_state_canDiverge {start : State}
    (hstart : R.CanDiverge start) (n : ℕ) :
    R.CanDiverge ((normalizedPath hstart).state n) :=
  (orbit ⟨start, hstart⟩ n).2

/-- The selected normalized path is divergent, has unit charge in every block,
and retains actual divergence at every selected boundary. -/
theorem exists_normalizedPath {start : State}
    (hstart : R.CanDiverge start) :
    ∃ path : R.InfinitePathFrom start,
      path.HasUnboundedCharge ∧
      (∀ n, 1 ≤ (path.segment n).chargeSum) ∧
      (∀ n, R.CanDiverge (path.state n)) := by
  refine ⟨normalizedPath hstart, ?_, normalizedPath_segment_unit hstart,
    normalizedPath_state_canDiverge hstart⟩
  exact (normalizedPath hstart).hasUnboundedCharge_of_one_le_segmentCharge
    (normalizedPath_segment_unit hstart)

end DivergentSelection

/-- Charge renewal: every state with unbounded finite charge has a unit-charge
block ending at another such state. -/
def ChargeRenewal : Prop :=
  ∀ start, R.HasUnboundedFiniteCharge start → R.HasViableUnitBlock start

namespace ChargeRenewal

variable {R}

/-- States at which finite charge is unbounded. -/
abbrev UnboundedState := {state : State // R.HasUnboundedFiniteCharge state}

/-- The canonical minimal viable block selected by renewal. -/
noncomputable def selectedBlock (h : R.ChargeRenewal)
    (state : { state : State // R.HasUnboundedFiniteCharge state }) :
    R.ViableUnitBlock state.1 :=
  R.minimalViableBlock (h state.1 state.2)

/-- The next viable state reached by the selected block. -/
noncomputable def nextState (h : R.ChargeRenewal)
    (state : { state : State // R.HasUnboundedFiniteCharge state }) :
    { state : State // R.HasUnboundedFiniteCharge state } :=
  ⟨(h.selectedBlock state).target,
    (h.selectedBlock state).target_unbounded⟩

/-- Iteration of the minimal viable-block selector. -/
noncomputable def orbit (h : R.ChargeRenewal)
    (initial : { state : State // R.HasUnboundedFiniteCharge state }) :
    ℕ → { state : State // R.HasUnboundedFiniteCharge state }
  | 0 => initial
  | n + 1 => h.nextState (h.orbit initial n)

/-- The selected viable blocks form one infinite path.  Its finite prefixes
are literal concatenations through `InfinitePathFrom.prefixPath`. -/
noncomputable def divergentPath (h : R.ChargeRenewal)
    (start : State) (hstart : R.HasUnboundedFiniteCharge start) :
    R.InfinitePathFrom start where
  state n := (h.orbit ⟨start, hstart⟩ n).1
  state_zero := rfl
  segment n := (h.selectedBlock (h.orbit ⟨start, hstart⟩ n)).path
  segment_length_pos n :=
    (h.selectedBlock (h.orbit ⟨start, hstart⟩ n)).path_length_pos

theorem divergentPath_segment_unit (h : R.ChargeRenewal)
    (start : State) (hstart : R.HasUnboundedFiniteCharge start) (n : ℕ) :
    1 ≤ ((h.divergentPath start hstart).segment n).chargeSum := by
  exact (h.selectedBlock (h.orbit ⟨start, hstart⟩ n)).unit_le

/-- Renewal constructs a divergent path from every state with unbounded
finite charge. -/
theorem canDiverge (h : R.ChargeRenewal) (start : State)
    (hstart : R.HasUnboundedFiniteCharge start) : R.CanDiverge start := by
  let path := h.divergentPath start hstart
  refine ⟨path, path.hasUnboundedCharge_of_one_le_segmentCharge ?_⟩
  intro n
  exact h.divergentPath_segment_unit start hstart n

end ChargeRenewal

/-- **Renewal equivalence.**  Over arbitrary nonnegatively charged
relations, charge renewal is exactly the condition under which unbounded
finite charge from a state can always be consolidated into one divergent
infinite path. -/
theorem chargeRenewal_iff_unboundedFiniteCharge_implies_canDiverge :
    R.ChargeRenewal ↔
      ∀ start, R.HasUnboundedFiniteCharge start → R.CanDiverge start := by
  constructor
  · intro h start hstart
    exact h.canDiverge start hstart
  · intro himplies start hstart
    obtain ⟨path, hpath⟩ := himplies start hstart
    obtain ⟨n, hunit⟩ := hpath 1
    let block : R.ViableUnitBlock start := {
      target := path.state n
      path := path.prefixPath n
      unit_le := by simpa using hunit
      target_unbounded :=
        InfinitePathFrom.hasUnboundedFiniteCharge_state (R := R) path hpath n }
    exact ⟨block⟩

end ChargedRelation
end ChargedPathBudget
end Math
