/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ChargedPathFiniteHorizon

noncomputable section

/-!
# Regression examples for charged-path selection

This module records four exact boundary tests:

* a serial one-step tower has unbounded finite charge at its root, while each
  infinite path chooses one finite charge and then accumulates zero;
* an arbitrarily long zero-charge delay may precede a positive recurrent loop;
* a locally greedy charged edge may enter a zero-charge trap, while a zero-charge
  first edge reaches a divergent recurrent state;
* the maximizing first branch may switch between horizons one and three.

The one-step tower is countable and no compact structure is asserted; it is not
a substitute for a compact metastability example.  Together the examples fence
the scope of `ChargeRenewal`, delayed selection, local greediness, and
finite-horizon maximization.
-/

universe u v

namespace Math
namespace ChargedPathBudget
namespace ChargedRelation
namespace OneStepTower

/-- The root is `none`; every `some n` is a leaf with a zero-charge loop. -/
abbrev State := Option ℕ

/-- A `rootEdge n` goes from the root to leaf `n`; a `leafLoop n` is
the zero-charge self-loop at that leaf. -/
inductive Edge
  | rootEdge (n : ℕ)
  | leafLoop (n : ℕ)

/-- The serial one-step-tower relation. -/
def relation : ChargedRelation State Edge where
  src
    | .rootEdge _ => none
    | .leafLoop n => some n
  tgt
    | .rootEdge n => some n
    | .leafLoop n => some n
  charge
    | .rootEdge n => n
    | .leafLoop _ => 0
  charge_nonneg
    | .rootEdge n => Nat.cast_nonneg n
    | .leafLoop _ => le_rfl

/-- Every state admits an outgoing edge. -/
theorem isSerial (state : State) : ∃ edge, relation.src edge = state := by
  cases state with
  | none => exact ⟨.rootEdge 0, rfl⟩
  | some n => exact ⟨.leafLoop n, rfl⟩

private theorem path_from_leaf {source target : State}
    (path : relation.Path source target) (n : ℕ)
    (hsource : source = some n) :
    path.chargeSum = 0 ∧ target = some n := by
  induction path with
  | nil state => exact ⟨rfl, hsource⟩
  | cons edge rest ih =>
      cases edge with
      | rootEdge m => simp [relation] at hsource
      | leafLoop m =>
          have hmn : m = n := by simpa [relation] using hsource
          subst n
          have hrest := ih rfl
          exact ⟨by simpa [relation] using hrest.1, hrest.2⟩

private theorem chargeSum_eq_zero_from_leaf (n : ℕ) {target : State}
    (path : relation.Path (some n) target) : path.chargeSum = 0 :=
  (path_from_leaf path n rfl).1

private theorem target_eq_leaf_of_root_path_length_pos
    {source target : State} (path : relation.Path source target)
    (hsource : source = none) (hpos : 0 < path.length) :
    ∃ n, target = some n := by
  induction path with
  | nil state => simp at hpos
  | cons edge rest ih =>
      cases edge with
      | rootEdge n =>
          exact ⟨n, (path_from_leaf rest n rfl).2⟩
      | leafLoop n => simp [relation] at hsource

private theorem length_castSrc {source source' target : State}
    (h : source = source') (path : relation.Path source target) :
    (path.castSrc h).length = path.length := by
  subst h
  rfl

/-- Finite path charge from the root is unbounded. -/
theorem root_hasUnboundedFiniteCharge :
    relation.HasUnboundedFiniteCharge none := by
  intro bound
  obtain ⟨n, hn⟩ := exists_nat_gt bound
  refine ⟨some n, Path.single (Edge.rootEdge n), ?_⟩
  simpa [relation] using hn.le

/-- Along every infinite path from the root, all charge after its first block is
zero.  The first block already ends at the selected leaf, and every path from a
leaf consists entirely of zero-charge self-loops. -/
theorem partialCharge_le_firstBlock
    (path : relation.InfinitePathFrom none) (blocks : ℕ) :
    path.partialCharge blocks ≤ path.partialCharge 1 := by
  let first : relation.Path none (path.state 1) :=
    (path.segment 0).castSrc path.state_zero
  have hfirstPos : 0 < first.length := by
    rw [length_castSrc]
    simpa using path.segment_length_pos 0
  obtain ⟨leaf, hstateOne⟩ :=
    target_eq_leaf_of_root_path_length_pos first rfl hfirstPos
  cases blocks with
  | zero =>
      rw [path.partialCharge_zero]
      exact (path.partialCharge_mono (Nat.zero_le 1))
  | succ fuel =>
      have htail : (path.betweenPath 1 fuel).chargeSum = 0 := by
        let tail : relation.Path (some leaf) (path.state (1 + fuel)) :=
          (path.betweenPath 1 fuel).castSrc hstateOne
        have hzero := chargeSum_eq_zero_from_leaf leaf tail
        simpa [tail] using hzero
      rw [show fuel + 1 = 1 + fuel by omega,
        path.partialCharge_add 1 fuel, htail, add_zero]

/-- Despite seriality, no infinite path from the root has unbounded charge. -/
theorem not_canDiverge : ¬ relation.CanDiverge none := by
  rintro ⟨path, hpath⟩
  obtain ⟨blocks, hlarge⟩ := hpath (path.partialCharge 1 + 1)
  have hbound := partialCharge_le_firstBlock path blocks
  linarith

/-- Unbounded finite charge does not imply existence of a divergent path for
arbitrary charged relations. -/
theorem unboundedFiniteCharge_and_not_canDiverge :
    relation.HasUnboundedFiniteCharge none ∧ ¬ relation.CanDiverge none := by
  exact ⟨root_hasUnboundedFiniteCharge, not_canDiverge⟩

/-- Consequently, the one-step tower does not satisfy charge renewal. -/
theorem not_chargeRenewal : ¬ relation.ChargeRenewal := by
  intro hrenewal
  exact unboundedFiniteCharge_and_not_canDiverge.2
    (hrenewal.canDiverge none root_hasUnboundedFiniteCharge)

end OneStepTower

/-! ## Arbitrarily long zero delay before recurrent positive charge -/

namespace DelayedPositiveLoop

/-- `descend n` moves from `n+1` to `n` at zero charge; `liveLoop` is the
unit-charge loop at zero. -/
inductive Edge
  | descend (n : ℕ)
  | liveLoop

def relation : ChargedRelation ℕ Edge where
  src
    | .descend n => n + 1
    | .liveLoop => 0
  tgt
    | .descend n => n
    | .liveLoop => 0
  charge
    | .descend _ => 0
    | .liveLoop => 1
  charge_nonneg
    | .descend _ => le_rfl
    | .liveLoop => zero_le_one

/-- The deterministic zero-charge countdown from `delay` to the live state. -/
def descentPath : ∀ delay : ℕ, relation.Path delay 0
  | 0 => Path.nil 0
  | delay + 1 => Path.cons (Edge.descend delay) (descentPath delay)

@[simp] theorem descentPath_chargeSum (delay : ℕ) :
    (descentPath delay).chargeSum = 0 := by
  induction delay with
  | zero => rfl
  | succ delay ih => simpa [descentPath, relation] using ih

@[simp] theorem descentPath_length (delay : ℕ) :
    (descentPath delay).length = delay := by
  induction delay with
  | zero => rfl
  | succ delay ih =>
      change (descentPath delay).length + 1 = delay + 1
      omega

private theorem length_append {source middle target : ℕ}
    (first : relation.Path source middle)
    (second : relation.Path middle target) :
    (first.append second).length = first.length + second.length := by
  induction first with
  | nil =>
      change second.length = 0 + second.length
      omega
  | cons edge rest ih =>
      change (rest.append second).length + 1 =
        (rest.length + 1) + second.length
      rw [ih]
      omega

/-- One selected unit block may contain an arbitrarily long initial zero-charge
delay before its final positive loop. -/
def firstUnitBlock (delay : ℕ) : relation.Path delay 0 :=
  (descentPath delay).append (Path.single Edge.liveLoop)

@[simp] theorem firstUnitBlock_chargeSum (delay : ℕ) :
    (firstUnitBlock delay).chargeSum = 1 := by
  rw [firstUnitBlock, Path.chargeSum_append, descentPath_chargeSum]
  change 0 + (relation.charge Edge.liveLoop + 0) = 1
  norm_num [relation]

@[simp] theorem firstUnitBlock_length (delay : ℕ) :
    (firstUnitBlock delay).length = delay + 1 := by
  rw [firstUnitBlock, length_append, descentPath_length]
  rfl

theorem firstUnitBlock_length_pos (delay : ℕ) :
    0 < (firstUnitBlock delay).length := by
  rw [firstUnitBlock_length]
  omega

/-- After the delayed first unit block, repeat the positive loop forever. -/
def divergentPath (delay : ℕ) : relation.InfinitePathFrom delay where
  state
    | 0 => delay
    | _ + 1 => 0
  state_zero := rfl
  segment
    | 0 => firstUnitBlock delay
    | _ + 1 => Path.single Edge.liveLoop
  segment_length_pos
    | 0 => firstUnitBlock_length_pos delay
    | _ + 1 => by
        change 0 < 1
        omega

theorem divergentPath_segment_unit (delay n : ℕ) :
    1 ≤ ((divergentPath delay).segment n).chargeSum := by
  cases n with
  | zero => simp [divergentPath]
  | succ n => simp [divergentPath, relation]

/-- Every finite delay still admits divergent accumulated charge. -/
theorem canDiverge (delay : ℕ) : relation.CanDiverge delay := by
  refine ⟨divergentPath delay, ?_⟩
  exact (divergentPath delay).hasUnboundedCharge_of_one_le_segmentCharge
    (divergentPath_segment_unit delay)

end DelayedPositiveLoop

/-! ## A locally greedy charged edge can destroy divergence -/

namespace GreedyTrap

inductive State
  | start
  | trap
  | live

inductive Edge
  | greedy
  | patient
  | trapLoop
  | liveLoop

/-- The greedy edge pays one immediately and enters a zero-charge trap.  The
patient edge pays zero and enters a unit-charge recurrent state. -/
def relation : ChargedRelation State Edge where
  src
    | .greedy | .patient => .start
    | .trapLoop => .trap
    | .liveLoop => .live
  tgt
    | .greedy | .trapLoop => .trap
    | .patient | .liveLoop => .live
  charge
    | .greedy | .liveLoop => 1
    | .patient | .trapLoop => 0
  charge_nonneg edge := by cases edge <;> simp

private theorem chargeSum_eq_zero_from_trap {source target : State}
    (path : relation.Path source target) (hsource : source = .trap) :
    path.chargeSum = 0 := by
  induction path with
  | nil => rfl
  | cons edge rest ih =>
      cases edge with
      | greedy => simp [relation] at hsource
      | patient => simp [relation] at hsource
      | trapLoop => simpa [relation] using ih rfl
      | liveLoop => simp [relation] at hsource

/-- The immediate reward from the greedy edge is strictly larger. -/
theorem greedy_charge_gt_patient_charge :
    relation.charge .patient < relation.charge .greedy := by
  norm_num [relation]

/-- Entering the trap destroys every possibility of divergent charge. -/
theorem not_canDiverge_trap : ¬ relation.CanDiverge .trap := by
  rintro ⟨path, hpath⟩
  obtain ⟨blocks, hone⟩ := hpath 1
  have hzero : (path.prefixPath blocks).chargeSum = 0 :=
    chargeSum_eq_zero_from_trap (path.prefixPath blocks) rfl
  rw [path.chargeSum_prefixPath] at hzero
  linarith

/-- The patient edge followed by the live loop forms the first selected unit
block. -/
def patientUnitBlock : relation.Path .start .live :=
  (Path.single Edge.patient).append (Path.single Edge.liveLoop)

def divergentPath : relation.InfinitePathFrom .start where
  state
    | 0 => .start
    | _ + 1 => .live
  state_zero := rfl
  segment
    | 0 => patientUnitBlock
    | _ + 1 => Path.single Edge.liveLoop
  segment_length_pos n := by
    cases n with
    | zero =>
        change 0 < 2
        omega
    | succ n =>
        change 0 < 1
        omega

theorem divergentPath_segment_unit (n : ℕ) :
    1 ≤ (divergentPath.segment n).chargeSum := by
  cases n <;> simp [divergentPath, patientUnitBlock, relation]

/-- The relation diverges from the start only by declining the greedy trap. -/
theorem canDiverge_start : relation.CanDiverge .start := by
  refine ⟨divergentPath, ?_⟩
  exact divergentPath.hasUnboundedCharge_of_one_le_segmentCharge
    divergentPath_segment_unit

theorem greedy_target_not_canDiverge :
    ¬ relation.CanDiverge (relation.tgt .greedy) := by
  simpa [relation] using not_canDiverge_trap

end GreedyTrap

/-! ## Finite-horizon maximizers can switch branches -/

namespace IncompatibleHorizonOptima

inductive State
  | start
  | trap
  | live
  deriving DecidableEq

inductive Edge
  | immediate
  | invest
  | trapLoop
  | liveLoop
  deriving DecidableEq, Fintype

/-- The immediate branch pays one and then stops earning.  The investment
branch pays zero initially and then earns `3/5` per step. -/
def relation : ChargedRelation State Edge where
  src
    | .immediate | .invest => .start
    | .trapLoop => .trap
    | .liveLoop => .live
  tgt
    | .immediate | .trapLoop => .trap
    | .invest | .liveLoop => .live
  charge
    | .immediate => 1
    | .invest | .trapLoop => 0
    | .liveLoop => 3 / 5
  charge_nonneg edge := by cases edge <;> norm_num

def immediatePathOne : relation.Path .start .trap :=
  Path.single Edge.immediate

def investPathOne : relation.Path .start .live :=
  Path.single Edge.invest

def immediatePathThree : relation.Path .start .trap :=
  Path.cons Edge.immediate
    (Path.cons Edge.trapLoop (Path.single Edge.trapLoop))

def investPathThree : relation.Path .start .live :=
  Path.cons Edge.invest
    (Path.cons Edge.liveLoop (Path.single Edge.liveLoop))

@[simp] theorem finiteHorizonCandidates_start :
    relation.finiteHorizonCandidates .start =
      {Edge.immediate, Edge.invest} := by
  ext edge
  cases edge <;> simp [finiteHorizonCandidates, relation]

@[simp] theorem finiteHorizonCandidates_trap :
    relation.finiteHorizonCandidates .trap = {Edge.trapLoop} := by
  ext edge
  cases edge <;> simp [finiteHorizonCandidates, relation]

@[simp] theorem finiteHorizonCandidates_live :
    relation.finiteHorizonCandidates .live = {Edge.liveLoop} := by
  ext edge
  cases edge <;> simp [finiteHorizonCandidates, relation]

@[simp] theorem finiteHorizonMaxCharge_trap : ∀ horizon : ℕ,
    relation.finiteHorizonMaxCharge .trap horizon = 0
  | 0 => rfl
  | horizon + 1 => by
      rw [relation.finiteHorizonMaxCharge_succ,
        finiteHorizonCandidates_trap, Finset.fold_singleton]
      change max (0 + relation.finiteHorizonMaxCharge .trap horizon) 0 = 0
      rw [finiteHorizonMaxCharge_trap horizon]
      norm_num

@[simp] theorem finiteHorizonMaxCharge_live : ∀ horizon : ℕ,
    relation.finiteHorizonMaxCharge .live horizon = horizon * (3 / 5 : ℝ)
  | 0 => by norm_num
  | horizon + 1 => by
      rw [relation.finiteHorizonMaxCharge_succ,
        finiteHorizonCandidates_live, Finset.fold_singleton]
      change max ((3 / 5 : ℝ) +
        relation.finiteHorizonMaxCharge .live horizon) 0 =
        (↑(horizon + 1) : ℝ) * (3 / 5)
      rw [finiteHorizonMaxCharge_live horizon, max_eq_left]
      · push_cast
        ring
      · positivity

theorem explicit_path_lengths :
    immediatePathOne.length = 1 ∧ investPathOne.length = 1 ∧
      immediatePathThree.length = 3 ∧ investPathThree.length = 3 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

theorem explicit_path_charges :
    immediatePathOne.chargeSum = 1 ∧ investPathOne.chargeSum = 0 ∧
      immediatePathThree.chargeSum = 1 ∧
        investPathThree.chargeSum = 6 / 5 := by
  norm_num [immediatePathOne, investPathOne, immediatePathThree,
    investPathThree, relation, Path.single, Path.chargeSum]

/-- At horizon one, the immediate branch attains the dynamic-programming
maximum and strictly beats investment. -/
theorem horizon_one_immediate_optimum :
    relation.finiteHorizonMaxCharge .start 1 = 1 ∧
      immediatePathOne.chargeSum =
        relation.finiteHorizonMaxCharge .start 1 ∧
      investPathOne.chargeSum < immediatePathOne.chargeSum := by
  have hmax : relation.finiteHorizonMaxCharge .start 1 = 1 := by
    rw [relation.finiteHorizonMaxCharge_succ,
      finiteHorizonCandidates_start]
    change max (1 + relation.finiteHorizonMaxCharge .trap 0)
      (max (0 + relation.finiteHorizonMaxCharge .live 0) 0) = 1
    norm_num
  refine ⟨hmax, ?_, ?_⟩
  · rw [explicit_path_charges.1, hmax]
  · rw [explicit_path_charges.1, explicit_path_charges.2.1]
    norm_num

/-- At horizon three, the investment branch attains the
dynamic-programming maximum and strictly beats the immediate branch. -/
theorem horizon_three_investment_optimum :
    relation.finiteHorizonMaxCharge .start 3 = 6 / 5 ∧
      investPathThree.chargeSum =
        relation.finiteHorizonMaxCharge .start 3 ∧
      immediatePathThree.chargeSum < investPathThree.chargeSum := by
  have hmax : relation.finiteHorizonMaxCharge .start 3 = 6 / 5 := by
    rw [relation.finiteHorizonMaxCharge_succ,
      finiteHorizonCandidates_start]
    change max (1 + relation.finiteHorizonMaxCharge .trap 2)
      (max (0 + relation.finiteHorizonMaxCharge .live 2) 0) = 6 / 5
    rw [finiteHorizonMaxCharge_trap, finiteHorizonMaxCharge_live]
    norm_num
  refine ⟨hmax, ?_, ?_⟩
  · rw [explicit_path_charges.2.2.2, hmax]
  · rw [explicit_path_charges.2.2.1, explicit_path_charges.2.2.2]
    norm_num

/-- The horizon-one and horizon-three maximizing branches are incompatible:
the former commits to the trap while the latter commits to the live state. -/
theorem maximizing_first_edges_switch :
    relation.tgt .immediate = .trap ∧ relation.tgt .invest = .live ∧
      relation.charge .invest < relation.charge .immediate := by
  norm_num [relation]

end IncompatibleHorizonOptima

end ChargedRelation
end ChargedPathBudget
end Math
