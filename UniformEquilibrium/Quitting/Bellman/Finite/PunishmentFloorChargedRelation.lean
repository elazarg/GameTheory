/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ChargedPathBudget
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorForward

/-!
# The punishment-floor reachable charged relation

This module attaches the actual one-stage absorption charge to every exact
Nash--Bellman predecessor edge reachable from the behavioral punishment
floor.

The orientation is important.  If `current` is an exact Nash--Bellman
predecessor of `tail`, the charged edge runs from `tail` to `current`.  Thus a
path starts at the punishment-floor anchor and grows outward by predecessor
selection, in the same direction as `quittingPunishmentFloorForwardPoint`.
The edge charge is the absorption mass of `current`'s root, which is the root
performing that Bellman update.

Reachability is deliberately existential and includes every legal exact
predecessor choice in the canonical box.  It is stronger than the one orbit
selected by classical choice in `PunishmentFloorForward`.  No compactness or
closedness of the reachable subtype is asserted.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A canonical boxed Nash--Bellman state for the given quitting game. -/
abbrev QuittingPunishmentFloorBoxState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  (canonicalQuittingNashBellmanSerialRelation reward).box

/-- The behavioral punishment-floor anchor, regarded as a boxed state. -/
def quittingPunishmentFloorBoxAnchor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingPunishmentFloorBoxState reward :=
  quittingPunishmentFloorAnchor reward

/-- One boxed exact predecessor edge.  The semantic direction is from `tail`
to `current`, although `IsQuittingNashBellmanEdge` lists the predecessor
first. -/
structure QuittingPunishmentFloorBoxEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  tail : QuittingPunishmentFloorBoxState reward
  current : QuittingPunishmentFloorBoxState reward
  exactEdge : IsQuittingNashBellmanEdge reward current.1 tail.1

namespace QuittingPunishmentFloorBoxEdge

/-- The product root performing this predecessor update. -/
def root (edge : QuittingPunishmentFloorBoxEdge reward) : ι → PMF Bool :=
  quittingRootOfSimplex edge.current.1.2

/-- Actual one-stage absorption mass of the predecessor root. -/
def absorptionCharge (edge : QuittingPunishmentFloorBoxEdge reward) : ℝ :=
  quittingRootAbsorptionMass edge.root

/-- Absorption charge is nonnegative. -/
theorem absorptionCharge_nonneg
    (edge : QuittingPunishmentFloorBoxEdge reward) :
    0 ≤ edge.absorptionCharge := by
  unfold absorptionCharge quittingRootAbsorptionMass
  exact sub_nonneg.mpr (quittingStationaryContinueMass_le_one edge.root)

end QuittingPunishmentFloorBoxEdge

/-- The full boxed charged predecessor relation, before restricting to the
class reachable from the punishment floor. -/
def quittingPunishmentFloorBoxChargedRelation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ChargedRelation (QuittingPunishmentFloorBoxState reward)
      (QuittingPunishmentFloorBoxEdge reward) where
  src edge := edge.tail
  tgt edge := edge.current
  charge edge := edge.absorptionCharge
  charge_nonneg := QuittingPunishmentFloorBoxEdge.absorptionCharge_nonneg

/-- A boxed state is reachable when some finite exact predecessor path leads
to it from the punishment-floor anchor. -/
def IsQuittingPunishmentFloorReachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (state : QuittingPunishmentFloorBoxState reward) : Prop :=
  Nonempty ((quittingPunishmentFloorBoxChargedRelation reward).Path
    (quittingPunishmentFloorBoxAnchor reward) state)

/-- The punishment-floor anchor is reachable by the empty path. -/
theorem isQuittingPunishmentFloorReachable_anchor :
    IsQuittingPunishmentFloorReachable reward
      (quittingPunishmentFloorBoxAnchor reward) :=
  ⟨ChargedRelation.Path.nil _⟩

/-- Reachability is preserved by one exact predecessor step. -/
theorem IsQuittingPunishmentFloorReachable.step
    {tail current : QuittingPunishmentFloorBoxState reward}
    (htail : IsQuittingPunishmentFloorReachable reward tail)
    (hedge : IsQuittingNashBellmanEdge reward current.1 tail.1) :
    IsQuittingPunishmentFloorReachable reward current := by
  rcases htail with ⟨path⟩
  let edge : QuittingPunishmentFloorBoxEdge reward :=
    ⟨tail, current, hedge⟩
  exact ⟨path.append (ChargedRelation.Path.single edge)⟩

/-- Boxed states reachable by finite exact predecessor prefixes. -/
abbrev QuittingPunishmentFloorReachableState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  {state : QuittingPunishmentFloorBoxState reward //
    IsQuittingPunishmentFloorReachable reward state}

/-- One exact edge between reachable states. -/
structure QuittingPunishmentFloorReachableEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  tail : QuittingPunishmentFloorReachableState reward
  current : QuittingPunishmentFloorReachableState reward
  exactEdge : IsQuittingNashBellmanEdge reward current.1.1 tail.1.1

namespace QuittingPunishmentFloorReachableEdge

/-- Forget reachability proofs from an edge. -/
def toBoxEdge (edge : QuittingPunishmentFloorReachableEdge reward) :
    QuittingPunishmentFloorBoxEdge reward where
  tail := edge.tail.1
  current := edge.current.1
  exactEdge := edge.exactEdge

end QuittingPunishmentFloorReachableEdge

/-- The charged relation restricted to the punishment-floor reachable class.
The direction remains tail-to-predecessor and the charge remains actual
absorption mass. -/
def quittingPunishmentFloorReachableChargedRelation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ChargedRelation (QuittingPunishmentFloorReachableState reward)
      (QuittingPunishmentFloorReachableEdge reward) where
  src edge := edge.tail
  tgt edge := edge.current
  charge edge := edge.toBoxEdge.absorptionCharge
  charge_nonneg edge :=
    QuittingPunishmentFloorBoxEdge.absorptionCharge_nonneg edge.toBoxEdge

namespace QuittingPunishmentFloorReachableChargedRelation

private abbrev BoxRelation :=
  quittingPunishmentFloorBoxChargedRelation reward

private abbrev ReachableRelation :=
  quittingPunishmentFloorReachableChargedRelation reward

/-- Forget reachability proofs from a finite reachable path. -/
def pathToBoxPath :
    {source target : QuittingPunishmentFloorReachableState reward} →
      ReachableRelation.Path source target →
      BoxRelation.Path source.1 target.1
  | _, _, .nil state => .nil state.1
  | _, _, .cons edge rest =>
      .cons edge.toBoxEdge (pathToBoxPath rest)

/-- Forgetting reachability proofs preserves total absorption charge. -/
@[simp] theorem chargeSum_pathToBoxPath
    {source target : QuittingPunishmentFloorReachableState reward}
    (path : ReachableRelation.Path source target) :
    (pathToBoxPath path).chargeSum = path.chargeSum := by
  induction path with
  | nil state => rfl
  | cons edge rest ih =>
      change edge.toBoxEdge.absorptionCharge +
          (pathToBoxPath rest).chargeSum =
        edge.toBoxEdge.absorptionCharge + rest.chargeSum
      rw [ih]

end QuittingPunishmentFloorReachableChargedRelation

/-! ## Anchored exact-prefix budgets -/

/-- A common bound on every finite exact predecessor prefix anchored at the
punishment floor. -/
def HasQuittingPunishmentFloorAnchoredChargeBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (chargeBound : ℝ) : Prop :=
  ∀ {target : QuittingPunishmentFloorBoxState reward}
    (path : (quittingPunishmentFloorBoxChargedRelation reward).Path
      (quittingPunishmentFloorBoxAnchor reward) target),
    path.chargeSum ≤ chargeBound

/-- Any common anchored-prefix bound is nonnegative because it bounds the
empty prefix. -/
theorem HasQuittingPunishmentFloorAnchoredChargeBound.nonneg
    {chargeBound : ℝ}
    (hbound : HasQuittingPunishmentFloorAnchoredChargeBound reward chargeBound) :
    0 ≤ chargeBound := by
  simpa using hbound (ChargedRelation.Path.nil
    (quittingPunishmentFloorBoxAnchor reward))

/-- A common anchored-prefix bound also bounds every path whose source is
merely reachable: prepend any witness path from the anchor and use
nonnegativity of its charge. -/
theorem reachablePath_chargeSum_le_of_anchoredChargeBound
    {chargeBound : ℝ}
    (hbound : HasQuittingPunishmentFloorAnchoredChargeBound reward chargeBound)
    {source target : QuittingPunishmentFloorReachableState reward}
    (path : (quittingPunishmentFloorReachableChargedRelation reward).Path
      source target) :
    path.chargeSum ≤ chargeBound := by
  rcases source.2 with ⟨anchorPath⟩
  let boxPath :=
    QuittingPunishmentFloorReachableChargedRelation.pathToBoxPath path
  have htotal := hbound (anchorPath.append boxPath)
  rw [ChargedRelation.Path.chargeSum_append,
    QuittingPunishmentFloorReachableChargedRelation.chargeSum_pathToBoxPath]
    at htotal
  linarith [anchorPath.chargeSum_nonneg]

/-- A uniform bound on all anchored finite exact prefixes induces a finite
path budget on the entire reachable charged relation. -/
theorem quittingPunishmentFloorReachable_hasFiniteBudget_of_anchoredChargeBound
    {chargeBound : ℝ}
    (hbound : HasQuittingPunishmentFloorAnchoredChargeBound reward chargeBound) :
    (quittingPunishmentFloorReachableChargedRelation reward).HasFiniteBudget := by
  refine ⟨chargeBound, ?_⟩
  rintro charge ⟨source, target, path, rfl⟩
  exact reachablePath_chargeSum_le_of_anchoredChargeBound hbound path

/-! ## The selected punishment-floor orbit lies in the reachable class -/

/-- The chosen forward-orbit point, with its canonical box certificate. -/
def quittingPunishmentFloorSelectedBoxState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (time : ℕ) :
    QuittingPunishmentFloorBoxState reward :=
  ⟨quittingPunishmentFloorForwardPoint reward time,
    quittingPunishmentFloorForwardPoint_mem reward time⟩

@[simp] theorem quittingPunishmentFloorSelectedBoxState_zero :
    quittingPunishmentFloorSelectedBoxState reward 0 =
      quittingPunishmentFloorBoxAnchor reward := by
  apply Subtype.ext
  simp [quittingPunishmentFloorSelectedBoxState,
    quittingPunishmentFloorBoxAnchor,
    quittingPunishmentFloorForwardPoint]

/-- Every point of the canonical punishment-floor forward orbit belongs to
the full reachable predecessor class. -/
theorem isQuittingPunishmentFloorReachable_selectedBoxState
    (time : ℕ) :
    IsQuittingPunishmentFloorReachable reward
      (quittingPunishmentFloorSelectedBoxState reward time) := by
  induction time with
  | zero =>
      rw [quittingPunishmentFloorSelectedBoxState_zero]
      exact isQuittingPunishmentFloorReachable_anchor
  | succ time ih =>
      apply ih.step
      exact quittingPunishmentFloorForwardPoint_related reward time

end GameTheory
