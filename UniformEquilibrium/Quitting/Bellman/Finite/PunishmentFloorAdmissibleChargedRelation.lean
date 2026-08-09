/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefixChargedBridge

/-!
# The full floor-admissible boxed charged relation

The punishment-floor finite-prefix interface is anchored by an inequality,
not by equality with the punishment vector.  Consequently its common charge
bound controls exact predecessor paths from every canonical boxed state above
the behavioral punishment floor.  Restricting the potential to the connected
component of the literal floor anchor loses this useful generality.

This module defines the full floor-admissible subtype, decodes all of its
finite paths to the established prefix certificate, and installs the
canonical bounded budget-to-go potential whenever the prefix family has a
common charge bound.  It adds no strategic producer and makes no reachability
claim between distinct admissible states.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A canonical boxed Nash--Bellman state whose payoff dominates the
coordinatewise behavioral punishment floor. -/
abbrev QuittingPunishmentFloorAdmissibleState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  {state : QuittingPunishmentFloorBoxState reward //
    ∀ who, quittingPunishmentValue reward who ≤ state.1.1 who}

/-- One exact predecessor edge between floor-admissible boxed states. -/
structure QuittingPunishmentFloorAdmissibleEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  tail : QuittingPunishmentFloorAdmissibleState reward
  current : QuittingPunishmentFloorAdmissibleState reward
  exactEdge : IsQuittingNashBellmanEdge reward current.1.1 tail.1.1

namespace QuittingPunishmentFloorAdmissibleEdge

/-- Forget the two floor certificates. -/
def toBoxEdge (edge : QuittingPunishmentFloorAdmissibleEdge reward) :
    QuittingPunishmentFloorBoxEdge reward where
  tail := edge.tail.1
  current := edge.current.1
  exactEdge := edge.exactEdge

/-- Exact predecessor transport preserves floor admissibility. -/
def ofExactEdge
    (tail : QuittingPunishmentFloorAdmissibleState reward)
    (current : QuittingPunishmentFloorBoxState reward)
    (exactEdge : IsQuittingNashBellmanEdge reward current.1 tail.1.1) :
    QuittingPunishmentFloorAdmissibleEdge reward where
  tail := tail
  current := ⟨current, fun who => by
    have hnash :=
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward tail.1.1.1 (quittingRootOfSimplex current.1.2)).1
        exactEdge.2
    have hfloor := quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge
      reward tail.1.1.1 (quittingRootOfSimplex current.1.2) who
        (tail.2 who) hnash
    rw [← congrFun exactEdge.1 who] at hfloor
    exact hfloor⟩
  exactEdge := exactEdge

end QuittingPunishmentFloorAdmissibleEdge

/-- The full exact predecessor relation on all boxed floor-admissible states,
charged by literal one-stage absorption mass. -/
def quittingPunishmentFloorAdmissibleChargedRelation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ChargedRelation (QuittingPunishmentFloorAdmissibleState reward)
      (QuittingPunishmentFloorAdmissibleEdge reward) where
  src edge := edge.tail
  tgt edge := edge.current
  charge edge := edge.toBoxEdge.absorptionCharge
  charge_nonneg edge := edge.toBoxEdge.absorptionCharge_nonneg

namespace QuittingPunishmentFloorAdmissibleChargedRelation

private abbrev AdmissibleRelation :=
  quittingPunishmentFloorAdmissibleChargedRelation reward

private abbrev BoxRelation :=
  quittingPunishmentFloorBoxChargedRelation reward

/-- Forget floor proofs from every state and edge of a finite admissible
path. -/
def pathToBoxPath :
    {source target : QuittingPunishmentFloorAdmissibleState reward} →
      AdmissibleRelation.Path source target →
      BoxRelation.Path source.1 target.1
  | _, _, .nil state => .nil state.1
  | _, _, .cons edge rest =>
      .cons edge.toBoxEdge (pathToBoxPath rest)

/-- Forgetting floor proofs preserves total absorption charge. -/
@[simp] theorem chargeSum_pathToBoxPath
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : AdmissibleRelation.Path source target) :
    (pathToBoxPath path).chargeSum = path.chargeSum := by
  induction path with
  | nil state => rfl
  | cons edge rest ih =>
      change edge.toBoxEdge.absorptionCharge +
          (pathToBoxPath rest).chargeSum =
        edge.toBoxEdge.absorptionCharge + rest.chargeSum
      rw [ih]

/-- Every finite path from an arbitrary floor-admissible source is one of the
established exact punishment-floor prefix certificates. -/
def pathToFinitePrefix
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : AdmissibleRelation.Path source target) :
    QuittingPunishmentFloorFinitePrefix reward := by
  let boxPath := pathToBoxPath path
  exact {
    roots := QuittingPunishmentFloorBoxPath.root boxPath
    value := QuittingPunishmentFloorBoxPath.value boxPath
    horizon := boxPath.length
    value_mem := fun time htime =>
      QuittingPunishmentFloorBoxPath.value_mem boxPath time htime
    anchor_floor := fun who => by
      rw [QuittingPunishmentFloorBoxPath.value_zero]
      exact source.2 who
    policy := fun time htime =>
      QuittingPunishmentFloorBoxPath.policy boxPath time htime
    exactNash := fun time htime =>
      QuittingPunishmentFloorBoxPath.exactNash boxPath time htime }

/-- Decoding an admissible path preserves its charge exactly. -/
@[simp] theorem pathToFinitePrefix_charge
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : AdmissibleRelation.Path source target) :
    (pathToFinitePrefix path).charge = path.chargeSum := by
  change (∑ time ∈ Finset.range (pathToBoxPath path).length,
      quittingRootAbsorptionMass
        (QuittingPunishmentFloorBoxPath.root (pathToBoxPath path) time)) =
    path.chargeSum
  rw [QuittingPunishmentFloorBoxPath.sum_absorptionMass_root_eq_chargeSum,
    chargeSum_pathToBoxPath]

end QuittingPunishmentFloorAdmissibleChargedRelation

/-- A common charge bound for all punishment-floor prefix certificates gives
a finite budget on the full floor-admissible relation. -/
theorem quittingPunishmentFloorAdmissible_hasFiniteBudget_of_finitePrefixChargeBound
    {chargeBound : ℝ}
    (hbound : ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
      cert.charge ≤ chargeBound) :
    (quittingPunishmentFloorAdmissibleChargedRelation reward).HasFiniteBudget := by
  refine ⟨chargeBound, ?_⟩
  rintro charge ⟨source, target, path, rfl⟩
  rw [← QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_charge
    path]
  exact hbound
    (QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix path)

/-- The canonical budget-to-go on all boxed floor-admissible states. -/
def quittingPunishmentFloorAdmissiblePotential
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (state : QuittingPunishmentFloorAdmissibleState reward) : ℝ :=
  (quittingPunishmentFloorAdmissibleChargedRelation reward).value state

/-- A common finite-prefix charge bound makes the global admissible
budget-to-go a bounded potential. -/
theorem quittingPunishmentFloorAdmissiblePotential_isBoundedPotential
    {chargeBound : ℝ}
    (hbound : ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
      cert.charge ≤ chargeBound) :
    (quittingPunishmentFloorAdmissibleChargedRelation reward).IsBoundedPotential
      (quittingPunishmentFloorAdmissiblePotential reward) := by
  exact
    (quittingPunishmentFloorAdmissibleChargedRelation reward).value_isBoundedPotential
      (quittingPunishmentFloorAdmissible_hasFiniteBudget_of_finitePrefixChargeBound
        hbound)

/-- Every global admissible predecessor edge spends its literal absorption
mass as a decrement of the canonical potential. -/
theorem quittingPunishmentFloorAdmissiblePotential_predecessor_decrement
    {chargeBound : ℝ}
    (hbound : ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
      cert.charge ≤ chargeBound)
    (edge : QuittingPunishmentFloorAdmissibleEdge reward) :
    quittingPunishmentFloorAdmissiblePotential reward edge.current +
        edge.toBoxEdge.absorptionCharge ≤
      quittingPunishmentFloorAdmissiblePotential reward edge.tail := by
  exact
    (quittingPunishmentFloorAdmissiblePotential_isBoundedPotential hbound).isPotential
      edge

end GameTheory
