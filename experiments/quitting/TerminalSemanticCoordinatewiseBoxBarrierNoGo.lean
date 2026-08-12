/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import experiments.quitting.TerminalSemanticGlobalDebtBarrierCertificate
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Coordinatewise semantic boxes cannot certify a positive debt floor

The elementary boundaries already rule out the simplest polyhedral barrier
language.  Put

`u i = max 0 (reward {i} i)`.

The Never boundary has prescribed coordinate zero and envelope coordinate
`u i`.  If `u i = 0`, it therefore supplies `u i` also in the prescribed
projection.  If `u i > 0`, the sure-solo-`i` boundary supplies prescribed
coordinate `reward {i} i = u i`.  Thus independent recombination of the
coordinate projections puts the diagonal pair `(u,u)` in the barrier.
Its total semantic debt is zero.

Consequently no Cartesian product of coordinate sets, no axis-aligned box,
and no such product intersected with the natural order constraints `x ≤ v`
can be a positive-floor instance of
`TerminalSemanticGlobalDebtBarrierCertificate.Certificate`.  This no-go uses
only the required elementary boundaries; prefix invariance cannot repair it.
-/

noncomputable section

namespace GameTheory
namespace TerminalSemanticCoordinatewiseBoxBarrierNoGo

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The positive part of each player's singleton quitting reward. -/
def singletonPositivePart
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Payoff ι :=
  fun who => max 0 (reward (quittingSingletonTerminal who) who)

/-- A barrier is coordinatewise order-rectangular if any prescribed and
envelope vectors whose individual coordinates occur somewhere in the
barrier can be recombined whenever the natural order `prescribed ≤ envelope`
holds.  Cartesian products of arbitrary coordinate sets have this property;
intersecting such a product with `prescribed ≤ envelope` still has it. -/
def IsCoordinatewiseOrderRectangular
    (barrier : Set (QuittingTerminalSemanticPair ι)) : Prop :=
  ∀ prescribed envelope : Payoff ι,
    (∀ who, ∃ pair ∈ barrier, pair.1 who = prescribed who) →
    (∀ who, ∃ pair ∈ barrier, pair.2 who = envelope who) →
    (∀ who, prescribed who ≤ envelope who) →
    (prescribed, envelope) ∈ barrier

private theorem sureSoloBoundary_prescribed_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    (quittingElementaryBoundarySemanticPair reward (.sureSolo owner)).1 owner =
      reward (quittingSingletonTerminal owner) owner := by
  change quittingRootSuccessorPayoff reward
      (quittingNeverBoundarySemanticPair reward).1
        (quittingSureSoloRoot owner) owner = _
  have hroot : quittingSureSoloRoot owner =
      QuittingSureSetOwnerRepair.quittingPureSetRoot ({owner} : Finset ι) := by
    funext who
    by_cases hwho : who = owner
    · subst who
      simp [quittingSureSoloRoot,
        QuittingSureSetOwnerRepair.quittingPureSetRoot,
        QuittingSureSetOwnerRepair.quittingSetAction]
    · simp [quittingSureSoloRoot, quittingAllContinueRoot,
        QuittingSureSetOwnerRepair.quittingPureSetRoot,
        QuittingSureSetOwnerRepair.quittingSetAction, hwho]
  rw [hroot]
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  rw [QuittingSureSetOwnerRepair.quittingRootAbsorbingContribution_pureSetRoot]
  have hnonempty : ({owner} : Finset ι).Nonempty :=
    Finset.singleton_nonempty owner
  rw [QuittingSureSetOwnerRepair.stationaryContinueMass_pureSetRoot_of_nonempty
    hnonempty]
  simp [QuittingSureSetOwnerRepair.quittingSetReward,
    quittingSingletonTerminal]

/-- Every barrier containing the elementary boundaries and closed under
coordinatewise order-compatible recombination contains the singleton
positive-part diagonal. -/
theorem singletonPositivePart_diagonal_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (barrier : Set (QuittingTerminalSemanticPair ι))
    (hboundary : ∀ cap : QuittingElementaryTailCap ι,
      quittingElementaryBoundarySemanticPair reward cap ∈ barrier)
    (hrectangular : IsCoordinatewiseOrderRectangular barrier) :
    (singletonPositivePart reward, singletonPositivePart reward) ∈ barrier := by
  apply hrectangular
  · intro who
    by_cases hsolo : 0 ≤ reward (quittingSingletonTerminal who) who
    · refine ⟨quittingElementaryBoundarySemanticPair reward (.sureSolo who),
          hboundary (.sureSolo who), ?_⟩
      rw [sureSoloBoundary_prescribed_owner]
      simp [singletonPositivePart, max_eq_right hsolo]
    · refine ⟨quittingElementaryBoundarySemanticPair reward (.never),
          hboundary .never, ?_⟩
      simp [quittingElementaryBoundarySemanticPair,
        quittingNeverBoundarySemanticPair, singletonPositivePart,
        max_eq_left (le_of_not_ge hsolo)]
  · intro who
    refine ⟨quittingElementaryBoundarySemanticPair reward (.never),
      hboundary .never, ?_⟩
    rfl
  · intro who
    exact le_rfl

omit [DecidableEq ι] in
/-- The forced diagonal has exactly zero total semantic debt. -/
theorem singletonPositivePart_diagonal_debtSum_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingTerminalSemanticDebtSum
        (singletonPositivePart reward, singletonPositivePart reward) = 0 := by
  unfold quittingTerminalSemanticDebtSum quittingTerminalSemanticDebt
  simp

/-- **Coordinatewise-box no-go.**  Elementary-boundary containment,
coordinatewise recombination, and a strictly positive debt floor are
inconsistent.  No prefix-invariance hypothesis is needed. -/
theorem not_positiveDebtFloor_of_elementaryBoundaries_of_coordinatewiseOrderRectangular
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (barrier : Set (QuittingTerminalSemanticPair ι)) (δ : ℝ)
    (hboundary : ∀ cap : QuittingElementaryTailCap ι,
      quittingElementaryBoundarySemanticPair reward cap ∈ barrier)
    (hrectangular : IsCoordinatewiseOrderRectangular barrier)
    (hfloor : ∀ pair ∈ barrier,
      δ ≤ quittingTerminalSemanticDebtSum pair)
    (hδ : 0 < δ) : False := by
  have hdiagonal := singletonPositivePart_diagonal_mem
    reward barrier hboundary hrectangular
  have hfloorDiagonal := hfloor _ hdiagonal
  rw [singletonPositivePart_diagonal_debtSum_eq_zero] at hfloorDiagonal
  linarith

/-- Certificate-facing form: no positive global-debt certificate can use an
order-rectangular barrier. -/
theorem certificate_barrier_not_coordinatewiseOrderRectangular
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {δ : ℝ}
    (hδ : 0 < δ)
    (certificate :
      TerminalSemanticGlobalDebtBarrierCertificate.Certificate reward δ) :
    ¬ IsCoordinatewiseOrderRectangular certificate.barrier := by
  intro hrectangular
  exact not_positiveDebtFloor_of_elementaryBoundaries_of_coordinatewiseOrderRectangular
    reward certificate.barrier δ certificate.elementaryBoundary_mem
      hrectangular certificate.debt_floor hδ

end TerminalSemanticCoordinatewiseBoxBarrierNoGo
end GameTheory

namespace GameTheory.TerminalSemanticCoordinatewiseBoxBarrierNoGo

#print axioms singletonPositivePart_diagonal_mem
#print axioms singletonPositivePart_diagonal_debtSum_eq_zero
#print axioms not_positiveDebtFloor_of_elementaryBoundaries_of_coordinatewiseOrderRectangular
#print axioms certificate_barrier_not_coordinatewiseOrderRectangular

end GameTheory.TerminalSemanticCoordinatewiseBoxBarrierNoGo
