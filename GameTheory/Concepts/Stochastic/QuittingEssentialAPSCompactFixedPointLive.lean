/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSCompactFixedPoint

/-!
# Compact greatest essential-APS families with unique live successors

Graph-theoretic uniqueness is stronger than the closure bootstrap needs.  The
one-fiber formula only requires that every competing exact successor have an
empty continuation fiber.  Empty fibers remain empty after coordinatewise
closure, so the bootstrap proving closedness and compactness of the greatest
APS family extends unchanged to unique live successors.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type}

/-- A restricted APS image is closed when the displayed successor is the only
successor with a live family fiber. -/
theorem isClosed_quittingEssentialAPSRestrictedOperator_of_unique_live
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier family : ι → Set (Payoff ι))
    {owner successor : ι}
    (hedge : QuittingFleschSuccessor reward owner successor)
    (huniqueLive : ∀ candidate,
      QuittingFleschSuccessor reward owner candidate →
        candidate ≠ successor → family candidate = ∅)
    (hcarrierClosed : IsClosed (carrier owner))
    (hfamilyCompact : IsCompact (family successor))
    (hfamilyConvex : Convex ℝ (family successor)) :
    IsClosed
      (quittingEssentialAPSRestrictedOperator reward carrier family owner) := by
  unfold quittingEssentialAPSRestrictedOperator
  apply hcarrierClosed.inter
  change IsClosed (quittingEssentialAPSOwnerStep reward family owner)
  rw [quittingEssentialAPSOwnerStep_eq_prefix]
  rw [quittingEssentialAPSSuccessorSet_eq_of_unique_live
    reward family hedge huniqueLive]
  exact isClosed_quittingEssentialAPSPrefix_of_compact_convex
    reward owner hfamilyCompact hfamilyConvex

/-- **Closed greatest APS fibers with unique live successors.**  Competing
exact successors may exist in the ambient graph, but their greatest-family
fibers must be empty. -/
theorem
    isClosed_quittingEssentialAPSGreatestFamily_of_compact_convex_unique_live
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrierCompact : ∀ player, IsCompact (carrier player))
    (hcarrierConvex : ∀ player, Convex ℝ (carrier player))
    (successor : ι → ι)
    (hedge : ∀ owner,
      QuittingFleschSuccessor reward owner (successor owner))
    (huniqueLive : ∀ owner candidate,
      QuittingFleschSuccessor reward owner candidate →
        candidate ≠ successor owner →
          quittingEssentialAPSGreatestFamily reward carrier candidate = ∅)
    (owner : ι) :
    IsClosed (quittingEssentialAPSGreatestFamily reward carrier owner) := by
  let greatest := quittingEssentialAPSGreatestFamily reward carrier
  let closedFamily : ι → Set (Payoff ι) :=
    fun player ↦ closure (greatest player)
  have hgreatestSub :=
    quittingEssentialAPSGreatestFamily_subinvariant reward carrier
  have hgreatestCarrier : ∀ player, greatest player ⊆ carrier player := by
    intro player value hvalue
    exact (hgreatestSub player hvalue).1
  have hgreatest_le_closed : greatest ≤ closedFamily := by
    intro player value hvalue
    exact subset_closure hvalue
  have hclosedCompact : ∀ player, IsCompact (closedFamily player) := by
    intro player
    dsimp only [closedFamily]
    exact (hcarrierCompact player).of_isClosed_subset isClosed_closure
      (closure_minimal (hgreatestCarrier player)
        (hcarrierCompact player).isClosed)
  have hclosedConvex : ∀ player, Convex ℝ (closedFamily player) := by
    intro player
    dsimp only [closedFamily, greatest]
    exact (convex_quittingEssentialAPSGreatestFamily
      reward carrier hcarrierConvex player).closure
  have hclosedUniqueLive : ∀ player candidate,
      QuittingFleschSuccessor reward player candidate →
        candidate ≠ successor player → closedFamily candidate = ∅ := by
    intro player candidate hcandidate hne
    dsimp only [closedFamily, greatest]
    rw [huniqueLive player candidate hcandidate hne]
    exact closure_empty
  have hclosedSubinvariant :
      IsQuittingEssentialAPSSubinvariantWithin
        reward carrier closedFamily := by
    intro player current hcurrent
    change current ∈ closure (greatest player) at hcurrent
    have htargetClosed : IsClosed
        (quittingEssentialAPSRestrictedOperator reward carrier
          closedFamily player) :=
      isClosed_quittingEssentialAPSRestrictedOperator_of_unique_live
        reward carrier closedFamily (hedge player)
          (hclosedUniqueLive player)
          (hcarrierCompact player).isClosed
          (hclosedCompact (successor player))
          (hclosedConvex (successor player))
    have hgreatestSubsetTarget :
        greatest player ⊆
          quittingEssentialAPSRestrictedOperator reward carrier
            closedFamily player := by
      intro value hvalue
      exact monotone_quittingEssentialAPSRestrictedOperator
        reward carrier hgreatest_le_closed player
          (hgreatestSub player hvalue)
    exact (closure_minimal hgreatestSubsetTarget htargetClosed) hcurrent
  have hclosed_le_greatest : closedFamily ≤ greatest :=
    quittingEssentialAPSFamily_le_greatest reward carrier
      closedFamily hclosedSubinvariant
  have hclosureSubset : closure (greatest owner) ⊆ greatest owner := by
    simpa only [closedFamily] using hclosed_le_greatest owner
  have hclosureEq : closure (greatest owner) = greatest owner :=
    Set.Subset.antisymm hclosureSubset subset_closure
  simpa only [greatest, hclosureEq] using
    (isClosed_closure : IsClosed (closure (greatest owner)))

/-- **Compact greatest APS fibers with unique live successors.** -/
theorem
    isCompact_quittingEssentialAPSGreatestFamily_of_compact_convex_unique_live
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrierCompact : ∀ player, IsCompact (carrier player))
    (hcarrierConvex : ∀ player, Convex ℝ (carrier player))
    (successor : ι → ι)
    (hedge : ∀ owner,
      QuittingFleschSuccessor reward owner (successor owner))
    (huniqueLive : ∀ owner candidate,
      QuittingFleschSuccessor reward owner candidate →
        candidate ≠ successor owner →
          quittingEssentialAPSGreatestFamily reward carrier candidate = ∅)
    (owner : ι) :
    IsCompact (quittingEssentialAPSGreatestFamily reward carrier owner) := by
  apply (hcarrierCompact owner).of_isClosed_subset
  · exact
      isClosed_quittingEssentialAPSGreatestFamily_of_compact_convex_unique_live
        reward carrier hcarrierCompact hcarrierConvex
          successor hedge huniqueLive owner
  · intro value hvalue
    exact
      (quittingEssentialAPSGreatestFamily_subinvariant
        reward carrier owner hvalue).1

end GameTheory
