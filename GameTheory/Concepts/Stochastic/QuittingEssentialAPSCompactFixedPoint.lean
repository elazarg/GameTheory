/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSCircuitProgressTotal
import Mathlib.Analysis.Convex.Topology

/-!
# Compact greatest essential-APS families on unique-successor graphs

The essential-APS greatest family is constructed as a Tarski union of
subinvariant families, so compactness does not follow formally from its
definition.  On a unique-successor graph, however, the operator has a closed
one-fiber form.  This file proves a closure bootstrap:

1. a convex join of one root with a compact payoff set is compact;
2. hence a full APS prefix over a compact convex continuation fiber is closed;
3. the coordinatewise closure of the greatest family is again subinvariant;
4. maximality then forces the greatest family to equal its closure.

Therefore compact convex carriers produce compact greatest-family fibers when
every owner has a displayed unique Flesch successor.  This is the topological
input needed to upgrade bounded-window pointwise progress to a uniform positive
mass bound by an extreme-value argument.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type}

/-- The convex join of one payoff with a compact payoff set is compact. -/
theorem isCompact_convexJoin_singleton_payoff
    (root : Payoff ι) {E : Set (Payoff ι)}
    (hEcompact : IsCompact E) :
    IsCompact (convexJoin ℝ ({root} : Set (Payoff ι)) E) := by
  let mix : ℝ × Payoff ι → Payoff ι :=
    fun pair ↦ pair.1 • root + (1 - pair.1) • pair.2
  have hmixContinuous : Continuous mix := by
    dsimp only [mix]
    fun_prop
  have himage :
      convexJoin ℝ ({root} : Set (Payoff ι)) E =
        mix '' (Set.Icc (0 : ℝ) 1 ×ˢ E) := by
    ext current
    constructor
    · intro hcurrent
      rcases mem_convexJoin.mp hcurrent with
        ⟨chosenRoot, hchosenRoot, next, hnext,
          p, q, hp, hq, hpq, hcombo⟩
      have hchosenRootEq : chosenRoot = root := by
        simpa only [Set.mem_singleton_iff] using hchosenRoot
      subst chosenRoot
      have hp_le_one : p ≤ 1 := by linarith
      have hqEq : q = 1 - p := by linarith
      refine ⟨(p, next), ⟨⟨hp, hp_le_one⟩, hnext⟩, ?_⟩
      dsimp only [mix]
      rw [← hqEq]
      exact hcombo
    · rintro ⟨⟨p, next⟩, ⟨hp, hnext⟩, rfl⟩
      apply mem_convexJoin.mpr
      refine ⟨root, Set.mem_singleton root, next, hnext,
        p, 1 - p, hp.1, sub_nonneg.mpr hp.2, ?_, ?_⟩
      · ring
      · rfl
  rw [himage]
  exact (isCompact_Icc.prod hEcompact).image_of_continuousOn
    hmixContinuous.continuousOn

/-- Adding one root to a compact convex payoff set and taking the convex hull
preserves compactness.  The empty continuation case is the singleton hull. -/
theorem isCompact_convexHull_insert_payoff_of_compact_convex
    (root : Payoff ι) {E : Set (Payoff ι)}
    (hEcompact : IsCompact E) (hEconvex : Convex ℝ E) :
    IsCompact (convexHull ℝ (Set.insert root E)) := by
  by_cases hEnonempty : E.Nonempty
  · have hjoinEq :
        convexHull ℝ (Set.insert root E) =
          convexJoin ℝ ({root} : Set (Payoff ι)) E := by
      apply Set.Subset.antisymm
      · apply convexHull_min
        · intro value hvalue
          rcases Set.mem_insert_iff.mp hvalue with hroot | hEvalue
          · subst value
            exact subset_convexJoin_left hEnonempty
              (Set.mem_singleton root)
          · exact subset_convexJoin_right
              (Set.singleton_nonempty root) hEvalue
        · exact (convex_singleton root).convexJoin hEconvex
      · apply convexJoin_subset
        · intro value hvalue
          have hroot : value = root := by
            simpa only [Set.mem_singleton_iff] using hvalue
          subst value
          exact subset_convexHull ℝ _ (Set.mem_insert root E)
        · intro value hEvalue
          exact subset_convexHull ℝ _
            (Set.mem_insert_of_mem root hEvalue)
        · exact convex_convexHull ℝ _
    rw [hjoinEq]
    exact isCompact_convexJoin_singleton_payoff root hEcompact
  · have hsingleton :
        Set.insert root E = ({root} : Set (Payoff ι)) := by
      apply Set.Subset.antisymm
      · intro value hvalue
        rcases Set.mem_insert_iff.mp hvalue with hroot | hEvalue
        · subst value
          exact Set.mem_singleton root
        · exact False.elim (hEnonempty ⟨value, hEvalue⟩)
      · intro value hvalue
        have hroot : value = root := by
          simpa only [Set.mem_singleton_iff] using hvalue
        subst value
        exact Set.mem_insert _ _
    rw [hsingleton, convexHull_singleton]
    exact isCompact_singleton

/-- The coordinatewise lower-bound region in the APS viability condition is
closed in the product topology on payoff vectors. -/
theorem isClosed_quittingEssentialAPSViableSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsClosed {value : Payoff ι |
      QuittingEssentialAPSViable reward value} := by
  have hsetEq :
      {value : Payoff ι |
          QuittingEssentialAPSViable reward value} =
        ⋂ who, {value : Payoff ι |
          value who ∈ Set.Ici (quittingSoloBaseline reward who)} := by
    ext value
    simp [QuittingEssentialAPSViable]
  rw [hsetEq]
  apply isClosed_iInter
  intro who
  exact isClosed_Ici.preimage (continuous_apply who)

/-- The active-coordinate hyperplane of an owner is closed. -/
theorem isClosed_quittingEssentialAPSActiveSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) :
    IsClosed {value : Payoff ι |
      value owner = quittingSoloReward reward owner owner} := by
  have hsetEq :
      {value : Payoff ι |
          value owner = quittingSoloReward reward owner owner} =
        (fun value : Payoff ι ↦ value owner) ⁻¹'
          ({quittingSoloReward reward owner owner} : Set ℝ) := by
    ext value
    simp only [Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
  rw [hsetEq]
  exact isClosed_singleton.preimage (continuous_apply owner)

/-- A full APS prefix over a compact convex continuation fiber is closed. -/
theorem isClosed_quittingEssentialAPSPrefix_of_compact_convex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {E : Set (Payoff ι)}
    (hEcompact : IsCompact E) (hEconvex : Convex ℝ E) :
    IsClosed (quittingEssentialAPSPrefix reward owner E) := by
  have hviable := isClosed_quittingEssentialAPSViableSet reward
  have hhull : IsClosed
      (convexHull ℝ
        (Set.insert (quittingSoloReward reward owner) E)) :=
    (isCompact_convexHull_insert_payoff_of_compact_convex
      (quittingSoloReward reward owner) hEcompact hEconvex).isClosed
  have hactive := isClosed_quittingEssentialAPSActiveSet reward owner
  change IsClosed {current : Payoff ι |
    QuittingEssentialAPSViable reward current ∧
      current ∈ convexHull ℝ
        (Set.insert (quittingSoloReward reward owner) E) ∧
      current owner = quittingSoloReward reward owner owner}
  have hsetEq :
      {current : Payoff ι |
        QuittingEssentialAPSViable reward current ∧
          current ∈ convexHull ℝ
            (Set.insert (quittingSoloReward reward owner) E) ∧
          current owner = quittingSoloReward reward owner owner} =
      {current : Payoff ι |
        QuittingEssentialAPSViable reward current} ∩
        (convexHull ℝ
          (Set.insert (quittingSoloReward reward owner) E) ∩
          {current : Payoff ι |
            current owner = quittingSoloReward reward owner owner}) := by
    ext current
    rfl
  rw [hsetEq]
  exact hviable.inter (hhull.inter hactive)

/-- Under a displayed unique successor, a restricted APS image is closed when
the carrier fiber is closed and the successor fiber is compact and convex. -/
theorem isClosed_quittingEssentialAPSRestrictedOperator_of_unique
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier family : ι → Set (Payoff ι))
    {owner successor : ι}
    (hedge : QuittingFleschSuccessor reward owner successor)
    (hunique : ∀ candidate,
      QuittingFleschSuccessor reward owner candidate →
        candidate = successor)
    (hcarrierClosed : IsClosed (carrier owner))
    (hfamilyCompact : IsCompact (family successor))
    (hfamilyConvex : Convex ℝ (family successor)) :
    IsClosed
      (quittingEssentialAPSRestrictedOperator reward carrier family owner) := by
  unfold quittingEssentialAPSRestrictedOperator
  apply hcarrierClosed.inter
  change IsClosed (quittingEssentialAPSOwnerStep reward family owner)
  rw [quittingEssentialAPSOwnerStep_eq_prefix]
  rw [quittingEssentialAPSSuccessorSet_eq_of_unique
    reward family hedge hunique]
  exact isClosed_quittingEssentialAPSPrefix_of_compact_convex
    reward owner hfamilyCompact hfamilyConvex

/-- **Closed greatest APS fibers on a unique-successor graph.**  If every
carrier fiber is compact and convex and every owner has a displayed unique
Flesch successor, then every greatest-family fiber is closed. -/
theorem isClosed_quittingEssentialAPSGreatestFamily_of_compact_convex_unique
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrierCompact : ∀ player, IsCompact (carrier player))
    (hcarrierConvex : ∀ player, Convex ℝ (carrier player))
    (successor : ι → ι)
    (hedge : ∀ owner,
      QuittingFleschSuccessor reward owner (successor owner))
    (hunique : ∀ owner candidate,
      QuittingFleschSuccessor reward owner candidate →
        candidate = successor owner)
    (owner : ι) :
    IsClosed (quittingEssentialAPSGreatestFamily reward carrier owner) := by
  let closedFamily : ι → Set (Payoff ι) :=
    fun player ↦ closure
      (quittingEssentialAPSGreatestFamily reward carrier player)
  have hgreatestSub :=
    quittingEssentialAPSGreatestFamily_subinvariant reward carrier
  have hgreatestCarrier : ∀ player,
      quittingEssentialAPSGreatestFamily reward carrier player ⊆
        carrier player := by
    intro player value hvalue
    exact (hgreatestSub player hvalue).1
  have hgreatest_le_closed :
      quittingEssentialAPSGreatestFamily reward carrier ≤ closedFamily := by
    intro player value hvalue
    exact subset_closure hvalue
  have hclosedCompact : ∀ player,
      IsCompact (closedFamily player) := by
    intro player
    dsimp only [closedFamily]
    exact (hcarrierCompact player).of_isClosed_subset isClosed_closure
      (closure_minimal (hgreatestCarrier player)
        (hcarrierCompact player).isClosed)
  have hclosedConvex : ∀ player,
      Convex ℝ (closedFamily player) := by
    intro player
    dsimp only [closedFamily]
    exact (convex_quittingEssentialAPSGreatestFamily
      reward carrier hcarrierConvex player).closure
  have hclosedSubinvariant :
      IsQuittingEssentialAPSSubinvariant reward carrier closedFamily := by
    intro player current hcurrent
    change current ∈ closure
      (quittingEssentialAPSGreatestFamily reward carrier player) at hcurrent
    have htargetClosed : IsClosed
        (quittingEssentialAPSRestrictedOperator reward carrier
          closedFamily player) :=
      isClosed_quittingEssentialAPSRestrictedOperator_of_unique
        reward carrier closedFamily (hedge player) (hunique player)
        (hcarrierCompact player).isClosed
        (hclosedCompact (successor player))
        (hclosedConvex (successor player))
    have hgreatestSubsetTarget :
        quittingEssentialAPSGreatestFamily reward carrier player ⊆
          quittingEssentialAPSRestrictedOperator reward carrier
            closedFamily player := by
      intro value hvalue
      exact monotone_quittingEssentialAPSRestrictedOperator
        reward carrier hgreatest_le_closed player
          (hgreatestSub player hvalue)
    exact (closure_minimal hgreatestSubsetTarget htargetClosed) hcurrent
  have hclosed_le_greatest :
      closedFamily ≤
        quittingEssentialAPSGreatestFamily reward carrier :=
    quittingEssentialAPSFamily_le_greatest reward carrier
      closedFamily hclosedSubinvariant
  have hclosureSubset :
      closure (quittingEssentialAPSGreatestFamily reward carrier owner) ⊆
        quittingEssentialAPSGreatestFamily reward carrier owner := by
    simpa only [closedFamily] using hclosed_le_greatest owner
  have hclosureEq :
      closure (quittingEssentialAPSGreatestFamily reward carrier owner) =
        quittingEssentialAPSGreatestFamily reward carrier owner :=
    Set.Subset.antisymm hclosureSubset subset_closure
  simpa only [hclosureEq] using
    (isClosed_closure : IsClosed
      (closure (quittingEssentialAPSGreatestFamily reward carrier owner)))

/-- **Compact greatest APS fibers on a unique-successor graph.**  Compactness
now follows from closedness inside the compact carrier. -/
theorem isCompact_quittingEssentialAPSGreatestFamily_of_compact_convex_unique
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrierCompact : ∀ player, IsCompact (carrier player))
    (hcarrierConvex : ∀ player, Convex ℝ (carrier player))
    (successor : ι → ι)
    (hedge : ∀ owner,
      QuittingFleschSuccessor reward owner (successor owner))
    (hunique : ∀ owner candidate,
      QuittingFleschSuccessor reward owner candidate →
        candidate = successor owner)
    (owner : ι) :
    IsCompact (quittingEssentialAPSGreatestFamily reward carrier owner) := by
  apply (hcarrierCompact owner).of_isClosed_subset
  · exact
      isClosed_quittingEssentialAPSGreatestFamily_of_compact_convex_unique
        reward carrier hcarrierCompact hcarrierConvex
        successor hedge hunique owner
  · intro value hvalue
    exact
      (quittingEssentialAPSGreatestFamily_subinvariant
        reward carrier owner hvalue).1

end GameTheory
