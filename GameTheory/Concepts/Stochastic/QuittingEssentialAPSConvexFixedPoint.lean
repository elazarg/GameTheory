/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSConvexProgress
import GameTheory.Concepts.Stochastic.QuittingEssentialAPSFixedPoint

/-!
# Convexity and local progress in essential-APS fixed families

The terminal disjunct in an essential-APS owner step is set-theoretically
redundant: every viable solo endpoint already belongs to the full prefix,
independently of the continuation set.  Since the full prefix is an
intersection of convex conditions around a convex hull, every owner-step image
is convex even when the raw union of successor fibers is not.

This observation propagates through the carrier-restricted fixed-point
construction.  If each carrier fiber is convex, then every fiber of the
greatest essential-APS family inside that carrier is convex.  Consequently,
at an owner with a unique exact Flesch successor, the successor union is one
convex fixed-point fiber and the convex progress extraction theorem applies.
A current value then has exactly three possibilities:

* it is the viable solo terminal endpoint;
* it is already in the successor fiber, the zero-mass endpoint case; or
* it has a proper one-continuation segment witness with mass in `(0,1)`.

Thus the remaining obstruction on unique-successor regions is localized to
zero-mass endpoint propagation, not convexification.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type}

/-- Every viable solo terminal endpoint is already a full-prefix point, for
any continuation set. -/
theorem quittingEssentialAPSTerminal_subset_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (E : Set (Payoff ι)) :
    quittingEssentialAPSTerminal reward owner ⊆
      quittingEssentialAPSPrefix reward owner E := by
  intro current hcurrent
  rcases hcurrent with ⟨rfl, hviable⟩
  refine ⟨hviable, ?_, rfl⟩
  exact subset_convexHull ℝ _
    (Set.mem_insert (quittingSoloReward reward owner) E)

/-- The explicit terminal union in an owner step is redundant. -/
theorem quittingEssentialAPSOwnerStep_eq_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) (owner : ι) :
    quittingEssentialAPSOwnerStep reward family owner =
      quittingEssentialAPSPrefix reward owner
        (quittingEssentialAPSSuccessorSet reward family owner) := by
  apply Set.Subset.antisymm
  · intro current hcurrent
    rcases hcurrent with hterminal | hprefix
    · exact quittingEssentialAPSTerminal_subset_prefix reward owner _ hterminal
    · exact hprefix
  · intro current hprefix
    exact Or.inr hprefix

/-- The full essential-APS prefix is convex for every continuation set.  No
convexity of the continuation set is needed because the definition already
takes its convex hull. -/
theorem convex_quittingEssentialAPSPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (E : Set (Payoff ι)) :
    Convex ℝ (quittingEssentialAPSPrefix reward owner E) := by
  rw [convex_iff_add_mem]
  rintro x ⟨hxviable, hxconvex, hxactive⟩
    y ⟨hyviable, hyconvex, hyactive⟩ a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro who
    have hxscaled :=
      mul_le_mul_of_nonneg_left (hxviable who) ha
    have hyscaled :=
      mul_le_mul_of_nonneg_left (hyviable who) hb
    have hbound :
        quittingSoloBaseline reward who ≤
          a * x who + b * y who := by
      calc
        quittingSoloBaseline reward who =
            a * quittingSoloBaseline reward who +
              b * quittingSoloBaseline reward who := by
                rw [← add_mul, hab, one_mul]
        _ ≤ a * x who + b * y who :=
          add_le_add hxscaled hyscaled
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hbound
  · exact (convex_iff_add_mem.mp (convex_convexHull ℝ _))
      hxconvex hyconvex ha hb hab
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hxactive, hyactive, ← add_mul, hab, one_mul]

/-- Every full owner-step image is convex, despite possible nonconvexity of the
raw union of successor fibers. -/
theorem convex_quittingEssentialAPSOwnerStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) (owner : ι) :
    Convex ℝ (quittingEssentialAPSOwnerStep reward family owner) := by
  rw [quittingEssentialAPSOwnerStep_eq_prefix]
  exact convex_quittingEssentialAPSPrefix reward owner _

/-- Coordinatewise convexity of the unrestricted essential-APS operator. -/
theorem convex_quittingEssentialAPSOperator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) (owner : ι) :
    Convex ℝ (quittingEssentialAPSOperator reward family owner) := by
  exact convex_quittingEssentialAPSOwnerStep reward family owner

/-- A carrier-restricted APS image is convex whenever the corresponding
carrier fiber is convex. -/
theorem convex_quittingEssentialAPSRestrictedOperator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier family : ι → Set (Payoff ι))
    (hcarrier : ∀ owner, Convex ℝ (carrier owner)) (owner : ι) :
    Convex ℝ
      (quittingEssentialAPSRestrictedOperator reward carrier family owner) := by
  unfold quittingEssentialAPSRestrictedOperator
  exact (hcarrier owner).inter
    (convex_quittingEssentialAPSOperator reward family owner)

/-- **Convex greatest essential-APS fibers.**  Inside a coordinatewise convex
carrier, every fiber of the greatest restricted fixed family is convex. -/
theorem convex_quittingEssentialAPSGreatestFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrier : ∀ owner, Convex ℝ (carrier owner)) (owner : ι) :
    Convex ℝ (quittingEssentialAPSGreatestFamily reward carrier owner) := by
  have hfixed := congrFun
    (quittingEssentialAPSGreatestFamily_fixed reward carrier) owner
  rw [← hfixed]
  exact convex_quittingEssentialAPSRestrictedOperator
    reward carrier (quittingEssentialAPSGreatestFamily reward carrier)
      hcarrier owner

/-- The unrestricted greatest essential-APS family has convex fibers. -/
theorem convex_quittingEssentialAPSUnrestrictedGreatestFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) :
    Convex ℝ
      (quittingEssentialAPSUnrestrictedGreatestFamily reward owner) := by
  exact convex_quittingEssentialAPSGreatestFamily reward
    (fun _ ↦ Set.univ) (fun _ ↦ convex_univ) owner

/-- On a convex continuation set, the solo-root endpoint of the earlier
trichotomy is genuinely terminal because prefix membership supplies
viability. -/
theorem quittingEssentialAPSPrefix_terminal_or_continuation_or_proper_of_convex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {E : Set (Payoff ι)} {current : Payoff ι}
    (hEconvex : Convex ℝ E) (hEnonempty : E.Nonempty)
    (hcurrent : current ∈ quittingEssentialAPSPrefix reward owner E) :
    current ∈ quittingEssentialAPSTerminal reward owner ∨
      current ∈ E ∨
        current ∈ quittingProperEssentialAPSPrefix reward owner E := by
  rcases quittingEssentialAPSPrefix_endpoint_or_proper_of_convex
      reward owner hEconvex hEnonempty hcurrent with
    hroot | hcontinuation | hproper
  · exact Or.inl ⟨hroot, hcurrent.1⟩
  · exact Or.inr (Or.inl hcontinuation)
  · exact Or.inr (Or.inr hproper)

/-- Owner-step form of the sharp convex trichotomy. -/
theorem quittingEssentialAPSOwnerStep_terminal_or_successor_or_proper_of_convex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) (owner : ι)
    (hconvex : Convex ℝ
      (quittingEssentialAPSSuccessorSet reward family owner))
    (hnonempty :
      (quittingEssentialAPSSuccessorSet reward family owner).Nonempty)
    {current : Payoff ι}
    (hcurrent : current ∈
      quittingEssentialAPSOwnerStep reward family owner) :
    current ∈ quittingEssentialAPSTerminal reward owner ∨
      current ∈ quittingEssentialAPSSuccessorSet reward family owner ∨
      current ∈ quittingProperEssentialAPSPrefix reward owner
        (quittingEssentialAPSSuccessorSet reward family owner) := by
  rw [quittingEssentialAPSOwnerStep_eq_prefix] at hcurrent
  exact quittingEssentialAPSPrefix_terminal_or_continuation_or_proper_of_convex
    reward owner hconvex hnonempty hcurrent

/-- If an owner has a displayed exact successor and every exact successor is
that player, then the successor union is exactly the displayed fiber. -/
theorem quittingEssentialAPSSuccessorSet_eq_of_unique
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) {owner successor : ι}
    (hedge : QuittingFleschSuccessor reward owner successor)
    (hunique : ∀ candidate,
      QuittingFleschSuccessor reward owner candidate →
        candidate = successor) :
    quittingEssentialAPSSuccessorSet reward family owner =
      family successor := by
  ext next
  constructor
  · rintro ⟨candidate, hcandidate, hnext⟩
    have heq := hunique candidate hcandidate
    subst candidate
    exact hnext
  · intro hnext
    exact ⟨successor, hedge, hnext⟩

/-- A unique-successor union is convex when the displayed fiber is convex. -/
theorem convex_quittingEssentialAPSSuccessorSet_of_unique
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) {owner successor : ι}
    (hedge : QuittingFleschSuccessor reward owner successor)
    (hunique : ∀ candidate,
      QuittingFleschSuccessor reward owner candidate →
        candidate = successor)
    (hconvex : Convex ℝ (family successor)) :
    Convex ℝ (quittingEssentialAPSSuccessorSet reward family owner) := by
  rw [quittingEssentialAPSSuccessorSet_eq_of_unique
    reward family hedge hunique]
  exact hconvex

/-- **Local fixed-point progress at a unique successor.**  In a convex
carrier, a greatest-family point at an owner with a unique nonempty successor
fiber is terminal, is already in that successor fiber, or has a proper
positive-mass segment into it. -/
theorem
    quittingEssentialAPSGreatestFamily_terminal_or_successor_or_proper_of_unique
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrier : ∀ player, Convex ℝ (carrier player))
    {owner successor : ι}
    (hedge : QuittingFleschSuccessor reward owner successor)
    (hunique : ∀ candidate,
      QuittingFleschSuccessor reward owner candidate →
        candidate = successor)
    (hnonempty :
      (quittingEssentialAPSGreatestFamily reward carrier successor).Nonempty)
    {current : Payoff ι}
    (hcurrent : current ∈
      quittingEssentialAPSGreatestFamily reward carrier owner) :
    current ∈ quittingEssentialAPSTerminal reward owner ∨
      current ∈ quittingEssentialAPSGreatestFamily reward carrier successor ∨
      current ∈ quittingProperEssentialAPSPrefix reward owner
        (quittingEssentialAPSGreatestFamily reward carrier successor) := by
  have hfixedOwner := congrFun
    (quittingEssentialAPSGreatestFamily_fixed reward carrier) owner
  have hrestricted : current ∈
      quittingEssentialAPSRestrictedOperator reward carrier
        (quittingEssentialAPSGreatestFamily reward carrier) owner := by
    rw [hfixedOwner]
    exact hcurrent
  have hsuccessorEq :
      quittingEssentialAPSSuccessorSet reward
          (quittingEssentialAPSGreatestFamily reward carrier) owner =
        quittingEssentialAPSGreatestFamily reward carrier successor :=
    quittingEssentialAPSSuccessorSet_eq_of_unique reward
      (quittingEssentialAPSGreatestFamily reward carrier) hedge hunique
  have hsuccessorConvex : Convex ℝ
      (quittingEssentialAPSSuccessorSet reward
        (quittingEssentialAPSGreatestFamily reward carrier) owner) := by
    rw [hsuccessorEq]
    exact convex_quittingEssentialAPSGreatestFamily
      reward carrier hcarrier successor
  have hsuccessorNonempty :
      (quittingEssentialAPSSuccessorSet reward
        (quittingEssentialAPSGreatestFamily reward carrier) owner).Nonempty := by
    rw [hsuccessorEq]
    exact hnonempty
  have hstep :=
    quittingEssentialAPSOwnerStep_terminal_or_successor_or_proper_of_convex
      reward (quittingEssentialAPSGreatestFamily reward carrier) owner
      hsuccessorConvex hsuccessorNonempty hrestricted.2
  rw [hsuccessorEq] at hstep
  exact hstep

end GameTheory
