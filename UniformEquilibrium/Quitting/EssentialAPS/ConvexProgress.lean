/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.Basic
import Mathlib.Analysis.Convex.Join

/-!
# Convex progress extraction for essential APS

The full essential-APS prefix convexifies the solo endpoint together with an
arbitrary continuation set.  For a nonconvex continuation set this is strictly
more permissive than choosing one continuation and one singleton-flow segment.

This file identifies the exact boundary of that discrepancy.  If the
continuation set is nonempty and convex, Mathlib's convex-join theorem turns

`convexHull ({root} ∪ E)`

into the union of the segments from `root` to points of `E`.  Consequently the
full algebraic prefix and the one-continuation segment prefix coincide.
Moreover, every full-prefix point outside both endpoint loci has a proper
segment witness with absorption mass in `(0,1)`:

* mass `0` would put the current point in `E`;
* mass `1` would make it the solo endpoint.

Thus, on convex fibers, there is no hidden convexification obstruction and no
third degeneracy.  The only obstruction to executable positive progress is
membership in one of the two endpoint loci.  The owner-step corollaries lift
this statement directly to the essential-APS operator.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type}

/-- On a nonempty convex continuation set, every full convex-hull APS prefix
has a one-continuation segment representation. -/
theorem quittingEssentialAPSPrefix_subset_segment_of_convex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {E : Set (Payoff ι)}
    (hEconvex : Convex ℝ E) (hEnonempty : E.Nonempty) :
    quittingEssentialAPSPrefix reward owner E ⊆
      quittingSegmentEssentialAPSPrefix reward owner E := by
  intro current hcurrent
  rcases hcurrent with ⟨hviable, hconvexHull, hactive⟩
  have hjoin :
      current ∈ convexJoin ℝ
        ({quittingSoloReward reward owner} : Set (Payoff ι)) E := by
    apply (convexHull_min ?_
      ((convex_singleton (quittingSoloReward reward owner)).convexJoin
        hEconvex)) hconvexHull
    intro value hvalue
    rcases Set.mem_insert_iff.mp hvalue with hroot | hE
    · subst value
      exact subset_convexJoin_left hEnonempty
        (Set.mem_singleton (quittingSoloReward reward owner))
    · exact subset_convexJoin_right
        (Set.singleton_nonempty (quittingSoloReward reward owner)) hE
  rcases (mem_convexJoin.mp hjoin) with
    ⟨root, hroot, next, hnext, p, q, hp, hq, hpq, hcombo⟩
  have hrootEq : root = quittingSoloReward reward owner := by
    simpa only [Set.mem_singleton_iff] using hroot
  subst root
  have hp_le_one : p ≤ 1 := by linarith
  refine ⟨hviable, p, ⟨hp, hp_le_one⟩, next, hnext, ?_, hactive⟩
  rw [quittingSingletonArcPayoff_eq_smul_add]
  have hqEq : q = 1 - p := by linarith
  rw [← hqEq]
  exact hcombo.symm

/-- For a nonempty convex continuation set, the algebraic and segment prefix
notions coincide exactly. -/
theorem quittingEssentialAPSPrefix_eq_segment_of_convex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {E : Set (Payoff ι)}
    (hEconvex : Convex ℝ E) (hEnonempty : E.Nonempty) :
    quittingEssentialAPSPrefix reward owner E =
      quittingSegmentEssentialAPSPrefix reward owner E := by
  apply Set.Subset.antisymm
  · exact quittingEssentialAPSPrefix_subset_segment_of_convex
      reward owner hEconvex hEnonempty
  · exact quittingSegmentEssentialAPSPrefix_subset reward owner E

/-- Away from both endpoint loci, convex-prefix membership carries strictly
positive and strictly subunit absorption mass. -/
theorem mem_quittingProperEssentialAPSPrefix_of_convex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {E : Set (Payoff ι)} {current : Payoff ι}
    (hEconvex : Convex ℝ E) (hEnonempty : E.Nonempty)
    (hcurrent : current ∈ quittingEssentialAPSPrefix reward owner E)
    (hcurrent_ne_root : current ≠ quittingSoloReward reward owner)
    (hcurrent_not_mem : current ∉ E) :
    current ∈ quittingProperEssentialAPSPrefix reward owner E := by
  have hsegment :=
    quittingEssentialAPSPrefix_subset_segment_of_convex
      reward owner hEconvex hEnonempty hcurrent
  rcases hsegment with
    ⟨hviable, p, hp, next, hnext, harc, hactive⟩
  have hp_ne_zero : p ≠ 0 := by
    intro hpzero
    apply hcurrent_not_mem
    have hcurrentEq : current = next := by
      rw [harc, hpzero]
      funext who
      simp [quittingSingletonArcPayoff]
    rw [hcurrentEq]
    exact hnext
  have hp_ne_one : p ≠ 1 := by
    intro hpone
    apply hcurrent_ne_root
    rw [harc, hpone]
    funext who
    simp [quittingSingletonArcPayoff]
  refine ⟨hviable, p,
    ⟨lt_of_le_of_ne hp.1 hp_ne_zero.symm,
      lt_of_le_of_ne hp.2 hp_ne_one⟩,
    next, hnext, harc, hactive⟩

/-- Every point of a convex full prefix is either the solo endpoint, already
in the continuation set, or a proper positive-progress segment. -/
theorem quittingEssentialAPSPrefix_endpoint_or_proper_of_convex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {E : Set (Payoff ι)} {current : Payoff ι}
    (hEconvex : Convex ℝ E) (hEnonempty : E.Nonempty)
    (hcurrent : current ∈ quittingEssentialAPSPrefix reward owner E) :
    current = quittingSoloReward reward owner ∨
      current ∈ E ∨
        current ∈ quittingProperEssentialAPSPrefix reward owner E := by
  by_cases hroot : current = quittingSoloReward reward owner
  · exact Or.inl hroot
  by_cases hE : current ∈ E
  · exact Or.inr (Or.inl hE)
  · exact Or.inr (Or.inr <|
      mem_quittingProperEssentialAPSPrefix_of_convex
        reward owner hEconvex hEnonempty hcurrent hroot hE)

/-- Set-level form: removing the two endpoint loci from a convex full prefix
leaves only proper positive-progress points. -/
theorem quittingEssentialAPSPrefix_diff_endpoints_subset_proper_of_convex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {E : Set (Payoff ι)}
    (hEconvex : Convex ℝ E) (hEnonempty : E.Nonempty) :
    quittingEssentialAPSPrefix reward owner E \
        Set.insert (quittingSoloReward reward owner) E ⊆
      quittingProperEssentialAPSPrefix reward owner E := by
  intro current hcurrent
  apply mem_quittingProperEssentialAPSPrefix_of_convex
    reward owner hEconvex hEnonempty hcurrent.1
  · intro hroot
    subst current
    exact hcurrent.2 (Set.mem_insert _ _)
  · intro hE
    exact hcurrent.2 (Set.mem_insert_of_mem _ hE)

/-- If the successor continuation union is nonempty and convex, the full owner
step is exactly its one-continuation segment version. -/
theorem quittingEssentialAPSOwnerStep_eq_segment_of_convex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) (owner : ι)
    (hconvex : Convex ℝ
      (quittingEssentialAPSSuccessorSet reward family owner))
    (hnonempty :
      (quittingEssentialAPSSuccessorSet reward family owner).Nonempty) :
    quittingEssentialAPSOwnerStep reward family owner =
      quittingSegmentEssentialAPSOwnerStep reward family owner := by
  apply Set.Subset.antisymm
  · intro current hcurrent
    rcases hcurrent with hterminal | hprefix
    · exact Or.inl hterminal
    · exact Or.inr <|
        quittingEssentialAPSPrefix_subset_segment_of_convex
          reward owner hconvex hnonempty hprefix
  · exact quittingSegmentEssentialAPSOwnerStep_subset
      reward family owner

/-- Owner-step trichotomy on a convex successor fiber: terminal, endpoint,
already in the successor continuation union, or a proper progress segment. -/
theorem quittingEssentialAPSOwnerStep_terminal_or_proper_of_convex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) (owner : ι)
    (hconvex : Convex ℝ
      (quittingEssentialAPSSuccessorSet reward family owner))
    (hnonempty :
      (quittingEssentialAPSSuccessorSet reward family owner).Nonempty)
    {current : Payoff ι}
    (hcurrent :
      current ∈ quittingEssentialAPSOwnerStep reward family owner) :
    current ∈ quittingEssentialAPSTerminal reward owner ∨
      current = quittingSoloReward reward owner ∨
      current ∈ quittingEssentialAPSSuccessorSet reward family owner ∨
      current ∈ quittingProperEssentialAPSPrefix reward owner
        (quittingEssentialAPSSuccessorSet reward family owner) := by
  rcases hcurrent with hterminal | hprefix
  · exact Or.inl hterminal
  · rcases quittingEssentialAPSPrefix_endpoint_or_proper_of_convex
      reward owner hconvex hnonempty hprefix with
      hroot | hsuccessor | hproper
    · exact Or.inr (Or.inl hroot)
    · exact Or.inr (Or.inr (Or.inl hsuccessor))
    · exact Or.inr (Or.inr (Or.inr hproper))

end GameTheory
