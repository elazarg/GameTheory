/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed

/-!
# A fixed-tail endpoint root has positive absorption under a strict singleton gap

For a fixed continuation target, mixed-Nash existence supplies an exact
endpoint-Nash product root.  If its joint absorption were zero, every marginal
would be pure Continue, and the Continue-supported endpoint inequality would
force the singleton reward to be no larger than the continuation target.  Thus
a strict singleton gap guarantees positive one-stage absorption.

This is only an incoming fixed-tail endpoint-root statement.  It does not
match the root's successor to the tail, preserve a punishment floor, or build
a state-matched Bellman chronology.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Elementary zero-absorption lemma -/

omit [DecidableEq ι] in
/-- A product root with all-Continue mass one has every marginal pure Continue.

This local copy keeps the fixed-tail consumer independent of the much deeper
stationary min-max layer. -/
theorem eq_pure_false_of_quittingStationaryContinueMass_eq_one_local
    {root : ι → PMF Bool}
    (hmass : quittingStationaryContinueMass root = 1) (player : ι) :
    root player = PMF.pure false := by
  classical
  have hprod : ∏ index : ι, (root index false).toReal = 1 := by
    rw [← ENNReal.toReal_prod]
    simpa [quittingStationaryContinueMass, quittingAllContinueAction]
      using hmass
  have hnonneg : ∀ index : ι, 0 ≤ (root index false).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hle : ∀ index : ι, (root index false).toReal ≤ 1 := by
    intro index
    rw [← ENNReal.toReal_one,
      ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by simp)]
    exact PMF.coe_le_one _ _
  have hsplit : ∏ index : ι, (root index false).toReal =
      (root player false).toReal *
        ∏ index ∈ Finset.univ.erase player, (root index false).toReal :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ player)).symm
  have hrest : ∏ index ∈ Finset.univ.erase player,
      (root index false).toReal ≤ 1 :=
    Finset.prod_le_one (fun index _ => hnonneg index)
      (fun index _ => hle index)
  have hfalse : (root player false).toReal = 1 := by
    nlinarith [hnonneg player, hle player,
      Finset.prod_nonneg (fun index (_ : index ∈ Finset.univ.erase player) =>
        hnonneg index)]
  have htrue : (root player true).toReal = 0 := by
    have hsum := Math.ProbabilityMassFunction.sum_coe_fintype (root player)
    have hsumReal : (root player true).toReal + (root player false).toReal = 1 := by
      have hne : (root player true) + (root player false) ≠ ⊤ := by
        rw [Fintype.sum_bool] at hsum
        rw [hsum]
        simp
      rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
      rw [Fintype.sum_bool] at hsum
      rw [hsum]
      simp
    linarith
  have htrueZero : root player true = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff (root player true)).mp htrue with
      hzero | htop
    · exact hzero
    · exact absurd htop (PMF.apply_ne_top _ _)
  have hfalseOne : root player false = 1 := by
    have hsum := Math.ProbabilityMassFunction.sum_coe_fintype (root player)
    rw [Fintype.sum_bool, htrueZero, zero_add] at hsum
    exact hsum
  ext action
  cases action <;> simp [PMF.pure_apply, htrueZero, hfalseOne]

/-! ## Fixed-tail positive absorption -/

/-- A strict singleton endpoint gap forces some exact fixed-tail endpoint root
to have positive joint absorption. -/
theorem exists_isZeroQuittingRootEndpointNash_simplex_with_positive_absorption_of_singleton_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (who : ι)
    (hgap : tail who < reward (quittingSingletonTerminal who) who) :
    ∃ root : QuittingRootSimplex ι,
      IsεQuittingRootEndpointNash reward tail 0
          (quittingRootOfSimplex root) ∧
        0 < quittingRootAbsorptionMass (quittingRootOfSimplex root) := by
  obtain ⟨root, hnash⟩ :=
    exists_isZeroQuittingRootEndpointNash_simplex reward tail
  let rootPMF : ι → PMF Bool := quittingRootOfSimplex root
  have hnonneg : 0 ≤ quittingRootAbsorptionMass rootPMF := by
    unfold quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_le_one rootPMF]
  by_contra hnot
  have hnotRoot : ¬ 0 < quittingRootAbsorptionMass rootPMF := by
    intro hpositive
    apply hnot
    exact ⟨root, hnash, hpositive⟩
  have habs : quittingRootAbsorptionMass rootPMF = 0 := by
    apply le_antisymm
    · exact le_of_not_gt hnotRoot
    · exact hnonneg
  have hmass : quittingStationaryContinueMass rootPMF = 1 := by
    unfold quittingRootAbsorptionMass at habs
    linarith
  have hall : ∀ player, rootPMF player = PMF.pure false := by
    intro player
    exact eq_pure_false_of_quittingStationaryContinueMass_eq_one_local hmass player
  have hrootAll : rootPMF = (quittingAllContinueRoot : ι → PMF Bool) := by
    funext player
    exact hall player
  have hwho := (hnash who).1
  change (rootPMF who false).toReal *
      quittingRootEndpointDifference reward tail rootPMF who ≤ 0 at hwho
  rw [hrootAll, quittingRootEndpointDifference_allContinueRoot] at hwho
  have hwho' : reward (quittingSingletonTerminal who) who - tail who ≤ 0 := by
    simpa [quittingAllContinueRoot] using hwho
  linarith

end GameTheory
