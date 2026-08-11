/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseStrategicRescaling
import UniformEquilibrium.Quitting.Paths.JointPolicySeparatedErrorCompiler
import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import UniformEquilibrium.Quitting.Projective.AnalyticPacket
import Math.PMFProduct.CollisionMass

/-!
# Compiler for the tight diffuse conditioned branch

This module closes the finite-law seam in diffuse product rescaling.  The
basic estimate partitions a finite law into its empty atom, singleton atoms,
and collision atoms.  If the source singleton masses dominate the target
singleton masses, their total-variation distance is paid entirely by the
empty mismatch and the two collision masses.  Applied to hazards `a * x`
conditioned at scale `a` and the product hazards `x`, this gives the sharp
quadratic law error.

The final statements use the joint clock for the resulting policy error and
the deleted clock for Continue deviations.  Boundary tightness is explicit;
no assertion is made on a strict phantom-boundary coordinate.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Empty/singleton/collision partition -/

/-- Coalitions containing at least two players. -/
def quittingDiffuseCollisionCoalitions : Finset (Finset ι) :=
  Finset.univ.filter fun coalition : Finset ι => 2 ≤ coalition.card

omit [DecidableEq ι] in
/-- Every finite coalition sum is the sum of its empty, singleton, and
collision strata. -/
theorem sum_finset_eq_empty_add_singletons_add_collisions
    (f : Finset ι → ℝ) :
    ∑ coalition, f coalition =
      f ∅ + ∑ who, f {who} +
        ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
          f coalition := by
  classical
  let singles : Finset (Finset ι) :=
    Finset.univ.image fun who : ι => ({who} : Finset ι)
  let collisions : Finset (Finset ι) :=
    quittingDiffuseCollisionCoalitions (ι := ι)
  have hdisjoint : Disjoint singles collisions := by
    rw [Finset.disjoint_left]
    intro coalition hsingle hcollision
    simp only [singles, Finset.mem_image, Finset.mem_univ, true_and] at hsingle
    obtain ⟨who, rfl⟩ := hsingle
    simp [collisions, quittingDiffuseCollisionCoalitions] at hcollision
  have hpartition :
      Finset.univ.erase (∅ : Finset ι) = singles ∪ collisions := by
    ext coalition
    simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_union]
    constructor
    · intro hne
      have hpos : 0 < coalition.card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hne.1)
      by_cases hone : coalition.card = 1
      · left
        obtain ⟨who, rfl⟩ := Finset.card_eq_one.mp hone
        simp [singles]
      · right
        simp only [collisions, quittingDiffuseCollisionCoalitions,
          Finset.mem_filter, Finset.mem_univ, true_and]
        omega
    · rintro (hsingle | hcollision)
      · simp only [singles, Finset.mem_image, Finset.mem_univ, true_and]
          at hsingle
        obtain ⟨who, rfl⟩ := hsingle
        simp
      · simp only [collisions, quittingDiffuseCollisionCoalitions,
          Finset.mem_filter, Finset.mem_univ, true_and] at hcollision
        exact ⟨fun hempty => by simp [hempty] at hcollision, trivial⟩
  have hsingleSum : ∑ coalition ∈ singles, f coalition = ∑ who, f {who} := by
    rw [show singles = Finset.univ.image
      (fun who : ι => ({who} : Finset ι)) by rfl, Finset.sum_image]
    intro first _ second _ heq
    simpa using heq
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ ∅),
    hpartition, Finset.sum_union hdisjoint, hsingleSum]
  dsimp only [collisions]
  ring

omit [DecidableEq ι] in
/-- Abstract three-stratum comparison.  No probability representation is
needed: total mass, singleton domination, and collision bounds suffice. -/
theorem abs_sum_mul_sub_sum_mul_le_of_singleton_domination
    (source target payoff : Finset ι → ℝ)
    {bound emptyError sourceCollision targetCollision : ℝ}
    (hbound : 0 ≤ bound)
    (hpayoff : ∀ coalition, |payoff coalition| ≤ bound)
    (hsourceNonneg : ∀ coalition, 0 ≤ source coalition)
    (htargetNonneg : ∀ coalition, 0 ≤ target coalition)
    (hsourceTotal : ∑ coalition, source coalition = 1)
    (htargetTotal : ∑ coalition, target coalition = 1)
    (hsingleton : ∀ who, target {who} ≤ source {who})
    (hempty : |source ∅ - target ∅| ≤ emptyError)
    (hsourceCollision :
      ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        source coalition ≤ sourceCollision)
    (htargetCollision :
      ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        target coalition ≤ targetCollision) :
    |(∑ coalition, source coalition * payoff coalition) -
        ∑ coalition, target coalition * payoff coalition| ≤
      bound *
        (2 * emptyError + 2 * (sourceCollision + targetCollision)) := by
  classical
  let sourceColl :=
    ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
      source coalition
  let targetColl :=
    ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
      target coalition
  let singletonDifference := ∑ who, (source {who} - target {who})
  have hsourceColl0 : 0 ≤ sourceColl :=
    Finset.sum_nonneg fun coalition _ => hsourceNonneg coalition
  have htargetColl0 : 0 ≤ targetColl :=
    Finset.sum_nonneg fun coalition _ => htargetNonneg coalition
  have hsingle0 : 0 ≤ singletonDifference :=
    Finset.sum_nonneg fun who _ => sub_nonneg.mpr (hsingleton who)
  have hmass :
      (source ∅ - target ∅) + singletonDifference +
          (sourceColl - targetColl) = 0 := by
    have hs := sum_finset_eq_empty_add_singletons_add_collisions source
    have ht := sum_finset_eq_empty_add_singletons_add_collisions target
    rw [hsourceTotal] at hs
    rw [htargetTotal] at ht
    dsimp only [sourceColl, targetColl, singletonDifference]
    rw [Finset.sum_sub_distrib]
    linarith
  have hsingleBound : singletonDifference ≤
      emptyError + sourceCollision + targetCollision := by
    have habsLower := neg_le_of_abs_le hempty
    have hsc := hsourceCollision
    have htc := htargetCollision
    change sourceColl ≤ sourceCollision at hsc
    change targetColl ≤ targetCollision at htc
    linarith
  have hemptyTerm :
      |(source ∅ - target ∅) * payoff ∅| ≤ bound * emptyError := by
    have hemptyError0 : 0 ≤ emptyError :=
      (abs_nonneg (source ∅ - target ∅)).trans hempty
    calc
      |(source ∅ - target ∅) * payoff ∅| =
          |source ∅ - target ∅| * |payoff ∅| := abs_mul _ _
      _ ≤ emptyError * bound :=
        mul_le_mul hempty (hpayoff ∅) (abs_nonneg _) hemptyError0
      _ = bound * emptyError := mul_comm _ _
  have hsingletonTerm :
      |∑ who, (source {who} - target {who}) * payoff {who}| ≤
        bound * singletonDifference := by
    calc
      |∑ who, (source {who} - target {who}) * payoff {who}| ≤
          ∑ who, |(source {who} - target {who}) * payoff {who}| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ who, (source {who} - target {who}) * |payoff {who}| := by
        apply Finset.sum_congr rfl
        intro who _
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hsingleton who))]
      _ ≤ ∑ who, (source {who} - target {who}) * bound := by
        apply Finset.sum_le_sum
        intro who _
        exact mul_le_mul_of_nonneg_left (hpayoff {who})
          (sub_nonneg.mpr (hsingleton who))
      _ = bound * singletonDifference := by
        rw [← Finset.sum_mul]
        dsimp only [singletonDifference]
        ring
  have hcollisionTerm :
      |(∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
          source coalition * payoff coalition) -
        ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
          target coalition * payoff coalition| ≤
        bound * (sourceCollision + targetCollision) := by
    calc
      |_ - _| ≤
          |∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            source coalition * payoff coalition| +
          |∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            target coalition * payoff coalition| := abs_sub _ _
      _ ≤ bound * sourceColl + bound * targetColl := by
        apply add_le_add
        · calc
            |∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
                source coalition * payoff coalition| ≤ ∑ coalition ∈
                quittingDiffuseCollisionCoalitions (ι := ι),
                |source coalition * payoff coalition| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ coalition ∈
                quittingDiffuseCollisionCoalitions (ι := ι),
                source coalition * bound := by
              apply Finset.sum_le_sum
              intro coalition _
              rw [abs_mul, abs_of_nonneg (hsourceNonneg coalition)]
              exact mul_le_mul_of_nonneg_left (hpayoff coalition)
                (hsourceNonneg coalition)
            _ = bound * sourceColl := by
              rw [← Finset.sum_mul]
              change (∑ coalition ∈
                quittingDiffuseCollisionCoalitions (ι := ι),
                source coalition) * bound = bound * sourceColl
              dsimp only [sourceColl]
              ring
        · calc
            |∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
                target coalition * payoff coalition| ≤ ∑ coalition ∈
                quittingDiffuseCollisionCoalitions (ι := ι),
                |target coalition * payoff coalition| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ coalition ∈
                quittingDiffuseCollisionCoalitions (ι := ι),
                target coalition * bound := by
              apply Finset.sum_le_sum
              intro coalition _
              rw [abs_mul, abs_of_nonneg (htargetNonneg coalition)]
              exact mul_le_mul_of_nonneg_left (hpayoff coalition)
                (htargetNonneg coalition)
            _ = bound * targetColl := by
              rw [← Finset.sum_mul]
              change (∑ coalition ∈
                quittingDiffuseCollisionCoalitions (ι := ι),
                target coalition) * bound = bound * targetColl
              dsimp only [targetColl]
              ring
      _ ≤ bound * sourceCollision + bound * targetCollision := by
        change sourceColl ≤ sourceCollision at hsourceCollision
        change targetColl ≤ targetCollision at htargetCollision
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsourceCollision hbound)
          (mul_le_mul_of_nonneg_left htargetCollision hbound)
      _ = bound * (sourceCollision + targetCollision) := by ring
  have hsourceSplit :=
    sum_finset_eq_empty_add_singletons_add_collisions
      (fun coalition => source coalition * payoff coalition)
  have htargetSplit :=
    sum_finset_eq_empty_add_singletons_add_collisions
      (fun coalition => target coalition * payoff coalition)
  rw [hsourceSplit, htargetSplit]
  have hrewrite :
      source ∅ * payoff ∅ + ∑ who, source {who} * payoff {who} +
          ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            source coalition * payoff coalition -
        (target ∅ * payoff ∅ + ∑ who, target {who} * payoff {who} +
          ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            target coalition * payoff coalition) =
      (source ∅ - target ∅) * payoff ∅ +
        ∑ who, (source {who} - target {who}) * payoff {who} +
        ((∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            source coalition * payoff coalition) -
          ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            target coalition * payoff coalition) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hrewrite]
  calc
    |_ + _ + _| ≤
        |(source ∅ - target ∅) * payoff ∅| +
          |∑ who, (source {who} - target {who}) * payoff {who}| +
          |(∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
              source coalition * payoff coalition) -
            ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
              target coalition * payoff coalition| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ bound * emptyError +
          bound * singletonDifference +
          bound * (sourceCollision + targetCollision) :=
      add_le_add (add_le_add hemptyTerm hsingletonTerm) hcollisionTerm
    _ ≤ bound * emptyError +
          bound * (emptyError + sourceCollision + targetCollision) +
          bound * (sourceCollision + targetCollision) := by
      gcongr
    _ = bound *
        (2 * emptyError + 2 * (sourceCollision + targetCollision)) := by ring

/-- Comparison of the nonempty parts of two subprobability laws.  The total
mass mismatch replaces the empty-atom mismatch in the probability-law
version. -/
theorem abs_sum_nonempty_mul_sub_sum_nonempty_mul_le_of_singleton_domination
    (source target payoff : Finset ι → ℝ)
    {bound totalError sourceCollision targetCollision : ℝ}
    (hbound : 0 ≤ bound)
    (hpayoff : ∀ coalition, |payoff coalition| ≤ bound)
    (hsourceNonneg : ∀ coalition, 0 ≤ source coalition)
    (htargetNonneg : ∀ coalition, 0 ≤ target coalition)
    (hsingleton : ∀ who, target {who} ≤ source {who})
    (htotal :
      |(∑ coalition ∈ Finset.univ.erase (∅ : Finset ι), source coalition) -
        ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι), target coalition| ≤
          totalError)
    (hsourceCollision :
      ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        source coalition ≤ sourceCollision)
    (htargetCollision :
      ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        target coalition ≤ targetCollision) :
    |(∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          source coalition * payoff coalition) -
        ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          target coalition * payoff coalition| ≤
      bound * (totalError + 2 * (sourceCollision + targetCollision)) := by
  classical
  let sourceColl :=
    ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
      source coalition
  let targetColl :=
    ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
      target coalition
  let singletonDifference := ∑ who, (source {who} - target {who})
  have hsourceColl0 : 0 ≤ sourceColl :=
    Finset.sum_nonneg fun coalition _ => hsourceNonneg coalition
  have htargetColl0 : 0 ≤ targetColl :=
    Finset.sum_nonneg fun coalition _ => htargetNonneg coalition
  have hsingle0 : 0 ≤ singletonDifference :=
    Finset.sum_nonneg fun who _ => sub_nonneg.mpr (hsingleton who)
  have hsourceSplit := sum_finset_eq_empty_add_singletons_add_collisions source
  have htargetSplit := sum_finset_eq_empty_add_singletons_add_collisions target
  have hsourceErase :
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι), source coalition) =
        (∑ who, source {who}) + sourceColl := by
    rw [← Finset.add_sum_erase Finset.univ source (Finset.mem_univ ∅)] at hsourceSplit
    dsimp only [sourceColl]
    linarith
  have htargetErase :
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι), target coalition) =
        (∑ who, target {who}) + targetColl := by
    rw [← Finset.add_sum_erase Finset.univ target (Finset.mem_univ ∅)] at htargetSplit
    dsimp only [targetColl]
    linarith
  have hmass :
      ((∑ coalition ∈ Finset.univ.erase (∅ : Finset ι), source coalition) -
          ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι), target coalition) =
        singletonDifference + (sourceColl - targetColl) := by
    rw [hsourceErase, htargetErase]
    dsimp only [singletonDifference]
    rw [Finset.sum_sub_distrib]
    ring
  have htotal0 : 0 ≤ totalError := (abs_nonneg _).trans htotal
  have hsingleBound : singletonDifference ≤
      totalError + sourceCollision + targetCollision := by
    have hmassUpper := le_of_abs_le htotal
    rw [hmass] at hmassUpper
    change sourceColl ≤ sourceCollision at hsourceCollision
    change targetColl ≤ targetCollision at htargetCollision
    linarith
  have hsingletonTerm :
      |∑ who, (source {who} - target {who}) * payoff {who}| ≤
        bound * singletonDifference := by
    calc
      |∑ who, (source {who} - target {who}) * payoff {who}| ≤
          ∑ who, |(source {who} - target {who}) * payoff {who}| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ who, (source {who} - target {who}) * |payoff {who}| := by
        apply Finset.sum_congr rfl
        intro who _
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hsingleton who))]
      _ ≤ ∑ who, (source {who} - target {who}) * bound := by
        apply Finset.sum_le_sum
        intro who _
        exact mul_le_mul_of_nonneg_left (hpayoff {who})
          (sub_nonneg.mpr (hsingleton who))
      _ = bound * singletonDifference := by
        rw [← Finset.sum_mul]
        dsimp only [singletonDifference]
        ring
  have hcollisionTerm :
      |(∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
          source coalition * payoff coalition) -
        ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
          target coalition * payoff coalition| ≤
        bound * (sourceCollision + targetCollision) := by
    calc
      |_ - _| ≤
          |∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            source coalition * payoff coalition| +
          |∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            target coalition * payoff coalition| := abs_sub _ _
      _ ≤ bound * sourceColl + bound * targetColl := by
        apply add_le_add
        · calc
            |∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
                source coalition * payoff coalition| ≤ ∑ coalition ∈
                quittingDiffuseCollisionCoalitions (ι := ι),
                |source coalition * payoff coalition| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ coalition ∈
                quittingDiffuseCollisionCoalitions (ι := ι),
                source coalition * bound := by
              apply Finset.sum_le_sum
              intro coalition _
              rw [abs_mul, abs_of_nonneg (hsourceNonneg coalition)]
              exact mul_le_mul_of_nonneg_left (hpayoff coalition)
                (hsourceNonneg coalition)
            _ = bound * sourceColl := by
              rw [← Finset.sum_mul]
              dsimp only [sourceColl]
              ring
        · calc
            |∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
                target coalition * payoff coalition| ≤ ∑ coalition ∈
                quittingDiffuseCollisionCoalitions (ι := ι),
                |target coalition * payoff coalition| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ coalition ∈
                quittingDiffuseCollisionCoalitions (ι := ι),
                target coalition * bound := by
              apply Finset.sum_le_sum
              intro coalition _
              rw [abs_mul, abs_of_nonneg (htargetNonneg coalition)]
              exact mul_le_mul_of_nonneg_left (hpayoff coalition)
                (htargetNonneg coalition)
            _ = bound * targetColl := by
              rw [← Finset.sum_mul]
              dsimp only [targetColl]
              ring
      _ ≤ bound * sourceCollision + bound * targetCollision := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsourceCollision hbound)
          (mul_le_mul_of_nonneg_left htargetCollision hbound)
      _ = bound * (sourceCollision + targetCollision) := by ring
  have hsourceWeighted :=
    sum_finset_eq_empty_add_singletons_add_collisions
      (fun coalition => source coalition * payoff coalition)
  have htargetWeighted :=
    sum_finset_eq_empty_add_singletons_add_collisions
      (fun coalition => target coalition * payoff coalition)
  have hsourceWeightedErase :
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          source coalition * payoff coalition) =
        (∑ who, source {who} * payoff {who}) +
          ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            source coalition * payoff coalition := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun coalition => source coalition * payoff coalition)
      (Finset.mem_univ ∅)] at hsourceWeighted
    linarith
  have htargetWeightedErase :
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          target coalition * payoff coalition) =
        (∑ who, target {who} * payoff {who}) +
          ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            target coalition * payoff coalition := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun coalition => target coalition * payoff coalition)
      (Finset.mem_univ ∅)] at htargetWeighted
    linarith
  rw [hsourceWeightedErase, htargetWeightedErase]
  have hrewrite :
      (∑ who, source {who} * payoff {who}) +
          ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            source coalition * payoff coalition -
        ((∑ who, target {who} * payoff {who}) +
          ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            target coalition * payoff coalition) =
      (∑ who, (source {who} - target {who}) * payoff {who}) +
        ((∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            source coalition * payoff coalition) -
          ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
            target coalition * payoff coalition) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hrewrite]
  calc
    |_ + _| ≤
        |∑ who, (source {who} - target {who}) * payoff {who}| +
          |(∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
              source coalition * payoff coalition) -
            ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
              target coalition * payoff coalition| := abs_add_le _ _
    _ ≤ bound * singletonDifference +
        bound * (sourceCollision + targetCollision) :=
      add_le_add hsingletonTerm hcollisionTerm
    _ ≤ bound * (totalError + sourceCollision + targetCollision) +
        bound * (sourceCollision + targetCollision) := by
      gcongr
    _ = bound * (totalError + 2 *
        (sourceCollision + targetCollision)) := by ring

/-! ## Scaled product laws -/

/-- A singleton atom of the rescaled product law is no larger than the same
singleton atom of the source law divided by the scale. -/
theorem coalitionMass_singleton_le_scaled_div
    (x : ι → ℝ) (scale : ℝ) (who : ι)
    (hscale : 0 < scale) (hscaleOne : scale ≤ 1)
    (hx0 : ∀ player, 0 ≤ x player)
    (hx1 : ∀ player, x player ≤ 1) :
    coalitionMass x {who} ≤
      coalitionMass (fun player => scale * x player) {who} / scale := by
  classical
  have hfactor : ∀ player ∈ ({who} : Finset ι)ᶜ,
      1 - x player ≤ 1 - scale * x player := by
    intro player _
    nlinarith [hx0 player]
  have hnonneg : ∀ player ∈ ({who} : Finset ι)ᶜ,
      0 ≤ 1 - x player := fun player _ => sub_nonneg.mpr (hx1 player)
  have hproduct :
      (∏ player ∈ ({who} : Finset ι)ᶜ, (1 - x player)) ≤
        ∏ player ∈ ({who} : Finset ι)ᶜ,
          (1 - scale * x player) := by
    apply Finset.prod_le_prod hnonneg
    intro player hplayer
    exact hfactor player hplayer
  unfold coalitionMass
  simp only [Finset.prod_singleton]
  have hscaled :
      (scale * x who *
          ∏ player ∈ ({who} : Finset ι)ᶜ,
            (1 - scale * x player)) / scale =
        x who *
          ∏ player ∈ ({who} : Finset ι)ᶜ,
            (1 - scale * x player) := by
    field_simp [hscale.ne']
  rw [hscaled]
  exact mul_le_mul_of_nonneg_left hproduct (hx0 who)

/-- Collision mass of a scaled product law, divided by the scale, is at
most half the square of the unscaled marginal total. -/
theorem collisionMass_scaled_div_le_sum_sq_div_two
    (x : ι → ℝ) (scale : ℝ)
    (hscale : 0 < scale) (hscaleOne : scale ≤ 1)
    (hx0 : ∀ player, 0 ≤ x player)
    (hx1 : ∀ player, x player ≤ 1) :
    collisionMass (fun player => scale * x player) / scale ≤
      (∑ player, x player) ^ 2 / 2 := by
  let scaled : ι → ℝ := fun player => scale * x player
  have hscaled0 : ∀ player, 0 ≤ scaled player := fun player =>
    mul_nonneg hscale.le (hx0 player)
  have hscaled1 : ∀ player, scaled player ≤ 1 := fun player => by
    dsimp only [scaled]
    nlinarith [hx0 player, hx1 player]
  have hcollision := collisionMass_le_pairMulSum scaled hscaled0 hscaled1
  have hpair := Math.pairMulSum_le_sq_sum_div_two scaled Finset.univ
  have hsum : (∑ player, scaled player) =
      scale * ∑ player, x player := by
    unfold scaled
    rw [Finset.mul_sum]
  have hbound : collisionMass scaled ≤
      (scale * ∑ player, x player) ^ 2 / 2 := by
    rw [← hsum]
    exact hcollision.trans hpair
  apply (div_le_iff₀ hscale).2
  nlinarith [sq_nonneg (∑ player, x player)]

/-- Unscaled collision mass is at most half the squared marginal total. -/
theorem collisionMass_le_sum_sq_div_two
    (x : ι → ℝ)
    (hx0 : ∀ player, 0 ≤ x player)
    (hx1 : ∀ player, x player ≤ 1) :
    collisionMass x ≤ (∑ player, x player) ^ 2 / 2 := by
  exact (collisionMass_le_pairMulSum x hx0 hx1).trans
    (Math.pairMulSum_le_sq_sum_div_two x Finset.univ)

/-! ## The conditioned source law -/

/-- The source one-stage coalition law after conditioning the whole tail on
eventual absorption.  Nonempty atoms are divided by remaining eventual
absorption; the empty atom transports the next remaining mass. -/
def quittingTailConditionedCoalitionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (coalition : Finset ι) : ℝ :=
  if coalition = ∅ then
    quittingStationaryContinueMass (roots time) *
        quittingTailEventualAbsorption roots (time + 1) /
      quittingTailEventualAbsorption roots time
  else
    quittingRootCoalitionMass (roots time) coalition /
      quittingTailEventualAbsorption roots time

/-- The conditioned source coalition weights have total mass one. -/
theorem sum_quittingTailConditionedCoalitionMass_eq_one
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    ∑ coalition, quittingTailConditionedCoalitionMass roots time coalition = 1 := by
  have hnonempty := quittingRootCoalitionMass_sum_nonempty (roots time)
  have heventual :=
    quittingTailEventualAbsorption_eq_absorption_add_continue_mul_succ
      roots time
  rw [← Finset.add_sum_erase Finset.univ
    (quittingTailConditionedCoalitionMass roots time)
    (Finset.mem_univ ∅)]
  have herase :
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingTailConditionedCoalitionMass roots time coalition) =
        quittingRootAbsorptionMass (roots time) /
          quittingTailEventualAbsorption roots time := by
    calc
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingTailConditionedCoalitionMass roots time coalition) =
          ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
            quittingRootCoalitionMass (roots time) coalition /
              quittingTailEventualAbsorption roots time := by
        apply Finset.sum_congr rfl
        intro coalition hcoalition
        simp [quittingTailConditionedCoalitionMass,
          (Finset.ne_of_mem_erase hcoalition)]
      _ = _ := by
        rw [← Finset.sum_div, hnonempty]
        unfold quittingRootAbsorptionMass
        rfl
  rw [herase]
  simp only [quittingTailConditionedCoalitionMass, if_pos]
  rw [← add_div]
  have hnumerator :
      quittingStationaryContinueMass (roots time) *
          quittingTailEventualAbsorption roots (time + 1) +
        quittingRootAbsorptionMass (roots time) =
      quittingTailEventualAbsorption roots time := by
    linarith [heventual]
  rw [hnumerator]
  exact div_self hpositive.ne'

/-- Every conditioned source coalition weight is nonnegative. -/
theorem quittingTailConditionedCoalitionMass_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (coalition : Finset ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    0 ≤ quittingTailConditionedCoalitionMass roots time coalition := by
  unfold quittingTailConditionedCoalitionMass
  split_ifs
  · exact div_nonneg
      (mul_nonneg (quittingStationaryContinueMass_nonneg _)
        (quittingTailEventualAbsorption_mem_unitInterval roots (time + 1)).1)
      hpositive.le
  · unfold quittingRootCoalitionMass coalitionMass quittingRootQuitRates
    exact div_nonneg
      (mul_nonneg
        (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)
        (Finset.prod_nonneg fun player _ =>
          sub_nonneg.mpr (hazardOfRoot_le_one (roots time) player)))
      hpositive.le

/-- Every ordinary product coalition weight is nonnegative. -/
theorem quittingRootCoalitionMass_nonneg'
    (root : ι → PMF Bool) (coalition : Finset ι) :
    0 ≤ quittingRootCoalitionMass root coalition := by
  unfold quittingRootCoalitionMass coalitionMass quittingRootQuitRates
  exact mul_nonneg
    (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)
    (Finset.prod_nonneg fun player _ =>
      sub_nonneg.mpr (hazardOfRoot_le_one root player))

/-- All ordinary product coalition weights, including the empty atom, sum
to one. -/
theorem sum_quittingRootCoalitionMass_eq_one
    (root : ι → PMF Bool) :
    ∑ coalition, quittingRootCoalitionMass root coalition = 1 := by
  rw [← Finset.add_sum_erase Finset.univ
    (quittingRootCoalitionMass root) (Finset.mem_univ ∅),
    quittingRootCoalitionMass_sum_nonempty]
  have hempty : quittingRootCoalitionMass root ∅ =
      quittingStationaryContinueMass root := by
    unfold quittingRootCoalitionMass
    rw [coalitionMass_empty, continueMass_quittingRootQuitRates]
  rw [hempty]
  ring

/-- The conditioned source singleton atom dominates the rescaled target
singleton atom. -/
theorem quittingRootCoalitionMass_rescaled_le_conditioned_singleton
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingRootCoalitionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) {who} ≤
      quittingTailConditionedCoalitionMass roots time {who} := by
  let scale := quittingTailEventualAbsorption roots time
  let x := quittingTailDiffuseRescaledHazard roots time
  have hscaleOne : scale ≤ 1 :=
    (quittingTailEventualAbsorption_mem_unitInterval roots time).2
  have hx0 : ∀ player, 0 ≤ x player := fun player =>
    quittingTailDiffuseRescaledHazard_nonneg roots time player hpositive
  have hx1 : ∀ player, x player ≤ 1 := fun player =>
    quittingTailDiffuseRescaledHazard_le_one roots time player hpositive
  have htargetRates :
      quittingRootQuitRates
          (quittingTailDiffuseRescaledRoot roots time hpositive) = x := by
    funext player
    change hazardOfRoot
      (quittingTailDiffuseRescaledRoot roots time hpositive) player = x player
    rw [hazardOfRoot_quittingTailDiffuseRescaledRoot]
  have hsourceRates : quittingRootQuitRates (roots time) =
      fun player => scale * x player := by
    funext player
    unfold quittingRootQuitRates x quittingTailDiffuseRescaledHazard scale
    field_simp [hpositive.ne']
  have hscaled := coalitionMass_singleton_le_scaled_div
    x scale who hpositive hscaleOne hx0 hx1
  unfold quittingRootCoalitionMass
  rw [htargetRates]
  have hsource :
      quittingTailConditionedCoalitionMass roots time {who} =
        coalitionMass (fun player => scale * x player) {who} / scale := by
    simp only [quittingTailConditionedCoalitionMass,
      show ({who} : Finset ι) ≠ ∅ by simp, if_false]
    unfold quittingRootCoalitionMass
    rw [hsourceRates]
  rw [hsource]
  exact hscaled

/-- Conditioned source collision mass is at most half the squared rescaled
marginal total. -/
theorem conditionedCoalitionCollisionMass_le_rescaledTotal_sq_div_two
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    (∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        quittingTailConditionedCoalitionMass roots time coalition) ≤
      quittingTailDiffuseRescaledTotal roots time ^ 2 / 2 := by
  let scale := quittingTailEventualAbsorption roots time
  let x := quittingTailDiffuseRescaledHazard roots time
  have hscaleOne : scale ≤ 1 :=
    (quittingTailEventualAbsorption_mem_unitInterval roots time).2
  have hx0 : ∀ player, 0 ≤ x player := fun player =>
    quittingTailDiffuseRescaledHazard_nonneg roots time player hpositive
  have hx1 : ∀ player, x player ≤ 1 := fun player =>
    quittingTailDiffuseRescaledHazard_le_one roots time player hpositive
  have hsourceRates : quittingRootQuitRates (roots time) =
      fun player => scale * x player := by
    funext player
    unfold quittingRootQuitRates x quittingTailDiffuseRescaledHazard scale
    field_simp [hpositive.ne']
  have hsum : (∑ player, x player) =
      quittingTailDiffuseRescaledTotal roots time := rfl
  have hcollision := collisionMass_scaled_div_le_sum_sq_div_two
    x scale hpositive hscaleOne hx0 hx1
  have hleft :
      (∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
          quittingTailConditionedCoalitionMass roots time coalition) =
        collisionMass (fun player => scale * x player) / scale := by
    calc
      _ = (∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
          quittingRootCoalitionMass (roots time) coalition) / scale := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro coalition hcoalition
        have hcard : 2 ≤ coalition.card :=
          (Finset.mem_filter.mp hcoalition).2
        have hne : coalition ≠ ∅ := by
          intro hempty
          simp [hempty] at hcard
        simp only [quittingTailConditionedCoalitionMass, hne, if_false]
        rfl
      _ = collisionMass (fun player => scale * x player) / scale := by
        change collisionMass (quittingRootQuitRates (roots time)) / scale =
          collisionMass (fun player => scale * x player) / scale
        rw [hsourceRates]
  rw [hleft, ← hsum]
  exact hcollision

/-- Target rescaled collision mass obeys the same quadratic bound. -/
theorem rescaledCoalitionCollisionMass_le_rescaledTotal_sq_div_two
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    (∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        quittingRootCoalitionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive) coalition) ≤
      quittingTailDiffuseRescaledTotal roots time ^ 2 / 2 := by
  let x := quittingTailDiffuseRescaledHazard roots time
  have hx0 : ∀ player, 0 ≤ x player := fun player =>
    quittingTailDiffuseRescaledHazard_nonneg roots time player hpositive
  have hx1 : ∀ player, x player ≤ 1 := fun player =>
    quittingTailDiffuseRescaledHazard_le_one roots time player hpositive
  have htargetRates :
      quittingRootQuitRates
          (quittingTailDiffuseRescaledRoot roots time hpositive) = x := by
    funext player
    change hazardOfRoot
      (quittingTailDiffuseRescaledRoot roots time hpositive) player = x player
    rw [hazardOfRoot_quittingTailDiffuseRescaledRoot]
  have hcollision := collisionMass_le_sum_sq_div_two x hx0 hx1
  change collisionMass (quittingRootQuitRates
      (quittingTailDiffuseRescaledRoot roots time hpositive)) ≤
    quittingTailDiffuseRescaledTotal roots time ^ 2 / 2
  rw [htargetRates]
  exact hcollision

/-- The empty atoms of the conditioned source and target product laws differ
at most quadratically. -/
theorem abs_conditionedCoalitionMass_empty_sub_rescaled_empty_le
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    |quittingTailConditionedCoalitionMass roots time ∅ -
        quittingRootCoalitionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive) ∅| ≤
      quittingTailDiffuseRescaledTotal roots time ^ 2 / 2 := by
  have hsource : quittingTailConditionedCoalitionMass roots time ∅ =
      1 - quittingTailConditionedAbsorptionWeight roots time := by
    simp only [quittingTailConditionedCoalitionMass, if_pos]
    rw [← quittingTailConditionedContinuationWeight]
    exact quittingTailConditionedContinuationWeight_eq_one_sub
      roots time hpositive
  have htarget : quittingRootCoalitionMass
      (quittingTailDiffuseRescaledRoot roots time hpositive) ∅ =
      1 - quittingRootAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) := by
    unfold quittingRootCoalitionMass
    rw [coalitionMass_empty, continueMass_quittingRootQuitRates]
    unfold quittingRootAbsorptionMass
    ring
  rw [hsource, htarget]
  have hcomparison :=
    abs_conditionedWeight_sub_rescaledRoot_absorptionMass_le
      roots time hpositive
  have habs :
      |1 - quittingTailConditionedAbsorptionWeight roots time -
          (1 - quittingRootAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hpositive))| =
        |quittingTailConditionedAbsorptionWeight roots time -
          quittingRootAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hpositive)| := by
    rw [show 1 - quittingTailConditionedAbsorptionWeight roots time -
        (1 - quittingRootAbsorptionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive)) =
      -(quittingTailConditionedAbsorptionWeight roots time -
        quittingRootAbsorptionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive)) by ring,
      abs_neg]
  rw [habs]
  exact hcomparison

/-- **Quadratic conditioned-law comparison.**  Every bounded observable of
the whole quitter coalition changes by at most `3 M s²` under product
rescaling. -/
theorem abs_conditionedCoalitionExpectation_sub_rescaled_le
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (observable : Finset ι → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hobservable : ∀ coalition, |observable coalition| ≤ M)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    |(∑ coalition,
          quittingTailConditionedCoalitionMass roots time coalition *
            observable coalition) -
        ∑ coalition,
          quittingRootCoalitionMass
              (quittingTailDiffuseRescaledRoot roots time hpositive) coalition *
            observable coalition| ≤
      3 * M * quittingTailDiffuseRescaledTotal roots time ^ 2 := by
  have habstract :=
    abs_sum_mul_sub_sum_mul_le_of_singleton_domination
      (quittingTailConditionedCoalitionMass roots time)
      (quittingRootCoalitionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive))
      observable hM hobservable
      (fun coalition =>
        quittingTailConditionedCoalitionMass_nonneg
          roots time coalition hpositive)
      (quittingRootCoalitionMass_nonneg'
        (quittingTailDiffuseRescaledRoot roots time hpositive))
      (sum_quittingTailConditionedCoalitionMass_eq_one
        roots time hpositive)
      (sum_quittingRootCoalitionMass_eq_one
        (quittingTailDiffuseRescaledRoot roots time hpositive))
      (fun who =>
        quittingRootCoalitionMass_rescaled_le_conditioned_singleton
          roots time who hpositive)
      (abs_conditionedCoalitionMass_empty_sub_rescaled_empty_le
        roots time hpositive)
      (conditionedCoalitionCollisionMass_le_rescaledTotal_sq_div_two
        roots time hpositive)
      (rescaledCoalitionCollisionMass_le_rescaledTotal_sq_div_two
        roots time hpositive)
  calc
    |_ - _| ≤ M *
        (2 * (quittingTailDiffuseRescaledTotal roots time ^ 2 / 2) +
          2 * (quittingTailDiffuseRescaledTotal roots time ^ 2 / 2 +
            quittingTailDiffuseRescaledTotal roots time ^ 2 / 2)) := habstract
    _ = 3 * M * quittingTailDiffuseRescaledTotal roots time ^ 2 := by ring

/-! ## Deleted-player absorbing laws -/

/-- Nonempty opponent-coalition mass in the source row, normalized by the
full tail absorption scale. -/
def quittingTailConditionedOpponentCoalitionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (coalition : Finset ι) : ℝ :=
  quittingRootCoalitionMass
      (Function.update (roots time) who (PMF.pure false)) coalition /
    quittingTailEventualAbsorption roots time

/-- The rescaled target law with the selected player forced to Continue. -/
def quittingTailRescaledOpponentCoalitionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (coalition : Finset ι) : ℝ :=
  quittingRootCoalitionMass
    (Function.update (quittingTailDiffuseRescaledRoot roots time hpositive)
      who (PMF.pure false)) coalition

theorem quittingTailConditionedOpponentCoalitionMass_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (coalition : Finset ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    0 ≤ quittingTailConditionedOpponentCoalitionMass
      roots time who coalition :=
  div_nonneg (quittingRootCoalitionMass_nonneg' _ _) hpositive.le

theorem quittingTailRescaledOpponentCoalitionMass_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (coalition : Finset ι) :
    0 ≤ quittingTailRescaledOpponentCoalitionMass
      roots time who hpositive coalition :=
  quittingRootCoalitionMass_nonneg' _ _

/-- The nonempty normalized source opponent law has total mass equal to the
conditioned deleted-clock charge. -/
theorem sum_quittingTailConditionedOpponentCoalitionMass_nonempty
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) :
    (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
        quittingTailConditionedOpponentCoalitionMass
          roots time who coalition) =
      quittingTailConditionedOpponentWeight roots time who := by
  unfold quittingTailConditionedOpponentCoalitionMass
  rw [← Finset.sum_div, quittingRootCoalitionMass_sum_nonempty]
  rfl

/-- The nonempty rescaled opponent law has total mass equal to target
opponent absorption. -/
theorem sum_quittingTailRescaledOpponentCoalitionMass_nonempty
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
        quittingTailRescaledOpponentCoalitionMass
          roots time who hpositive coalition) =
      quittingRootOpponentAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) who := by
  unfold quittingTailRescaledOpponentCoalitionMass
  rw [quittingRootCoalitionMass_sum_nonempty]
  rfl

/-- Target singleton opponent atoms are dominated by their normalized source
counterparts. -/
theorem quittingTailRescaledOpponentCoalitionMass_singleton_le_conditioned
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who other : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailRescaledOpponentCoalitionMass
        roots time who hpositive {other} ≤
      quittingTailConditionedOpponentCoalitionMass
        roots time who {other} := by
  let scale := quittingTailEventualAbsorption roots time
  let x : ι → ℝ := Function.update
    (quittingTailDiffuseRescaledHazard roots time) who 0
  have hscaleOne : scale ≤ 1 :=
    (quittingTailEventualAbsorption_mem_unitInterval roots time).2
  have hx0 : ∀ player, 0 ≤ x player := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [x]
    · simpa [x, Function.update_of_ne hplayer] using
        (quittingTailDiffuseRescaledHazard_nonneg
          roots time player hpositive)
  have hx1 : ∀ player, x player ≤ 1 := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [x]
    · simpa [x, Function.update_of_ne hplayer] using
        (quittingTailDiffuseRescaledHazard_le_one
          roots time player hpositive)
  have htargetRates : quittingRootQuitRates
      (Function.update
        (quittingTailDiffuseRescaledRoot roots time hpositive)
        who (PMF.pure false)) = x := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingRootQuitRates, x]
    · simp only [quittingRootQuitRates, x,
        Function.update_of_ne hplayer]
      change hazardOfRoot
        (quittingTailDiffuseRescaledRoot roots time hpositive) player = _
      rw [hazardOfRoot_quittingTailDiffuseRescaledRoot]
  have hsourceRates : quittingRootQuitRates
      (Function.update (roots time) who (PMF.pure false)) =
        fun player => scale * x player := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingRootQuitRates, x]
    · simp only [quittingRootQuitRates, x,
        Function.update_of_ne hplayer]
      unfold quittingTailDiffuseRescaledHazard scale
      field_simp [hpositive.ne']
  have hscaled := coalitionMass_singleton_le_scaled_div
    x scale other hpositive hscaleOne hx0 hx1
  unfold quittingTailRescaledOpponentCoalitionMass
    quittingTailConditionedOpponentCoalitionMass quittingRootCoalitionMass
  rw [htargetRates, hsourceRates]
  exact hscaled

/-- Source collision mass in the forced-Continue opponent law. -/
theorem conditionedOpponentCoalitionCollisionMass_le_total_sq_div_two
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    (∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        quittingTailConditionedOpponentCoalitionMass
          roots time who coalition) ≤
      quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2 := by
  let scale := quittingTailEventualAbsorption roots time
  let x : ι → ℝ := Function.update
    (quittingTailDiffuseRescaledHazard roots time) who 0
  have hscaleOne : scale ≤ 1 :=
    (quittingTailEventualAbsorption_mem_unitInterval roots time).2
  have hx0 : ∀ player, 0 ≤ x player := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [x]
    · simpa [x, Function.update_of_ne hplayer] using
        (quittingTailDiffuseRescaledHazard_nonneg
          roots time player hpositive)
  have hx1 : ∀ player, x player ≤ 1 := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [x]
    · simpa [x, Function.update_of_ne hplayer] using
        (quittingTailDiffuseRescaledHazard_le_one
          roots time player hpositive)
  have hsourceRates : quittingRootQuitRates
      (Function.update (roots time) who (PMF.pure false)) =
        fun player => scale * x player := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingRootQuitRates, x]
    · simp only [quittingRootQuitRates, x,
        Function.update_of_ne hplayer]
      unfold quittingTailDiffuseRescaledHazard scale
      field_simp [hpositive.ne']
  have hsum : (∑ player, x player) =
      quittingTailDiffuseRescaledOpponentTotal roots time who := by
    unfold x quittingTailDiffuseRescaledOpponentTotal
    rw [Finset.sum_update_of_mem (Finset.mem_univ who)]
    simp [Finset.erase_eq]
  have hcollision := collisionMass_scaled_div_le_sum_sq_div_two
    x scale hpositive hscaleOne hx0 hx1
  unfold quittingTailConditionedOpponentCoalitionMass
  rw [← Finset.sum_div]
  change collisionMass (quittingRootQuitRates
      (Function.update (roots time) who (PMF.pure false))) / scale ≤ _
  rw [hsourceRates]
  rw [hsum] at hcollision
  exact hcollision

/-- Target collision mass in the forced-Continue opponent law. -/
theorem rescaledOpponentCoalitionCollisionMass_le_total_sq_div_two
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    (∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        quittingTailRescaledOpponentCoalitionMass
          roots time who hpositive coalition) ≤
      quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2 := by
  let x : ι → ℝ := Function.update
    (quittingTailDiffuseRescaledHazard roots time) who 0
  have hx0 : ∀ player, 0 ≤ x player := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [x]
    · simpa [x, Function.update_of_ne hplayer] using
        (quittingTailDiffuseRescaledHazard_nonneg
          roots time player hpositive)
  have hx1 : ∀ player, x player ≤ 1 := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [x]
    · simpa [x, Function.update_of_ne hplayer] using
        (quittingTailDiffuseRescaledHazard_le_one
          roots time player hpositive)
  have htargetRates : quittingRootQuitRates
      (Function.update
        (quittingTailDiffuseRescaledRoot roots time hpositive)
        who (PMF.pure false)) = x := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingRootQuitRates, x]
    · simp only [quittingRootQuitRates, x,
        Function.update_of_ne hplayer]
      change hazardOfRoot
        (quittingTailDiffuseRescaledRoot roots time hpositive) player = _
      rw [hazardOfRoot_quittingTailDiffuseRescaledRoot]
  have hsum : (∑ player, x player) =
      quittingTailDiffuseRescaledOpponentTotal roots time who := by
    unfold x quittingTailDiffuseRescaledOpponentTotal
    rw [Finset.sum_update_of_mem (Finset.mem_univ who)]
    simp [Finset.erase_eq]
  have hcollision := collisionMass_le_sum_sq_div_two x hx0 hx1
  unfold quittingTailRescaledOpponentCoalitionMass
  change collisionMass (quittingRootQuitRates
      (Function.update
        (quittingTailDiffuseRescaledRoot roots time hpositive)
        who (PMF.pure false))) ≤ _
  rw [htargetRates]
  rw [hsum] at hcollision
  exact hcollision

/-- **Quadratic forced-Continue absorbing-law comparison.** -/
theorem abs_conditionedOpponentAbsorbingReward_sub_rescaled_le
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    |quittingStationaryFixedOpponentsContinueReward reward (roots time) who /
          quittingTailEventualAbsorption roots time -
        quittingStationaryFixedOpponentsContinueReward reward
          (quittingTailDiffuseRescaledRoot roots time hpositive) who| ≤
      3 * M *
        quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 := by
  let payoff : Finset ι → ℝ := fun coalition =>
    if h : coalition.Nonempty then reward ⟨coalition, h⟩ who else 0
  have hpayoff : ∀ coalition, |payoff coalition| ≤ M := by
    intro coalition
    by_cases hcoalition : coalition.Nonempty
    · simpa [payoff, hcoalition] using hreward ⟨coalition, hcoalition⟩ who
    · simp [payoff, hcoalition, hM]
  have habstract :=
    abs_sum_nonempty_mul_sub_sum_nonempty_mul_le_of_singleton_domination
      (totalError :=
        quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2)
      (sourceCollision :=
        quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2)
      (targetCollision :=
        quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2)
      (quittingTailConditionedOpponentCoalitionMass roots time who)
      (quittingTailRescaledOpponentCoalitionMass
        roots time who hpositive)
      payoff hM hpayoff
      (fun coalition => quittingTailConditionedOpponentCoalitionMass_nonneg
        roots time who coalition hpositive)
      (quittingTailRescaledOpponentCoalitionMass_nonneg
        roots time who hpositive)
      (fun other =>
        quittingTailRescaledOpponentCoalitionMass_singleton_le_conditioned
          roots time who other hpositive)
      (by
        rw [sum_quittingTailConditionedOpponentCoalitionMass_nonempty,
          sum_quittingTailRescaledOpponentCoalitionMass_nonempty]
        simpa using
          (abs_conditionedOpponentWeight_sub_rescaledRoot_opponentAbsorption_le
            roots time who hpositive))
      (conditionedOpponentCoalitionCollisionMass_le_total_sq_div_two
        roots time who hpositive)
      (rescaledOpponentCoalitionCollisionMass_le_total_sq_div_two
        roots time who hpositive)
  have hsource :
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingTailConditionedOpponentCoalitionMass roots time who coalition *
            payoff coalition) =
        quittingStationaryFixedOpponentsContinueReward reward (roots time) who /
          quittingTailEventualAbsorption roots time := by
    unfold quittingTailConditionedOpponentCoalitionMass
    calc
      _ = (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingRootCoalitionMass
              (Function.update (roots time) who (PMF.pure false)) coalition *
            payoff coalition) /
          quittingTailEventualAbsorption roots time := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro coalition _
        ring
      _ = _ := by
        apply congrArg (fun z : ℝ =>
          z / quittingTailEventualAbsorption roots time)
        calc
          _ = ∑ coalition,
              quittingRootCoalitionMass
                  (Function.update (roots time) who (PMF.pure false)) coalition *
                quittingProjectiveCoalitionReward reward coalition who := by
            rw [← Finset.add_sum_erase Finset.univ
              (fun coalition => quittingRootCoalitionMass
                (Function.update (roots time) who (PMF.pure false)) coalition *
                  quittingProjectiveCoalitionReward reward coalition who)
              (Finset.mem_univ ∅)]
            simp only [quittingProjectiveCoalitionReward_empty, mul_zero,
              zero_add]
            apply Finset.sum_congr rfl
            intro coalition hcoalition
            have hnonempty : coalition.Nonempty :=
              Finset.nonempty_iff_ne_empty.mpr
                (Finset.ne_of_mem_erase hcoalition)
            simp [payoff, quittingProjectiveCoalitionReward, hnonempty]
          _ = quittingRootAbsorbingContribution reward
              (Function.update (roots time) who (PMF.pure false)) who :=
            (quittingRootAbsorbingContribution_eq_sum_coalitionMass
              reward _ who).symm
  have htarget :
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingTailRescaledOpponentCoalitionMass
              roots time who hpositive coalition * payoff coalition) =
        quittingStationaryFixedOpponentsContinueReward reward
          (quittingTailDiffuseRescaledRoot roots time hpositive) who := by
    unfold quittingTailRescaledOpponentCoalitionMass
    calc
      _ = ∑ coalition,
          quittingRootCoalitionMass
            (Function.update
              (quittingTailDiffuseRescaledRoot roots time hpositive)
              who (PMF.pure false)) coalition *
            quittingProjectiveCoalitionReward reward coalition who := by
        rw [← Finset.add_sum_erase Finset.univ
          (fun coalition => quittingRootCoalitionMass
            (Function.update
              (quittingTailDiffuseRescaledRoot roots time hpositive)
              who (PMF.pure false)) coalition *
              quittingProjectiveCoalitionReward reward coalition who)
          (Finset.mem_univ ∅)]
        simp only [quittingProjectiveCoalitionReward_empty, mul_zero, zero_add]
        apply Finset.sum_congr rfl
        intro coalition hcoalition
        have hnonempty : coalition.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr
            (Finset.ne_of_mem_erase hcoalition)
        simp [payoff, quittingProjectiveCoalitionReward, hnonempty]
      _ = quittingRootAbsorbingContribution reward
          (Function.update
            (quittingTailDiffuseRescaledRoot roots time hpositive)
            who (PMF.pure false)) who :=
        (quittingRootAbsorbingContribution_eq_sum_coalitionMass
          reward _ who).symm
      _ = _ := rfl
  rw [← hsource, ← htarget]
  calc
    |_ - _| ≤ M *
        (quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2 +
          2 * (quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2 +
            quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2)) :=
      habstract
    _ = 5 / 2 * M *
        quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 := by ring
    _ ≤ 3 * M *
        quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 := by
      have hsq : 0 ≤ quittingTailDiffuseRescaledOpponentTotal
          roots time who ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg hM hsq]

/-- Exact source refusal inequality after conditioning.  The last term is
the phantom mass carried by counterfactual own Quit; it is retained rather
than discarded. -/
theorem conditionedSourceContinueBase_le_conditionedValue_sub_phantom
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (time : ℕ) (who : ι)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1)) :
    quittingStationaryFixedOpponentsContinueReward reward (roots time) who /
          quittingTailEventualAbsorption roots time +
        quittingStationaryFixedOpponentsContinueMass (roots time) who *
          quittingTailEventualAbsorption roots (time + 1) /
          quittingTailEventualAbsorption roots time *
          quittingTailConditionedValue roots value boundary (time + 1) who ≤
      quittingTailConditionedValue roots value boundary time who -
        quittingStationaryFixedOpponentsContinueMass (roots time) who *
          quittingTailDiffuseRescaledHazard roots time who *
          quittingJointSurvivalLimit roots (time + 1) * boundary who := by
  have hnashRoot :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (value (time + 1)) (roots time)).1 (hnash time)
  have hcontinue :=
    quittingRootContinuePayoff_le_successor_of_isZeroNash
      reward (value (time + 1)) (roots time) who hnashRoot
  rw [quittingRootContinuePayoff_eq_fixedOpponents
    reward roots who (value (time + 1)) time] at hcontinue
  rw [← congrFun (hpolicy time) who] at hcontinue
  have hsurvival := quittingJointSurvivalLimit_eq_continue_mul_succ roots time
  have hcontinueMass :
      quittingStationaryContinueMass (roots time) =
        quittingStationaryFixedOpponentsContinueMass (roots time) who *
          (roots time who false).toReal :=
    quittingStationaryContinueMass_eq_forcedContinue_mul_own
      (roots time) who
  have hown : (roots time who false).toReal =
      1 - (roots time who true).toReal := by
    linarith [quittingRoot_continueProbability_add_quitProbability
      (roots time) who]
  have hscaled : (roots time who true).toReal =
      quittingTailEventualAbsorption roots time *
        quittingTailDiffuseRescaledHazard roots time who := by
    unfold quittingTailDiffuseRescaledHazard
    field_simp [hcurrent.ne']
  let sourceContinue :=
    quittingStationaryFixedOpponentsContinueMass (roots time) who
  let sourceReward :=
    quittingStationaryFixedOpponentsContinueReward reward (roots time) who
  let eventual := quittingTailEventualAbsorption roots time
  let phantom := quittingJointSurvivalLimit roots (time + 1)
  let ownScaled := quittingTailDiffuseRescaledHazard roots time who
  have hcontinue' : sourceReward + sourceContinue * value (time + 1) who ≤
      value time who := by
    simpa [sourceReward, sourceContinue,
      quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass] using hcontinue
  calc
    sourceReward / eventual +
          sourceContinue * quittingTailEventualAbsorption roots (time + 1) /
            eventual *
            quittingTailConditionedValue roots value boundary (time + 1) who =
        (sourceReward + sourceContinue * value (time + 1) who -
          sourceContinue * phantom * boundary who) / eventual := by
      unfold quittingTailConditionedValue
      dsimp only [eventual, phantom]
      field_simp [hcurrent.ne', hnext.ne']
      ring
    _ ≤ (value time who - sourceContinue * phantom * boundary who) /
        eventual := by
      exact div_le_div_of_nonneg_right (by linarith) hcurrent.le
    _ = quittingTailConditionedValue roots value boundary time who -
        sourceContinue * ownScaled * phantom * boundary who := by
      unfold quittingTailConditionedValue
      dsimp only [eventual, phantom, sourceContinue, ownScaled]
      rw [hsurvival, hcontinueMass, hown, hscaled]
      field_simp [hcurrent.ne']
      ring

/-- **Deleted-clock Continue estimate.**  On the singleton-tight diffuse
stratum, the rescaled Continue endpoint has only collision-order error plus
the explicitly controlled phantom own-clock term. -/
theorem rescaledContinuePayoff_le_conditionedValue_add_deletedCharge
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (time : ℕ) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hconditionedBound :
      |quittingTailConditionedValue roots value boundary (time + 1) who| ≤ M)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (htight : boundary who = quittingSoloBaseline reward who)
    (hsmall : Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1)
    (hhalf : quittingTailConditionedAbsorptionWeight roots time ≤ 1 / 2) :
    quittingStationaryFixedOpponentsContinueReward reward
          (quittingTailDiffuseRescaledRoot roots time hcurrent) who +
        quittingStationaryFixedOpponentsContinueMass
            (quittingTailDiffuseRescaledRoot roots time hcurrent) who *
          quittingTailConditionedValue roots value boundary (time + 1) who ≤
      quittingTailConditionedValue roots value boundary time who +
        (7 * Fintype.card ι + 16) * M *
          quittingTailConditionedAbsorptionWeight roots time *
          quittingRootOpponentAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hcurrent) who := by
  let alpha := quittingTailConditionedAbsorptionWeight roots time
  let opponentTotal :=
    quittingTailDiffuseRescaledOpponentTotal roots time who
  let sourceOpponent := quittingTailConditionedOpponentWeight roots time who
  let targetOpponent := quittingRootOpponentAbsorptionMass
    (quittingTailDiffuseRescaledRoot roots time hcurrent) who
  let sourceContinue :=
    quittingStationaryFixedOpponentsContinueMass (roots time) who
  let targetContinue := quittingStationaryFixedOpponentsContinueMass
    (quittingTailDiffuseRescaledRoot roots time hcurrent) who
  let sourceReward :=
    quittingStationaryFixedOpponentsContinueReward reward (roots time) who
  let targetReward := quittingStationaryFixedOpponentsContinueReward reward
    (quittingTailDiffuseRescaledRoot roots time hcurrent) who
  let own := quittingTailDiffuseRescaledHazard roots time who
  let phantom := quittingJointSurvivalLimit roots (time + 1)
  let nextValue :=
    quittingTailConditionedValue roots value boundary (time + 1) who
  let currentValue :=
    quittingTailConditionedValue roots value boundary time who
  have hsource :=
    conditionedSourceContinueBase_le_conditionedValue_sub_phantom
      roots value boundary hpolicy hnash time who hcurrent hnext
  change sourceReward / quittingTailEventualAbsorption roots time +
      sourceContinue * quittingTailEventualAbsorption roots (time + 1) /
        quittingTailEventualAbsorption roots time * nextValue ≤
    currentValue - sourceContinue * own * phantom * boundary who at hsource
  have hrewards := abs_conditionedOpponentAbsorbingReward_sub_rescaled_le
    (reward := reward) roots time who hM hreward hcurrent
  change |sourceReward / quittingTailEventualAbsorption roots time -
      targetReward| ≤ 3 * M * opponentTotal ^ 2 at hrewards
  have hclock :=
    abs_conditionedOpponentWeight_sub_rescaledRoot_opponentAbsorption_le
      roots time who hcurrent
  change |sourceOpponent - targetOpponent| ≤ opponentTotal ^ 2 / 2 at hclock
  have hseam :=
    quittingTailDiffuse_deletedContinuation_rescaling_identity
      roots time who hcurrent
  have hsourceContinueEq : sourceContinue =
      1 - quittingRootOpponentAbsorptionMass (roots time) who := by
    unfold sourceContinue quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueMass quittingRootOpponentAbsorptionMass
      quittingRootAbsorptionMass
    ring
  have htargetContinueEq : targetContinue =
      1 - quittingRootOpponentAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hcurrent) who := by
    unfold targetContinue quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueMass quittingRootOpponentAbsorptionMass
      quittingRootAbsorptionMass
    ring
  rw [← hsourceContinueEq, ← htargetContinueEq] at hseam
  change targetContinue -
      sourceContinue * quittingTailEventualAbsorption roots (time + 1) /
        quittingTailEventualAbsorption roots time =
    sourceOpponent - targetOpponent + sourceContinue * own * phantom at hseam
  have hdecompose :
      targetReward + targetContinue * nextValue =
        (sourceReward / quittingTailEventualAbsorption roots time +
          sourceContinue * quittingTailEventualAbsorption roots (time + 1) /
            quittingTailEventualAbsorption roots time * nextValue) +
        (targetReward -
          sourceReward / quittingTailEventualAbsorption roots time) +
        (sourceOpponent - targetOpponent) * nextValue +
        sourceContinue * own * phantom * nextValue := by
    have htargetContinue : targetContinue =
        sourceContinue * quittingTailEventualAbsorption roots (time + 1) /
            quittingTailEventualAbsorption roots time +
          sourceOpponent - targetOpponent + sourceContinue * own * phantom := by
      linarith [hseam]
    rw [htargetContinue]
    ring
  have hopponentTotal0 : 0 ≤ opponentTotal := by
    unfold opponentTotal quittingTailDiffuseRescaledOpponentTotal
    exact Finset.sum_nonneg fun player _ =>
      quittingTailDiffuseRescaledHazard_nonneg roots time player hcurrent
  have halpha0 : 0 ≤ alpha :=
    quittingTailConditionedAbsorptionWeight_nonneg roots time hcurrent
  have htargetOpponent0 : 0 ≤ targetOpponent := by
    unfold targetOpponent
    exact quittingRootAbsorptionMass_nonneg _
  have hsourceOpponent0 : 0 ≤ sourceOpponent := by
    exact quittingTailConditionedOpponentWeight_nonneg roots time who hcurrent
  have htotalUpper : opponentTotal ≤ Fintype.card ι * alpha :=
    (quittingTailDiffuseRescaledOpponentTotal_le_total
      roots time who hcurrent).trans
      (quittingTailDiffuseRescaledTotal_le_card_mul_conditionedWeight
        roots time hcurrent)
  have htotalOne : opponentTotal ≤ 1 := htotalUpper.trans hsmall
  have htargetLower :=
    quittingTailDiffuseRescaledOpponentTotal_sub_sq_div_two_le_opponentAbsorption
      roots time who hcurrent
  change opponentTotal - opponentTotal ^ 2 / 2 ≤ targetOpponent at htargetLower
  have htotalHalf : opponentTotal / 2 ≤ targetOpponent := by
    nlinarith [sq_nonneg opponentTotal]
  have hsquare : opponentTotal ^ 2 ≤
      2 * (Fintype.card ι * alpha) * targetOpponent := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr htotalUpper) (sub_nonneg.mpr (by
        linarith [htotalHalf] : opponentTotal ≤ 2 * targetOpponent))]
  have hsourceClock :=
    half_conditionedOpponentWeight_le_rescaledRoot_opponentAbsorption
      roots time who hcurrent hsmall
  change sourceOpponent / 2 ≤ targetOpponent at hsourceClock
  have hsourceContinue0 : 0 ≤ sourceContinue := by
    exact quittingStationaryFixedOpponentsContinueMass_nonneg (roots time) who
  have hsourceContinue1 : sourceContinue ≤ 1 := by
    exact quittingStationaryFixedOpponentsContinueMass_le_one (roots time) who
  have hown0 : 0 ≤ own :=
    quittingTailDiffuseRescaledHazard_nonneg roots time who hcurrent
  have hownAlpha : own ≤ alpha :=
    quittingTailDiffuseRescaledHazard_le_conditionedWeight
      roots time who hcurrent
  have hphantom0 : 0 ≤ phantom :=
    quittingJointSurvivalLimit_nonneg roots (time + 1)
  have hphantom1 : phantom ≤ 1 := by
    have hnextNonneg :=
      (quittingTailEventualAbsorption_mem_unitInterval roots (time + 1)).1
    unfold phantom quittingTailEventualAbsorption at hnextNonneg
    linarith
  have hownTerm :
      sourceContinue * own * phantom * (nextValue - boundary who) ≤
        16 * M * alpha * targetOpponent := by
    by_cases hownZero : own = 0
    · rw [hownZero, mul_zero, zero_mul]
      have h16M : 0 ≤ (16 : ℝ) * M :=
        mul_nonneg (by norm_num) hM
      have hnonneg := mul_nonneg (mul_nonneg h16M halpha0) htargetOpponent0
      simpa only [zero_mul] using hnonneg
    · have hownPos : 0 < own := lt_of_le_of_ne hown0 (Ne.symm hownZero)
      have hactive : 0 < (roots time who true).toReal := by
        have hscaledOwn : (roots time who true).toReal =
            quittingTailEventualAbsorption roots time * own := by
          unfold own quittingTailDiffuseRescaledHazard
          field_simp [hcurrent.ne']
        rw [hscaledOwn]
        positivity
      have hgap :=
        abs_quittingTailConditionedValue_succ_sub_singleton_le
          roots value boundary hpolicy hnash time who hM hreward hcurrent hnext
            hactive htight hhalf
      have hboundary : boundary who =
          reward (quittingSingletonTerminal who) who := by
        simpa [quittingSoloBaseline, quittingSoloReward,
          quittingSingletonTerminal] using htight
      rw [← hboundary] at hgap
      change |nextValue - boundary who| ≤ 8 * M * sourceOpponent at hgap
      have hnextGap : |nextValue - boundary who| ≤
          16 * M * targetOpponent := by
        nlinarith [mul_nonneg hM hsourceOpponent0,
          mul_nonneg hM htargetOpponent0]
      have hprefix0 : 0 ≤ sourceContinue * own * phantom :=
        mul_nonneg (mul_nonneg hsourceContinue0 hown0) hphantom0
      have habsTerm := mul_le_mul_of_nonneg_left hnextGap hprefix0
      have hcombined : sourceContinue * phantom ≤ 1 := by
        nlinarith [mul_nonneg hsourceContinue0 hphantom0,
          mul_nonneg (sub_nonneg.mpr hsourceContinue1)
            (sub_nonneg.mpr hphantom1)]
      have hprefixOwn : sourceContinue * own * phantom ≤ own := by
        calc
          sourceContinue * own * phantom = own * (sourceContinue * phantom) := by
            ring
          _ ≤ own * 1 := mul_le_mul_of_nonneg_left hcombined hown0
          _ = own := mul_one _
      have hcoefficient0 : 0 ≤ 16 * M * targetOpponent :=
        mul_nonneg (mul_nonneg (by norm_num) hM) htargetOpponent0
      have habsUpper : sourceContinue * own * phantom *
            |nextValue - boundary who| ≤
          16 * M * alpha * targetOpponent := by
        calc
          sourceContinue * own * phantom * |nextValue - boundary who| ≤
              sourceContinue * own * phantom *
                (16 * M * targetOpponent) := habsTerm
          _ ≤ own * (16 * M * targetOpponent) := by
            exact mul_le_mul_of_nonneg_right hprefixOwn hcoefficient0
          _ ≤ alpha * (16 * M * targetOpponent) :=
            mul_le_mul_of_nonneg_right hownAlpha hcoefficient0
          _ = 16 * M * alpha * targetOpponent := by ring
      calc
        sourceContinue * own * phantom * (nextValue - boundary who) ≤
            |sourceContinue * own * phantom *
              (nextValue - boundary who)| := le_abs_self _
        _ = sourceContinue * own * phantom *
              |nextValue - boundary who| := by
          rw [abs_mul, abs_of_nonneg hprefix0]
        _ ≤ 16 * M * alpha * targetOpponent := habsUpper
  have hrewardsUpper : targetReward -
      sourceReward / quittingTailEventualAbsorption roots time ≤
        3 * M * opponentTotal ^ 2 := by
    have := neg_le_of_abs_le hrewards
    linarith
  have hclockTerm : (sourceOpponent - targetOpponent) * nextValue ≤
      M * (opponentTotal ^ 2 / 2) := by
    calc
      (sourceOpponent - targetOpponent) * nextValue ≤
          |sourceOpponent - targetOpponent| * |nextValue| := by
        exact (le_abs_self _).trans_eq (abs_mul _ _)
      _ ≤ (opponentTotal ^ 2 / 2) * M :=
        mul_le_mul hclock hconditionedBound (abs_nonneg _)
          (by positivity)
      _ = M * (opponentTotal ^ 2 / 2) := by ring
  rw [hdecompose]
  calc
    _ ≤ (currentValue - sourceContinue * own * phantom * boundary who) +
          (3 * M * opponentTotal ^ 2) +
          M * (opponentTotal ^ 2 / 2) +
          sourceContinue * own * phantom * nextValue := by
      gcongr
    _ = currentValue + 3 * M * opponentTotal ^ 2 +
          M * (opponentTotal ^ 2 / 2) +
          sourceContinue * own * phantom * (nextValue - boundary who) := by
      ring
    _ ≤ currentValue + 3 * M * opponentTotal ^ 2 +
          M * (opponentTotal ^ 2 / 2) +
          16 * M * alpha * targetOpponent := by
      gcongr
    _ = currentValue + 7 / 2 * M * opponentTotal ^ 2 +
          16 * M * alpha * targetOpponent := by ring
    _ ≤ currentValue +
          7 * M * (Fintype.card ι * alpha) * targetOpponent +
          16 * M * alpha * targetOpponent := by
      have hcoefficient : 0 ≤ 7 / 2 * M := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hsquare hcoefficient
      have hscaled' : 7 / 2 * M * opponentTotal ^ 2 ≤
          7 * M * (Fintype.card ι * alpha) * targetOpponent := by
        calc
          7 / 2 * M * opponentTotal ^ 2 ≤
              7 / 2 * M *
                (2 * (Fintype.card ι * alpha) * targetOpponent) := hscaled
          _ = 7 * M * (Fintype.card ι * alpha) * targetOpponent := by ring
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_right (add_le_add_left hscaled' currentValue)
          (16 * M * alpha * targetOpponent))
    _ = currentValue +
        (7 * Fintype.card ι + 16) * M * alpha * targetOpponent := by ring

/-- The conditioned source coalition law evaluates exactly to the
conditioned Bellman state. -/
theorem sum_conditionedCoalitionMass_mul_stagePayoff_eq_conditionedValue
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (time : ℕ)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (who : ι) :
    (∑ coalition,
        quittingTailConditionedCoalitionMass roots time coalition *
          quittingStageCoalitionPayoff reward
            (quittingTailConditionedValue roots value boundary (time + 1))
            coalition who) =
      quittingTailConditionedValue roots value boundary time who := by
  let next := quittingTailConditionedValue roots value boundary (time + 1)
  let currentScale := quittingTailEventualAbsorption roots time
  let nextScale := quittingTailEventualAbsorption roots (time + 1)
  let continueMass := quittingStationaryContinueMass (roots time)
  have habsorbing :
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingRootCoalitionMass (roots time) coalition *
            quittingStageCoalitionPayoff reward next coalition who) =
        quittingRootAbsorbingContribution reward (roots time) who := by
    rw [quittingRootAbsorbingContribution_eq_sum_coalitionMass]
    change _ = ∑ coalition,
      quittingRootCoalitionMass (roots time) coalition *
        quittingProjectiveCoalitionReward reward coalition who
    rw [← Finset.add_sum_erase Finset.univ
      (fun coalition => quittingRootCoalitionMass (roots time) coalition *
        quittingProjectiveCoalitionReward reward coalition who)
      (Finset.mem_univ ∅)]
    simp only [quittingProjectiveCoalitionReward_empty, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro coalition hcoalition
    have hne : coalition.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hcoalition)
    simp [quittingStageCoalitionPayoff, quittingProjectiveCoalitionReward,
      hne]
  have hsum :
      (∑ coalition,
          quittingTailConditionedCoalitionMass roots time coalition *
            quittingStageCoalitionPayoff reward next coalition who) =
        (quittingRootAbsorbingContribution reward (roots time) who +
          continueMass * nextScale * next who) / currentScale := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun coalition =>
        quittingTailConditionedCoalitionMass roots time coalition *
          quittingStageCoalitionPayoff reward next coalition who)
      (Finset.mem_univ ∅)]
    have herase :
        (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingTailConditionedCoalitionMass roots time coalition *
            quittingStageCoalitionPayoff reward next coalition who) =
          quittingRootAbsorbingContribution reward (roots time) who /
            currentScale := by
      calc
        _ = (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
            quittingRootCoalitionMass (roots time) coalition *
              quittingStageCoalitionPayoff reward next coalition who) /
              currentScale := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro coalition hcoalition
          have hne : coalition ≠ ∅ := Finset.ne_of_mem_erase hcoalition
          simp only [quittingTailConditionedCoalitionMass, hne, if_false]
          ring
        _ = _ := by rw [habsorbing]
    rw [herase]
    simp only [quittingTailConditionedCoalitionMass, if_pos,
      quittingStageCoalitionPayoff, Finset.not_nonempty_empty, dite_false]
    dsimp only [currentScale, nextScale, continueMass]
    ring
  rw [hsum]
  have hstep := congrFun (hpolicy time) who
  rw [quittingRootSuccessorPayoff_apply_eq_affine] at hstep
  have hsurvival := quittingJointSurvivalLimit_eq_continue_mul_succ roots time
  dsimp only [next, currentScale, nextScale, continueMass]
  have hnextValue :
      quittingTailEventualAbsorption roots (time + 1) *
          quittingTailConditionedValue roots value boundary (time + 1) who =
        value (time + 1) who -
          quittingJointSurvivalLimit roots (time + 1) * boundary who := by
    unfold quittingTailConditionedValue
    field_simp [hnext.ne']
  rw [mul_assoc, hnextValue]
  unfold quittingTailConditionedValue
  rw [hstep, hsurvival]
  field_simp [hcurrent.ne', hnext.ne']
  ring

omit [DecidableEq ι] in
/-- **Quadratic policy error of diffuse product rescaling.** -/
theorem abs_conditionedValue_sub_rescaledSuccessorPayoff_le
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (time : ℕ)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (who : ι) :
    |quittingTailConditionedValue roots value boundary time who -
        quittingRootSuccessorPayoff reward
          (quittingTailConditionedValue roots value boundary (time + 1))
          (quittingTailDiffuseRescaledRoot roots time hcurrent) who| ≤
      3 * M * quittingTailDiffuseRescaledTotal roots time ^ 2 := by
  classical
  let next := quittingTailConditionedValue roots value boundary (time + 1)
  let observable : Finset ι → ℝ := fun coalition =>
    quittingStageCoalitionPayoff reward next coalition who
  have hobservable : ∀ coalition, |observable coalition| ≤ M := by
    intro coalition
    by_cases hnonempty : coalition.Nonempty
    · simpa [observable, quittingStageCoalitionPayoff, hnonempty] using
        hreward ⟨coalition, hnonempty⟩ who
    · simpa [observable, quittingStageCoalitionPayoff, hnonempty, next] using
        hconditionedBound (time + 1) who
  have hlaw := abs_conditionedCoalitionExpectation_sub_rescaled_le
    roots time observable hM hobservable hcurrent
  have hsource :=
    sum_conditionedCoalitionMass_mul_stagePayoff_eq_conditionedValue
      roots value boundary hpolicy time hcurrent hnext who
  have htarget := quittingRootExpectedPayoff_eq_sum_coalitionMass
    reward next (quittingTailDiffuseRescaledRoot roots time hcurrent) who
  change |quittingTailConditionedValue roots value boundary time who -
      quittingRootExpectedPayoff reward next
        (quittingTailDiffuseRescaledRoot roots time hcurrent) who| ≤ _
  rw [htarget]
  rw [← hsource]
  exact hlaw

/-! ## Infinite-path certificate -/

omit [DecidableEq ι] in
/-- Quadratic policy error rewritten as a joint-clock charge under a uniform
mesh cap. -/
theorem abs_conditionedValue_sub_rescaledSuccessorPayoff_le_jointCharge
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M rho : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (time : ℕ) (who : ι)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (hmesh : quittingTailConditionedAbsorptionWeight roots time ≤ rho)
    (hsmall : Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1) :
    |quittingTailConditionedValue roots value boundary time who -
        quittingRootSuccessorPayoff reward
          (quittingTailConditionedValue roots value boundary (time + 1))
          (quittingTailDiffuseRescaledRoot roots time hcurrent) who| ≤
      (6 * M * Fintype.card ι * rho) *
        quittingRootAbsorptionMass
          (quittingTailDiffuseRescaledRoot roots time hcurrent) := by
  let alpha := quittingTailConditionedAbsorptionWeight roots time
  let total := quittingTailDiffuseRescaledTotal roots time
  let absorption := quittingRootAbsorptionMass
    (quittingTailDiffuseRescaledRoot roots time hcurrent)
  have hbase := abs_conditionedValue_sub_rescaledSuccessorPayoff_le
    (reward := reward) roots value boundary hpolicy hM hreward hconditionedBound
      time hcurrent hnext who
  change |_ - _| ≤ 3 * M * total ^ 2 at hbase
  have halpha0 : 0 ≤ alpha :=
    quittingTailConditionedAbsorptionWeight_nonneg roots time hcurrent
  have hrho0 : 0 ≤ rho := halpha0.trans hmesh
  have htotal0 : 0 ≤ total := by
    unfold total quittingTailDiffuseRescaledTotal
    exact Finset.sum_nonneg fun player _ =>
      quittingTailDiffuseRescaledHazard_nonneg roots time player hcurrent
  have htotalUpper : total ≤ Fintype.card ι * alpha :=
    quittingTailDiffuseRescaledTotal_le_card_mul_conditionedWeight
      roots time hcurrent
  have htotalOne : total ≤ 1 := htotalUpper.trans hsmall
  have hbonferroni :=
    quittingTailDiffuseRescaledTotal_sub_sq_div_two_le_absorptionMass
      roots time hcurrent
  change total - total ^ 2 / 2 ≤ absorption at hbonferroni
  have hhalfTotal : total / 2 ≤ absorption := by
    nlinarith [sq_nonneg total]
  have habsorption0 : 0 ≤ absorption := by
    unfold absorption
    exact quittingRootAbsorptionMass_nonneg _
  have hsquare : total ^ 2 ≤
      2 * (Fintype.card ι * rho) * absorption := by
    have htotalRho : total ≤ Fintype.card ι * rho :=
      htotalUpper.trans (mul_le_mul_of_nonneg_left hmesh (Nat.cast_nonneg _))
    have htotalAbsorption : total ≤ 2 * absorption := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr htotalRho)
      (sub_nonneg.mpr htotalAbsorption)]
  have hcoefficient : 0 ≤ 3 * M := mul_nonneg (by norm_num) hM
  calc
    |_ - _| ≤ 3 * M * total ^ 2 := hbase
    _ ≤ 3 * M * (2 * (Fintype.card ι * rho) * absorption) :=
      mul_le_mul_of_nonneg_left hsquare hcoefficient
    _ = (6 * M * Fintype.card ι * rho) * absorption := by ring

/-- A source spectator needs no singleton-boundary estimate for its Continue
endpoint.  Diffuse rescaling keeps the player at literal Never, so its
prescribed endpoint is pure Continue and the joint policy error is already a
deleted-clock error for that player. -/
theorem rescaledContinuePayoff_le_conditionedValue_add_jointCharge_of_source_pure_false
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M rho : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (time : ℕ) (who : ι)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (hinactive : roots time who = PMF.pure false)
    (hmesh : quittingTailConditionedAbsorptionWeight roots time ≤ rho)
    (hsmall : Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1) :
    quittingStationaryFixedOpponentsContinueReward reward
          (quittingTailDiffuseRescaledRoot roots time hcurrent) who +
        quittingStationaryFixedOpponentsContinueMass
            (quittingTailDiffuseRescaledRoot roots time hcurrent) who *
          quittingTailConditionedValue roots value boundary (time + 1) who ≤
      quittingTailConditionedValue roots value boundary time who +
        (6 * M * Fintype.card ι * rho) *
          quittingRootOpponentAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hcurrent) who := by
  let targetRoot := quittingTailDiffuseRescaledRoot roots time hcurrent
  let next := quittingTailConditionedValue roots value boundary (time + 1)
  have htargetInactive : targetRoot who = PMF.pure false :=
    quittingTailDiffuseRescaledRoot_eq_pure_false_of_source_eq_pure_false
      roots time who hcurrent hinactive
  have hsuccessor :
      quittingRootSuccessorPayoff reward next targetRoot who =
        quittingStationaryFixedOpponentsContinueReward reward targetRoot who +
          quittingStationaryFixedOpponentsContinueMass targetRoot who *
            next who := by
    rw [quittingRootSuccessorPayoff_eq_endpointMix, htargetInactive]
    simp [PMF.pure_apply]
    simpa [quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass] using
        quittingRootContinuePayoff_eq_fixedOpponents
          reward (fun _ => targetRoot) who next 0
  have habsorption : quittingRootAbsorptionMass targetRoot =
      quittingRootOpponentAbsorptionMass targetRoot who := by
    unfold quittingRootOpponentAbsorptionMass
    congr 1
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [htargetInactive]
    · simp [Function.update_of_ne hplayer]
  have hpolicyBound :=
    abs_conditionedValue_sub_rescaledSuccessorPayoff_le_jointCharge
      (reward := reward) roots value boundary hpolicy hM hreward
        hconditionedBound time who hcurrent hnext hmesh hsmall
  have hupper := neg_le_of_abs_le hpolicyBound
  dsimp only [targetRoot, next] at hsuccessor habsorption
  rw [hsuccessor, habsorption] at hupper
  linarith

/-- **Compiler for the singleton-tight deleted-complete diffuse branch.**
Every hypothesis is local to the conditioned source chronology.  The target
product path has separated joint-policy and deleted-refusal errors, hence is
an explicit asymptotic approximate Nash profile. -/
theorem conditionedDiffuseRescaledRoots_isεAsymptoticNash_and_approximates
    [Nonempty ι]
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {M rho : ℝ} (hM : 0 ≤ M) (hrho : 0 ≤ rho)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (htight : ∀ who,
      boundary who = quittingSoloBaseline reward who)
    (hmesh : ∀ time,
      quittingTailConditionedAbsorptionWeight roots time ≤ rho)
    (hsmall : ∀ time, Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1)
    (hhalf : ∀ time,
      quittingTailConditionedAbsorptionWeight roots time ≤ 1 / 2)
    (hdeletedComplete : ∀ who start,
      ¬Summable (fun offset =>
        quittingTailConditionedOpponentWeight roots (start + offset) who)) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        ((6 * M * Fintype.card ι * rho) +
          (6 * M * Fintype.card ι * rho) +
          ((7 * Fintype.card ι + 16) * M * rho))
        (quittingInfinitePathProfile reward
          (quittingTailDiffuseRescaledRoots roots hpositive)) ∧
      ∀ who,
        |quittingTerminalPayoff reward
            (quittingInfinitePathProfile reward
              (quittingTailDiffuseRescaledRoots roots hpositive)) who -
          quittingTailConditionedValue roots value boundary 0 who| ≤
        6 * M * Fintype.card ι * rho := by
  let policyCoefficient := 6 * M * Fintype.card ι * rho
  let quitError := 6 * M * Fintype.card ι * rho
  let refusalCoefficient := (7 * Fintype.card ι + 16) * M * rho
  let target := quittingTailConditionedValue roots value boundary 0
  let targetRoots := quittingTailDiffuseRescaledRoots roots hpositive
  let targetValue : ℕ → Payoff ι := fun time =>
    quittingTailConditionedValue roots value boundary time
  have hopponentSurvival : ∀ who start,
      Tendsto (quittingOpponentSurvivalWeight targetRoots who start)
        atTop (nhds 0) := by
    intro who start
    exact tendsto_zero_opponentSurvivalWeight_quittingTailDiffuseRescaledRoots
      roots hpositive hsmall who start (hdeletedComplete who start)
  have hjointSurvival : ∀ start,
      Tendsto (quittingJointSurvivalWeight targetRoots start)
        atTop (nhds 0) := by
    intro start
    let who : ι := Classical.choice (inferInstance : Nonempty ι)
    exact squeeze_zero
      (fun fuel => quittingJointSurvivalWeight_nonneg targetRoots start fuel)
      (fun fuel =>
        quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
          targetRoots who start fuel)
      (hopponentSurvival who start)
  let certificate : QuittingInfinitePathJointPolicySeparatedErrorCertificate
      reward target policyCoefficient quitError refusalCoefficient M :=
    { roots := targetRoots
      value := targetValue
      value_zero := rfl
      joint_survival := hjointSurvival
      opponent_survival := hopponentSurvival
      value_bound := hconditionedBound
      policy_error := by
        intro time who
        exact abs_conditionedValue_sub_rescaledSuccessorPayoff_le_jointCharge
          (reward := reward) roots value boundary hpolicy hM hreward
            hconditionedBound time who (hpositive time) (hpositive (time + 1))
              (hmesh time) (hsmall time)
      quit_le := by
        intro time who
        have hquit :=
          quittingStationaryFixedOpponentsQuitValue_rescaledRoot_le_conditionedValue_add_of_nash
            (reward := reward) roots value boundary hpolicy hnash time who hM
              hreward (hpositive time) (htight who) (hsmall time)
        change _ ≤ targetValue time who + quitError
        dsimp only [targetValue, quitError]
        calc
          _ ≤ quittingTailConditionedValue roots value boundary time who +
              6 * M * Fintype.card ι *
                quittingTailConditionedAbsorptionWeight roots time := hquit
          _ ≤ quittingTailConditionedValue roots value boundary time who +
              6 * M * Fintype.card ι * rho := by
            have hcoefficient : 0 ≤ 6 * M * (Fintype.card ι : ℝ) := by
              positivity
            simpa [add_comm] using
              (add_le_add_left
                (mul_le_mul_of_nonneg_left (hmesh time) hcoefficient)
                (quittingTailConditionedValue roots value boundary time who))
      continue_le := by
        intro time who
        have hcontinue :=
          rescaledContinuePayoff_le_conditionedValue_add_deletedCharge
            (reward := reward) roots value boundary hpolicy hnash time who hM
              hreward (hconditionedBound (time + 1) who) (hpositive time)
                (hpositive (time + 1)) (htight who) (hsmall time) (hhalf time)
        change _ ≤ targetValue time who + refusalCoefficient *
          (1 - quittingStationaryFixedOpponentsContinueMass
            (targetRoots time) who)
        have hopponentIdentity :
            1 - quittingStationaryFixedOpponentsContinueMass
                (targetRoots time) who =
              quittingRootOpponentAbsorptionMass (targetRoots time) who := by
          unfold quittingStationaryFixedOpponentsContinueMass
            quittingFixedOpponentsContinueMass
            quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
          ring
        rw [hopponentIdentity]
        dsimp only [targetRoots, targetValue, refusalCoefficient]
        change _ ≤ _ + _ *
          quittingRootOpponentAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who
        calc
          _ ≤ quittingTailConditionedValue roots value boundary time who +
              (7 * Fintype.card ι + 16) * M *
                quittingTailConditionedAbsorptionWeight roots time *
                quittingRootOpponentAbsorptionMass
                  (quittingTailDiffuseRescaledRoot roots time
                    (hpositive time)) who := hcontinue
          _ ≤ quittingTailConditionedValue roots value boundary time who +
              ((7 * Fintype.card ι + 16) * M * rho) *
                quittingRootOpponentAbsorptionMass
                  (quittingTailDiffuseRescaledRoot roots time
                    (hpositive time)) who := by
            have hfactor : 0 ≤
                (7 * Fintype.card ι + 16) * M := by positivity
            have hcharge := mul_le_mul_of_nonneg_left (hmesh time) hfactor
            have hopponent0 := quittingRootAbsorptionMass_nonneg
              (Function.update
                (quittingTailDiffuseRescaledRoot roots time (hpositive time))
                who (PMF.pure false))
            gcongr }
  have hpolicyCoefficient : 0 ≤ policyCoefficient := by
    unfold policyCoefficient
    positivity
  have hquitError : 0 ≤ quitError := by
    unfold quitError
    positivity
  have hrefusal : 0 ≤ refusalCoefficient := by
    unfold refusalCoefficient
    positivity
  simpa [certificate, policyCoefficient, quitError, refusalCoefficient,
    target, targetRoots] using
    (certificate.isεAsymptoticNash_and_approximates reward target
      hpolicyCoefficient hquitError hrefusal hM hreward)

/-- **Proper-face diffuse compiler.**  A late source row may contain both
singleton-tight active players and literal-Never spectators.  Tight players
use the deleted-clock strategic estimate.  Spectators remain pure Continue
after rescaling, so their Continue endpoint is controlled by the joint
policy estimate; only their pure-Quit endpoint must be supplied separately.

This is the exact compiler interface for the proper singleton-tight face:
strict plateau coordinates cost no Continue error and expose only an
immediate-Quit obstruction. -/
theorem
    conditionedDiffuseRescaledRoots_isεAsymptoticNash_and_approximates_of_tight_or_inactive
    [Nonempty ι]
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {M rho quitError : ℝ} (hM : 0 ≤ M) (hrho : 0 ≤ rho)
    (hquitError : 0 ≤ quitError)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (htightOrInactive : ∀ time who,
      boundary who = quittingSoloBaseline reward who ∨
        roots time who = PMF.pure false)
    (hquit_le : ∀ time who,
      quittingStationaryFixedOpponentsQuitValue reward
          (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who ≤
        quittingTailConditionedValue roots value boundary time who +
          quitError)
    (hmesh : ∀ time,
      quittingTailConditionedAbsorptionWeight roots time ≤ rho)
    (hsmall : ∀ time, Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1)
    (hhalf : ∀ time,
      quittingTailConditionedAbsorptionWeight roots time ≤ 1 / 2)
    (hdeletedComplete : ∀ who start,
      ¬Summable (fun offset =>
        quittingTailConditionedOpponentWeight roots (start + offset) who)) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        ((6 * M * Fintype.card ι * rho) + quitError +
          ((13 * Fintype.card ι + 16) * M * rho))
        (quittingInfinitePathProfile reward
          (quittingTailDiffuseRescaledRoots roots hpositive)) ∧
      ∀ who,
        |quittingTerminalPayoff reward
            (quittingInfinitePathProfile reward
              (quittingTailDiffuseRescaledRoots roots hpositive)) who -
          quittingTailConditionedValue roots value boundary 0 who| ≤
        6 * M * Fintype.card ι * rho := by
  let policyCoefficient := 6 * M * Fintype.card ι * rho
  let refusalCoefficient := (13 * Fintype.card ι + 16) * M * rho
  let target := quittingTailConditionedValue roots value boundary 0
  let targetRoots := quittingTailDiffuseRescaledRoots roots hpositive
  let targetValue : ℕ → Payoff ι := fun time =>
    quittingTailConditionedValue roots value boundary time
  have hopponentSurvival : ∀ who start,
      Tendsto (quittingOpponentSurvivalWeight targetRoots who start)
        atTop (nhds 0) := by
    intro who start
    exact tendsto_zero_opponentSurvivalWeight_quittingTailDiffuseRescaledRoots
      roots hpositive hsmall who start (hdeletedComplete who start)
  have hjointSurvival : ∀ start,
      Tendsto (quittingJointSurvivalWeight targetRoots start)
        atTop (nhds 0) := by
    intro start
    let who : ι := Classical.choice (inferInstance : Nonempty ι)
    exact squeeze_zero
      (fun fuel => quittingJointSurvivalWeight_nonneg targetRoots start fuel)
      (fun fuel =>
        quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
          targetRoots who start fuel)
      (hopponentSurvival who start)
  have hpolicy_le_refusal :
      6 * M * Fintype.card ι * rho ≤
        (13 * Fintype.card ι + 16) * M * rho := by
    have hMrho : 0 ≤ M * rho := mul_nonneg hM hrho
    calc
      6 * M * Fintype.card ι * rho =
          (6 * Fintype.card ι) * (M * rho) := by ring
      _ ≤ (13 * Fintype.card ι + 16) * (M * rho) := by
        exact mul_le_mul_of_nonneg_right (by
          have hcard : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
          linarith) hMrho
      _ = (13 * Fintype.card ι + 16) * M * rho := by ring
  let certificate : QuittingInfinitePathJointPolicySeparatedErrorCertificate
      reward target policyCoefficient quitError refusalCoefficient M :=
    { roots := targetRoots
      value := targetValue
      value_zero := rfl
      joint_survival := hjointSurvival
      opponent_survival := hopponentSurvival
      value_bound := hconditionedBound
      policy_error := by
        intro time who
        exact abs_conditionedValue_sub_rescaledSuccessorPayoff_le_jointCharge
          (reward := reward) roots value boundary hpolicy hM hreward
            hconditionedBound time who (hpositive time) (hpositive (time + 1))
              (hmesh time) (hsmall time)
      quit_le := by
        intro time who
        exact hquit_le time who
      continue_le := by
        intro time who
        have hopponentIdentity :
            1 - quittingStationaryFixedOpponentsContinueMass
                (targetRoots time) who =
              quittingRootOpponentAbsorptionMass (targetRoots time) who := by
          unfold quittingStationaryFixedOpponentsContinueMass
            quittingFixedOpponentsContinueMass
            quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
          ring
        rw [hopponentIdentity]
        rcases htightOrInactive time who with htight | hinactive
        · have hcontinue :=
            rescaledContinuePayoff_le_conditionedValue_add_deletedCharge
              (reward := reward) roots value boundary hpolicy hnash time who hM
                hreward (hconditionedBound (time + 1) who) (hpositive time)
                  (hpositive (time + 1)) htight (hsmall time) (hhalf time)
          dsimp only [targetRoots, targetValue, refusalCoefficient]
          change _ ≤ _ + _ *
            quittingRootOpponentAbsorptionMass
              (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who
          calc
            _ ≤ quittingTailConditionedValue roots value boundary time who +
                (7 * Fintype.card ι + 16) * M *
                  quittingTailConditionedAbsorptionWeight roots time *
                  quittingRootOpponentAbsorptionMass
                    (quittingTailDiffuseRescaledRoot roots time
                      (hpositive time)) who := hcontinue
            _ ≤ quittingTailConditionedValue roots value boundary time who +
                ((7 * Fintype.card ι + 16) * M * rho) *
                  quittingRootOpponentAbsorptionMass
                    (quittingTailDiffuseRescaledRoot roots time
                      (hpositive time)) who := by
              have hfactor : 0 ≤ (7 * Fintype.card ι + 16) * M := by
                positivity
              have hcharge := mul_le_mul_of_nonneg_left (hmesh time) hfactor
              have hopponent0 := quittingRootAbsorptionMass_nonneg
                (Function.update
                  (quittingTailDiffuseRescaledRoot roots time (hpositive time))
                  who (PMF.pure false))
              gcongr
            _ ≤ quittingTailConditionedValue roots value boundary time who +
                ((13 * Fintype.card ι + 16) * M * rho) *
                  quittingRootOpponentAbsorptionMass
                    (quittingTailDiffuseRescaledRoot roots time
                      (hpositive time)) who := by
              have hopponent0 := quittingRootAbsorptionMass_nonneg
                (Function.update
                  (quittingTailDiffuseRescaledRoot roots time (hpositive time))
                  who (PMF.pure false))
              have hMrho : 0 ≤ M * rho := mul_nonneg hM hrho
              have hcoefficient :
                  (7 * Fintype.card ι + 16) * M * rho ≤
                    (13 * Fintype.card ι + 16) * M * rho := by
                calc
                  (7 * Fintype.card ι + 16) * M * rho =
                      (7 * Fintype.card ι + 16) * (M * rho) := by ring
                  _ ≤ (13 * Fintype.card ι + 16) * (M * rho) := by
                    exact mul_le_mul_of_nonneg_right (by
                      have hcard : 0 ≤ (Fintype.card ι : ℝ) :=
                        Nat.cast_nonneg _
                      linarith) hMrho
                  _ = (13 * Fintype.card ι + 16) * M * rho := by ring
              gcongr
        · have hcontinue :=
            rescaledContinuePayoff_le_conditionedValue_add_jointCharge_of_source_pure_false
              (reward := reward) roots value boundary hpolicy hM hreward
                hconditionedBound time who (hpositive time)
                  (hpositive (time + 1)) hinactive (hmesh time) (hsmall time)
          dsimp only [targetRoots, targetValue, refusalCoefficient]
          change _ ≤ _ + _ *
            quittingRootOpponentAbsorptionMass
              (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who
          calc
            _ ≤ quittingTailConditionedValue roots value boundary time who +
                (6 * M * Fintype.card ι * rho) *
                  quittingRootOpponentAbsorptionMass
                    (quittingTailDiffuseRescaledRoot roots time
                      (hpositive time)) who := hcontinue
            _ ≤ quittingTailConditionedValue roots value boundary time who +
                ((13 * Fintype.card ι + 16) * M * rho) *
                  quittingRootOpponentAbsorptionMass
                    (quittingTailDiffuseRescaledRoot roots time
                      (hpositive time)) who := by
              have hopponent0 := quittingRootAbsorptionMass_nonneg
                (Function.update
                  (quittingTailDiffuseRescaledRoot roots time (hpositive time))
                  who (PMF.pure false))
              gcongr }
  have hpolicyCoefficient : 0 ≤ policyCoefficient := by
    unfold policyCoefficient
    positivity
  have hrefusal : 0 ≤ refusalCoefficient := by
    unfold refusalCoefficient
    positivity
  simpa [certificate, policyCoefficient, refusalCoefficient, target,
    targetRoots] using
    (certificate.isεAsymptoticNash_and_approximates reward target
      hpolicyCoefficient hquitError hrefusal hM hreward)

end GameTheory
