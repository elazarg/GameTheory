/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryConditioning
import UniformEquilibrium.Quitting.AbsorptionPath.RealizedMarkedAbsorptionCylinder
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium

/-!
# Product-root purification of a conditioned quitting chronology

Conditioning a quitting tail on eventual absorption gives an exact
state-matched affine chronology, but its one-stage absorbing law is the old
product law conditioned on a nonempty quitter coalition and then assigned a
new total hazard.  This file identifies exactly when that row remains a
product root.

The single-owner branch is flexible: its conditional absorbing law is a
point mass, so its total hazard may be changed freely.  The genuinely
multi-owner branch is rigid.  Once two owners have positive quitting
probability, the conditional nonempty-coalition law determines every
Bernoulli marginal.  Hence it also determines the total absorption mass and
cannot be assigned the larger conditioned hazard unless the remaining
eventual-absorption probability was already one.

This is a strategic purification obstruction, not merely a failure of a
particular construction.  It says that a positive phantom boundary can be
removed row by row inside ordinary independent play only on singleton-support
rows.  Multi-owner rows require a chronological chattering or public
correlation argument that changes the coalition law approximately rather
than an exact one-row replacement.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A product root realizes the source root's conditional absorbing law at
the new total scale `scale`.  The division-free form avoids choosing a
separate probability distribution on nonempty coalitions. -/
def IsQuittingConditionedProductPurification
    (source target : ι → PMF Bool) (scale : ℝ) : Prop :=
  ∀ coalition : Finset ι, coalition.Nonempty →
    scale * quittingRootCoalitionMass target coalition =
      quittingRootCoalitionMass source coalition

/-- The rescaling identity determines the target's total absorption mass. -/
theorem quittingRootAbsorptionMass_mul_eq_of_conditionedProductPurification
    (source target : ι → PMF Bool) (scale : ℝ)
    (hpure : IsQuittingConditionedProductPurification source target scale) :
    scale * quittingRootAbsorptionMass target =
      quittingRootAbsorptionMass source := by
  unfold quittingRootAbsorptionMass
  rw [← quittingRootCoalitionMass_sum_nonempty target,
    ← quittingRootCoalitionMass_sum_nonempty source,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coalition hcoalition
  exact hpure coalition <| Finset.nonempty_iff_ne_empty.mpr
    (Finset.mem_erase.mp hcoalition).1

omit [DecidableEq ι] in
/-- Positive all-Continue mass makes every marginal continuation probability
strictly positive. -/
theorem quittingRoot_continueProbability_pos_of_continueMass_pos
    (root : ι → PMF Bool)
    (hcontinue : 0 < quittingStationaryContinueMass root) (who : ι) :
    0 < (root who false).toReal := by
  have hproduct : 0 < ∏ player, (root player false).toReal := by
    simpa [quittingStationaryContinueMass_eq_prod_continueProbability]
      using hcontinue
  have hnonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  by_contra hnot
  have hzero : (root who false).toReal = 0 :=
    le_antisymm (le_of_not_gt hnot) hnonneg
  have hproductZero : (∏ player, (root player false).toReal) = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ who) hzero
  rw [hproductZero] at hproduct
  exact (lt_irrefl 0) hproduct

/-- The exact-coalition odds identity.  It is the division-free statement
that adjoining `other` multiplies a singleton coalition's mass by the odds
of `other` quitting. -/
theorem quittingRootCoalitionMass_pair_mul_continue_eq_singleton_mul_quit
    (root : ι → PMF Bool) {owner other : ι} (hne : owner ≠ other) :
    quittingRootCoalitionMass root {owner, other} *
        (root other false).toReal =
      quittingRootCoalitionMass root {owner} *
        (root other true).toReal := by
  classical
  have hcomplement : ({owner}ᶜ : Finset ι) =
      insert other ({owner, other}ᶜ : Finset ι) := by
    ext player
    simp only [Finset.mem_compl, Finset.mem_singleton,
      Finset.mem_insert]
    constructor
    · intro hplayer
      by_cases hother : player = other
      · exact Or.inl hother
      · exact Or.inr (fun h ↦ h.elim hplayer hother)
    · rintro (rfl | hplayer)
      · exact hne.symm
      · exact fun h ↦ hplayer (Or.inl h)
  simp only [quittingRootCoalitionMass, quittingRootQuitRates,
    coalitionMass]
  rw [hcomplement]
  simp only [Finset.prod_singleton]
  have hproduct :
      (∏ player ∈ insert other ({owner, other}ᶜ : Finset ι),
          (1 - (root player true).toReal)) =
        (1 - (root other true).toReal) *
          ∏ player ∈ ({owner, other}ᶜ : Finset ι),
            (1 - (root player true).toReal) := by
    rw [Finset.prod_insert]
    simp
  have hpairProduct :
      (∏ player ∈ ({owner, other} : Finset ι),
          (root player true).toReal) =
        (root owner true).toReal * (root other true).toReal := by
    simp [hne]
  rw [hproduct]
  rw [hpairProduct]
  rw [pmfBool_false_toReal]
  ring

/-- A positive marginal quit rate has positive singleton-coalition mass when
the whole row has positive all-Continue mass. -/
theorem quittingRootCoalitionMass_singleton_pos_of_continueMass_pos
    (root : ι → PMF Bool) (owner : ι)
    (hcontinue : 0 < quittingStationaryContinueMass root)
    (hquit : 0 < (root owner true).toReal) :
    0 < quittingRootCoalitionMass root {owner} := by
  have houtside : 0 <
      ∏ player ∈ ({owner}ᶜ : Finset ι),
        (1 - (root player true).toReal) := by
    apply Finset.prod_pos
    intro player _
    rw [← pmfBool_false_toReal]
    exact quittingRoot_continueProbability_pos_of_continueMass_pos
      root hcontinue player
  unfold quittingRootCoalitionMass quittingRootQuitRates coalitionMass
  simp only [Finset.prod_singleton]
  exact mul_pos hquit houtside

/-- **Multi-owner conditional-law rigidity.**  On a row with positive
all-Continue mass and two positive quit marginals, the conditional law on
nonempty coalitions determines the entire product root.  Consequently an
exact conditional purification cannot change its total absorption scale. -/
theorem scale_eq_one_of_conditionedProductPurification_two_active
    (source target : ι → PMF Bool) (scale : ℝ)
    (hpure : IsQuittingConditionedProductPurification source target scale)
    (hcontinue : 0 < quittingStationaryContinueMass source)
    {first second : ι} (hne : first ≠ second)
    (hfirst : 0 < (source first true).toReal)
    (hsecond : 0 < (source second true).toReal) :
    scale = 1 := by
  have hfirstMass : 0 < quittingRootCoalitionMass source {first} :=
    quittingRootCoalitionMass_singleton_pos_of_continueMass_pos
      source first hcontinue hfirst
  have hsecondMass : 0 < quittingRootCoalitionMass source {second} :=
    quittingRootCoalitionMass_singleton_pos_of_continueMass_pos
      source second hcontinue hsecond
  have hcoordinate (anchor player : ι) (hanchorPlayer : anchor ≠ player)
      (hanchorMass : 0 < quittingRootCoalitionMass source {anchor}) :
      (target player true).toReal = (source player true).toReal := by
    have htargetOdds :=
      quittingRootCoalitionMass_pair_mul_continue_eq_singleton_mul_quit
        target hanchorPlayer
    have hsourceOdds :=
      quittingRootCoalitionMass_pair_mul_continue_eq_singleton_mul_quit
        source hanchorPlayer
    have hscaledOdds :
        quittingRootCoalitionMass source {anchor, player} *
            (target player false).toReal =
          quittingRootCoalitionMass source {anchor} *
            (target player true).toReal := by
      calc
        quittingRootCoalitionMass source {anchor, player} *
              (target player false).toReal =
            (scale * quittingRootCoalitionMass target {anchor, player}) *
              (target player false).toReal := by
                rw [hpure {anchor, player} (by simp)]
        _ = scale *
              (quittingRootCoalitionMass target {anchor, player} *
                (target player false).toReal) := by ring
        _ = scale *
              (quittingRootCoalitionMass target {anchor} *
                (target player true).toReal) := by rw [htargetOdds]
        _ = (scale * quittingRootCoalitionMass target {anchor}) *
              (target player true).toReal := by ring
        _ = quittingRootCoalitionMass source {anchor} *
              (target player true).toReal := by
                rw [hpure {anchor} (by simp)]
    have hpairNonneg :
        0 ≤ quittingRootCoalitionMass source {anchor, player} :=
      by
        unfold quittingRootCoalitionMass quittingRootQuitRates coalitionMass
        apply mul_nonneg
        · exact Finset.prod_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
        · exact Finset.prod_nonneg fun who _ ↦
            sub_nonneg.mpr (hazardOfRoot_le_one source who)
    rw [pmfBool_false_toReal] at hscaledOdds hsourceOdds
    nlinarith
  have hhazard : hazardOfRoot target = hazardOfRoot source := by
    funext player
    unfold hazardOfRoot
    by_cases hplayer : player = first
    · subst player
      exact hcoordinate second first hne.symm hsecondMass
    · exact hcoordinate first player (Ne.symm hplayer) hfirstMass
  have hroot : target = source := by
    funext player
    apply PMF.ext
    intro action
    apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    cases action with
    | true => exact congrFun hhazard player
    | false =>
        rw [pmfBool_false_toReal, pmfBool_false_toReal]
        exact congrArg (fun probability : ℝ ↦ 1 - probability)
          (congrFun hhazard player)
  have habsorptionPositive : 0 < quittingRootAbsorptionMass source := by
    unfold quittingRootAbsorptionMass
    have hstrict : quittingStationaryContinueMass source < 1 := by
      have hfalse := pmfBool_false_toReal (source first)
      have hfalseLt : (source first false).toReal < 1 := by linarith
      let remainder := ∏ player ∈ (Finset.univ.erase first),
        (source player false).toReal
      have hremainderNonneg : 0 ≤ remainder :=
        Finset.prod_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
      have hremainderLe : remainder ≤ 1 :=
        Finset.prod_le_one (fun _ _ ↦ ENNReal.toReal_nonneg) fun player _ ↦ by
          simpa using ENNReal.toReal_mono ENNReal.one_ne_top
            (PMF.coe_le_one (source player) false)
      have hfactor : quittingStationaryContinueMass source =
          (source first false).toReal * remainder := by
        rw [quittingStationaryContinueMass_eq_prod_continueProbability]
        exact (Finset.mul_prod_erase Finset.univ
          (fun player ↦ (source player false).toReal)
          (Finset.mem_univ first)).symm
      have hfactorLe :
          (source first false).toReal * remainder ≤
            (source first false).toReal := by
        nlinarith [show 0 ≤ (source first false).toReal from
          ENNReal.toReal_nonneg]
      rw [hfactor]
      linarith
    linarith
  have hscale :=
    quittingRootAbsorptionMass_mul_eq_of_conditionedProductPurification
      source target scale hpure
  rw [hroot] at hscale
  nlinarith

/-- On a solo root, every nonempty coalition except the owner's singleton
has zero mass.  This is the atomic side of the purification dichotomy. -/
theorem quittingRootCoalitionMass_solo_of_nonempty
    (owner : ι) (hazard : PMF Bool) (coalition : Finset ι)
    (hcoalition : coalition.Nonempty) :
    quittingRootCoalitionMass
        (quittingSoloStationaryRoot owner hazard) coalition =
      if coalition = {owner} then (hazard true).toReal else 0 := by
  split_ifs with hsingleton
  · subst coalition
    unfold quittingRootCoalitionMass quittingRootQuitRates coalitionMass
    simp only [Finset.prod_singleton]
    have houtside :
        (∏ player ∈ ({owner}ᶜ : Finset ι),
          (1 - ((quittingSoloStationaryRoot owner hazard player) true).toReal)) =
            1 := by
      apply Finset.prod_eq_one
      intro player hplayer
      have hplayerOwner : player ≠ owner := by simpa using hplayer
      simp [quittingSoloStationaryRoot, hplayerOwner]
    rw [houtside, mul_one]
    simp [quittingSoloStationaryRoot]
  · have hneOwner : ∃ player ∈ coalition, player ≠ owner := by
      by_contra hnot
      have hnot' : ∀ player ∈ coalition, player = owner := by
        intro player hplayer
        by_contra hplayerOwner
        exact hnot ⟨player, hplayer, hplayerOwner⟩
      have hsubset : coalition ⊆ {owner} := by
        intro player hplayer
        simp [hnot' player hplayer]
      obtain ⟨player, hplayer⟩ := hcoalition
      have hownerMem : owner ∈ coalition := by
        simpa [hnot' player hplayer] using hplayer
      have hreverse : {owner} ⊆ coalition := by simpa
      exact hsingleton (Finset.Subset.antisymm hsubset hreverse)
    obtain ⟨player, hplayer, hplayerOwner⟩ := hneOwner
    unfold quittingRootCoalitionMass coalitionMass
    have hzero : quittingRootQuitRates
        (quittingSoloStationaryRoot owner hazard) player = 0 := by
      simp [quittingRootQuitRates, quittingSoloStationaryRoot,
        hplayerOwner]
    rw [Finset.prod_eq_zero hplayer hzero, zero_mul]

/-- **Atomic exact purification.**  A singleton-support product root can be
assigned any larger or smaller admissible total hazard while preserving its
conditional nonempty-coalition law exactly. -/
theorem conditionedProductPurification_solo
    (owner : ι) (hazard : PMF Bool) (scale : ℝ)
    (hscale : 0 < scale)
    (hratioOne : (hazard true).toReal / scale ≤ 1) :
    IsQuittingConditionedProductPurification
      (quittingSoloStationaryRoot owner hazard)
      (quittingSoloStationaryRoot owner
        (quittingHazardCoin ((hazard true).toReal / scale)
          (div_nonneg ENNReal.toReal_nonneg hscale.le) hratioOne))
      scale := by
  intro coalition hcoalition
  rw [quittingRootCoalitionMass_solo_of_nonempty
      owner hazard coalition hcoalition,
    quittingRootCoalitionMass_solo_of_nonempty owner
      (quittingHazardCoin ((hazard true).toReal / scale)
        (div_nonneg ENNReal.toReal_nonneg hscale.le) hratioOne)
      coalition hcoalition]
  split_ifs
  · rw [quittingHazardCoin_true_toReal]
    field_simp [hscale.ne']
  · ring

/-- Conditional absorbing delivery at a solo root is exactly the owner's
singleton reward, independently of the original hazard. -/
theorem quittingRootConditionalAbsorbingDelivery_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (habsorption : 0 < (hazard true).toReal) :
    quittingRootConditionalAbsorbingDelivery reward
        (quittingSoloStationaryRoot owner hazard) =
      quittingSoloReward reward owner := by
  funext who
  unfold quittingRootConditionalAbsorbingDelivery
  rw [quittingRootAbsorbingContribution_solo,
    quittingRootAbsorptionMass_soloStationaryRoot]
  field_simp [habsorption.ne']

/-- **Atomic physical chronology compiler.**  At a singleton-support stage,
conditioning on eventual absorption is realized by an ordinary product root
with the rescaled hazard.  The conditioned values obey the exact Bellman
equation for that root, and its nonempty-coalition law is the exact
conditional rescaling of the original row.

No endpoint-Nash conclusion is included: inactive players' quitting
inequalities need not survive conditioning without an additional punishment
or sequential-perfection argument. -/
theorem exists_conditionedSingletonProductRoot_step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (time : ℕ) (owner : ι) (hazard : PMF Bool)
    (hroot : roots time = quittingSoloStationaryRoot owner hazard)
    (habsorption : 0 < quittingRootAbsorptionMass (roots time))
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1)) :
    ∃ conditionedRoot : ι → PMF Bool,
      IsQuittingConditionedProductPurification
          (roots time) conditionedRoot
          (quittingTailEventualAbsorption roots time) ∧
        quittingTailConditionedValue roots value boundary time =
          quittingRootSuccessorPayoff reward
            (quittingTailConditionedValue roots value boundary (time + 1))
            conditionedRoot := by
  let scale := quittingTailEventualAbsorption roots time
  let ratio := (hazard true).toReal / scale
  have hweight : quittingTailConditionedAbsorptionWeight roots time = ratio := by
    unfold quittingTailConditionedAbsorptionWeight ratio scale
    rw [hroot, quittingRootAbsorptionMass_soloStationaryRoot]
  have hweights := quittingTailConditionedWeights_mem_unitInterval
    roots time hnext.le hcurrent
  have hratioNonneg : 0 ≤ ratio := by
    rw [← hweight]
    exact hweights.1.1
  have hratioOne : ratio ≤ 1 := by
    rw [← hweight]
    exact hweights.1.2
  let conditionedRoot := quittingSoloStationaryRoot owner
    (quittingHazardCoin ratio hratioNonneg hratioOne)
  refine ⟨conditionedRoot, ?_, ?_⟩
  · rw [hroot]
    exact conditionedProductPurification_solo owner hazard scale
      hcurrent hratioOne
  · have hhazardPositive : 0 < (hazard true).toReal := by
      rw [hroot, quittingRootAbsorptionMass_soloStationaryRoot]
        at habsorption
      exact habsorption
    have hdelivery :
        quittingRootConditionalAbsorbingDelivery reward (roots time) =
          quittingSoloReward reward owner := by
      rw [hroot]
      exact quittingRootConditionalAbsorbingDelivery_solo
        reward owner hazard hhazardPositive
    have hcontinuation :
        quittingTailConditionedContinuationWeight roots time = 1 - ratio := by
      have hsum := quittingTailConditionedWeights_add roots time hcurrent
      rw [hweight] at hsum
      linarith
    have hstep := quittingTailConditionedValue_step
      roots value boundary hpolicy time habsorption hcurrent hnext
    rw [quittingRootSuccessorPayoff_solo]
    funext who
    have hstepWho := congrFun hstep who
    change quittingTailConditionedValue roots value boundary time who = _
    simp only [quittingHazardCoin_true_toReal,
      quittingHazardCoin_false_toReal]
    rw [hweight, hdelivery, hcontinuation] at hstepWho
    exact hstepWho

/-- Rowwise atomic purification assembles into one ordinary product-root
sequence carrying the entire conditioned Bellman chronology.  This closes
physical realization of the conditioned path when every source row has
singleton support; strategic endpoint inequalities remain the separate seams
displayed below. -/
theorem exists_conditionedSingletonProductRoot_path
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (owner : ℕ → ι) (hazard : ℕ → PMF Bool)
    (hroot : ∀ time,
      roots time = quittingSoloStationaryRoot (owner time) (hazard time))
    (habsorption : ∀ time,
      0 < quittingRootAbsorptionMass (roots time))
    (heventual : ∀ time,
      0 < quittingTailEventualAbsorption roots time) :
    ∃ conditionedRoots : ℕ → ι → PMF Bool,
      ∀ time,
        IsQuittingConditionedProductPurification
            (roots time) (conditionedRoots time)
            (quittingTailEventualAbsorption roots time) ∧
          quittingTailConditionedValue roots value boundary time =
            quittingRootSuccessorPayoff reward
              (quittingTailConditionedValue roots value boundary (time + 1))
              (conditionedRoots time) := by
  have hstage : ∀ time, ∃ conditionedRoot : ι → PMF Bool,
      IsQuittingConditionedProductPurification
          (roots time) conditionedRoot
          (quittingTailEventualAbsorption roots time) ∧
        quittingTailConditionedValue roots value boundary time =
          quittingRootSuccessorPayoff reward
            (quittingTailConditionedValue roots value boundary (time + 1))
            conditionedRoot := by
    intro time
    exact exists_conditionedSingletonProductRoot_step
      reward roots value boundary hpolicy time (owner time) (hazard time)
        (hroot time) (habsorption time) (heventual time) (heventual (time + 1))
  choose conditionedRoots hconditionedRoots using hstage
  exact ⟨conditionedRoots, hconditionedRoots⟩

/-- The active owner's exact strategic seam after atomic purification.  A
positive interior conditioned hazard can be support-perfect only when the
conditioned successor remains pinned to the owner's singleton payoff. -/
theorem quittingRootEndpointDifference_conditionedSolo_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (ratio : ℝ) (hratioNonneg : 0 ≤ ratio)
    (hratioOne : ratio ≤ 1) (tail : Payoff ι) :
    quittingRootEndpointDifference reward tail
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin ratio hratioNonneg hratioOne)) owner =
      quittingSoloReward reward owner owner - tail owner := by
  unfold quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_soloStationaryRoot_owner,
    quittingRootContinuePayoff_soloStationaryRoot_owner]

/-- The inactive player's exact strategic seam after atomic purification.
This is the sharp residual that a diffuse singleton-chattering or punishment
argument must control; exact physical Bellman realization alone gives no sign
for it. -/
theorem quittingRootEndpointDifference_conditionedSolo_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner)
    (ratio : ℝ) (hratioNonneg : 0 ≤ ratio) (hratioOne : ratio ≤ 1)
    (tail : Payoff ι) :
    quittingRootEndpointDifference reward tail
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin ratio hratioNonneg hratioOne)) other =
      (1 - ratio) *
          (quittingSoloReward reward other other - tail other) +
        ratio *
          (quittingSingletonCollisionReward reward owner other -
            quittingSoloReward reward owner other) := by
  unfold quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_soloStationaryRoot_other reward hne,
    quittingRootContinuePayoff_soloStationaryRoot_other reward hne,
    quittingHazardCoin_true_toReal,
    quittingHazardCoin_false_toReal]
  ring

/-- **Phantom-boundary multi-owner obstruction.**  If a conditioned row is
realized exactly by another product root and the source row has two active
owners, then the tail's remaining eventual-absorption probability is already
one.  Thus a genuine positive phantom boundary cannot be removed by exact
rowwise product-root purification on a multi-owner stage. -/
theorem quittingTailEventualAbsorption_eq_one_of_two_active_purification
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (target : ι → PMF Bool)
    (hpure : IsQuittingConditionedProductPurification
      (roots time) target (quittingTailEventualAbsorption roots time))
    (hcontinue : 0 < quittingStationaryContinueMass (roots time))
    {first second : ι} (hne : first ≠ second)
    (hfirst : 0 < (roots time first true).toReal)
    (hsecond : 0 < (roots time second true).toReal) :
    quittingTailEventualAbsorption roots time = 1 :=
  scale_eq_one_of_conditionedProductPurification_two_active
    (roots time) target (quittingTailEventualAbsorption roots time)
      hpure hcontinue hne hfirst hsecond

/-- Equivalent no-go form for a genuine phantom-boundary row. -/
theorem no_conditionedProductPurification_of_two_active_phantom
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hphantom : quittingTailEventualAbsorption roots time ≠ 1)
    (hcontinue : 0 < quittingStationaryContinueMass (roots time))
    {first second : ι} (hne : first ≠ second)
    (hfirst : 0 < (roots time first true).toReal)
    (hsecond : 0 < (roots time second true).toReal) :
    ¬ ∃ target : ι → PMF Bool,
      IsQuittingConditionedProductPurification
        (roots time) target (quittingTailEventualAbsorption roots time) := by
  rintro ⟨target, hpure⟩
  exact hphantom <|
    quittingTailEventualAbsorption_eq_one_of_two_active_purification
      roots time target hpure hcontinue hne hfirst hsecond

end GameTheory
