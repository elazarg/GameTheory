/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.CollisionConcentration
import UniformEquilibrium.Quitting.AbsorptionPath.MarkedAbsorptionCylinder
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryLimitGeometry
import UniformEquilibrium.Quitting.Projective.AnalyticPacket

/-!
# Normalized occupation of a finite quitting window

A `QuittingFiniteRootWindow roots` retains a literal start and length inside
one source root sequence.  Its canonical masses use the source sequence's
joint survival before each phase:

* `singletonMass owner` records absorption by exactly `{owner}`;
* `collisionMass` records absorption by at least two players;
* `absorptionMass` records all nonempty absorption.

The raw masses are defined before normalization.  The zero-absorption branch
is explicit and contains no conditional quotient.  On the positive branch,
the normalized owner occupations and collision share sum to one.  Small
maximum one-stage absorption forces the normalized collision share to zero,
including for a sequence of windows of varying positions and lengths.

The payoff layer keeps three different objects separate: the normalized
singleton mixture, the full absorbing delivery, and refusal against a
periodic continuation.  Only the first two are compared here.  Identifying a
refusal law with an owner-deleted reweighting requires a separate strategic
conditioning theorem and is not asserted by this module.
-/

noncomputable section

namespace GameTheory

open Filter Math.PMFProduct Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A literal finite window in a fixed source root sequence. -/
structure QuittingFiniteRootWindow (roots : ℕ → ι → PMF Bool) where
  start : ℕ
  fuel : ℕ

namespace QuittingFiniteRootWindow

variable {roots : ℕ → ι → PMF Bool}

/-- The source root at a phase of the window. -/
def rootAt (window : QuittingFiniteRootWindow roots)
    (phase : Fin window.fuel) : ι → PMF Bool :=
  roots (window.start + phase.val)

/-- Probability that the source word is still live before this phase. -/
def survivalWeight (window : QuittingFiniteRootWindow roots)
    (phase : Fin window.fuel) : ℝ :=
  quittingJointSurvivalWeight roots window.start phase.val

/-- Raw survival-weighted probability of absorption by exactly `owner`. -/
def singletonMass (window : QuittingFiniteRootWindow roots) (owner : ι) : ℝ :=
  ∑ phase : Fin window.fuel,
    window.survivalWeight phase *
      quittingRootCoalitionMass (window.rootAt phase) {owner}

/-- Raw survival-weighted probability of absorption by at least two players. -/
def collisionMass (window : QuittingFiniteRootWindow roots) : ℝ :=
  ∑ phase : Fin window.fuel,
    window.survivalWeight phase *
      quittingRootCollisionMass (window.rootAt phase)

/-- Raw survival-weighted probability of any absorption in the window. -/
def absorptionMass (window : QuittingFiniteRootWindow roots) : ℝ :=
  ∑ phase : Fin window.fuel,
    window.survivalWeight phase *
      quittingRootAbsorptionMass (window.rootAt phase)

/-- Total singleton absorption, before normalization. -/
def singletonTotal (window : QuittingFiniteRootWindow roots) : ℝ :=
  ∑ owner : ι, window.singletonMass owner

/-- Canonical owner occupation conditional on absorption in the window.
When absorption mass is zero this expression is zero by `div_zero`; the
semantic zero branch is stated separately below. -/
def normalizedSingletonOccupation
    (window : QuittingFiniteRootWindow roots) (owner : ι) : ℝ :=
  window.singletonMass owner / window.absorptionMass

/-- Canonical conditional share of multi-quitter absorption. -/
def normalizedCollisionMass (window : QuittingFiniteRootWindow roots) : ℝ :=
  window.collisionMass / window.absorptionMass

omit [DecidableEq ι] in
/-- Every source survival weight is nonnegative. -/
theorem survivalWeight_nonneg (window : QuittingFiniteRootWindow roots)
    (phase : Fin window.fuel) :
    0 ≤ window.survivalWeight phase :=
  quittingJointSurvivalWeight_nonneg roots window.start phase.val

/-- Owner singleton mass is nonnegative. -/
theorem singletonMass_nonneg (window : QuittingFiniteRootWindow roots)
    (owner : ι) :
    0 ≤ window.singletonMass owner := by
  exact Finset.sum_nonneg fun phase _ =>
    mul_nonneg (window.survivalWeight_nonneg phase)
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg _ _)

/-- Total singleton mass is nonnegative. -/
theorem singletonTotal_nonneg (window : QuittingFiniteRootWindow roots) :
    0 ≤ window.singletonTotal :=
  Finset.sum_nonneg fun owner _ => window.singletonMass_nonneg owner

/-- Collision mass is nonnegative. -/
theorem collisionMass_nonneg (window : QuittingFiniteRootWindow roots) :
    0 ≤ window.collisionMass := by
  exact Finset.sum_nonneg fun phase _ =>
    mul_nonneg (window.survivalWeight_nonneg phase)
      (quittingRootCollisionMass_nonneg _)

omit [DecidableEq ι] in
/-- Absorption mass is nonnegative. -/
theorem absorptionMass_nonneg (window : QuittingFiniteRootWindow roots) :
    0 ≤ window.absorptionMass := by
  classical
  exact Finset.sum_nonneg fun phase _ =>
    mul_nonneg (window.survivalWeight_nonneg phase)
      (quittingRootAbsorptionMass_nonneg _)

/-- At one root, total absorption splits into singleton and collision mass. -/
theorem quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
    (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root =
      (∑ owner : ι, quittingRootCoalitionMass root {owner}) +
        quittingRootCollisionMass root := by
  have hpartition := sum_nonemptyFinset_eq_sum_singleton_add_sum_card_ge_two
    (ι := ι) (fun coalition => quittingRootCoalitionMass root coalition)
  have htotal := quittingRootCoalitionMass_sum_nonempty root
  rw [htotal] at hpartition
  rw [quittingRootCollisionMass_eq_sum_coalitionMass]
  exact hpartition

/-- Exact window mass decomposition. -/
theorem absorptionMass_eq_singletonTotal_add_collisionMass
    (window : QuittingFiniteRootWindow roots) :
    window.absorptionMass = window.singletonTotal + window.collisionMass := by
  unfold absorptionMass singletonTotal singletonMass collisionMass
  simp_rw [quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]

omit [DecidableEq ι] in
/-- Window absorption is exactly one minus survival through the whole source
word. -/
theorem absorptionMass_eq_one_sub_survivalWeight
    (window : QuittingFiniteRootWindow roots) :
    window.absorptionMass =
      1 - quittingJointSurvivalWeight roots window.start window.fuel := by
  classical
  unfold absorptionMass survivalWeight rootAt quittingRootAbsorptionMass
  rw [Fin.sum_univ_eq_sum_range
    (fun offset : ℕ =>
      quittingJointSurvivalWeight roots window.start offset *
        (1 - quittingStationaryContinueMass
          (roots (window.start + offset)))) window.fuel]
  exact sum_quittingJointSurvivalWeight_mul_one_sub_continueMass
    roots window.start window.fuel

/-- The canonical normalization has an explicit zero-denominator branch.
On the positive branch, normalized singleton occupation and normalized
collision share form a probability vector. -/
theorem zero_or_positive_normalizedMass
    (window : QuittingFiniteRootWindow roots) :
    (window.absorptionMass = 0 ∧ window.singletonTotal = 0 ∧
        window.collisionMass = 0 ∧
        ∀ owner, window.singletonMass owner = 0) ∨
      (0 < window.absorptionMass ∧
        (∑ owner : ι, window.normalizedSingletonOccupation owner) +
          window.normalizedCollisionMass = 1) := by
  rcases window.absorptionMass_nonneg.eq_or_lt with hzero | hpositive
  · left
    have hdecomposition := window.absorptionMass_eq_singletonTotal_add_collisionMass
    have hsingletonTotal : window.singletonTotal = 0 := by
      rw [← hzero] at hdecomposition
      nlinarith [window.singletonTotal_nonneg, window.collisionMass_nonneg]
    have hcollision : window.collisionMass = 0 := by
      rw [← hzero] at hdecomposition
      nlinarith [window.singletonTotal_nonneg, window.collisionMass_nonneg]
    refine ⟨hzero.symm, hsingletonTotal, hcollision, ?_⟩
    intro owner
    apply le_antisymm
    · have hle : window.singletonMass owner ≤ window.singletonTotal := by
        unfold singletonTotal
        exact Finset.single_le_sum
          (fun other _ => window.singletonMass_nonneg other)
          (Finset.mem_univ owner)
      linarith
    · exact window.singletonMass_nonneg owner
  · right
    refine ⟨hpositive, ?_⟩
    rw [show (∑ owner : ι, window.normalizedSingletonOccupation owner) =
        window.singletonTotal / window.absorptionMass by
      simp [normalizedSingletonOccupation, singletonTotal, Finset.sum_div]]
    unfold normalizedCollisionMass
    rw [← add_div, ← window.absorptionMass_eq_singletonTotal_add_collisionMass]
    exact div_self hpositive.ne'

/-- Conditional collision is bounded by the maximum one-stage absorption
inside the same source window.  The conclusion is valid in the zero branch
as well. -/
theorem normalizedCollisionMass_le
    (window : QuittingFiniteRootWindow roots) (rho : ℝ) (hrho : 0 ≤ rho)
    (hcap : ∀ phase : Fin window.fuel,
      quittingRootAbsorptionMass (window.rootAt phase) ≤ rho) :
    window.normalizedCollisionMass ≤
      (Fintype.card ι).choose 2 * rho := by
  have hconcentration := finiteQuittingRootCollisionConcentration_or_zero
    (fun phase : Fin window.fuel => window.survivalWeight phase)
    (fun phase => window.rootAt phase) rho
    (fun phase => window.survivalWeight_nonneg phase) hcap
  rcases hconcentration with hzero | hpositive
  · unfold normalizedCollisionMass collisionMass absorptionMass
    rw [hzero.1, hzero.2, zero_div]
    exact mul_nonneg (Nat.cast_nonneg _) hrho
  · exact hpositive.2

/-- Conditional collision share is nonnegative. -/
theorem normalizedCollisionMass_nonneg
    (window : QuittingFiniteRootWindow roots) :
    0 ≤ window.normalizedCollisionMass :=
  div_nonneg window.collisionMass_nonneg window.absorptionMass_nonneg

/-- Canonical singleton occupation is nonnegative. -/
theorem normalizedSingletonOccupation_nonneg
    (window : QuittingFiniteRootWindow roots) (owner : ι) :
    0 ≤ window.normalizedSingletonOccupation owner :=
  div_nonneg (window.singletonMass_nonneg owner)
    window.absorptionMass_nonneg

/-- On the positive-absorption branch, every canonical singleton occupation
coordinate is at most one. -/
theorem normalizedSingletonOccupation_le_one
    (window : QuittingFiniteRootWindow roots) (owner : ι)
    (habsorption : 0 < window.absorptionMass) :
    window.normalizedSingletonOccupation owner ≤ 1 := by
  have hprobability := (window.zero_or_positive_normalizedMass).resolve_left
    (fun hzero ↦ habsorption.ne' hzero.1)
  have howner : window.normalizedSingletonOccupation owner ≤
      ∑ player : ι, window.normalizedSingletonOccupation player :=
    Finset.single_le_sum
      (fun player _ ↦ window.normalizedSingletonOccupation_nonneg player)
      (Finset.mem_univ owner)
  linarith [window.normalizedCollisionMass_nonneg]

/-- For any sequence of source windows, if a common per-window ceiling on
one-stage absorption tends to zero, then normalized collision mass tends to
zero.  Window positions and lengths may vary arbitrarily. -/
theorem tendsto_normalizedCollisionMass_zero
    (window : ℕ → QuittingFiniteRootWindow roots) (rho : ℕ → ℝ)
    (hrho0 : ∀ index, 0 ≤ rho index)
    (hcap : ∀ index (phase : Fin (window index).fuel),
      quittingRootAbsorptionMass ((window index).rootAt phase) ≤ rho index)
    (hrho : Tendsto rho atTop (nhds 0)) :
    Tendsto (fun index => (window index).normalizedCollisionMass)
      atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun index => (window index).normalizedCollisionMass_nonneg
  · exact fun index => (window index).normalizedCollisionMass_le
      (rho index) (hrho0 index) (hcap index)
  · simpa using hrho.const_mul ((Fintype.card ι).choose 2 : ℝ)

/-- Conditional collision vanishes for arbitrary finite windows whose starts
escape to infinity whenever the source roots' one-stage absorption tends to
zero.  Window lengths may vary without any bound. -/
theorem tendsto_normalizedCollisionMass_zero_of_start_tendsto
    (window : ℕ → QuittingFiniteRootWindow roots)
    (hstart : Tendsto (fun index ↦ (window index).start) atTop atTop)
    (hroot : Tendsto (fun time ↦
      quittingRootAbsorptionMass (roots time)) atTop (nhds 0)) :
    Tendsto (fun index ↦ (window index).normalizedCollisionMass)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let pairCount : ℝ := (Fintype.card ι).choose 2
  let rho : ℝ := ε / (pairCount + 1)
  have hpairCount : 0 ≤ pairCount := by positivity
  have hrho : 0 < rho := div_pos hε (by linarith)
  obtain ⟨rootThreshold, hrootThreshold⟩ :=
    (Metric.tendsto_atTop.mp hroot) rho hrho
  obtain ⟨windowThreshold, hwindowThreshold⟩ :=
    eventually_atTop.1 ((tendsto_atTop.1 hstart) rootThreshold)
  refine ⟨windowThreshold, fun index hindex ↦ ?_⟩
  have hcap : ∀ phase : Fin (window index).fuel,
      quittingRootAbsorptionMass ((window index).rootAt phase) ≤ rho := by
    intro phase
    have htime : rootThreshold ≤ (window index).start + phase.val :=
      (hwindowThreshold index hindex).trans
        (Nat.le_add_right _ _)
    have hclose := hrootThreshold
      ((window index).start + phase.val) htime
    rw [Real.dist_eq, sub_zero] at hclose
    change quittingRootAbsorptionMass
      (roots ((window index).start + phase.val)) ≤ rho
    exact (le_abs_self _).trans hclose.le
  have hbound := (window index).normalizedCollisionMass_le
    rho hrho.le hcap
  have hstrict : pairCount * rho < ε := by
    dsimp only [rho]
    have hratio : pairCount / (pairCount + 1) < 1 := by
      exact (div_lt_one (by linarith)).2 (by linarith)
    calc
      pairCount * (ε / (pairCount + 1)) =
          ε * (pairCount / (pairCount + 1)) := by ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
      _ = ε := mul_one ε
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (window index).normalizedCollisionMass_nonneg]
  exact hbound.trans_lt hstrict

/-! ## Singleton mixture and absorbing delivery -/

/-- Collision-reward contribution at one product root. -/
def rootCollisionRewardContribution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  ∑ coalition ∈ Finset.univ.filter
      (fun coalition : Finset ι => 2 ≤ coalition.card),
    quittingRootCoalitionMass root coalition *
      quittingProjectiveCoalitionReward reward coalition who

/-- Survival-weighted reward contributed by singleton absorptions. -/
def singletonRewardContribution
    (window : QuittingFiniteRootWindow roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) : ℝ :=
  ∑ owner : ι,
    window.singletonMass owner *
      reward (quittingSingletonTerminal owner) who

/-- Survival-weighted reward contributed by multi-quitter absorptions. -/
def collisionRewardContribution
    (window : QuittingFiniteRootWindow roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) : ℝ :=
  ∑ phase : Fin window.fuel,
    window.survivalWeight phase *
      rootCollisionRewardContribution reward (window.rootAt phase) who

/-- Singleton payoff mixture, normalized by singleton mass alone.  Its
positive-denominator use is explicit in comparison theorems. -/
def singletonMixture
    (window : QuittingFiniteRootWindow roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) : ℝ :=
  window.singletonRewardContribution reward who / window.singletonTotal

/-- Singleton reward mixture normalized by total absorption rather than by
singleton absorption alone.  This is the natural coordinate for limits in
which conditional collision vanishes. -/
def absorptionNormalizedSingletonMixture
    (window : QuittingFiniteRootWindow roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) : ℝ :=
  ∑ owner : ι, window.normalizedSingletonOccupation owner *
    reward (quittingSingletonTerminal owner) who

/-- The absorption-normalized singleton mixture is the raw singleton reward
contribution divided by total absorption. -/
theorem absorptionNormalizedSingletonMixture_eq
    (window : QuittingFiniteRootWindow roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    window.absorptionNormalizedSingletonMixture reward who =
      window.singletonRewardContribution reward who /
        window.absorptionMass := by
  unfold absorptionNormalizedSingletonMixture normalizedSingletonOccupation
    singletonRewardContribution singletonMass
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

/-- Full absorbing delivery obtained by restarting the joint window.  This
uses joint absorption; it is not a player's periodic refusal value. -/
def absorbingDelivery
    (window : QuittingFiniteRootWindow roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) : ℝ :=
  quittingWindowRestartDelivery reward roots who window.start window.fuel

/-- One root's absorbing payoff splits exactly into singleton and collision
reward contributions. -/
theorem quittingRootAbsorbingContribution_eq_singleton_add_collision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootAbsorbingContribution reward root who =
      (∑ owner : ι, quittingRootCoalitionMass root {owner} *
        reward (quittingSingletonTerminal owner) who) +
      rootCollisionRewardContribution reward root who := by
  rw [quittingRootAbsorbingContribution_eq_sum_coalitionMass]
  change (∑ coalition : Finset ι,
      coalitionMass (quittingRootQuitRates root) coalition *
        quittingProjectiveCoalitionReward reward coalition who) = _
  have hpartition := sum_nonemptyFinset_eq_sum_singleton_add_sum_card_ge_two
    (ι := ι) (fun coalition =>
      quittingRootCoalitionMass root coalition *
        quittingProjectiveCoalitionReward reward coalition who)
  have hempty : coalitionMass (quittingRootQuitRates root) ∅ *
      quittingProjectiveCoalitionReward reward ∅ who = 0 := by simp
  have hall :
      ∑ coalition : Finset ι,
          coalitionMass (quittingRootQuitRates root) coalition *
            quittingProjectiveCoalitionReward reward coalition who =
        ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingRootCoalitionMass root coalition *
            quittingProjectiveCoalitionReward reward coalition who := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun coalition =>
        coalitionMass (quittingRootQuitRates root) coalition *
          quittingProjectiveCoalitionReward reward coalition who)
      (Finset.mem_univ ∅), hempty, zero_add]
    rfl
  rw [hall, hpartition]
  simp_rw [quittingProjectiveCoalitionReward_singleton]
  rfl

/-- The existing absorbing intercept is exactly the sum of the canonical
singleton and collision reward contributions. -/
theorem windowAbsorbingIntercept_eq_singleton_add_collision
    (window : QuittingFiniteRootWindow roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingWindowAbsorbingIntercept reward roots who window.start window.fuel =
      window.singletonRewardContribution reward who +
        window.collisionRewardContribution reward who := by
  unfold quittingWindowAbsorbingIntercept singletonRewardContribution
    collisionRewardContribution singletonMass survivalWeight rootAt
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [quittingRootAbsorbingContribution_eq_singleton_add_collision,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro owner _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro phase _
  ring

/-- On the positive-absorption branch, absorbing delivery is the normalized
sum of the canonical singleton and collision contributions. -/
theorem absorbingDelivery_eq
    (window : QuittingFiniteRootWindow roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    window.absorbingDelivery reward who =
      (window.singletonRewardContribution reward who +
        window.collisionRewardContribution reward who) /
          window.absorptionMass := by
  unfold absorbingDelivery quittingWindowRestartDelivery
  rw [window.windowAbsorbingIntercept_eq_singleton_add_collision reward who,
    window.absorptionMass_eq_one_sub_survivalWeight]

/-- Singleton reward contribution is controlled by singleton mass. -/
theorem abs_singletonRewardContribution_le
    (window : QuittingFiniteRootWindow roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |window.singletonRewardContribution reward who| ≤
      M * window.singletonTotal := by
  calc
    |window.singletonRewardContribution reward who| ≤
        ∑ owner : ι,
          |window.singletonMass owner *
            reward (quittingSingletonTerminal owner) who| := by
      unfold singletonRewardContribution
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ owner : ι, M * window.singletonMass owner := by
      apply Finset.sum_le_sum
      intro owner _
      rw [abs_mul, abs_of_nonneg (window.singletonMass_nonneg owner), mul_comm]
      exact mul_le_mul_of_nonneg_right
        (hreward (quittingSingletonTerminal owner) who)
        (window.singletonMass_nonneg owner)
    _ = M * window.singletonTotal := by
      rw [← Finset.mul_sum]
      rfl

/-- One root's collision reward is controlled by its collision mass. -/
theorem abs_rootCollisionRewardContribution_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |rootCollisionRewardContribution reward root who| ≤
      M * quittingRootCollisionMass root := by
  let collisions := Finset.univ.filter
    (fun coalition : Finset ι => 2 ≤ coalition.card)
  calc
    |rootCollisionRewardContribution reward root who| ≤
        ∑ coalition ∈ collisions,
          |quittingRootCoalitionMass root coalition *
            quittingProjectiveCoalitionReward reward coalition who| := by
      unfold rootCollisionRewardContribution collisions
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ coalition ∈ collisions,
        M * quittingRootCoalitionMass root coalition := by
      apply Finset.sum_le_sum
      intro coalition hcoalition
      have hcard : 2 ≤ coalition.card := by
        simpa [collisions] using hcoalition
      have hnonempty : coalition.Nonempty :=
        Finset.card_pos.mp (by omega)
      have hbound :
          |quittingProjectiveCoalitionReward reward coalition who| ≤ M := by
        simpa [quittingProjectiveCoalitionReward, hnonempty] using
          hreward ⟨coalition, hnonempty⟩ who
      rw [abs_mul,
        abs_of_nonneg
          (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root coalition),
        mul_comm]
      exact mul_le_mul_of_nonneg_right hbound
        (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root coalition)
    _ = M * quittingRootCollisionMass root := by
      rw [← Finset.mul_sum,
        quittingRootCollisionMass_eq_sum_coalitionMass]

/-- Window collision reward is controlled by raw collision mass. -/
theorem abs_collisionRewardContribution_le
    (window : QuittingFiniteRootWindow roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |window.collisionRewardContribution reward who| ≤
      M * window.collisionMass := by
  calc
    |window.collisionRewardContribution reward who| ≤
        ∑ phase : Fin window.fuel,
          |window.survivalWeight phase *
            rootCollisionRewardContribution reward (window.rootAt phase) who| := by
      unfold collisionRewardContribution
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ phase : Fin window.fuel,
        M * (window.survivalWeight phase *
          quittingRootCollisionMass (window.rootAt phase)) := by
      apply Finset.sum_le_sum
      intro phase _
      rw [abs_mul, abs_of_nonneg (window.survivalWeight_nonneg phase)]
      have hroot := abs_rootCollisionRewardContribution_le
        reward (window.rootAt phase) who hreward
      nlinarith [mul_le_mul_of_nonneg_left hroot
        (window.survivalWeight_nonneg phase)]
    _ = M * window.collisionMass := by
      rw [← Finset.mul_sum]
      rfl

/-- The normalized full absorbing delivery differs from the normalized
singleton mixture by at most twice the reward bound times conditional
collision mass. -/
theorem abs_absorbingDelivery_sub_singletonMixture_le
    (window : QuittingFiniteRootWindow roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (habsorption : 0 < window.absorptionMass)
    (hsingleton : 0 < window.singletonTotal) :
    |window.absorbingDelivery reward who -
        window.singletonMixture reward who| ≤
      2 * M * window.normalizedCollisionMass := by
  have h := abs_conditionalPayoff_sub_singletonMixture_le
    window.absorptionMass_eq_singletonTotal_add_collisionMass
    habsorption hsingleton window.collisionMass_nonneg hM
    (window.abs_singletonRewardContribution_le reward who hreward)
    (window.abs_collisionRewardContribution_le reward who hreward)
    (window.absorbingDelivery_eq reward who)
    (show window.singletonMixture reward who =
      window.singletonRewardContribution reward who /
        window.singletonTotal from rfl)
  simpa [normalizedCollisionMass, mul_div_assoc] using h

/-- The full restart delivery differs from the absorption-normalized
singleton mixture by at most one reward bound times conditional collision.
Unlike singleton-only normalization, this estimate needs no positive
singleton denominator. -/
theorem abs_delivery_sub_absorptionSingletonMixture_le
    (window : QuittingFiniteRootWindow roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (habsorption : 0 < window.absorptionMass) :
    |window.absorbingDelivery reward who -
        window.absorptionNormalizedSingletonMixture reward who| ≤
      M * window.normalizedCollisionMass := by
  rw [window.absorbingDelivery_eq reward who,
    window.absorptionNormalizedSingletonMixture_eq reward who, add_div,
    add_sub_cancel_left, abs_div, abs_of_pos habsorption]
  have hbound := window.abs_collisionRewardContribution_le
    reward who hreward
  have hdiv := div_le_div_of_nonneg_right hbound habsorption.le
  simpa [normalizedCollisionMass, mul_div_assoc] using hdiv

/-- Ceiling form of the delivery comparison. -/
theorem abs_absorbingDelivery_sub_singletonMixture_le_of_cap
    (window : QuittingFiniteRootWindow roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {M rho : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (habsorption : 0 < window.absorptionMass)
    (hsingleton : 0 < window.singletonTotal) (hrho : 0 ≤ rho)
    (hcap : ∀ phase : Fin window.fuel,
      quittingRootAbsorptionMass (window.rootAt phase) ≤ rho) :
    |window.absorbingDelivery reward who -
        window.singletonMixture reward who| ≤
      2 * M * ((Fintype.card ι).choose 2 * rho) := by
  exact (window.abs_absorbingDelivery_sub_singletonMixture_le
    reward who hM hreward habsorption hsingleton).trans
      (mul_le_mul_of_nonneg_left
        (window.normalizedCollisionMass_le rho hrho hcap)
        (mul_nonneg (by norm_num) hM))

/-! ## Active-owner provenance and boundary pinning -/

/-- Positive singleton coalition mass forces positive Quit probability for
its displayed owner at the same source root. -/
theorem quitProbability_pos_of_singletonCoalitionMass_pos
    (root : ι → PMF Bool) (owner : ι)
    (hmass : 0 < quittingRootCoalitionMass root {owner}) :
    0 < (root owner true).toReal := by
  by_contra hnot
  have hnonpos : (root owner true).toReal ≤ 0 := le_of_not_gt hnot
  have hzero : (root owner true).toReal = 0 :=
    le_antisymm hnonpos ENNReal.toReal_nonneg
  unfold quittingRootCoalitionMass coalitionMass quittingRootQuitRates at hmass
  simp [hzero] at hmass

/-- Positive normalized owner occupation contains a literal positive-hazard
phase of the same source window. -/
theorem exists_activePhase_of_normalizedSingletonOccupation_pos
    (window : QuittingFiniteRootWindow roots) (owner : ι)
    (hoccupation : 0 < window.normalizedSingletonOccupation owner) :
    ∃ phase : Fin window.fuel,
      0 < (window.rootAt phase owner true).toReal := by
  have hsingleton : 0 < window.singletonMass owner := by
    unfold normalizedSingletonOccupation at hoccupation
    rcases (div_pos_iff.mp hoccupation) with hpositive | hnegative
    · exact hpositive.1
    · exact (not_lt_of_ge window.absorptionMass_nonneg hnegative.2).elim
  unfold singletonMass at hsingleton
  obtain ⟨phase, _, hphase⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun phase _ =>
      mul_nonneg (window.survivalWeight_nonneg phase)
        (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg _ _))).mp hsingleton
  have hcoalition :
      0 < quittingRootCoalitionMass (window.rootAt phase) {owner} := by
    have hnonneg := window.survivalWeight_nonneg phase
    have hmassNonneg :=
      MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
        (window.rootAt phase) {owner}
    nlinarith
  exact ⟨phase,
    quitProbability_pos_of_singletonCoalitionMass_pos
      (window.rootAt phase) owner hcoalition⟩

/-- If each calendar-indexed source window starts after its calendar index,
positive canonical occupation supplies an active source date after the same
cutoff. -/
theorem normalizedSingletonOccupation_activeAfter
    (window : ℕ → QuittingFiniteRootWindow roots)
    (hstart : ∀ cutoff, cutoff ≤ (window cutoff).start) :
    ∀ cutoff owner,
      0 < (window cutoff).normalizedSingletonOccupation owner →
        ∃ time, cutoff ≤ time ∧ 0 < (roots time owner true).toReal := by
  intro cutoff owner hoccupation
  obtain ⟨phase, hphase⟩ :=
    (window cutoff).exists_activePhase_of_normalizedSingletonOccupation_pos
      owner hoccupation
  exact ⟨(window cutoff).start + phase.val,
    (hstart cutoff).trans (Nat.le_add_right _ _), hphase⟩

/-- Positive limiting canonical occupation pins the annotation boundary to
the corresponding singleton reward.  All activity provenance is discharged
by the literal source windows; no abstract occupation-to-support premise
remains. -/
theorem quittingAnnotationBoundary_eq_singleton_of_normalizedWindowOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (boundary : Payoff ι)
    (hboundary : ∀ who, Tendsto (fun time => value time who) atTop
      (nhds (boundary who)))
    (hcharge : Summable (fun time =>
      quittingRootAbsorptionMass (roots time)))
    (window : ℕ → QuittingFiniteRootWindow roots)
    (hstart : ∀ cutoff, cutoff ≤ (window cutoff).start)
    (limitOccupation : ι → ℝ)
    (hoccupation : ∀ who, Tendsto
      (fun cutoff => (window cutoff).normalizedSingletonOccupation who)
      atTop (nhds (limitOccupation who)))
    (who : ι) (hpositive : 0 < limitOccupation who) :
    boundary who = reward (quittingSingletonTerminal who) who := by
  exact quittingAnnotationBoundary_eq_singleton_of_positiveOccupation
    reward roots value hspine boundary hboundary hcharge
    (fun cutoff owner =>
      (window cutoff).normalizedSingletonOccupation owner)
    limitOccupation hoccupation
    (normalizedSingletonOccupation_activeAfter window hstart)
    who hpositive

end QuittingFiniteRootWindow

end GameTheory
