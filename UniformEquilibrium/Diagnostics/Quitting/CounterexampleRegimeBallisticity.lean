/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCapCarrier
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketDefect
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation

/-!
# Absorption-clock ballisticity of a quitting counterexample tail

The optimized exact dynamic-debt tail of a hypothetical counterexample is
punishment-rational in its unaugmented values at every date.  This closes the
endpoint premise in the tail-to-punishment-prefix bridge.

This module identifies the stronger late-window consequence.  A sequence of
tail windows cannot have endpoint displacement little-o of its absorbed mass.
Otherwise conditional collision vanishes, normalized singleton occupation
has a convergent subsequence, the restart delivery converges to the tail
boundary, and active owners are pinned to their singleton rewards.  The
limit is then a fully complementary normalized singleton packet, contradicting
the counterexample regime's strict packet defect.

The sequential exclusion is converted to one uniform estimate: after one
date, every positive-absorption window has endpoint distance at least a fixed
positive multiple of its absorbed mass.  This is a ballisticity theorem in
the finite absorption clock.  It is not recurrence: summable charge permits a
bounded path to approach its endpoint at nonzero clock speed, so a further
product-root return or terminal-realization argument is still required.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

/-- A source-typed finite window of the optimized exact-D tail. -/
def finiteRootWindow (start fuel : ℕ) :
    QuittingFiniteRootWindow (quittingDynamicDebtTailRoots seam.tail) where
  start := start
  fuel := fuel

@[simp]
theorem finiteRootWindow_start (start fuel : ℕ) :
    (seam.finiteRootWindow start fuel).start = start := rfl

@[simp]
theorem finiteRootWindow_fuel (start fuel : ℕ) :
    (seam.finiteRootWindow start fuel).fuel = fuel := rfl

/-- Endpoint displacement divided by literal absorbed mass.  The positive
denominator branch is explicit in every semantic use. -/
def normalizedEndpointDrift
    (window : QuittingFiniteRootWindow
      (quittingDynamicDebtTailRoots seam.tail)) : ℝ :=
  dist (seam.tail window.start).1.1
      (seam.tail (window.start + window.fuel)).1.1 /
    window.absorptionMass

/-- Forgetting exact debt leaves a canonical bounded exact Nash--Bellman
spine on the optimized tail. -/
theorem isCanonicalExactNashBellmanSpine :
    IsCanonicalExactQuittingNashBellmanSpine reward
      (fun time ↦ (seam.tail time).1.1)
      (quittingDynamicDebtTailRoots seam.tail) := by
  refine ⟨?_, ?_, ?_⟩
  · intro time who
    have hbox := (seam.tail_mem time).1
    change (seam.tail time).1.1 ∈ Set.Icc
      (fun _ ↦ -quittingRewardBound reward)
      (fun _ ↦ quittingRewardBound reward) at hbox
    exact abs_le.mpr ⟨hbox.1 who, hbox.2 who⟩
  · intro time
    exact (seam.tail_edge time).1.1
  · intro time
    exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (seam.tail (time + 1)).1.1
        (quittingDynamicDebtTailRoots seam.tail time)).1
      (seam.tail_edge time).1.2

/-- Each payoff coordinate of the optimized tail satisfies the prescribed
Bellman recursion on its operational roots. -/
theorem isLivePrescribedValue (who : ι) :
    IsQuittingLivePrescribedValue reward
      (quittingDynamicDebtTailRoots seam.tail) who
      (fun time ↦ (seam.tail time).1.1 who) := by
  intro time
  exact congrFun (seam.tail_edge time).1.1 who

/-- One-stage joint absorption along the optimized tail tends to zero. -/
theorem rootAbsorptionMass_tendsto_zero :
    Tendsto (fun time ↦ quittingRootAbsorptionMass
      (quittingDynamicDebtTailRoots seam.tail time)) atTop (nhds 0) := by
  change Tendsto (quittingDynamicDebtTailAbsorptionCharge seam.tail)
    atTop (nhds 0)
  exact seam.jointAbsorption_summable.tendsto_atTop_zero

/-- The punishment floor also survives at the limiting unaugmented value. -/
theorem punishmentValue_le_limitValue (who : ι) :
    quittingPunishmentValue reward who ≤ seam.limit.value who := by
  apply ge_of_tendsto (seam.value_tendsto who)
  exact Filter.Eventually.of_forall fun time ↦
    seam.punishmentValue_le_tailValue time who

/-- Positive limiting occupation in arbitrary windows whose starts escape to
infinity pins the corresponding boundary coordinate to its singleton reward.
No relation between the calendar index and the window start is required. -/
theorem limitValue_eq_singleton_of_windowOccupation
    (window : ℕ → QuittingFiniteRootWindow
      (quittingDynamicDebtTailRoots seam.tail))
    (hstart : Tendsto (fun index ↦ (window index).start) atTop atTop)
    (limitOccupation : ι → ℝ)
    (hoccupation : ∀ who, Tendsto
      (fun index ↦ (window index).normalizedSingletonOccupation who)
      atTop (nhds (limitOccupation who)))
    (who : ι) (hpositive : 0 < limitOccupation who) :
    seam.limit.value who = reward (quittingSingletonTerminal who) who := by
  have heventuallyPositive : ∀ᶠ index : ℕ in atTop,
      0 < (window index).normalizedSingletonOccupation who :=
    (hoccupation who).eventually (Ioi_mem_nhds hpositive)
  obtain ⟨positiveThreshold, hpositiveThreshold⟩ :=
    eventually_atTop.1 heventuallyPositive
  have hexists : ∀ cutoff, ∃ time, cutoff ≤ time ∧
      0 < (quittingDynamicDebtTailRoots seam.tail time who true).toReal := by
    intro cutoff
    obtain ⟨startThreshold, hstartThreshold⟩ :=
      eventually_atTop.1 ((tendsto_atTop.1 hstart) cutoff)
    let index := max positiveThreshold startThreshold
    have hoccupationPos :
        0 < (window index).normalizedSingletonOccupation who :=
      hpositiveThreshold index (le_max_left _ _)
    obtain ⟨phase, hphase⟩ :=
      (window index).exists_activePhase_of_normalizedSingletonOccupation_pos
        who hoccupationPos
    refine ⟨(window index).start + phase.val, ?_, ?_⟩
    · exact (hstartThreshold index (le_max_right _ _)).trans
        (Nat.le_add_right _ _)
    · exact hphase
  choose time htime hactive using hexists
  have htimeTendsto : Tendsto time atTop atTop :=
    Filter.tendsto_atTop_mono htime tendsto_id
  have hcharge : Summable (fun date ↦ quittingRootAbsorptionMass
      (quittingDynamicDebtTailRoots seam.tail date)) := by
    change Summable (quittingDynamicDebtTailAbsorptionCharge seam.tail)
    exact seam.jointAbsorption_summable
  exact quittingAnnotationBoundary_eq_singleton_of_activeSubsequence
    reward (quittingDynamicDebtTailRoots seam.tail)
      (fun date ↦ (seam.tail date).1.1)
      seam.isCanonicalExactNashBellmanSpine seam.limit.value
      seam.value_tendsto hcharge who time htimeTendsto hactive

/-- If endpoint displacement is little-o of absorbed mass along late windows,
then their absorbing restart delivery converges coordinatewise to the tail's
annotation boundary. -/
theorem tendsto_windowAbsorbingDelivery_of_normalizedEndpointDrift
    (window : ℕ → QuittingFiniteRootWindow
      (quittingDynamicDebtTailRoots seam.tail))
    (hstart : Tendsto (fun index ↦ (window index).start) atTop atTop)
    (habsorption : ∀ index, 0 < (window index).absorptionMass)
    (hdrift : Tendsto (fun index ↦ seam.normalizedEndpointDrift (window index))
      atTop (nhds 0))
    (who : ι) :
    Tendsto (fun index ↦ (window index).absorbingDelivery reward who)
      atTop (nhds (seam.limit.value who)) := by
  let roots := quittingDynamicDebtTailRoots seam.tail
  let prescribed : ℕ → ℝ := fun time ↦ (seam.tail time).1.1 who
  have hstartValue : Tendsto (fun index ↦ prescribed (window index).start)
      atTop (nhds (seam.limit.value who)) :=
    (seam.value_tendsto who).comp hstart
  have herrorBound : ∀ index,
      |(window index).absorbingDelivery reward who -
          prescribed (window index).start| ≤
        seam.normalizedEndpointDrift (window index) := by
    intro index
    let currentWindow := window index
    let survival := quittingJointSurvivalWeight roots
      currentWindow.start currentWindow.fuel
    have hmass : currentWindow.absorptionMass = 1 - survival :=
      currentWindow.absorptionMass_eq_one_sub_survivalWeight
    have hsurvivalNonneg : 0 ≤ survival :=
      quittingJointSurvivalWeight_nonneg roots
        currentWindow.start currentWindow.fuel
    have hsurvivalLe : survival ≤ 1 := by
      have hpositive := habsorption index
      change 0 < currentWindow.absorptionMass at hpositive
      rw [hmass] at hpositive
      linarith
    have hsurvivalLt : survival < 1 := by
      have hpositive := habsorption index
      change 0 < currentWindow.absorptionMass at hpositive
      rw [hmass] at hpositive
      linarith
    have hseam := quittingWindowRestartDelivery_sub_prescribed
      reward roots who prescribed (seam.isLivePrescribedValue who)
      currentWindow.start currentWindow.fuel hsurvivalLt
    rw [← hmass] at hseam
    have hmassNe : currentWindow.absorptionMass ≠ 0 :=
      (habsorption index).ne'
    have heq : currentWindow.absorbingDelivery reward who -
          prescribed currentWindow.start =
        survival *
          (prescribed currentWindow.start -
            prescribed (currentWindow.start + currentWindow.fuel)) /
          currentWindow.absorptionMass := by
      apply (eq_div_iff hmassNe).2
      rw [mul_comm]
      exact hseam
    have hcoordinate :
        |prescribed currentWindow.start -
            prescribed (currentWindow.start + currentWindow.fuel)| ≤
          dist (seam.tail currentWindow.start).1.1
            (seam.tail (currentWindow.start + currentWindow.fuel)).1.1 := by
      have hpi := (dist_pi_le_iff dist_nonneg).1
        (le_refl (dist (seam.tail currentWindow.start).1.1
          (seam.tail (currentWindow.start + currentWindow.fuel)).1.1)) who
      simpa [prescribed, Real.dist_eq] using hpi
    have hratioCoordinate :
        |prescribed currentWindow.start -
            prescribed (currentWindow.start + currentWindow.fuel)| /
            currentWindow.absorptionMass ≤
          seam.normalizedEndpointDrift currentWindow := by
      exact div_le_div_of_nonneg_right hcoordinate
        (habsorption index).le
    have hratioNonneg : 0 ≤ seam.normalizedEndpointDrift currentWindow :=
      div_nonneg dist_nonneg (habsorption index).le
    rw [heq, abs_div, abs_mul, abs_of_nonneg hsurvivalNonneg,
      abs_of_pos (habsorption index)]
    calc
      survival *
          |prescribed currentWindow.start -
            prescribed (currentWindow.start + currentWindow.fuel)| /
          currentWindow.absorptionMass =
        survival *
          (|prescribed currentWindow.start -
            prescribed (currentWindow.start + currentWindow.fuel)| /
              currentWindow.absorptionMass) := by ring
      _ ≤ survival * seam.normalizedEndpointDrift currentWindow :=
        mul_le_mul_of_nonneg_left hratioCoordinate hsurvivalNonneg
      _ ≤ 1 * seam.normalizedEndpointDrift currentWindow :=
        mul_le_mul_of_nonneg_right hsurvivalLe hratioNonneg
      _ = seam.normalizedEndpointDrift currentWindow := one_mul _
  have habsError : Tendsto (fun index ↦
      |(window index).absorbingDelivery reward who -
        prescribed (window index).start|) atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun _ ↦ abs_nonneg _
    · exact herrorBound
    · exact hdrift
  have herror : Tendsto (fun index ↦
      (window index).absorbingDelivery reward who -
        prescribed (window index).start) atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 habsError
  convert herror.add hstartValue using 1 <;> simp

/-- **No sublinear late return.**  There is no sequence of positive-absorption
tail windows, escaping to infinity, whose endpoint displacement is little-o
of absorbed mass. -/
theorem not_exists_sublinearAbsorptionReturn
    (window : ℕ → QuittingFiniteRootWindow
      (quittingDynamicDebtTailRoots seam.tail))
    (hstart : Tendsto (fun index ↦ (window index).start) atTop atTop)
    (habsorption : ∀ index, 0 < (window index).absorptionMass)
    (hdrift : Tendsto (fun index ↦ seam.normalizedEndpointDrift (window index))
      atTop (nhds 0)) : False := by
  letI : Nonempty ι := regime.nonempty_players
  let occupation : ℕ → Payoff ι := fun index owner ↦
    (window index).normalizedSingletonOccupation owner
  let occupationBox : Set (Payoff ι) :=
    Set.univ.pi (fun _ : ι ↦ Set.Icc (0 : ℝ) 1)
  have hboxCompact : IsCompact occupationBox :=
    isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hoccupationBox : ∀ index, occupation index ∈ occupationBox := by
    intro index
    rw [Set.mem_univ_pi]
    intro owner
    exact ⟨(window index).normalizedSingletonOccupation_nonneg owner,
      (window index).normalizedSingletonOccupation_le_one owner
        (habsorption index)⟩
  obtain ⟨limitOccupation, hlimitOccupationBox, subseq, hsubseq,
      hoccupationLimit⟩ := hboxCompact.tendsto_subseq hoccupationBox
  let selectedWindow : ℕ → QuittingFiniteRootWindow
      (quittingDynamicDebtTailRoots seam.tail) :=
    fun index ↦ window (subseq index)
  have hselectedStart : Tendsto
      (fun index ↦ (selectedWindow index).start) atTop atTop :=
    hstart.comp hsubseq.tendsto_atTop
  have hselectedAbsorption : ∀ index,
      0 < (selectedWindow index).absorptionMass :=
    fun index ↦ habsorption (subseq index)
  have hselectedDrift : Tendsto
      (fun index ↦ seam.normalizedEndpointDrift (selectedWindow index))
      atTop (nhds 0) :=
    hdrift.comp hsubseq.tendsto_atTop
  have hcoordinateLimit : ∀ owner, Tendsto
      (fun index ↦ (selectedWindow index).normalizedSingletonOccupation owner)
      atTop (nhds (limitOccupation owner)) := by
    intro owner
    exact (tendsto_pi_nhds.1 hoccupationLimit) owner
  have hcollision : Tendsto
      (fun index ↦ (selectedWindow index).normalizedCollisionMass)
      atTop (nhds 0) :=
    QuittingFiniteRootWindow.tendsto_normalizedCollisionMass_zero_of_start_tendsto
      selectedWindow hselectedStart seam.rootAbsorptionMass_tendsto_zero
  have hmassSum : ∑ owner : ι, limitOccupation owner = 1 := by
    have hsumLimit : Tendsto (fun index ↦
        (∑ owner : ι,
          (selectedWindow index).normalizedSingletonOccupation owner) +
          (selectedWindow index).normalizedCollisionMass)
        atTop (nhds ((∑ owner : ι, limitOccupation owner) + 0)) :=
      (tendsto_finsetSum Finset.univ
        (fun owner _ ↦ hcoordinateLimit owner)).add hcollision
    have hsumOne : (fun index ↦
        (∑ owner : ι,
          (selectedWindow index).normalizedSingletonOccupation owner) +
          (selectedWindow index).normalizedCollisionMass) =
        fun _ ↦ (1 : ℝ) := by
      funext index
      exact (selectedWindow index).zero_or_positive_normalizedMass.resolve_left
        (fun hzero ↦ (hselectedAbsorption index).ne' hzero.1) |>.2
    rw [hsumOne] at hsumLimit
    have := tendsto_nhds_unique hsumLimit tendsto_const_nhds
    linarith
  have hmassNonneg : ∀ owner, 0 ≤ limitOccupation owner := by
    rw [Set.mem_univ_pi] at hlimitOccupationBox
    intro owner
    exact (hlimitOccupationBox owner).1
  have hdelivery : ∀ who, Tendsto
      (fun index ↦ (selectedWindow index).absorbingDelivery reward who)
      atTop (nhds (seam.limit.value who)) :=
    fun who ↦ seam.tendsto_windowAbsorbingDelivery_of_normalizedEndpointDrift
      selectedWindow hselectedStart hselectedAbsorption hselectedDrift who
  have hmixture : ∀ who,
      quittingSingletonMixture reward limitOccupation who =
        seam.limit.value who := by
    intro who
    have hsingletonMixture : Tendsto (fun index ↦
        (selectedWindow index).absorptionNormalizedSingletonMixture
          reward who) atTop
        (nhds (quittingSingletonMixture reward limitOccupation who)) := by
      have hvector : Tendsto (fun index ↦ occupation (subseq index))
          atTop (nhds limitOccupation) := hoccupationLimit
      have hcontinuous :=
        continuous_quittingSingletonMixture_apply (reward := reward) who
      have htendsto := (hcontinuous.tendsto limitOccupation).comp hvector
      simpa [occupation, selectedWindow, Function.comp_def,
        QuittingFiniteRootWindow.absorptionNormalizedSingletonMixture,
        quittingSingletonMixture] using htendsto
    have herrorAbs : Tendsto (fun index ↦
        |(selectedWindow index).absorbingDelivery reward who -
          (selectedWindow index).absorptionNormalizedSingletonMixture
            reward who|) atTop (nhds 0) := by
      apply squeeze_zero
      · exact fun _ ↦ abs_nonneg _
      · intro index
        exact (selectedWindow index).abs_delivery_sub_absorptionSingletonMixture_le
            reward who
            (abs_reward_le_quittingRewardBound reward)
            (hselectedAbsorption index)
      · simpa using hcollision.const_mul (quittingRewardBound reward)
    have herror : Tendsto (fun index ↦
        (selectedWindow index).absorbingDelivery reward who -
          (selectedWindow index).absorptionNormalizedSingletonMixture
            reward who) atTop (nhds 0) :=
      (tendsto_zero_iff_abs_tendsto_zero _).2 herrorAbs
    have hlimitDifference := (hdelivery who).sub hsingletonMixture
    have heq := tendsto_nhds_unique hlimitDifference herror
    linarith
  have hcomplementary : ∀ owner,
      limitOccupation owner *
        (seam.limit.value owner -
          reward (quittingSingletonTerminal owner) owner) = 0 := by
    intro owner
    rcases (hmassNonneg owner).eq_or_lt with hzero | hpositive
    · rw [← hzero, zero_mul]
    · rw [seam.limitValue_eq_singleton_of_windowOccupation selectedWindow
        hselectedStart limitOccupation hcoordinateLimit owner hpositive,
      sub_self, mul_zero]
  have hpacketData : (limitOccupation, seam.limit.value) ∈
      quittingNormalizedSingletonPacketDataSet reward := by
    refine ⟨hmassNonneg, hmassSum, ?_, ?_, ?_, hcomplementary⟩
    · intro who
      exact (hmixture who).ge
    · intro who
      exact seam.limit.soloReward_le_value who
    · intro who
      exact seam.punishmentValue_le_limitValue who
  let packet := quittingNormalizedSingletonSourcePacketOfData
    (limitOccupation, seam.limit.value) hpacketData
  obtain ⟨owner, _, hstrict⟩ :=
    regime.exists_active_strictSingletonSurplus packet
  change seam.limit.value owner <
    quittingSingletonMixture reward limitOccupation owner at hstrict
  linarith [hmixture owner]

/-- **Uniform absorption-clock ballisticity.**  After one tail date, endpoint
distance across every positive-absorption window is bounded below by one
fixed positive multiple of the window's literal absorbed mass. -/
theorem exists_pos_eventually_endpointDistance_ge_absorptionMass :
    ∃ speed : ℝ, 0 < speed ∧ ∃ threshold : ℕ,
      ∀ start fuel, threshold ≤ start →
        0 < (seam.finiteRootWindow start fuel).absorptionMass →
        speed * (seam.finiteRootWindow start fuel).absorptionMass ≤
          dist (seam.tail start).1.1
            (seam.tail (start + fuel)).1.1 := by
  by_contra hballistic
  push Not at hballistic
  let rate : ℕ → ℝ := fun index ↦ 1 / ((index : ℝ) + 1)
  have hratePos : ∀ index, 0 < rate index := by
    intro index
    exact one_div_pos.mpr (by positivity)
  choose start fuel hstart habsorption hsmall using
    fun index ↦ hballistic (rate index) (hratePos index) index
  let window : ℕ → QuittingFiniteRootWindow
      (quittingDynamicDebtTailRoots seam.tail) :=
    fun index ↦ seam.finiteRootWindow (start index) (fuel index)
  have hstartTendsto : Tendsto (fun index ↦ (window index).start)
      atTop atTop := by
    change Tendsto start atTop atTop
    exact Filter.tendsto_atTop_mono hstart tendsto_id
  have habsorptionWindow : ∀ index, 0 < (window index).absorptionMass := by
    intro index
    exact habsorption index
  have hrate : Tendsto rate atTop (nhds 0) := by
    simpa [rate] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdrift : Tendsto
      (fun index ↦ seam.normalizedEndpointDrift (window index))
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro index
      exact div_nonneg dist_nonneg (habsorptionWindow index).le
    · intro index
      have hstrict : dist (seam.tail (start index)).1.1
          (seam.tail (start index + fuel index)).1.1 <
          rate index * (window index).absorptionMass :=
        by simpa [window] using hsmall index
      exact ((div_lt_iff₀ (habsorptionWindow index)).2 hstrict).le
    · exact hrate
  exact seam.not_exists_sublinearAbsorptionReturn window hstartTendsto
    habsorptionWindow hdrift

end QuittingCounterexampleSeamWitness

end GameTheory
