/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeBallisticity
import UniformEquilibrium.Quitting.Boundary.Analytic.SeamPriceResidual

/-!
# Charge-normalized tangent packets of a quitting counterexample tail

Positive-absorption windows in the optimized exact-D tail have three coupled
normalized coordinates: singleton-owner occupation, their far-end annotation,
and endpoint displacement per unit absorbed mass.  The finite Bellman
telescope identifies the last coordinate exactly with absorbing restart
delivery minus the far-end annotation.  Collision concentration and boundary
pinning therefore turn every convergent occupation subsequence into a
tail-derived tangent packet.

For a hypothetical counterexample the packet cannot be complementary.  Hence
its tangent has either a negative coordinate or, after excluding all negative
coordinates, a positive coordinate in the active owner support.  This is the
finite sign interface consumed respectively by phase repair and support
enlargement.  Neither consumer is constructed here.

The normalization has a genuine denominator boundary.  The capstone keeps it
as a literal alternative: either the tail is eventually the all-Continue root,
or a nonzero tangent packet is extracted from one-stage positive-absorption
windows.  No periodic attachment or positive-charge return is inferred.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

/-- Limit data obtained by blowing up a positive-absorption tail window at its
literal absorption scale. -/
structure QuittingChargeTangentData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  /-- Conditional singleton owner occupation. -/
  mass : ι → ℝ
  /-- Common far-end annotation boundary. -/
  boundary : Payoff ι
  /-- Endpoint displacement per unit absorbed mass. -/
  tangent : Payoff ι
  mass_nonneg : ∀ owner, 0 ≤ mass owner
  mass_sum : ∑ owner, mass owner = 1
  tangent_eq : ∀ who,
    tangent who = quittingSingletonMixture reward mass who - boundary who
  solo_le_boundary : ∀ who,
    reward (quittingSingletonTerminal who) who ≤ boundary who
  punishment_le_boundary : ∀ who,
    quittingPunishmentValue reward who ≤ boundary who
  positive_mass_pins_boundary : ∀ owner, 0 < mass owner →
    boundary owner = reward (quittingSingletonTerminal owner) owner

/-- A charge-tangent datum with genuine nonzero motion. -/
structure QuittingChargeTangentPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    extends QuittingChargeTangentData reward where
  tangent_ne_zero : tangent ≠ 0

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

/-- Coordinatewise endpoint displacement divided by literal window
absorption. -/
def normalizedEndpointTangent
    (window : QuittingFiniteRootWindow
      (quittingDynamicDebtTailRoots seam.tail)) : Payoff ι :=
  fun who ↦ ((seam.tail window.start).1.1 who -
    (seam.tail (window.start + window.fuel)).1.1 who) /
      window.absorptionMass

/-- Restart delivery minus the far-end annotation is exactly the normalized
endpoint tangent. -/
theorem absorbingDelivery_sub_terminal_eq_normalizedEndpointTangent
    (window : QuittingFiniteRootWindow
      (quittingDynamicDebtTailRoots seam.tail))
    (habsorption : 0 < window.absorptionMass) (who : ι) :
    window.absorbingDelivery reward who -
        (seam.tail (window.start + window.fuel)).1.1 who =
      seam.normalizedEndpointTangent window who := by
  let roots := quittingDynamicDebtTailRoots seam.tail
  let prescribed : ℕ → ℝ := fun time ↦ (seam.tail time).1.1 who
  have hsurvival :
      quittingJointSurvivalWeight roots window.start window.fuel < 1 := by
    rw [window.absorptionMass_eq_one_sub_survivalWeight] at habsorption
    exact sub_pos.mp habsorption
  have hseam :=
    quittingWindowRestartDelivery_sub_terminal_eq_endpointDrift_div_absorption
      reward roots who prescribed (seam.isLivePrescribedValue who)
        window.start window.fuel hsurvival
  simpa [QuittingFiniteRootWindow.absorbingDelivery,
    normalizedEndpointTangent,
    window.absorptionMass_eq_one_sub_survivalWeight] using hseam

/-- Every sequence of positive-absorption windows escaping to infinity has a
subsequence whose normalized occupation and normalized endpoint tangent
converge to one coherent charge-tangent datum. -/
theorem exists_chargeTangentData_of_windows
    (window : ℕ → QuittingFiniteRootWindow
      (quittingDynamicDebtTailRoots seam.tail))
    (hstart : Tendsto (fun index ↦ (window index).start) atTop atTop)
    (habsorption : ∀ index, 0 < (window index).absorptionMass) :
    ∃ data : QuittingChargeTangentData reward,
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        (∀ owner, Tendsto
          (fun index ↦
            (window (subseq index)).normalizedSingletonOccupation owner)
          atTop (nhds (data.mass owner))) ∧
        ∀ who, Tendsto
          (fun index ↦
            seam.normalizedEndpointTangent (window (subseq index)) who)
          atTop (nhds (data.tangent who)) := by
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
  have hselectedEnd : Tendsto
      (fun index ↦
        (selectedWindow index).start + (selectedWindow index).fuel)
      atTop atTop :=
    Filter.tendsto_atTop_mono
      (fun index ↦ Nat.le_add_right (selectedWindow index).start
        (selectedWindow index).fuel)
      hselectedStart
  have hselectedAbsorption : ∀ index,
      0 < (selectedWindow index).absorptionMass :=
    fun index ↦ habsorption (subseq index)
  have hcoordinateLimit : ∀ owner, Tendsto
      (fun index ↦
        (selectedWindow index).normalizedSingletonOccupation owner)
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
      atTop (nhds (quittingSingletonMixture reward limitOccupation who)) := by
    intro who
    have hsingletonMixture : Tendsto (fun index ↦
        (selectedWindow index).absorptionNormalizedSingletonMixture
          reward who) atTop
        (nhds (quittingSingletonMixture reward limitOccupation who)) := by
      have hvector : Tendsto
          (fun index ↦ occupation (subseq index)) atTop
          (nhds limitOccupation) := hoccupationLimit
      have htendsto :=
        ((continuous_quittingSingletonMixture_apply
          (reward := reward) who).tendsto limitOccupation).comp hvector
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
          reward who (abs_reward_le_quittingRewardBound reward)
            (hselectedAbsorption index)
      · simpa using hcollision.const_mul (quittingRewardBound reward)
    have herror : Tendsto (fun index ↦
        (selectedWindow index).absorbingDelivery reward who -
          (selectedWindow index).absorptionNormalizedSingletonMixture
            reward who) atTop (nhds 0) :=
      (tendsto_zero_iff_abs_tendsto_zero _).2 herrorAbs
    convert herror.add hsingletonMixture using 1 <;> simp
  let boundary : Payoff ι := seam.limit.value
  let tangent : Payoff ι := fun who ↦
    quittingSingletonMixture reward limitOccupation who - boundary who
  have htangent : ∀ who, Tendsto
      (fun index ↦ seam.normalizedEndpointTangent
        (selectedWindow index) who) atTop (nhds (tangent who)) := by
    intro who
    have hendValue : Tendsto (fun index ↦
        (seam.tail ((selectedWindow index).start +
          (selectedWindow index).fuel)).1.1 who)
        atTop (nhds (boundary who)) :=
      (seam.value_tendsto who).comp hselectedEnd
    have hdifference := (hdelivery who).sub hendValue
    simpa [tangent, boundary,
      seam.absorbingDelivery_sub_terminal_eq_normalizedEndpointTangent
        (habsorption := hselectedAbsorption _)] using hdifference
  let data : QuittingChargeTangentData reward :=
    { mass := limitOccupation
      boundary := boundary
      tangent := tangent
      mass_nonneg := hmassNonneg
      mass_sum := hmassSum
      tangent_eq := fun _ ↦ rfl
      solo_le_boundary := fun who ↦ seam.limit.soloReward_le_value who
      punishment_le_boundary := fun who ↦ seam.punishmentValue_le_limitValue who
      positive_mass_pins_boundary := fun owner hpositive ↦
        seam.limitValue_eq_singleton_of_windowOccupation selectedWindow
          hselectedStart limitOccupation hcoordinateLimit owner hpositive }
  refine ⟨data, subseq, hsubseq, ?_, ?_⟩
  · intro owner
    exact hcoordinateLimit owner
  · intro who
    exact htangent who

end QuittingCounterexampleSeamWitness

namespace QuittingCounterexampleRegime

/-- A tail-derived tangent datum in a counterexample is either underfunded in
some coordinate or, after all underfunding is excluded, strictly funded on an
active owner coordinate.  The excluded third case is exactly a complementary
singleton packet and is already compiled to a uniform payoff. -/
theorem chargeTangentData_underfunded_or_active_funded
    (regime : QuittingCounterexampleRegime reward)
    (data : QuittingChargeTangentData reward) :
    (∃ who, data.tangent who < 0) ∨
      ∃ owner, 0 < data.mass owner ∧ 0 < data.tangent owner := by
  letI : Nonempty ι := regime.nonempty_players
  by_contra hsign
  push Not at hsign
  have hmix : ∀ who,
      data.boundary who ≤
        quittingSingletonMixture reward data.mass who := by
    intro who
    have htangent := data.tangent_eq who
    linarith [hsign.1 who]
  have hactive : ∀ owner, 0 < data.mass owner →
      quittingSingletonMixture reward data.mass owner =
        reward (quittingSingletonTerminal owner) owner := by
    intro owner hmass
    have htangentZero : data.tangent owner = 0 := by
      have hnonneg := hsign.1 owner
      have hnonpos := hsign.2 owner hmass
      linarith
    have hpin := data.positive_mass_pins_boundary owner hmass
    have htangent := data.tangent_eq owner
    linarith
  apply regime.not_exists_uniformEquilibriumPayoff
  exact exists_uniformEquilibriumPayoff_of_complementarySingletonMixture
    reward data.mass data.boundary data.mass_nonneg data.mass_sum hmix
      hactive data.solo_le_boundary data.punishment_le_boundary

/-- Every charge-tangent datum extracted in a counterexample has nonzero
tangent and therefore upgrades canonically to a charge-tangent packet. -/
def chargeTangentPacketOfData
    (regime : QuittingCounterexampleRegime reward)
    (data : QuittingChargeTangentData reward) :
    QuittingChargeTangentPacket reward where
  toQuittingChargeTangentData := data
  tangent_ne_zero := by
    obtain hnegative | hpositive :=
      regime.chargeTangentData_underfunded_or_active_funded data
    · rintro htangent
      obtain ⟨who, hwho⟩ := hnegative
      simp [htangent] at hwho
    · rintro htangent
      obtain ⟨owner, -, howner⟩ := hpositive
      simp [htangent] at howner

/-- The same finite sign dispatch for a packaged nonzero tangent. -/
theorem chargeTangentPacket_underfunded_or_active_funded
    (regime : QuittingCounterexampleRegime reward)
    (packet : QuittingChargeTangentPacket reward) :
    (∃ who, packet.tangent who < 0) ∨
      ∃ owner, 0 < packet.mass owner ∧ 0 < packet.tangent owner :=
  regime.chargeTangentData_underfunded_or_active_funded
    packet.toQuittingChargeTangentData

end QuittingCounterexampleRegime

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

/-- **Counterexample tail alternative.**  Either the selected exact-D tail is
eventually the literal all-Continue root, or one-stage positive-absorption
windows escaping to infinity produce a nonzero charge-tangent packet with
explicit occupation and tangent convergence along a subsequence. -/
theorem eventually_allContinue_or_exists_chargeTangentPacket :
    (∃ threshold, ∀ time, threshold ≤ time →
      quittingDynamicDebtTailRoots seam.tail time =
        (quittingAllContinueRoot : ι → PMF Bool)) ∨
    ∃ packet : QuittingChargeTangentPacket reward,
      ∃ window : ℕ → QuittingFiniteRootWindow
          (quittingDynamicDebtTailRoots seam.tail),
        Tendsto (fun index ↦ (window index).start) atTop atTop ∧
        (∀ index, 0 < (window index).absorptionMass) ∧
        (∀ owner, Tendsto
          (fun index ↦
            (window index).normalizedSingletonOccupation owner)
          atTop (nhds (packet.mass owner))) ∧
        ∀ who, Tendsto
          (fun index ↦ seam.normalizedEndpointTangent (window index) who)
          atTop (nhds (packet.tangent who)) := by
  by_cases hplateau : ∃ threshold, ∀ time, threshold ≤ time →
      quittingDynamicDebtTailRoots seam.tail time =
        (quittingAllContinueRoot : ι → PMF Bool)
  · exact Or.inl hplateau
  · right
    push Not at hplateau
    choose start hstart hroot using hplateau
    let window : ℕ → QuittingFiniteRootWindow
        (quittingDynamicDebtTailRoots seam.tail) :=
      fun index ↦ seam.finiteRootWindow (start index) 1
    have hstartTendsto : Tendsto (fun index ↦ (window index).start)
        atTop atTop := by
      change Tendsto start atTop atTop
      exact Filter.tendsto_atTop_mono hstart tendsto_id
    have habsorption : ∀ index, 0 < (window index).absorptionMass := by
      intro index
      have hmassNe : quittingRootAbsorptionMass
          (quittingDynamicDebtTailRoots seam.tail (start index)) ≠ 0 := by
        intro hzero
        apply hroot index
        apply eq_quittingAllContinueRoot_of_continueMass_eq_one
        unfold quittingRootAbsorptionMass at hzero
        linarith
      have hmassPos : 0 < quittingRootAbsorptionMass
          (quittingDynamicDebtTailRoots seam.tail (start index)) :=
        lt_of_le_of_ne
          (quittingRootAbsorptionMass_nonneg
            (quittingDynamicDebtTailRoots seam.tail (start index)))
          (Ne.symm hmassNe)
      simpa [window, finiteRootWindow,
        QuittingFiniteRootWindow.absorptionMass,
        QuittingFiniteRootWindow.survivalWeight,
        QuittingFiniteRootWindow.rootAt] using hmassPos
    obtain ⟨data, subseq, hsubseq, hoccupation, htangent⟩ :=
      seam.exists_chargeTangentData_of_windows window hstartTendsto habsorption
    let selectedWindow : ℕ → QuittingFiniteRootWindow
        (quittingDynamicDebtTailRoots seam.tail) :=
      fun index ↦ window (subseq index)
    let packet := regime.chargeTangentPacketOfData data
    refine ⟨packet, selectedWindow, ?_, ?_, ?_, ?_⟩
    · exact hstartTendsto.comp hsubseq.tendsto_atTop
    · exact fun index ↦ habsorption (subseq index)
    · intro owner
      exact hoccupation owner
    · intro who
      exact htangent who

end QuittingCounterexampleSeamWitness

end GameTheory
