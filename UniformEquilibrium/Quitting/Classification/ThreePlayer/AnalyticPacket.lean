/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ThreePlayer.AuxiliaryShift
import UniformEquilibrium.Quitting.Classification.ThreePlayer.SingletonMixtureCompiler
import UniformEquilibrium.Quitting.Debt.Marked.TimeAdvance

/-!
# The all-Continue analytic endpoint packet

This module supplies the analytic classification used by the unconditional
three-player theorem. The construction itself is valid for any finite
player type.  It is applied to the punishment-normalized auxiliary reward.

At an all-Continue analytic endpoint the quit rates vanish at zero, hence the
least quit-rate order `m` is positive.  Comparing it with the germ
ramification `q` gives three branches.

* If `q < m`, discount (the cemetery event) is asymptotically dominant.  The
  auxiliary endpoint value is zero, so the original reward is zero-solo.
* If `q = m`, the matching-order projective packet applies.
* If `m < q`, the cemetery mass vanishes.  Conditional singleton masses are
  the normalized leading coefficients, nonsingleton mass vanishes, the
  endpoint value is their singleton-reward mixture, and positive masses pin
  their owners.

The last two branches are translated back to the original reward coordinates
and normalized after conditioning away the cemetery.  Their common output is
the complementary singleton source packet consumed by the one-face
circulation compiler.
-/

noncomputable section

namespace GameTheory

open Filter Set Topology
open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The normalized source packet passed from the analytic endpoint to the
finite-dimensional singleton alternative.  Its singleton mixture is denoted
implicitly by `quittingSingletonMixture reward mass`. -/
structure QuittingNormalizedSingletonSourcePacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  mass : ι → ℝ
  target : Payoff ι
  mass_nonneg : ∀ owner, 0 ≤ mass owner
  mass_sum : ∑ owner, mass owner = 1
  mix_ge_target : ∀ who,
    target who ≤ quittingSingletonMixture reward mass who
  solo_le_target : ∀ who,
    reward (quittingSingletonTerminal who) who ≤ target who
  punishment_le_target : ∀ who,
    quittingPunishmentValue reward who ≤ target who
  positive_mass_pins_target : ∀ owner,
    0 < mass owner →
      target owner = reward (quittingSingletonTerminal owner) owner

/-- The capstone-facing alternative produced at an all-Continue auxiliary
endpoint: either Never is a uniform equilibrium, or a normalized
complementary singleton source packet exists. -/
def QuittingAuxiliaryAllContinueAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  (IsQuittingZeroSolo reward ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none (0 : Payoff ι)) ∨
    Nonempty (QuittingNormalizedSingletonSourcePacket reward)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem quittingProjectiveSingletonTerminal_eq_quittingSingletonTerminal
    (who : ι) :
    quittingProjectiveSingletonTerminal who = quittingSingletonTerminal who := by
  rfl

/-! ## Endpoint facts forced by all-Continue -/

/-- Continue mass one makes the whole endpoint row pure Continue. -/
theorem quittingGerm_endpointProfile_eq_allContinue_of_continueMass_eq_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1) :
    g.endpointProfile none = (quittingAllContinueRoot : ι → PMF Bool) := by
  funext who
  exact eq_pure_false_of_quittingStationaryContinueMass_eq_one hcontinue who

/-- Every quit-rate germ vanishes at the all-Continue endpoint. -/
theorem quittingGermQuitRate_zero_eq_zero_of_endpoint_allContinue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1)
    (owner : ι) :
    quittingGermQuitRate g owner 0 = 0 := by
  rw [← quittingGerm_endpointProfile_apply_true_toReal g owner]
  rw [quittingGerm_endpointProfile_eq_allContinue_of_continueMass_eq_one
    g hcontinue]
  change ((PMF.pure false : PMF Bool) true).toReal = 0
  exact Math.Probability.pure_apply_toReal_of_ne _ _ (by decide)

/-- Pointwise continuity therefore sends every quit rate to zero from the
right, without any matching-order assumption. -/
theorem quittingGermQuitRate_tendsto_zero_of_endpoint_allContinue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1)
    (owner : ι) :
    Tendsto (quittingGermQuitRate g owner)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (analyticAt_quittingGermQuitRate g owner).continuousAt.tendsto
    |>.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa [quittingGermQuitRate_zero_eq_zero_of_endpoint_allContinue
    g hcontinue owner] using h

/-- At an all-Continue endpoint the finite family's least analytic order is
positive. -/
theorem one_le_quittingGerm_familyAnalyticOrder_of_endpoint_allContinue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1) :
    (1 : ℕ∞) ≤ Math.familyAnalyticOrder (quittingGermQuitRate g) := by
  unfold Math.familyAnalyticOrder
  apply Finset.le_inf
  intro owner _
  exact Order.one_le_iff_ne_zero.mpr <|
    analyticOrderAt_ne_zero.mpr
      ⟨analyticAt_quittingGermQuitRate g owner,
        quittingGermQuitRate_zero_eq_zero_of_endpoint_allContinue
          g hcontinue owner⟩

/-- Natural-number form of the preceding order bound. -/
theorem one_le_quittingGerm_leadingOrder_of_endpoint_allContinue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1)
    {m : ℕ}
    (horder : Math.familyAnalyticOrder (quittingGermQuitRate g) = m) :
    1 ≤ m := by
  have h :=
    one_le_quittingGerm_familyAnalyticOrder_of_endpoint_allContinue g hcontinue
  rw [horder] at h
  exact_mod_cast h

/-- The discount-complement power tends to zero for every analytic Bellman
germ. -/
theorem quittingGermDiscountComplement_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) :
    Tendsto (fun t : ℝ => t ^ g.ramification)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hfull : Tendsto (fun t : ℝ => t ^ g.ramification)
      (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ g.ramification)) :=
    (continuousAt_id.pow g.ramification).tendsto
  have hright := hfull.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa [zero_pow g.ramification_pos.ne'] using hright

/-- Exact endpoint Nash at an all-Continue row puts every singleton reward
below the analytic endpoint value. -/
theorem quittingGerm_solo_le_endpointValue_of_endpoint_allContinue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1)
    (who : ι) :
    reward (quittingSingletonTerminal who) who ≤
      quittingGermValue g 0 who := by
  have hnash := quittingGerm_endpoint_endpointNash g
  have hquit := (hnash who).1
  rw [quittingGerm_endpointProfile_eq_allContinue_of_continueMass_eq_one
    g hcontinue] at hquit
  norm_num [quittingAllContinueRoot] at hquit
  exact hquit

/-! ## Pure-Quit convergence with no matching assumption -/

/-- If all quit-rate coordinates vanish, forcing one owner to Quit converges
to that owner's singleton terminal event. -/
theorem quittingGermPureQuitCoalitionValue_tendsto_singleton_of_rates_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {g : (quittingGame reward).AnalyticBellmanGerm}
    (hrates : ∀ other,
      Tendsto (quittingGermQuitRate g other)
        (𝓝[>] (0 : ℝ)) (𝓝 0))
    (owner who : ι) :
    Tendsto (quittingGermPureQuitCoalitionValue g owner who)
      (𝓝[>] (0 : ℝ))
      (𝓝 (reward (quittingProjectiveSingletonTerminal owner) who)) := by
  let pureRates : ι → ℝ := Function.update (fun _ => 0) owner 1
  have hupdated : ∀ other,
      Tendsto
        (fun t => Function.update
          (fun player => quittingGermQuitRate g player t) owner 1 other)
        (𝓝[>] (0 : ℝ)) (𝓝 (pureRates other)) := by
    intro other
    by_cases hother : other = owner
    · subst other
      simp [pureRates]
    · simpa [pureRates, Function.update, hother] using hrates other
  have hsum :
      Tendsto
        (fun t => ∑ S : Finset ι,
          coalitionMass
              (Function.update
                (fun other => quittingGermQuitRate g other t) owner 1) S *
            quittingProjectiveCoalitionReward reward S who)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ S : Finset ι,
          coalitionMass pureRates S *
            quittingProjectiveCoalitionReward reward S who)) := by
    apply tendsto_finsetSum Finset.univ
    intro S _
    exact (coalitionMass_tendsto
      (fun other t => Function.update
        (fun player => quittingGermQuitRate g player t) owner 1 other)
      pureRates S hupdated).mul tendsto_const_nhds
  have hlimit :
      (∑ S : Finset ι,
          coalitionMass pureRates S *
            quittingProjectiveCoalitionReward reward S who) =
        reward (quittingProjectiveSingletonTerminal owner) who := by
    let pureRoot : ι → PMF Bool := fun other =>
      PMF.pure (if other = owner then true else false)
    have hpureRates :
        (fun other => (pureRoot other true).toReal) = pureRates := by
      funext other
      by_cases hother : other = owner
      · subst other
        simp [pureRoot, pureRates]
      · simp [pureRoot, pureRates, hother]
    have hexpansion :=
      quittingRootAbsorbingContribution_eq_sum_coalitionMass reward pureRoot who
    rw [hpureRates] at hexpansion
    rw [← hexpansion]
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    rw [pmfPi_pure, expect_pure]
    have hquitters :
        quittingQuitters (fun other => if other = owner then true else false) =
          {owner} := by
      ext other
      by_cases hother : other = owner <;>
        simp [quittingQuitters, hother]
    unfold quittingRootPayoff
    rw [dif_pos (by simp)]
    apply congrArg (fun terminal => reward terminal who)
    exact Subtype.ext hquitters
  unfold quittingGermPureQuitCoalitionValue
  rw [hlimit] at hsum
  exact hsum

/-- A positive limiting quit share pins its owner's auxiliary endpoint value
to its singleton reward. -/
theorem quittingGerm_endpointValue_eq_solo_of_positive_leadingShare
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1)
    (leading : ι → ℝ)
    (_hleadingSum : 0 < ∑ other, leading other)
    (hshare : ∀ owner,
      Tendsto
        (fun t => quittingGermQuitRate g owner t /
          ∑ other, quittingGermQuitRate g other t)
        (𝓝[>] (0 : ℝ))
        (𝓝 (leading owner / ∑ other, leading other)))
    (htotal :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        0 < ∑ other, quittingGermQuitRate g other t)
    (owner : ι)
    (hpositive : 0 < leading owner / ∑ other, leading other) :
    quittingGermValue g 0 owner =
      reward (quittingProjectiveSingletonTerminal owner) owner := by
  have hsharePos : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < quittingGermQuitRate g owner t /
        ∑ other, quittingGermQuitRate g other t :=
    (hshare owner).eventually (Ioi_mem_nhds hpositive)
  have hquitPos : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < quittingGermQuitRate g owner t := by
    filter_upwards [hsharePos, htotal] with t hratio hsum
    rcases div_pos_iff.mp hratio with hpos | hneg
    · exact hpos.1
    · exact absurd hneg.2 (not_lt_of_ge hsum.le)
  have hltOne : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from
      Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
  have hexact : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      quittingGermValue g t owner =
        (1 - t ^ g.ramification) *
          quittingGermPureQuitCoalitionValue g owner owner t := by
    filter_upwards [eventually_mem_Ioo_radius g, hltOne, hquitPos]
      with t ht ht1 hquit
    have hnash := isεQuittingRootEndpointNash_quittingGermRoot g ht ht1
    have hrootQuit :
        0 < ((quittingGermRoot g ht owner) true).toReal := by
      simpa [quittingGermRoot_apply_true_toReal g ht] using hquit
    have hpinned :=
      quittingRootQuitPayoff_eq_successor_of_endpointNash_of_quit_pos
        reward (quittingGermValue g t) (quittingGermRoot g ht) owner
        hnash hrootQuit
    have hrec := quittingGermValue_eq_smul_rootSuccessorPayoff g ht owner
    rw [← hpinned,
      quittingGermRootQuitPayoff_eq_pureQuitCoalitionValue g ht owner] at hrec
    exact hrec
  have hdiscount : Tendsto (fun t : ℝ => 1 - t ^ g.ramification)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
    simpa using hone.sub (quittingGermDiscountComplement_tendsto_zero g)
  have hrates := fun other =>
    quittingGermQuitRate_tendsto_zero_of_endpoint_allContinue
      g hcontinue other
  have hpure :=
    quittingGermPureQuitCoalitionValue_tendsto_singleton_of_rates_tendsto_zero
      hrates owner owner
  have hexactEq :
      (fun t : ℝ => quittingGermValue g t owner) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t => (1 - t ^ g.ramification) *
          quittingGermPureQuitCoalitionValue g owner owner t) := hexact
  have hfromPinned : Tendsto (fun t : ℝ => quittingGermValue g t owner)
      (𝓝[>] (0 : ℝ))
      (𝓝 (reward (quittingProjectiveSingletonTerminal owner) owner)) := by
    have hproduct := hdiscount.mul hpure
    simpa using hproduct.congr' hexactEq.symm
  exact tendsto_nhds_unique (quittingGermValue_tendsto_zero g owner) hfromPinned

/-! ## Conditioning a projective auxiliary packet -/

/-- The auxiliary endpoint value is coordinatewise nonnegative. -/
theorem quittingAuxiliaryGermEndpointValue_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame (quittingAuxiliaryReward reward)).AnalyticBellmanGerm)
    (who : ι) :
    0 ≤ quittingGermValue g 0 who := by
  exact quittingAuxiliaryGermValue_zero_nonneg reward g who

/-- Conditioning a projective auxiliary singleton packet on real absorption,
then undoing the reward translation, gives the normalized source packet used
by the finite-dimensional alternative. -/
def normalizedSingletonSourcePacket_of_auxiliaryProjectivePacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame (quittingAuxiliaryReward reward)).AnalyticBellmanGerm)
    (packet :
      QuittingProjectiveSingletonPacket (quittingAuxiliaryReward reward))
    (hvalue : packet.value = quittingGermValue g 0)
    (hcemetery : packet.cemetery < 1)
    (hvalueNonneg : ∀ who, 0 ≤ quittingGermValue g 0 who) :
    QuittingNormalizedSingletonSourcePacket reward := by
  let singletonTotal : ℝ := ∑ owner, packet.singleton owner
  have hsum : singletonTotal = 1 - packet.cemetery := by
    dsimp only [singletonTotal]
    linarith [packet.total]
  have hsumPos : 0 < singletonTotal := by
    rw [hsum]
    exact sub_pos.mpr hcemetery
  have hsumLe : singletonTotal ≤ 1 := by
    rw [hsum]
    linarith [packet.cemetery_nonneg]
  let mass : ι → ℝ := fun owner => packet.singleton owner / singletonTotal
  refine {
    mass := mass
    target := quittingAuxiliaryTarget reward (quittingGermValue g 0)
    mass_nonneg := ?_
    mass_sum := ?_
    mix_ge_target := ?_
    solo_le_target := ?_
    punishment_le_target := ?_
    positive_mass_pins_target := ?_ }
  · intro owner
    exact div_nonneg (packet.singleton_nonneg owner) hsumPos.le
  · dsimp only [mass]
    rw [← Finset.sum_div]
    dsimp only [singletonTotal]
    exact div_self hsumPos.ne'
  · intro who
    have hshiftMix := packet.value_eq_singleton_mix who
    simp only [quittingAuxiliaryReward, quittingRewardShift_apply,
      quittingProjectiveSingletonTerminal_eq_quittingSingletonTerminal]
        at hshiftMix
    have horiginalSum :
        (∑ owner, packet.singleton owner *
          reward (quittingSingletonTerminal owner) who) =
          packet.value who +
            singletonTotal * quittingAuxiliaryLive reward who := by
      rw [hshiftMix]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      dsimp only [singletonTotal]
      ring
    have hmix :
        quittingSingletonMixture reward mass who =
          packet.value who / singletonTotal +
            quittingAuxiliaryLive reward who := by
      unfold quittingSingletonMixture mass
      simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div, horiginalSum, add_div]
      field_simp [hsumPos.ne']
    have hscaled : quittingGermValue g 0 who ≤
        quittingGermValue g 0 who / singletonTotal := by
      rw [le_div_iff₀ hsumPos]
      exact mul_le_of_le_one_right (hvalueNonneg who) hsumLe
    rw [hmix, hvalue]
    simp only [quittingAuxiliaryTarget, quittingPayoffUnshift_apply]
    linarith [hscaled]
  · intro who
    have hsolo := packet.solo_le_value who
    rw [hvalue] at hsolo
    simp only [quittingProjectiveSingletonTerminal_eq_quittingSingletonTerminal,
      quittingAuxiliaryReward, quittingRewardShift_apply] at hsolo
    simp only [quittingAuxiliaryTarget, quittingPayoffUnshift_apply]
    exact sub_le_iff_le_add.mp hsolo
  · intro who
    exact quittingPunishmentValue_le_auxiliaryEndpointTarget reward g who
  · intro owner hmassPos
    have hsingletonPos : 0 < packet.singleton owner := by
      dsimp only [mass] at hmassPos
      rcases div_pos_iff.mp hmassPos with hpos | hneg
      · exact hpos.1
      · exact absurd hneg.2 (not_lt_of_ge hsumPos.le)
    have hpinned := packet.positive_singleton_pins owner hsingletonPos
    rw [hvalue] at hpinned
    simp only [quittingProjectiveSingletonTerminal_eq_quittingSingletonTerminal,
      quittingAuxiliaryReward, quittingRewardShift_apply] at hpinned
    simp only [quittingAuxiliaryTarget, quittingPayoffUnshift_apply]
    calc
      quittingGermValue g 0 owner + quittingAuxiliaryLive reward owner =
          (reward (quittingSingletonTerminal owner) owner -
            quittingAuxiliaryLive reward owner) +
            quittingAuxiliaryLive reward owner := by
            exact congrArg (fun z : ℝ => z + quittingAuxiliaryLive reward owner)
              hpinned
      _ = reward (quittingSingletonTerminal owner) owner := by ring

/-! ## The fast-quitting (`m < q`) packet -/

/-- Analytic data retained in the branch where quitting is asymptotically
faster than the discount complement.  The total quit mass and absorption are
asymptotic, while discount divided by absorption tends to zero. -/
structure QuittingGermFastLeadingData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame reward).AnalyticBellmanGerm) where
  leading : ι → ℝ
  leading_nonneg : ∀ owner, 0 ≤ leading owner
  leading_sum_pos : 0 < ∑ owner, leading owner
  eventually_total_pos :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < ∑ owner, quittingGermQuitRate g owner t
  share_tendsto : ∀ owner,
    Tendsto
      (fun t => quittingGermQuitRate g owner t /
        ∑ other, quittingGermQuitRate g other t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (leading owner / ∑ other, leading other))
  total_div_absorption_tendsto :
    Tendsto
      (fun t => (∑ owner, quittingGermQuitRate g owner t) /
        quittingGermAbsorption g t)
      (𝓝[>] (0 : ℝ)) (𝓝 1)
  discount_div_absorption_tendsto :
    Tendsto
      (fun t => t ^ g.ramification / quittingGermAbsorption g t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)
  quitRate_tendsto_zero : ∀ owner,
    Tendsto (quittingGermQuitRate g owner)
      (𝓝[>] (0 : ℝ)) (𝓝 0)

namespace QuittingGermFastLeadingData

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {g : (quittingGame reward).AnalyticBellmanGerm}

/-- Conditional limiting mass of one singleton owner. -/
def normalizedMass (data : QuittingGermFastLeadingData reward g)
    (owner : ι) : ℝ :=
  data.leading owner / ∑ other, data.leading other

theorem normalizedMass_nonneg
    (data : QuittingGermFastLeadingData reward g) (owner : ι) :
    0 ≤ data.normalizedMass owner :=
  div_nonneg (data.leading_nonneg owner) data.leading_sum_pos.le

theorem normalizedMass_sum
    (data : QuittingGermFastLeadingData reward g) :
    ∑ owner, data.normalizedMass owner = 1 := by
  unfold normalizedMass
  rw [← Finset.sum_div]
  exact div_self data.leading_sum_pos.ne'

/-- All players other than a specified owner continue with probability tending
to one. -/
theorem excludedContinueProduct_tendsto_one
    (data : QuittingGermFastLeadingData reward g) (owner : ι) :
    Tendsto
      (fun t : ℝ => ∏ other ∈ Finset.univ.erase owner,
        (1 - quittingGermQuitRate g other t))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have hprod :
      Tendsto
        (fun t : ℝ => ∏ other ∈ Finset.univ.erase owner,
          (1 - quittingGermQuitRate g other t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∏ _other ∈ Finset.univ.erase owner, (1 : ℝ))) :=
    tendsto_finsetProd (Finset.univ.erase owner)
      (fun other _ => by
        simpa using hone.sub (data.quitRate_tendsto_zero other))
  simpa using hprod

/-- A singleton event, normalized by total absorption, tends to its conditional
leading mass. -/
theorem singletonProbability_div_absorption_tendsto
    (data : QuittingGermFastLeadingData reward g) (owner : ι) :
    Tendsto
      (fun t => quittingGermSingletonProbability g owner t /
        quittingGermAbsorption g t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (data.normalizedMass owner)) := by
  have hraw := ((data.share_tendsto owner).mul
      data.total_div_absorption_tendsto).mul
        (data.excludedContinueProduct_tendsto_one owner)
  have hraw' :
      Tendsto
        (fun t =>
          (quittingGermQuitRate g owner t /
              ∑ other, quittingGermQuitRate g other t) *
            ((∑ other, quittingGermQuitRate g other t) /
              quittingGermAbsorption g t) *
            ∏ other ∈ Finset.univ.erase owner,
              (1 - quittingGermQuitRate g other t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (data.normalizedMass owner)) := by
    simpa [normalizedMass] using hraw
  refine hraw'.congr' ?_
  filter_upwards [eventually_mem_Ioo_radius g,
    data.eventually_total_pos] with t ht htotal
  have habs : 0 < quittingGermAbsorption g t :=
    quittingGermAbsorption_pos g ht htotal
  unfold quittingGermSingletonProbability
  field_simp [htotal.ne', habs.ne']

/-- In the fast branch the first-event denominator, divided by real
absorption, tends to one. -/
theorem firstEventDenominator_div_absorption_tendsto
    (data : QuittingGermFastLeadingData reward g) :
    Tendsto
      (fun t => quittingGermFirstEventDenominator g t /
        quittingGermAbsorption g t)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have hfactor := hone.sub (quittingGermDiscountComplement_tendsto_zero g)
  have hraw := data.discount_div_absorption_tendsto.add hfactor
  have hraw' : Tendsto
      (fun t => t ^ g.ramification / quittingGermAbsorption g t +
        (1 - t ^ g.ramification))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using hraw
  refine hraw'.congr' ?_
  filter_upwards [eventually_mem_Ioo_radius g,
    data.eventually_total_pos] with t ht htotal
  have habs : 0 < quittingGermAbsorption g t :=
    quittingGermAbsorption_pos g ht htotal
  unfold quittingGermFirstEventDenominator
  field_simp [habs.ne']

/-- Cemetery mass vanishes in the fast branch. -/
theorem cemeteryFirstEventWeight_tendsto_zero
    (data : QuittingGermFastLeadingData reward g) :
    Tendsto (quittingGermCemeteryFirstEventWeight g)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hratio := data.discount_div_absorption_tendsto.div
    data.firstEventDenominator_div_absorption_tendsto one_ne_zero
  have hratio' : Tendsto
      (fun t =>
        (t ^ g.ramification / quittingGermAbsorption g t) /
          (quittingGermFirstEventDenominator g t /
            quittingGermAbsorption g t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hratio using 1
    · funext t
      rfl
    · norm_num
  have hdenomPos : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < quittingGermFirstEventDenominator g t /
        quittingGermAbsorption g t :=
    data.firstEventDenominator_div_absorption_tendsto.eventually
      (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  refine hratio'.congr' ?_
  filter_upwards [eventually_mem_Ioo_radius g,
    data.eventually_total_pos, hdenomPos] with t ht htotal hdenom
  have habs : 0 < quittingGermAbsorption g t :=
    quittingGermAbsorption_pos g ht htotal
  have hD : quittingGermFirstEventDenominator g t ≠ 0 := by
    intro hzero
    rw [hzero, zero_div] at hdenom
    exact (lt_irrefl 0) hdenom
  unfold quittingGermCemeteryFirstEventWeight
  field_simp [habs.ne', hD]

/-- Each singleton first-event mass converges to its normalized leading
coefficient. -/
theorem singletonFirstEventWeight_tendsto
    (data : QuittingGermFastLeadingData reward g) (owner : ι) :
    Tendsto (quittingGermSingletonFirstEventWeight g owner)
      (𝓝[>] (0 : ℝ))
      (𝓝 (data.normalizedMass owner)) := by
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have hfactor := hone.sub (quittingGermDiscountComplement_tendsto_zero g)
  have hnumerator := hfactor.mul
    (data.singletonProbability_div_absorption_tendsto owner)
  have hraw := hnumerator.div
    data.firstEventDenominator_div_absorption_tendsto one_ne_zero
  have hraw' : Tendsto
      (fun t =>
        ((1 - t ^ g.ramification) *
            (quittingGermSingletonProbability g owner t /
              quittingGermAbsorption g t)) /
          (quittingGermFirstEventDenominator g t /
            quittingGermAbsorption g t))
      (𝓝[>] (0 : ℝ))
      (𝓝 (data.normalizedMass owner)) := by
    convert hraw using 1
    · funext t
      rfl
    · norm_num
  have hdenomPos : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < quittingGermFirstEventDenominator g t /
        quittingGermAbsorption g t :=
    data.firstEventDenominator_div_absorption_tendsto.eventually
      (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  refine hraw'.congr' ?_
  filter_upwards [eventually_mem_Ioo_radius g,
    data.eventually_total_pos, hdenomPos] with t ht htotal hdenom
  have habs : 0 < quittingGermAbsorption g t :=
    quittingGermAbsorption_pos g ht htotal
  have hD : quittingGermFirstEventDenominator g t ≠ 0 := by
    intro hzero
    rw [hzero, zero_div] at hdenom
    exact (lt_irrefl 0) hdenom
  unfold quittingGermSingletonFirstEventWeight
  field_simp [habs.ne', hD]

/-- Total real-absorption first-event mass tends to one. -/
theorem realAbsorptionFirstEventWeight_tendsto_one
    (data : QuittingGermFastLeadingData reward g) :
    Tendsto (quittingGermRealAbsorptionFirstEventWeight g)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have hfactor := hone.sub (quittingGermDiscountComplement_tendsto_zero g)
  have hraw := hfactor.div
    data.firstEventDenominator_div_absorption_tendsto one_ne_zero
  have hraw' : Tendsto
      (fun t => (1 - t ^ g.ramification) /
        (quittingGermFirstEventDenominator g t /
          quittingGermAbsorption g t))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    convert hraw using 1
    · funext t
      rfl
    · norm_num
  have hdenomPos : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < quittingGermFirstEventDenominator g t /
        quittingGermAbsorption g t :=
    data.firstEventDenominator_div_absorption_tendsto.eventually
      (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  refine hraw'.congr' ?_
  filter_upwards [eventually_mem_Ioo_radius g,
    data.eventually_total_pos, hdenomPos] with t ht htotal hdenom
  have habs : 0 < quittingGermAbsorption g t :=
    quittingGermAbsorption_pos g ht htotal
  have hD : quittingGermFirstEventDenominator g t ≠ 0 := by
    intro hzero
    rw [hzero, zero_div] at hdenom
    exact (lt_irrefl 0) hdenom
  unfold quittingGermRealAbsorptionFirstEventWeight
  field_simp [habs.ne', hD]

/-- After singleton events are removed, the residual first-event mass tends to
zero. -/
theorem nonsingletonFirstEventWeight_tendsto_zero
    (data : QuittingGermFastLeadingData reward g) :
    Tendsto (quittingGermNonsingletonFirstEventWeight g)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsingle :
      Tendsto
        (fun t : ℝ => ∑ owner,
          quittingGermSingletonFirstEventWeight g owner t)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ owner, data.normalizedMass owner)) :=
    tendsto_finsetSum Finset.univ
      (fun owner _ => data.singletonFirstEventWeight_tendsto owner)
  rw [data.normalizedMass_sum] at hsingle
  have h := data.realAbsorptionFirstEventWeight_tendsto_one.sub hsingle
  change Tendsto
    (fun t : ℝ => quittingGermRealAbsorptionFirstEventWeight g t -
      ∑ owner, quittingGermSingletonFirstEventWeight g owner t)
    (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa using h

/-- The reward carried by nonsingleton first events vanishes with their mass. -/
theorem nonsingletonRewardFirstEventWeight_tendsto_zero
    (data : QuittingGermFastLeadingData reward g) (who : ι) :
    Tendsto (quittingGermNonsingletonRewardFirstEventWeight g who)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hscaled : Tendsto
      (fun t => quittingRewardBound reward *
        quittingGermNonsingletonFirstEventWeight g t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using data.nonsingletonFirstEventWeight_tendsto_zero.const_mul
      (quittingRewardBound reward)
  have hltOne : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from
      Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
  have habs : Tendsto
      (fun t => |quittingGermNonsingletonRewardFirstEventWeight g who t|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun t => abs_nonneg _
    · filter_upwards [eventually_mem_Ioo_radius g, hltOne] with t ht ht1
      exact abs_quittingGermNonsingletonRewardFirstEventWeight_le
        g ht ht1 who
    · exact hscaled
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa [Real.norm_eq_abs] using habs

/-- The fast endpoint value is exactly the conditional singleton-reward
mixture. -/
theorem value_eq_singleton_mix
    (data : QuittingGermFastLeadingData reward g) (who : ι) :
    quittingGermValue g 0 who =
      ∑ owner, data.normalizedMass owner *
        reward (quittingProjectiveSingletonTerminal owner) who := by
  have hsingle : Tendsto
      (fun t => ∑ owner,
        quittingGermSingletonFirstEventWeight g owner t *
          reward (quittingProjectiveSingletonTerminal owner) who)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ owner, data.normalizedMass owner *
        reward (quittingProjectiveSingletonTerminal owner) who)) := by
    apply tendsto_finsetSum Finset.univ
    intro owner _
    exact (data.singletonFirstEventWeight_tendsto owner).mul
      tendsto_const_nhds
  have hright := hsingle.add
    (data.nonsingletonRewardFirstEventWeight_tendsto_zero who)
  have hltOne : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from
      Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
  have hexact :
      (fun t => quittingGermValue g t who) =ᶠ[𝓝[>] (0 : ℝ)]
        fun t =>
          (∑ owner, quittingGermSingletonFirstEventWeight g owner t *
            reward (quittingProjectiveSingletonTerminal owner) who) +
          quittingGermNonsingletonRewardFirstEventWeight g who t := by
    filter_upwards [eventually_mem_Ioo_radius g, hltOne] with t ht ht1
    exact quittingGermValue_eq_singleton_sum_add_nonsingletonReward
      g ht ht1 who
  have hfromRight : Tendsto (fun t => quittingGermValue g t who)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∑ owner, data.normalizedMass owner *
        reward (quittingProjectiveSingletonTerminal owner) who) + 0)) :=
    hright.congr' hexact.symm
  simpa using tendsto_nhds_unique
    (quittingGermValue_tendsto_zero g who) hfromRight

/-- Every singleton reward lies below the fast endpoint value. -/
theorem solo_le_value
    (_data : QuittingGermFastLeadingData reward g)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1)
    (who : ι) :
    reward (quittingProjectiveSingletonTerminal who) who ≤
      quittingGermValue g 0 who := by
  simpa using
    quittingGerm_solo_le_endpointValue_of_endpoint_allContinue
      g hcontinue who

/-- Positive fast singleton mass pins its owner's endpoint value. -/
theorem positive_singleton_pins
    (data : QuittingGermFastLeadingData reward g)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1)
    (owner : ι)
    (hpositive : 0 < data.normalizedMass owner) :
    quittingGermValue g 0 owner =
      reward (quittingProjectiveSingletonTerminal owner) owner := by
  exact quittingGerm_endpointValue_eq_solo_of_positive_leadingShare
    g hcontinue data.leading data.leading_sum_pos data.share_tendsto
      data.eventually_total_pos owner hpositive

/-- Fast leading data construct the cemetery-zero projective packet, including
the complete residual, value, and complementarity limits. -/
def toProjectiveSingletonPacket
    (data : QuittingGermFastLeadingData reward g)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1) :
    QuittingProjectiveSingletonPacket reward where
  cemetery := 0
  singleton := data.normalizedMass
  value := quittingGermValue g 0
  cemetery_nonneg := le_rfl
  singleton_nonneg := data.normalizedMass_nonneg
  total := by simp [data.normalizedMass_sum]
  value_eq_singleton_mix := data.value_eq_singleton_mix
  solo_le_value := data.solo_le_value hcontinue
  positive_singleton_pins := data.positive_singleton_pins hcontinue

end QuittingGermFastLeadingData

/-! ## The slow-quitting (`q < m`) Never branch -/

/-- If discount divided by real absorption tends to infinity, real absorption
divided by discount tends to zero. -/
theorem quittingGermAbsorption_div_discount_tendsto_zero_of_discount_dominates
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (habsorption :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < quittingGermAbsorption g t)
    (hdominates : Tendsto
      (fun t : ℝ => t ^ g.ramification / quittingGermAbsorption g t)
      (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto
      (fun t : ℝ => quittingGermAbsorption g t / t ^ g.ramification)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hinv : Tendsto
      (fun t : ℝ =>
        (t ^ g.ramification / quittingGermAbsorption g t)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_inv_atTop_zero :
      Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hdominates
  refine hinv.congr' ?_
  filter_upwards [self_mem_nhdsWithin, habsorption] with t ht habs
  change 0 < t at ht
  have hpow : t ^ g.ramification ≠ 0 :=
    pow_ne_zero _ (ne_of_gt ht)
  field_simp [hpow, habs.ne']

/-- In the dominant-cemetery branch the first-event denominator, divided by
discount, tends to one. -/
theorem quittingGermFirstEventDenominator_div_discount_tendsto_one_of_discount_dominates
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (habsorption :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < quittingGermAbsorption g t)
    (hdominates : Tendsto
      (fun t : ℝ => t ^ g.ramification / quittingGermAbsorption g t)
      (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto
      (fun t : ℝ => quittingGermFirstEventDenominator g t /
        t ^ g.ramification)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hA :=
    quittingGermAbsorption_div_discount_tendsto_zero_of_discount_dominates
      g habsorption hdominates
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have hfactor := hone.sub (quittingGermDiscountComplement_tendsto_zero g)
  have hraw := hone.add (hfactor.mul hA)
  have hraw' : Tendsto
      (fun t : ℝ => 1 + (1 - t ^ g.ramification) *
        (quittingGermAbsorption g t / t ^ g.ramification))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using hraw
  refine hraw'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have hpow : t ^ g.ramification ≠ 0 :=
    pow_ne_zero _ (ne_of_gt ht)
  unfold quittingGermFirstEventDenominator
  field_simp [hpow]

/-- The normalized cemetery first-event mass tends to one in the slow-quitting
branch. -/
theorem quittingGermCemeteryFirstEventWeight_tendsto_one_of_discount_dominates
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (habsorption :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < quittingGermAbsorption g t)
    (hdominates : Tendsto
      (fun t : ℝ => t ^ g.ramification / quittingGermAbsorption g t)
      (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto (quittingGermCemeteryFirstEventWeight g)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hdenom :=
    quittingGermFirstEventDenominator_div_discount_tendsto_one_of_discount_dominates
      g habsorption hdominates
  have hinv := hdenom.inv₀ one_ne_zero
  have hinv' : Tendsto (fun t =>
      (quittingGermFirstEventDenominator g t / t ^ g.ramification)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using hinv
  have hdenomPos : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < quittingGermFirstEventDenominator g t / t ^ g.ramification :=
    hdenom.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  refine hinv'.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hdenomPos] with t ht hdenomRatio
  change 0 < t at ht
  have hpow : t ^ g.ramification ≠ 0 :=
    pow_ne_zero _ (ne_of_gt ht)
  have hD : quittingGermFirstEventDenominator g t ≠ 0 := by
    intro hzero
    rw [hzero, zero_div] at hdenomRatio
    exact (lt_irrefl 0) hdenomRatio
  unfold quittingGermCemeteryFirstEventWeight
  field_simp [hpow, hD]

/-- Total normalized real-absorption mass tends to zero when cemetery is
dominant. -/
theorem quittingGermRealAbsorptionFirstEventWeight_tendsto_zero_of_discount_dominates
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (habsorption :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < quittingGermAbsorption g t)
    (hdominates : Tendsto
      (fun t : ℝ => t ^ g.ramification / quittingGermAbsorption g t)
      (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto (quittingGermRealAbsorptionFirstEventWeight g)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hA :=
    quittingGermAbsorption_div_discount_tendsto_zero_of_discount_dominates
      g habsorption hdominates
  have hdenom :=
    quittingGermFirstEventDenominator_div_discount_tendsto_one_of_discount_dominates
      g habsorption hdominates
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have hfactor := hone.sub (quittingGermDiscountComplement_tendsto_zero g)
  have hnumerator := hfactor.mul hA
  have hraw := hnumerator.div hdenom one_ne_zero
  have hraw' : Tendsto
      (fun t : ℝ =>
        ((1 - t ^ g.ramification) *
            (quittingGermAbsorption g t / t ^ g.ramification)) /
          (quittingGermFirstEventDenominator g t / t ^ g.ramification))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hraw using 1
    · funext t
      rfl
    · norm_num
  have hdenomPos : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < quittingGermFirstEventDenominator g t / t ^ g.ramification :=
    hdenom.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  refine hraw'.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hdenomPos] with t ht hdenomRatio
  change 0 < t at ht
  have hpow : t ^ g.ramification ≠ 0 :=
    pow_ne_zero _ (ne_of_gt ht)
  have hD : quittingGermFirstEventDenominator g t ≠ 0 := by
    intro hzero
    rw [hzero, zero_div] at hdenomRatio
    exact (lt_irrefl 0) hdenomRatio
  unfold quittingGermRealAbsorptionFirstEventWeight
  field_simp [hpow, hD]

/-- Pointwise Bellman control by total normalized real-absorption mass. -/
theorem abs_quittingGermValue_le_rewardBound_mul_realAbsorptionFirstEventWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) g.radius) (ht1 : t < 1)
    (who : ι) :
    |quittingGermValue g t who| ≤
      quittingRewardBound reward *
        quittingGermRealAbsorptionFirstEventWeight g t := by
  have hfactor : 0 ≤ 1 - t ^ g.ramification :=
    (quittingGerm_discountFactor_pos g ht ht1).le
  have habsNonneg : 0 ≤ quittingGermAbsorption g t := by
    rw [quittingGermAbsorption_eq g ht]
    exact sub_nonneg.mpr (quittingStationaryContinueMass_le_one _)
  have hdenomPos : 0 < quittingGermFirstEventDenominator g t := by
    unfold quittingGermFirstEventDenominator
    exact add_pos_of_pos_of_nonneg (pow_pos ht.1 _)
      (mul_nonneg hfactor habsNonneg)
  have hdenom :
      1 - (1 - t ^ g.ramification) *
          quittingStationaryContinueMass (quittingGermRoot g ht) =
        quittingGermFirstEventDenominator g t := by
    rw [quittingStationaryContinueMass_quittingGermRoot g ht]
    unfold quittingGermFirstEventDenominator quittingGermAbsorption
    ring
  have hbalance := quittingGermValue_mul_one_sub g ht who
  rw [hdenom] at hbalance
  have hrootBound := abs_quittingRootAbsorbingContribution_le
    reward (quittingGermRoot g ht) who (quittingRewardBound reward)
      (fun S player => abs_reward_le_quittingRewardBound reward S player)
  rw [← quittingGermAbsorption_eq g ht] at hrootBound
  have hvalue : quittingGermValue g t who =
      ((1 - t ^ g.ramification) *
        quittingRootAbsorbingContribution reward (quittingGermRoot g ht) who) /
          quittingGermFirstEventDenominator g t :=
    (eq_div_iff hdenomPos.ne').2 hbalance
  rw [hvalue, abs_div, abs_mul, abs_of_nonneg hfactor,
    abs_of_pos hdenomPos]
  calc
    (1 - t ^ g.ramification) *
          |quittingRootAbsorbingContribution reward
            (quittingGermRoot g ht) who| /
        quittingGermFirstEventDenominator g t ≤
      (1 - t ^ g.ramification) *
          (quittingRewardBound reward * quittingGermAbsorption g t) /
        quittingGermFirstEventDenominator g t :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrootBound hfactor) hdenomPos.le
    _ = quittingRewardBound reward *
        quittingGermRealAbsorptionFirstEventWeight g t := by
      unfold quittingGermRealAbsorptionFirstEventWeight
      ring

/-- Dominant cemetery mass forces the analytic endpoint value to be zero. -/
theorem quittingGermValue_zero_eq_zero_of_discount_dominates
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (habsorption :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < quittingGermAbsorption g t)
    (hdominates : Tendsto
      (fun t : ℝ => t ^ g.ramification / quittingGermAbsorption g t)
      (𝓝[>] (0 : ℝ)) atTop) :
    quittingGermValue g 0 = 0 := by
  have hreal :=
    quittingGermRealAbsorptionFirstEventWeight_tendsto_zero_of_discount_dominates
      g habsorption hdominates
  funext who
  have hscaled : Tendsto
      (fun t => quittingRewardBound reward *
        quittingGermRealAbsorptionFirstEventWeight g t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hreal.const_mul (quittingRewardBound reward)
  have hltOne : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from
      Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
  have habsValue : Tendsto (fun t => |quittingGermValue g t who|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun t => abs_nonneg _
    · filter_upwards [eventually_mem_Ioo_radius g, hltOne] with t ht ht1
      exact
        abs_quittingGermValue_le_rewardBound_mul_realAbsorptionFirstEventWeight
          g ht ht1 who
    · exact hscaled
  have hvalueToZero : Tendsto (fun t => quittingGermValue g t who)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simpa [Real.norm_eq_abs] using habsValue
  exact tendsto_nhds_unique (quittingGermValue_tendsto_zero g who) hvalueToZero

/-! ## All-Continue endpoint classification for the auxiliary germ -/

/-- **All-Continue endpoint classification.**  For the punishment-normalized
auxiliary germ, an all-Continue endpoint yields either the original Never
uniform equilibrium or a normalized complementary singleton source packet.

The proof includes the stagnant shifted-zero-solo branch and all three
comparisons of the germ ramification with the least quit-rate order. -/
theorem quittingAuxiliaryGerm_allContinueAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame (quittingAuxiliaryReward reward)).AnalyticBellmanGerm)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1) :
    QuittingAuxiliaryAllContinueAlternative reward := by
  classical
  let auxiliary := quittingAuxiliaryReward reward
  by_cases hzeroAux : IsQuittingZeroSolo auxiliary
  · have hzero : IsQuittingZeroSolo reward :=
      isQuittingZeroSolo_of_auxiliaryReward_zeroSolo reward hzeroAux
    exact Or.inl ⟨hzero,
      quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo reward hzero⟩
  · obtain ⟨m, leading, horder, hleadingNonneg, hleadingSumPos, hsupport,
      htotal, hshare, hsmall, hmatchingLimit, hbig⟩ :=
        quittingGermLeadingOrderNormalization_of_not_isQuittingZeroSolo
          g hzeroAux
    have hm : 1 ≤ m :=
      one_le_quittingGerm_leadingOrder_of_endpoint_allContinue
        g hcontinue horder
    have hne : ∃ owner,
        ¬∀ᶠ t in 𝓝[>] (0 : ℝ), quittingGermQuitRate g owner t = 0 :=
      exists_not_eventually_quittingGermQuitRate_eq_zero_of_not_isQuittingZeroSolo
        g hzeroAux
    rcases lt_trichotomy g.ramification m with hslow | hmatching | hfast
    · have habsorption :
          ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < quittingGermAbsorption g t :=
        eventually_quittingGermAbsorption_pos g htotal
      have hdominates : Tendsto
          (fun t : ℝ => t ^ g.ramification / quittingGermAbsorption g t)
          (𝓝[>] (0 : ℝ)) atTop :=
        tendsto_pow_div_quittingGermAbsorption_atTop
          g htotal (hbig hslow)
      have hvalueZero :=
        quittingGermValue_zero_eq_zero_of_discount_dominates
          g habsorption hdominates
      have hzero : IsQuittingZeroSolo reward := by
        intro who
        have hsolo :=
          quittingGerm_solo_le_endpointValue_of_endpoint_allContinue
            g hcontinue who
        have hvalueWho := congrFun hvalueZero who
        have hlive := quittingAuxiliaryLive_nonpos reward who
        change reward (quittingSingletonTerminal who) who -
            quittingAuxiliaryLive reward who ≤ quittingGermValue g 0 who at hsolo
        simp only [Pi.zero_apply] at hvalueWho
        rw [hvalueWho] at hsolo
        linarith
      exact Or.inl ⟨hzero,
        quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo reward hzero⟩
    · have hmatchingOrder :
          Math.familyAnalyticOrder (quittingGermQuitRate g) =
            g.ramification := by
        rw [horder]
        exact_mod_cast hmatching.symm
      obtain ⟨matchingData⟩ :=
        exists_quittingGermMatchingLeadingData auxiliary g hne hmatchingOrder
      let packet := matchingData.toProjectiveSingletonPacket
      have hcemetery : packet.cemetery < 1 := by
        change 1 / (1 + ∑ owner, matchingData.leading owner) < 1
        rw [div_lt_iff₀ (by linarith [matchingData.leading_sum_pos])]
        linarith [matchingData.leading_sum_pos]
      have hpacket :
          QuittingNormalizedSingletonSourcePacket reward :=
        normalizedSingletonSourcePacket_of_auxiliaryProjectivePacket
          reward g packet rfl hcemetery
            (quittingAuxiliaryGermEndpointValue_nonneg reward g)
      exact Or.inr ⟨hpacket⟩
    · let hfastData : QuittingGermFastLeadingData auxiliary g :=
        { leading := leading
          leading_nonneg := hleadingNonneg
          leading_sum_pos := hleadingSumPos
          eventually_total_pos := htotal
          share_tendsto := hshare
          total_div_absorption_tendsto :=
            tendsto_sum_div_quittingGermAbsorption g hm horder htotal
          discount_div_absorption_tendsto :=
            tendsto_pow_div_quittingGermAbsorption_nhds_zero
              g htotal (hsmall hfast)
          quitRate_tendsto_zero := fun owner =>
            quittingGermQuitRate_tendsto_zero_of_endpoint_allContinue
              g hcontinue owner }
      let packet := hfastData.toProjectiveSingletonPacket hcontinue
      have hpacket :
          QuittingNormalizedSingletonSourcePacket reward :=
        normalizedSingletonSourcePacket_of_auxiliaryProjectivePacket
          reward g packet rfl (by simp [packet,
            QuittingGermFastLeadingData.toProjectiveSingletonPacket])
          (quittingAuxiliaryGermEndpointValue_nonneg reward g)
      exact Or.inr ⟨hpacket⟩

end GameTheory
