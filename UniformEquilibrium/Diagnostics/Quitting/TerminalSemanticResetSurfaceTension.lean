/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio

/-!
# Surface tension on the positive-incidence reset face

Let `D_*` be the positive global minimum total debt and let `I` be total
opponent incidence relative to a reset owner.  The natural excess density is

`(D - D_*) / I`.

This quotient need not attain on an arbitrary positive-incidence domain if
both excess and incidence approach zero.  The correct first step is to
minimize `D` on the closed joint reset face.  There are then two exact cases.

* The reset-face minimum equals `D_*`, so the joint reset face already meets
  the global minimum fiber.
* The reset face is separated from the global minimum by `Delta > 0`.  Then
  every reset point has excess at least `Delta`, so the excess/incidence
  quotient is coercive at `I = 0` and attains a positive-incidence minimum.

At a slope minimizer, an exact cap--Nash prefix has

`D' = c D`,  `I' = F + c I`.

Cross-multiplying the slope inequality and cancelling the common transported
term gives the division-free maximum principle

`(D - D_*) F + (1 - c) D_* I <= 0`.

All terms are nonnegative and `D_*`, `I`, and `D-D_*` are positive.  Hence
`c = 1` and `F = 0`; every exact cap root is all-Continue.  Unlike the
unshifted `D/I` selector, no secondary debt minimization is needed.
-/

noncomputable section

namespace GameTheory

open Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- **Division-free surface-tension maximum principle.** -/
theorem surfaceTension_maximumPrinciple
    (minimumDebt debt incidence survival freshIncidence : ℝ)
    (hminimumDebt : 0 < minimumDebt)
    (hexcess : 0 < debt - minimumDebt)
    (hincidence : 0 < incidence)
    (hsurvivalLe : survival ≤ 1)
    (hfreshNonneg : 0 ≤ freshIncidence)
    (hcross : (debt - minimumDebt) *
        (freshIncidence + survival * incidence) ≤
      (survival * debt - minimumDebt) * incidence) :
    survival = 1 ∧ freshIncidence = 0 := by
  have hsum : (debt - minimumDebt) * freshIncidence +
      (1 - survival) * minimumDebt * incidence ≤ 0 := by
    nlinarith
  have hfirst : 0 ≤ (debt - minimumDebt) * freshIncidence :=
    mul_nonneg hexcess.le hfreshNonneg
  have hsecond : 0 ≤ (1 - survival) * minimumDebt * incidence :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hsurvivalLe) hminimumDebt.le)
      hincidence.le
  have hsurvival : survival = 1 := by
    by_contra hne
    have hstrict : 0 < 1 - survival :=
      sub_pos.mpr (lt_of_le_of_ne hsurvivalLe hne)
    have : 0 < (1 - survival) * minimumDebt * incidence :=
      mul_pos (mul_pos hstrict hminimumDebt) hincidence
    linarith
  have hfresh : freshIncidence = 0 := by
    rw [hsurvival] at hsum
    norm_num at hsum
    nlinarith
  exact ⟨hsurvival, hfresh⟩

/-- The compact joint reset face has a total-debt minimizer. -/
theorem exists_joint_resetFace_debtMinimizer
    (target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htarget : (target, mass) ∈
      quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt target owner = 0) :
    ∃ resetMinimum : QuittingTerminalSemanticLawPoint ι,
      resetMinimum ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt resetMinimum.1 owner = 0 ∧
      ∀ candidate ∈ quittingTerminalSemanticLawCarrier reward,
        quittingTerminalSemanticDebt candidate.1 owner = 0 →
        quittingTerminalSemanticDebtSum resetMinimum.1 ≤
          quittingTerminalSemanticDebtSum candidate.1 := by
  let resetFace : Set (QuittingTerminalSemanticLawPoint ι) :=
    quittingTerminalSemanticLawCarrier reward ∩
      {point | quittingTerminalSemanticDebt point.1 owner = 0}
  have hresetClosed : IsClosed
      {point : QuittingTerminalSemanticLawPoint ι |
        quittingTerminalSemanticDebt point.1 owner = 0} :=
    isClosed_eq
      ((continuous_quittingTerminalSemanticDebt owner).comp continuous_fst)
      continuous_const
  have hresetCompact : IsCompact resetFace :=
    (quittingTerminalSemanticLawCarrier_isCompact reward hM hreward).inter_right
      hresetClosed
  have hresetNonempty : resetFace.Nonempty :=
    ⟨(target, mass), htarget, hreset⟩
  obtain ⟨resetMinimum, hresetMinimum, hminimal⟩ :=
    hresetCompact.exists_isMinOn hresetNonempty
      (continuous_quittingTerminalSemanticDebtSum.comp
        continuous_fst).continuousOn
  exact ⟨resetMinimum, hresetMinimum.1, hresetMinimum.2,
    fun candidate hcandidate hcandidateReset =>
      hminimal ⟨hcandidate, hcandidateReset⟩⟩

/-- **Attainment of positive excess per unit incidence on a separated reset
face.**  Separation supplies the positive numerator floor which closes the
apparently open domain `I > 0`. -/
theorem exists_resetFace_minimizer_excess_div_totalOpponentIncidence
    (source : QuittingTerminalSemanticPair ι)
    (resetMinimum target : QuittingTerminalSemanticLawPoint ι)
    (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hresetMinimumIsMin : ∀ candidate ∈
      quittingTerminalSemanticLawCarrier reward,
      quittingTerminalSemanticDebt candidate.1 owner = 0 →
      quittingTerminalSemanticDebtSum resetMinimum.1 ≤
        quittingTerminalSemanticDebtSum candidate.1)
    (hseparated : quittingTerminalSemanticDebtSum source <
      quittingTerminalSemanticDebtSum resetMinimum.1)
    (htarget : target ∈ quittingTerminalSemanticLawCarrier reward)
    (htargetReset : quittingTerminalSemanticDebt target.1 owner = 0)
    (htargetIncidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner target.2) :
    ∃ returned : QuittingTerminalSemanticLawPoint ι,
      returned ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt returned.1 owner = 0 ∧
      0 < quittingTerminalTotalOpponentIncidenceMass owner returned.2 ∧
      quittingTerminalSemanticDebtSum resetMinimum.1 ≤
        quittingTerminalSemanticDebtSum returned.1 ∧
      ∀ candidate ∈ quittingTerminalSemanticLawCarrier reward,
        quittingTerminalSemanticDebt candidate.1 owner = 0 →
        0 < quittingTerminalTotalOpponentIncidenceMass owner candidate.2 →
        (quittingTerminalSemanticDebtSum returned.1 -
              quittingTerminalSemanticDebtSum source) /
            quittingTerminalTotalOpponentIncidenceMass owner returned.2 ≤
          (quittingTerminalSemanticDebtSum candidate.1 -
              quittingTerminalSemanticDebtSum source) /
            quittingTerminalTotalOpponentIncidenceMass owner candidate.2 := by
  let minimumDebt := quittingTerminalSemanticDebtSum source
  let gap := quittingTerminalSemanticDebtSum resetMinimum.1 - minimumDebt
  let targetExcess :=
    quittingTerminalSemanticDebtSum target.1 - minimumDebt
  let targetIncidence :=
    quittingTerminalTotalOpponentIncidenceMass owner target.2
  let incidenceFloor := gap * targetIncidence / targetExcess
  let incidence : QuittingTerminalSemanticLawPoint ι → ℝ := fun point =>
    quittingTerminalTotalOpponentIncidenceMass owner point.2
  let excess : QuittingTerminalSemanticLawPoint ι → ℝ := fun point =>
    quittingTerminalSemanticDebtSum point.1 - minimumDebt
  let slope : QuittingTerminalSemanticLawPoint ι → ℝ := fun point =>
    excess point / incidence point
  let admissible : Set (QuittingTerminalSemanticLawPoint ι) :=
    quittingTerminalSemanticLawCarrier reward ∩
      {point | quittingTerminalSemanticDebt point.1 owner = 0} ∩
      {point | incidenceFloor ≤ incidence point}
  have hgapPositive : 0 < gap := by
    dsimp only [gap, minimumDebt]
    linarith
  have htargetLower := hresetMinimumIsMin target htarget htargetReset
  have htargetExcessPositive : 0 < targetExcess := by
    dsimp only [targetExcess, minimumDebt]
    linarith
  have hfloorPositive : 0 < incidenceFloor := by
    dsimp only [incidenceFloor, gap, targetIncidence, targetExcess]
    positivity
  have hfloorLeTarget : incidenceFloor ≤ targetIncidence := by
    rw [show incidenceFloor = gap * targetIncidence / targetExcess by rfl,
      div_le_iff₀ htargetExcessPositive]
    dsimp only [gap, targetExcess, minimumDebt]
    nlinarith
  have hincidenceContinuous : Continuous incidence :=
    (continuous_quittingTerminalTotalOpponentIncidenceMass owner).comp
      continuous_snd
  have hexcessContinuous : Continuous excess :=
    (continuous_quittingTerminalSemanticDebtSum.comp continuous_fst).sub
      continuous_const
  have hresetClosed : IsClosed
      {point : QuittingTerminalSemanticLawPoint ι |
        quittingTerminalSemanticDebt point.1 owner = 0} :=
    isClosed_eq
      ((continuous_quittingTerminalSemanticDebt owner).comp continuous_fst)
      continuous_const
  have hfloorClosed : IsClosed
      {point : QuittingTerminalSemanticLawPoint ι |
        incidenceFloor ≤ incidence point} :=
    isClosed_Ici.preimage hincidenceContinuous
  have hadmissibleCompact : IsCompact admissible :=
    ((quittingTerminalSemanticLawCarrier_isCompact reward hM hreward).inter_right
      hresetClosed).inter_right hfloorClosed
  have htargetAdmissible : target ∈ admissible :=
    ⟨⟨htarget, htargetReset⟩, hfloorLeTarget⟩
  have hslopeContinuous : ContinuousOn slope admissible := by
    apply hexcessContinuous.continuousOn.div hincidenceContinuous.continuousOn
    intro point hpoint
    exact ne_of_gt (hfloorPositive.trans_le hpoint.2)
  obtain ⟨returned, hreturnedAdmissible, hreturnedMin⟩ :=
    hadmissibleCompact.exists_isMinOn ⟨target, htargetAdmissible⟩
      hslopeContinuous
  have hreturnedJoint := hreturnedAdmissible.1.1
  have hreturnedReset := hreturnedAdmissible.1.2
  have hreturnedIncidence : 0 < incidence returned :=
    hfloorPositive.trans_le hreturnedAdmissible.2
  have hresetMinLeReturned :=
    hresetMinimumIsMin returned hreturnedJoint hreturnedReset
  have hreturnedLeTarget : slope returned ≤ slope target :=
    hreturnedMin htargetAdmissible
  refine ⟨returned, hreturnedJoint, hreturnedReset, hreturnedIncidence,
    hresetMinLeReturned, ?_⟩
  intro candidate hcandidate hcandidateReset hcandidateIncidence
  by_cases hcandidateFloor : incidenceFloor ≤ incidence candidate
  · exact hreturnedMin ⟨⟨hcandidate, hcandidateReset⟩, hcandidateFloor⟩
  · have hcandidateFloorLt : incidence candidate < incidenceFloor :=
      lt_of_not_ge hcandidateFloor
    have hresetMinLeCandidate :=
      hresetMinimumIsMin candidate hcandidate hcandidateReset
    have hsmall : incidence candidate * targetExcess <
        gap * targetIncidence := by
      rw [show incidenceFloor = gap * targetIncidence / targetExcess by rfl,
        lt_div_iff₀ htargetExcessPositive] at hcandidateFloorLt
      simpa [mul_comm] using hcandidateFloorLt
    have htargetSlopeLt : slope target < slope candidate := by
      rw [show slope target = targetExcess / targetIncidence by rfl,
        show slope candidate = excess candidate / incidence candidate by rfl,
        div_lt_div_iff₀ htargetIncidence hcandidateIncidence]
      have hcandidateExcessLower : gap ≤ excess candidate := by
        dsimp only [gap, excess, minimumDebt]
        linarith
      nlinarith
    exact hreturnedLeTarget.trans htargetSlopeLt.le

/-- At a separated surface-tension minimizer, every exact cap--Nash root is
all-Continue directly from the division-free maximum principle. -/
theorem root_eq_allContinue_of_minimal_surfaceTension
    (source : QuittingTerminalSemanticPair ι)
    (returned : QuittingTerminalSemanticLawPoint ι)
    (owner : ι) (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (hreturned : returned ∈ quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt returned.1 owner = 0)
    (hexcess : quittingTerminalSemanticDebtSum source <
      quittingTerminalSemanticDebtSum returned.1)
    (hincidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner returned.2)
    (hslope : ∀ candidate ∈ quittingTerminalSemanticLawCarrier reward,
      quittingTerminalSemanticDebt candidate.1 owner = 0 →
      0 < quittingTerminalTotalOpponentIncidenceMass owner candidate.2 →
      (quittingTerminalSemanticDebtSum returned.1 -
            quittingTerminalSemanticDebtSum source) /
          quittingTerminalTotalOpponentIncidenceMass owner returned.2 ≤
        (quittingTerminalSemanticDebtSum candidate.1 -
            quittingTerminalSemanticDebtSum source) /
          quittingTerminalTotalOpponentIncidenceMass owner candidate.2)
    (hnash : IsεQuittingRootNash reward returned.1.2 0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  let prefixed := quittingTerminalSemanticPrefix reward root returned.1
  let prefixedMass := quittingTerminalOutcomeLawPrefix root returned.2
  let survival := quittingStationaryContinueMass root
  let oldIncidence :=
    quittingTerminalTotalOpponentIncidenceMass owner returned.2
  let freshIncidence := quittingRootTotalOpponentIncidenceMass owner root
  have hprefixedJoint : (prefixed, prefixedMass) ∈
      quittingTerminalSemanticLawCarrier reward :=
    quittingTerminalSemanticLawPrefix_mem_carrier
      reward root returned hM hreward hreturned
  have hprefixedCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier
      (prefixed, prefixedMass) hprefixedJoint
  have hprefixedReset : quittingTerminalSemanticDebt prefixed owner = 0 := by
    rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) returned.1 root owner hnash, hreset, mul_zero]
  have hdebtScale : quittingTerminalSemanticDebtSum prefixed =
      survival * quittingTerminalSemanticDebtSum returned.1 :=
    quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) returned.1 root hnash
  have hsourceLePrefixed := hminimum prefixed hprefixedCarrier
  have hsurvivalPositive : 0 < survival := by
    by_contra hnot
    have hzero : survival = 0 :=
      le_antisymm (le_of_not_gt hnot)
        (quittingStationaryContinueMass_nonneg root)
    rw [hdebtScale, hzero, zero_mul] at hsourceLePrefixed
    linarith
  have hincidenceAction :
      quittingTerminalTotalOpponentIncidenceMass owner prefixedMass =
        freshIncidence + survival * oldIncidence :=
    quittingTerminalTotalOpponentIncidenceMass_lawPrefix
      owner root returned.2
  have hprefixedIncidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner prefixedMass := by
    rw [hincidenceAction]
    exact add_pos_of_nonneg_of_pos
      (quittingRootTotalOpponentIncidenceMass_nonneg owner root)
      (mul_pos hsurvivalPositive hincidence)
  have hslopePrefix := hslope (prefixed, prefixedMass) hprefixedJoint
    hprefixedReset hprefixedIncidence
  have hcross :
      (quittingTerminalSemanticDebtSum returned.1 -
          quittingTerminalSemanticDebtSum source) *
        (freshIncidence + survival * oldIncidence) ≤
      (survival * quittingTerminalSemanticDebtSum returned.1 -
          quittingTerminalSemanticDebtSum source) * oldIncidence := by
    change (quittingTerminalSemanticDebtSum returned.1 -
          quittingTerminalSemanticDebtSum source) / oldIncidence ≤
      (quittingTerminalSemanticDebtSum prefixed -
          quittingTerminalSemanticDebtSum source) /
        quittingTerminalTotalOpponentIncidenceMass owner prefixedMass
        at hslopePrefix
    have holdPositive : 0 < oldIncidence := hincidence
    have hnewPositive : 0 < freshIncidence + survival * oldIncidence := by
      rw [← hincidenceAction]
      exact hprefixedIncidence
    rw [hdebtScale, hincidenceAction,
      div_le_div_iff₀ holdPositive hnewPositive] at hslopePrefix
    exact hslopePrefix
  have hprinciple := surfaceTension_maximumPrinciple
    (quittingTerminalSemanticDebtSum source)
    (quittingTerminalSemanticDebtSum returned.1) oldIncidence survival
      freshIncidence hsourcePositive (sub_pos.mpr hexcess) hincidence
      (quittingStationaryContinueMass_le_one root)
      (quittingRootTotalOpponentIncidenceMass_nonneg owner root) hcross
  funext player
  have hpure := eq_pure_false_of_quittingStationaryContinueMass_eq_one
    hprinciple.1 player
  simpa [quittingAllContinueRoot] using hpure

/-- **Exact reset-face surface-tension dichotomy.**  Either the joint reset
face reaches the global minimum-debt fiber, or a positive-incidence slope
minimizer exists and has the singleton all-Continue exact cap correspondence. -/
theorem resetFace_globalMinimum_or_surfaceTension_allContinue
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (htarget : (target, mass) ∈
      quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt target owner = 0)
    (hincidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner mass) :
    (∃ resetMinimum : QuittingTerminalSemanticLawPoint ι,
      resetMinimum ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt resetMinimum.1 owner = 0 ∧
      quittingTerminalSemanticDebtSum resetMinimum.1 =
        quittingTerminalSemanticDebtSum source) ∨
    ∃ returned : QuittingTerminalSemanticLawPoint ι,
      returned ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt returned.1 owner = 0 ∧
      0 < quittingTerminalTotalOpponentIncidenceMass owner returned.2 ∧
      quittingTerminalSemanticDebtSum source <
        quittingTerminalSemanticDebtSum returned.1 ∧
      ∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward returned.1.2 0 root →
          root = (quittingAllContinueRoot : ι → PMF Bool) := by
  obtain ⟨resetMinimum, hresetMinimum, hresetMinimumReset,
      hresetMinimumIsMin⟩ :=
    exists_joint_resetFace_debtMinimizer target mass owner hM hreward
      htarget hreset
  have hresetMinimumCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier resetMinimum hresetMinimum
  have hsourceLeReset := hminimum resetMinimum.1 hresetMinimumCarrier
  rcases hsourceLeReset.eq_or_lt with heq | hstrict
  · exact Or.inl ⟨resetMinimum, hresetMinimum, hresetMinimumReset, heq.symm⟩
  · obtain ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
        hresetMinLeReturned, hslope⟩ :=
      exists_resetFace_minimizer_excess_div_totalOpponentIncidence
        source resetMinimum (target, mass) owner hM hreward
          hresetMinimumIsMin hstrict htarget hreset hincidence
    have hreturnedStrict : quittingTerminalSemanticDebtSum source <
        quittingTerminalSemanticDebtSum returned.1 :=
      hstrict.trans_le hresetMinLeReturned
    refine Or.inr ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
      hreturnedStrict, ?_⟩
    intro root hnash
    exact root_eq_allContinue_of_minimal_surfaceTension
      source returned owner root hM hreward hminimum hsourcePositive
        hreturned hreturnedReset hreturnedStrict hreturnedIncidence
        hslope hnash

/-! ## Face-preserving fractional transfer at the excess scale -/

/-- If a candidate stays on the slope's reset face and retains the
`1-lambda` fraction of total opponent incidence, an own-coordinate debt gain
forces opposite-coordinate transfer up to exactly `lambda` times the excess
above the global minimum. -/
theorem partialTransferCut_of_minimal_surfaceTension
    (source : QuittingTerminalSemanticPair ι)
    (returned candidate : QuittingTerminalSemanticLawPoint ι)
    (resetOwner mover owner : ι) (lambda gain : ℝ)
    (hminimum : ∀ point ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum point)
    (hreturned : returned ∈ quittingTerminalSemanticLawCarrier reward)
    (hreturnedIncidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner returned.2)
    (hslope : ∀ point ∈ quittingTerminalSemanticLawCarrier reward,
      quittingTerminalSemanticDebt point.1 resetOwner = 0 →
      0 < quittingTerminalTotalOpponentIncidenceMass owner point.2 →
      (quittingTerminalSemanticDebtSum returned.1 -
            quittingTerminalSemanticDebtSum source) /
          quittingTerminalTotalOpponentIncidenceMass owner returned.2 ≤
        (quittingTerminalSemanticDebtSum point.1 -
            quittingTerminalSemanticDebtSum source) /
          quittingTerminalTotalOpponentIncidenceMass owner point.2)
    (hcandidate : candidate ∈ quittingTerminalSemanticLawCarrier reward)
    (hcandidateReset :
      quittingTerminalSemanticDebt candidate.1 resetOwner = 0)
    (hlambdaStrict : lambda < 1)
    (hincidenceRetention :
      (1 - lambda) *
          quittingTerminalTotalOpponentIncidenceMass owner returned.2 ≤
        quittingTerminalTotalOpponentIncidenceMass owner candidate.2)
    (hdecrease : quittingTerminalSemanticDebt candidate.1 mover =
      quittingTerminalSemanticDebt returned.1 mover - gain) :
    gain - lambda *
        (quittingTerminalSemanticDebtSum returned.1 -
          quittingTerminalSemanticDebtSum source) ≤
      ∑ recipient ∈ Finset.univ.erase mover,
        quittingTerminalSemanticDebtChange
          returned.1 candidate.1 recipient := by
  let oldIncidence :=
    quittingTerminalTotalOpponentIncidenceMass owner returned.2
  let newIncidence :=
    quittingTerminalTotalOpponentIncidenceMass owner candidate.2
  let oldExcess := quittingTerminalSemanticDebtSum returned.1 -
    quittingTerminalSemanticDebtSum source
  let newExcess := quittingTerminalSemanticDebtSum candidate.1 -
    quittingTerminalSemanticDebtSum source
  have hnewIncidence : 0 < newIncidence := by
    exact (mul_pos (sub_pos.mpr hlambdaStrict) hreturnedIncidence).trans_le
      hincidenceRetention
  have hslopeCandidate := hslope candidate hcandidate hcandidateReset
    hnewIncidence
  have hcross : oldExcess * newIncidence ≤ newExcess * oldIncidence := by
    change oldExcess / oldIncidence ≤ newExcess / newIncidence
      at hslopeCandidate
    rw [div_le_div_iff₀ hreturnedIncidence hnewIncidence] at hslopeCandidate
    exact hslopeCandidate
  have holdExcessNonneg : 0 ≤ oldExcess := by
    have hreturnedCarrier :=
      terminalSemanticLawCarrier_fst_mem_carrier returned hreturned
    dsimp only [oldExcess]
    linarith [hminimum returned.1 hreturnedCarrier]
  have hnewExcessLower : (1 - lambda) * oldExcess ≤ newExcess := by
    have holdIncidence : 0 < oldIncidence := hreturnedIncidence
    have hretention : (1 - lambda) * oldIncidence ≤ newIncidence :=
      hincidenceRetention
    nlinarith
  have hsum := Finset.sum_erase_add Finset.univ
    (fun player => quittingTerminalSemanticDebtChange
      returned.1 candidate.1 player)
    (Finset.mem_univ mover)
  have htotal : (∑ player,
      quittingTerminalSemanticDebtChange returned.1 candidate.1 player) =
      newExcess - oldExcess := by
    dsimp only [newExcess, oldExcess]
    unfold quittingTerminalSemanticDebtChange
      quittingTerminalSemanticDebtSum
    rw [Finset.sum_sub_distrib]
    ring
  have hmover : quittingTerminalSemanticDebtChange
      returned.1 candidate.1 mover = -gain := by
    unfold quittingTerminalSemanticDebtChange
    rw [hdecrease]
    ring
  rw [htotal, hmover] at hsum
  nlinarith

end GameTheory
