/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAtomicBlockerBarrier
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPartialResetTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauFractionalResetDropout
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSignedPairDropoutConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveMinimumUnitResetOrientation

/-!
# Atomic-blocker/reset adapter

This module connects the finite forced-owner blocker wall to literal
coordinatewise fractional best-endpoint moves.

The essential provenance fact is exact: when `owner` Quits surely, every
outsider's root Nash defect is independent of the attached continuation and
equals its coordinate in the forced-owner blocker defect.  Consequently a
blocker-wall landing can be followed by one literal half-best-endpoint splice.
The resulting gain is at least half the terminal gap and is charged either to
the actual prefixed source's excess above a minimum reference or to debt gained
by the other player coordinates.

For a finite fractional reset word, the existing mountain-pass theorem then
gives an honest trichotomy:

* a fixed prefixed-source excess;
* a fixed aggregate transfer to coordinates other than the selected outsider;
* one actual prefix edge with a blocker-balance drop larger than half the gap.

The blocker balance is exactly affine in every moved outsider marginal.  If
terminal rewards and the owner's punishment value are bounded by `M`, its
endpoint oscillation is at most `4M`; hence the third branch has reset weight
strictly larger than `η/(8M)`.  This is a macroscopic geometric reset, but it
need not be a unit overwrite and its interpolation weight is not a
chronological survival weight.  Independently, the fractional-reset
floor/dropout modules turn zero final root defect over a positive collision
into an actual unit overwrite, and the signed/oriented consumers describe that
unit edge once their extra minimum-fiber and best-endpoint hypotheses are
supplied.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Affinity in an arbitrary moved marginal -/

/-- A product-root payoff is affine in any one selected marginal, not only in
the marginal of the player whose payoff is evaluated. -/
theorem quittingRootExpectedPayoff_updateCoordinate_eq_endpointMix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (coordinate beneficiary : ι) (marginal : PMF Bool) :
    quittingRootExpectedPayoff reward tail
        (Function.update root coordinate marginal) beneficiary =
      (marginal true).toReal *
          quittingRootExpectedPayoff reward tail
            (Function.update root coordinate (PMF.pure true)) beneficiary +
        (marginal false).toReal *
          quittingRootExpectedPayoff reward tail
            (Function.update root coordinate (PMF.pure false)) beneficiary := by
  unfold quittingRootExpectedPayoff
  rw [pmfPi_update_bind, expect_bind, expect_eq_sum, Fintype.sum_bool]

/-- Hence a literal partial endpoint root is the exact affine interpolation
between its source row and the corresponding pure endpoint row, for every
payoff coordinate. -/
theorem quittingRootExpectedPayoff_partialEndpointRoot_affine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (coordinate beneficiary : ι) (action : Bool)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingRootExpectedPayoff reward tail
        (quittingPartialEndpointRoot root coordinate action lambda
          hlambda0 hlambda1) beneficiary =
      (1 - lambda) *
          quittingRootExpectedPayoff reward tail root beneficiary +
        lambda * quittingRootExpectedPayoff reward tail
          (Function.update root coordinate (PMF.pure action)) beneficiary := by
  have hpartial := quittingRootExpectedPayoff_updateCoordinate_eq_endpointMix
    reward tail root coordinate beneficiary
      (quittingPartialEndpointMarginal root coordinate action lambda
        hlambda0 hlambda1)
  have hsource := quittingRootExpectedPayoff_updateCoordinate_eq_endpointMix
    reward tail root coordinate beneficiary (root coordinate)
  have hpure := quittingRootExpectedPayoff_updateCoordinate_eq_endpointMix
    reward tail root coordinate beneficiary (PMF.pure action)
  rw [Function.update_eq_self] at hsource
  unfold quittingPartialEndpointRoot
  rw [hpartial, quittingPartialEndpointMarginal_true_toReal,
    quittingPartialEndpointMarginal_false_toReal, hsource, hpure]
  ring

/-- The atomic blocker balance is exactly affine along every outsider
fractional endpoint move.  The owner need not already be pure for this
algebraic identity; `coordinate ≠ owner` is the essential face condition. -/
theorem quittingAtomicBlockerBalance_partialEndpointRoot_affine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner coordinate : ι) (hcoordinate : coordinate ≠ owner)
    (action : Bool) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingAtomicBlockerBalance reward
        (quittingPartialEndpointRoot root coordinate action lambda
          hlambda0 hlambda1) owner =
      (1 - lambda) * quittingAtomicBlockerBalance reward root owner +
        lambda * quittingAtomicBlockerBalance reward
          (Function.update root coordinate (PMF.pure action)) owner := by
  let partialRoot := quittingPartialEndpointRoot root coordinate action lambda
    hlambda0 hlambda1
  let endpoint := Function.update root coordinate (PMF.pure action)
  let refused := Function.update root owner (PMF.pure false)
  have hrefusedCoordinate : refused coordinate = root coordinate := by
    simp [refused, hcoordinate]
  have hmarginal :
      quittingPartialEndpointMarginal refused coordinate action lambda
          hlambda0 hlambda1 =
        quittingPartialEndpointMarginal root coordinate action lambda
          hlambda0 hlambda1 := by
    have hq : quittingPartialEndpointQuitProbability refused coordinate
        action lambda =
      quittingPartialEndpointQuitProbability root coordinate action lambda := by
      unfold quittingPartialEndpointQuitProbability
      rw [hrefusedCoordinate]
    unfold quittingPartialEndpointMarginal
    congr
  have hpartialRefused : Function.update partialRoot owner (PMF.pure false) =
      quittingPartialEndpointRoot refused coordinate action lambda
        hlambda0 hlambda1 := by
    funext player
    by_cases hplayerOwner : player = owner
    · subst player
      simp [partialRoot, refused, quittingPartialEndpointRoot,
        Ne.symm hcoordinate]
    · by_cases hplayerCoordinate : player = coordinate
      · subst player
        simp [partialRoot, refused, quittingPartialEndpointRoot, hmarginal,
          hcoordinate]
      · simp [partialRoot, refused, quittingPartialEndpointRoot,
          hmarginal, hplayerOwner, hplayerCoordinate]
  have hendpointRefused : Function.update endpoint owner (PMF.pure false) =
      Function.update refused coordinate (PMF.pure action) := by
    funext player
    by_cases hplayerOwner : player = owner
    · subst player
      simp [endpoint, refused, Ne.symm hcoordinate]
    · by_cases hplayerCoordinate : player = coordinate
      · subst player
        simp [endpoint, refused, hcoordinate]
      · simp [endpoint, refused, hplayerOwner, hplayerCoordinate]
  have hobey := quittingRootExpectedPayoff_partialEndpointRoot_affine
    reward (0 : Payoff ι) root coordinate owner action lambda
      hlambda0 hlambda1
  have hrefusalReward := quittingRootExpectedPayoff_partialEndpointRoot_affine
    reward (0 : Payoff ι) refused coordinate owner action lambda
      hlambda0 hlambda1
  have hrefusalMass := quittingStationaryContinueMass_partialEndpointRoot
    refused coordinate action lambda hlambda0 hlambda1
  change quittingRootExpectedPayoff reward 0 partialRoot owner -
      (quittingRootExpectedPayoff reward 0
          (Function.update partialRoot owner (PMF.pure false)) owner +
        quittingStationaryContinueMass
            (Function.update partialRoot owner (PMF.pure false)) *
          quittingPunishmentValue reward owner) =
    (1 - lambda) *
      (quittingRootExpectedPayoff reward 0 root owner -
        (quittingRootExpectedPayoff reward 0 refused owner +
          quittingStationaryContinueMass refused *
            quittingPunishmentValue reward owner)) +
      lambda *
        (quittingRootExpectedPayoff reward 0 endpoint owner -
          (quittingRootExpectedPayoff reward 0
              (Function.update endpoint owner (PMF.pure false)) owner +
            quittingStationaryContinueMass
                (Function.update endpoint owner (PMF.pure false)) *
              quittingPunishmentValue reward owner))
  rw [hpartialRefused, hendpointRefused, hobey, hrefusalReward,
    hrefusalMass]
  ring

/-- The refusal cap is itself one bounded root expectation: force the owner to
Continue and use its punishment value on the all-Continue outcome. -/
theorem quittingForcedOwnerRefusalCap_eq_rootExpectedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) :
    quittingForcedOwnerRefusalCap reward root owner =
      quittingRootExpectedPayoff reward
        (fun _ => quittingPunishmentValue reward owner)
        (Function.update root owner (PMF.pure false)) owner := by
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  rfl

/-- If terminal rewards and the owner's punishment value are bounded by `M`,
then every blocker balance lies in `[-2M,2M]`. -/
theorem abs_quittingAtomicBlockerBalance_le_two_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) {M : ℝ}
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hpunish : |quittingPunishmentValue reward owner| ≤ M) :
    |quittingAtomicBlockerBalance reward root owner| ≤ 2 * M := by
  have hobey : |quittingRootExpectedPayoff reward (0 : Payoff ι)
      root owner| ≤ M := by
    apply abs_quittingRootExpectedPayoff_le_bound reward
    · exact hreward
    · intro player
      have hnonneg : 0 ≤ M :=
        (abs_nonneg (quittingPunishmentValue reward owner)).trans hpunish
      simpa only [Pi.zero_apply, abs_zero] using hnonneg
  have hrefusal : |quittingRootExpectedPayoff reward
      (fun _ => quittingPunishmentValue reward owner)
      (Function.update root owner (PMF.pure false)) owner| ≤ M := by
    apply abs_quittingRootExpectedPayoff_le_bound reward
    · exact hreward
    · intro player
      exact hpunish
  unfold quittingAtomicBlockerBalance quittingForcedOwnerObeyValue
  rw [quittingForcedOwnerRefusalCap_eq_rootExpectedPayoff]
  calc
    |quittingRootExpectedPayoff reward 0 root owner -
        quittingRootExpectedPayoff reward
          (fun _ => quittingPunishmentValue reward owner)
          (Function.update root owner (PMF.pure false)) owner| ≤
      |quittingRootExpectedPayoff reward 0 root owner| +
        |quittingRootExpectedPayoff reward
          (fun _ => quittingPunishmentValue reward owner)
          (Function.update root owner (PMF.pure false)) owner| :=
        abs_sub _ _
    _ ≤ M + M := add_le_add hobey hrefusal
    _ = 2 * M := by ring

/-- The blocker-balance oscillation between two arbitrary rows is at most
`4M`.  In particular this bounds the source-to-endpoint slope of every
fractional reset edge. -/
theorem abs_quittingAtomicBlockerBalance_sub_le_four_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι → PMF Bool) (owner : ι) {M : ℝ}
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hpunish : |quittingPunishmentValue reward owner| ≤ M) :
    |quittingAtomicBlockerBalance reward first owner -
        quittingAtomicBlockerBalance reward second owner| ≤ 4 * M := by
  have hfirst := abs_quittingAtomicBlockerBalance_le_two_mul
    reward first owner hreward hpunish
  have hsecond := abs_quittingAtomicBlockerBalance_le_two_mul
    reward second owner hreward hpunish
  calc
    |quittingAtomicBlockerBalance reward first owner -
        quittingAtomicBlockerBalance reward second owner| ≤
      |quittingAtomicBlockerBalance reward first owner| +
        |quittingAtomicBlockerBalance reward second owner| := abs_sub _ _
    _ ≤ 2 * M + 2 * M := add_le_add hfirst hsecond
    _ = 4 * M := by ring

/-- A blocker drop along one literal fractional outsider reset is bounded by
`4M` times that same reset weight.  This is the missing path-variation
adapter; it does not introduce any survival-clock weight. -/
theorem atomicBlockerBalance_sub_apply_le_four_mul_weight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (move : QuittingFractionalEndpointMove ι) (hmove : move.who ≠ owner)
    {M : ℝ}
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hpunish : |quittingPunishmentValue reward owner| ≤ M) :
    quittingAtomicBlockerBalance reward root owner -
        quittingAtomicBlockerBalance reward (move.apply root) owner ≤
      4 * M * move.weight := by
  let endpoint := Function.update root move.who (PMF.pure move.action)
  have haffine := quittingAtomicBlockerBalance_partialEndpointRoot_affine
    reward root owner move.who hmove move.action move.weight
      move.weight_nonneg move.weight_le_one
  have hslopeAbs := abs_quittingAtomicBlockerBalance_sub_le_four_mul
    reward root endpoint owner hreward hpunish
  have hslope : quittingAtomicBlockerBalance reward root owner -
      quittingAtomicBlockerBalance reward endpoint owner ≤ 4 * M :=
    (le_abs_self _).trans hslopeAbs
  have hscaled := mul_le_mul_of_nonneg_left hslope move.weight_nonneg
  unfold QuittingFractionalEndpointMove.apply
  dsimp only [endpoint] at haffine hscaled
  rw [haffine]
  nlinarith

/-- Therefore a blocker drop larger than `η/2` forces a quantitative reset
weight `η/(8M)`, though not a unit overwrite. -/
theorem weight_gt_gap_div_eight_mul_of_atomicBlockerDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (move : QuittingFractionalEndpointMove ι) (hmove : move.who ≠ owner)
    {M η : ℝ} (hM : 0 < M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hpunish : |quittingPunishmentValue reward owner| ≤ M)
    (hdrop : η / 2 < quittingAtomicBlockerBalance reward root owner -
      quittingAtomicBlockerBalance reward (move.apply root) owner) :
    η / (8 * M) < move.weight := by
  have hupper := atomicBlockerBalance_sub_apply_le_four_mul_weight
    reward root owner move hmove hreward hpunish
  apply (div_lt_iff₀ (by positivity : 0 < 8 * M)).2
  nlinarith

/-! ## Forced-owner defect provenance -/

/-- On a forced-owner row, an outsider's local root Nash defect is independent
of the attached continuation and is exactly the raw finite blocker gain. -/
theorem quittingRootCoordinateNashDefect_eq_forcedOwnerGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (owner who : ι)
    (howner : root owner = PMF.pure true) (hwho : who ≠ owner) :
    quittingRootCoordinateNashDefect reward tail root who =
      max (quittingStationaryFixedOpponentsQuitValue reward root who)
          (quittingStationaryFixedOpponentsContinueReward reward root who) -
        quittingRootAbsorbingContribution reward root who := by
  have hrootContinue : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_eq_zero_of_owner_eq_pure howner
  have hquitOwner :
      Function.update root who (PMF.pure true) owner = PMF.pure true := by
    rw [Function.update_of_ne (Ne.symm hwho)]
    exact howner
  have hcontinueOwner :
      Function.update root who (PMF.pure false) owner = PMF.pure true := by
    rw [Function.update_of_ne (Ne.symm hwho)]
    exact howner
  have hquitContinue : quittingStationaryContinueMass
      (Function.update root who (PMF.pure true)) = 0 :=
    quittingStationaryContinueMass_eq_zero_of_owner_eq_pure hquitOwner
  have hpureContinue : quittingStationaryContinueMass
      (Function.update root who (PMF.pure false)) = 0 :=
    quittingStationaryContinueMass_eq_zero_of_owner_eq_pure hcontinueOwner
  have hrootPayoff : quittingRootSuccessorPayoff reward tail root who =
      quittingRootAbsorbingContribution reward root who := by
    unfold quittingRootSuccessorPayoff
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
      hrootContinue, zero_mul, add_zero]
  have hquitPayoff : quittingRootQuitPayoff reward tail root who =
      quittingStationaryFixedOpponentsQuitValue reward root who := by
    unfold quittingRootQuitPayoff quittingStationaryFixedOpponentsQuitValue
      quittingFixedOpponentsQuitValue
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
      hquitContinue, zero_mul, add_zero]
  have hcontinuePayoff : quittingRootContinuePayoff reward tail root who =
      quittingStationaryFixedOpponentsContinueReward reward root who := by
    unfold quittingRootContinuePayoff
      quittingStationaryFixedOpponentsContinueReward
      quittingFixedOpponentsContinueReward
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
      hpureContinue, zero_mul, add_zero]
  rw [quittingRootCoordinateNashDefect, hrootPayoff, hquitPayoff,
    hcontinuePayoff]

/-- A positive lower bound on the forced-owner sup defect selects an actual
outsider coordinate carrying the same lower bound. -/
theorem exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (owner : ι) {η : ℝ}
    (howner : root owner = PMF.pure true) (hη : 0 < η)
    (hdefect : η ≤ quittingForcedOwnerOutsiderDefect reward root owner) :
    ∃ who, who ≠ owner ∧
      η ≤ quittingRootCoordinateNashDefect reward tail root who := by
  letI : Nonempty ι := ⟨owner⟩
  obtain ⟨who, _hwhoMem, hsup⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (quittingForcedOwnerOutsiderCoordinateDefect reward root owner)
  have hcoordinate : η ≤
      quittingForcedOwnerOutsiderCoordinateDefect reward root owner who := by
    rw [← hsup]
    exact hdefect
  have hwho : who ≠ owner := by
    intro heq
    subst who
    simp [quittingForcedOwnerOutsiderCoordinateDefect] at hcoordinate
    linarith
  have hraw : η ≤
      max (quittingStationaryFixedOpponentsQuitValue reward root who)
          (quittingStationaryFixedOpponentsContinueReward reward root who) -
        quittingRootAbsorbingContribution reward root who := by
    have hpositive : 0 <
        max (quittingStationaryFixedOpponentsQuitValue reward root who)
            (quittingStationaryFixedOpponentsContinueReward reward root who) -
          quittingRootAbsorbingContribution reward root who := by
      by_contra hnot
      have hnonpos :
          max (quittingStationaryFixedOpponentsQuitValue reward root who)
              (quittingStationaryFixedOpponentsContinueReward reward root who) -
            quittingRootAbsorbingContribution reward root who ≤ 0 :=
        le_of_not_gt hnot
      simp [quittingForcedOwnerOutsiderCoordinateDefect, hwho,
        max_eq_left hnonpos] at hcoordinate
      linarith
    simpa [quittingForcedOwnerOutsiderCoordinateDefect, hwho,
      max_eq_right hpositive.le] using hcoordinate
  refine ⟨who, hwho, ?_⟩
  rw [quittingRootCoordinateNashDefect_eq_forcedOwnerGain
    reward tail root owner who howner hwho]
  exact hraw

/-! ## One literal half-reset consumes the wall -/

/-- A forced-owner defect wall can be consumed at the same literal product
row.  Moving the selected outsider halfway toward its better endpoint gives a
gain at least `η / 2`.  Minimum-reference accounting forces either source
excess at least `η / 4` or aggregate debt gain at least `η / 4` on the other
player coordinates.

The source and target are the actual root-prefix profiles displayed below;
no compactness representative or recomputed row is substituted. -/
theorem exists_halfBestEndpoint_excess_or_outsiderTransfer_of_forcedOwnerDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (owner : ι) {η : ℝ}
    (howner : root owner = PMF.pure true) (hη : 0 < η)
    (hdefect : η ≤ quittingForcedOwnerOutsiderDefect reward root owner)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ who, who ≠ owner ∧
      let tail := quittingTerminalSemanticPair reward continuation
      let action := quittingRootBestEndpointAction reward tail.1 root who
      let targetRoot := quittingPartialEndpointRoot root who action (1 / 2)
        (by norm_num) (by norm_num)
      let sourceProfile :=
        quittingRootThenContinuationProfile reward root continuation
      let targetProfile := quittingRootThenContinuationProfile reward
        targetRoot continuation
      let source := quittingTerminalSemanticPair reward sourceProfile
      let target := quittingTerminalSemanticPair reward targetProfile
      let gain := (1 / 2 : ℝ) *
        quittingRootCoordinateNashDefect reward tail.1 root who
      η / 2 ≤ gain ∧
        target ∈ quittingTerminalSemanticCarrier reward ∧
        quittingTerminalSemanticDebt target who =
          quittingTerminalSemanticDebt source who - gain ∧
        (η / 4 ≤ quittingTerminalSemanticDebtSum source -
            quittingTerminalSemanticDebtSum minimum ∨
          η / 4 ≤ ∑ recipient ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebtChange source target recipient) := by
  let tail := quittingTerminalSemanticPair reward continuation
  obtain ⟨who, hwho, hcoordinate⟩ :=
    exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge
      reward tail.1 root owner howner hη hdefect
  refine ⟨who, hwho, ?_⟩
  dsimp only
  let action := quittingRootBestEndpointAction reward tail.1 root who
  let targetRoot := quittingPartialEndpointRoot root who action (1 / 2)
    (by norm_num) (by norm_num)
  let sourceProfile :=
    quittingRootThenContinuationProfile reward root continuation
  let targetProfile := quittingRootThenContinuationProfile reward
    targetRoot continuation
  let source := quittingTerminalSemanticPair reward sourceProfile
  let target := quittingTerminalSemanticPair reward targetProfile
  let gain := (1 / 2 : ℝ) *
    quittingRootCoordinateNashDefect reward tail.1 root who
  have hgain : η / 2 ≤ gain := by
    dsimp [gain]
    linarith
  have htargetMem : target ∈ quittingTerminalSemanticCarrier reward := by
    apply subset_closure
    exact ⟨targetProfile, rfl⟩
  have henvelope : quittingContinuationBestResponseValue reward
      targetProfile who =
      quittingContinuationBestResponseValue reward sourceProfile who := by
    dsimp [targetProfile, targetRoot, sourceProfile]
    rw [quittingRootThenContinuation_partialEndpoint_eq_updateSelf]
    exact quittingContinuationBestResponseValue_update_self _ _ _ _
  have hpayoff : quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward sourceProfile who = gain := by
    dsimp only [targetProfile, sourceProfile]
    rw [quittingTerminalPayoff_rootThenContinuation_eq,
      quittingTerminalPayoff_rootThenContinuation_eq]
    change quittingRootSuccessorPayoff reward tail.1 targetRoot who -
      quittingRootSuccessorPayoff reward tail.1 root who = gain
    dsimp only [targetRoot, gain, action]
    simpa using
      (quittingRootSuccessorPayoff_partialBestEndpoint_sub_eq_mul_defect
        reward tail.1 root who
          (1 / 2) (by norm_num) (by norm_num))
  have hdecrease : quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - gain := by
    change quittingContinuationBestResponseValue reward targetProfile who -
        quittingTerminalPayoff reward targetProfile who =
      quittingContinuationBestResponseValue reward sourceProfile who -
        quittingTerminalPayoff reward sourceProfile who - gain
    linarith
  have haccount := minimumReference_opponentTransfer_of_coordinateDecrease
    reward minimum source target who gain hminimum htargetMem hdecrease
  have halternative :
      η / 4 ≤ quittingTerminalSemanticDebtSum source -
          quittingTerminalSemanticDebtSum minimum ∨
        η / 4 ≤ ∑ recipient ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source target recipient := by
    by_contra hnot
    push Not at hnot
    linarith
  exact ⟨hgain, htargetMem, hdecrease, halternative⟩

/-- Named form of the literal half-reset conclusion, used to keep finite-word
adapters readable. -/
def HasAtomicBlockerHalfResetCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (owner : ι) (η : ℝ) : Prop :=
  ∃ who, who ≠ owner ∧
    let tail := quittingTerminalSemanticPair reward continuation
    let action := quittingRootBestEndpointAction reward tail.1 root who
    let targetRoot := quittingPartialEndpointRoot root who action (1 / 2)
      (by norm_num) (by norm_num)
    let sourceProfile :=
      quittingRootThenContinuationProfile reward root continuation
    let targetProfile := quittingRootThenContinuationProfile reward
      targetRoot continuation
    let source := quittingTerminalSemanticPair reward sourceProfile
    let target := quittingTerminalSemanticPair reward targetProfile
    let gain := (1 / 2 : ℝ) *
      quittingRootCoordinateNashDefect reward tail.1 root who
    η / 2 ≤ gain ∧
      target ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebt target who =
        quittingTerminalSemanticDebt source who - gain ∧
      (η / 4 ≤ quittingTerminalSemanticDebtSum source -
          quittingTerminalSemanticDebtSum minimum ∨
        η / 4 ≤ ∑ recipient ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source target recipient)

/-! ## Finite reset-word trichotomy -/

/-- The root reached after the first `time` members of a fractional endpoint
word. -/
def quittingFractionalEndpointPrefixRoot
    (root : ι → PMF Bool) (moves : List (QuittingFractionalEndpointMove ι))
    (time : ℕ) : ι → PMF Bool :=
  quittingFractionalEndpointMoves (moves.take time) root

omit [Fintype ι] in
/-- Consecutive prefix roots really are the two literal roots around the
corresponding member of the reset word.  This records the row provenance
which the blocker-balance trichotomy uses. -/
theorem exists_fractionalEndpointPrefixEdge
    (root : ι → PMF Bool) (moves : List (QuittingFractionalEndpointMove ι))
    (time : ℕ) (htime : time < moves.length) :
    ∃ before move after,
      moves = before ++ move :: after ∧
        before.length = time ∧
        quittingFractionalEndpointPrefixRoot root moves time =
          quittingFractionalEndpointMoves before root ∧
        quittingFractionalEndpointPrefixRoot root moves (time + 1) =
          move.apply (quittingFractionalEndpointPrefixRoot root moves time) := by
  induction moves generalizing root time with
  | nil => simp at htime
  | cons first moves ih =>
      cases time with
      | zero =>
          refine ⟨[], first, moves, by simp, by simp, ?_, ?_⟩
          · simp [quittingFractionalEndpointPrefixRoot,
              quittingFractionalEndpointMoves]
          · simp [quittingFractionalEndpointPrefixRoot,
              quittingFractionalEndpointMoves]
      | succ time =>
          have htail : time < moves.length := by
            simpa using htime
          obtain ⟨before, move, after, hsplit, hlength, hbefore, hafter⟩ :=
            ih (root := first.apply root) time htail
          refine ⟨first :: before, move, after, ?_, ?_, ?_, ?_⟩
          · simp [hsplit]
          · simp [hlength]
          · simpa [quittingFractionalEndpointPrefixRoot,
              quittingFractionalEndpointMoves] using hbefore
          · simpa [quittingFractionalEndpointPrefixRoot,
              quittingFractionalEndpointMoves, Nat.succ_eq_add_one,
              Nat.add_assoc] using hafter

omit [Fintype ι] in
/-- Outsider-only fractional moves preserve a surely quitting owner. -/
theorem quittingFractionalEndpointMoves_owner_eq_pure
    (root : ι → PMF Bool) (moves : List (QuittingFractionalEndpointMove ι))
    (owner : ι) (hroot : root owner = PMF.pure true)
    (houtsider : ∀ move ∈ moves, move.who ≠ owner) :
    quittingFractionalEndpointMoves moves root owner = PMF.pure true := by
  induction moves generalizing root with
  | nil => simpa [quittingFractionalEndpointMoves] using hroot
  | cons move moves ih =>
      have hmove : move.who ≠ owner := houtsider move (by simp)
      have happly : move.apply root owner = PMF.pure true := by
        unfold QuittingFractionalEndpointMove.apply
          quittingPartialEndpointRoot
        rw [Function.update_of_ne (Ne.symm hmove)]
        exact hroot
      rw [quittingFractionalEndpointMoves]
      apply ih (root := move.apply root) happly
      intro later hlater
      exact houtsider later (by simp [hlater])

/-- **Game-facing blocker/reset trichotomy.**

Let an outsider-only fractional endpoint word start in the positive blocker
region and end below the negative terminal gap.  Then one actual consecutive
prefix edge has one of the following consequences:

1. its landing root supports a literal half-best-endpoint splice whose
   prefixed source lies at least `η / 4` above the minimum debt fiber;
2. the same splice transfers aggregate debt at least `η / 4` to coordinates
   other than the selected outsider;
3. the original word edge itself drops blocker balance by more than `η / 2`.

The last disjunct is the precise unresolved coarse-edge branch.  No path
length, reset weight, or survival clock is inserted into the statement. -/
theorem exists_prefix_excess_or_outsiderTransfer_or_blockerDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (moves : List (QuittingFractionalEndpointMove ι))
    (owner : ι) {η : ℝ}
    (hrootOwner : root owner = PMF.pure true)
    (houtsider : ∀ move ∈ moves, move.who ≠ owner)
    (hη : 0 < η) (hgap : HasTerminalExploitabilityGap reward η)
    (hstart : 0 < quittingAtomicBlockerBalance reward root owner)
    (hend : quittingAtomicBlockerBalance reward
      (quittingFractionalEndpointMoves moves root) owner ≤ -η)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ time, time < moves.length ∧
      let beforeRoot := quittingFractionalEndpointPrefixRoot root moves time
      let afterRoot :=
        quittingFractionalEndpointPrefixRoot root moves (time + 1)
      (η / 2 < quittingAtomicBlockerBalance reward beforeRoot owner -
            quittingAtomicBlockerBalance reward afterRoot owner ∨
        ∃ who, who ≠ owner ∧
          let tail := quittingTerminalSemanticPair reward continuation
          let action := quittingRootBestEndpointAction reward tail.1 afterRoot who
          let targetRoot := quittingPartialEndpointRoot afterRoot who action
            (1 / 2) (by norm_num) (by norm_num)
          let sourceProfile := quittingRootThenContinuationProfile reward
            afterRoot continuation
          let targetProfile := quittingRootThenContinuationProfile reward
            targetRoot continuation
          let source := quittingTerminalSemanticPair reward sourceProfile
          let target := quittingTerminalSemanticPair reward targetProfile
          let gain := (1 / 2 : ℝ) *
            quittingRootCoordinateNashDefect reward tail.1 afterRoot who
          η / 2 ≤ gain ∧
            target ∈ quittingTerminalSemanticCarrier reward ∧
            quittingTerminalSemanticDebt target who =
              quittingTerminalSemanticDebt source who - gain ∧
            (η / 4 ≤ quittingTerminalSemanticDebtSum source -
                quittingTerminalSemanticDebtSum minimum ∨
              η / 4 ≤ ∑ recipient ∈ Finset.univ.erase who,
                quittingTerminalSemanticDebtChange source target recipient)) := by
  let roots : ℕ → ι → PMF Bool := fun time =>
    quittingFractionalEndpointPrefixRoot root moves time
  have howner : ∀ time, time ≤ moves.length →
      roots time owner = PMF.pure true := by
    intro time _htime
    apply quittingFractionalEndpointMoves_owner_eq_pure root
      (moves.take time) owner hrootOwner
    intro move hmove
    exact houtsider move (List.mem_of_mem_take hmove)
  have hrootsZero : roots 0 = root := by
    simp [roots, quittingFractionalEndpointPrefixRoot,
      quittingFractionalEndpointMoves]
  have hrootsFinal : roots moves.length =
      quittingFractionalEndpointMoves moves root := by
    simp [roots, quittingFractionalEndpointPrefixRoot]
  obtain ⟨time, htime, hdrop | hwall⟩ :=
    exists_atomicBlockerDefect_or_balanceDrop_on_finiteWord
      (reward := reward) roots owner howner hη hgap
        (by simpa [hrootsZero] using hstart)
        (by simpa [hrootsFinal] using hend)
  · refine ⟨time, htime, Or.inl ?_⟩
    simpa [roots] using hdrop
  · have hafterOwner : roots (time + 1) owner = PMF.pure true :=
      howner (time + 1) (by omega)
    obtain ⟨who, hwho, hhalf⟩ :=
      exists_halfBestEndpoint_excess_or_outsiderTransfer_of_forcedOwnerDefect
        reward minimum (roots (time + 1)) continuation owner hafterOwner hη
          hwall hminimum
    refine ⟨time, htime, Or.inr ?_⟩
    refine ⟨who, hwho, ?_⟩
    exact hhalf

/-- **Quantitative reset-weight form of the blocker/reset adapter.**

Under a positive reward scale, the coarse blocker-drop branch of the finite
mountain pass is an actual member of the supplied reset word with weight
strictly larger than `η / (8M)`.  Otherwise a landing prefix supports the
literal half-reset source-excess/outsider-transfer charge.

This is the strongest consequence of edge affinity: a unit overwrite is not
forced, and the reset weight is not identified with a chronological survival
weight. -/
theorem exists_prefix_halfResetCharge_or_macroscopicResetWeight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (moves : List (QuittingFractionalEndpointMove ι))
    (owner : ι) {M η : ℝ}
    (hrootOwner : root owner = PMF.pure true)
    (houtsider : ∀ move ∈ moves, move.who ≠ owner)
    (hM : 0 < M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hpunish : |quittingPunishmentValue reward owner| ≤ M)
    (hη : 0 < η) (hgap : HasTerminalExploitabilityGap reward η)
    (hstart : 0 < quittingAtomicBlockerBalance reward root owner)
    (hend : quittingAtomicBlockerBalance reward
      (quittingFractionalEndpointMoves moves root) owner ≤ -η)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    (∃ time, time < moves.length ∧
      HasAtomicBlockerHalfResetCharge reward minimum
        (quittingFractionalEndpointPrefixRoot root moves (time + 1))
        continuation owner η) ∨
      ∃ time before move after,
        time < moves.length ∧
          moves = before ++ move :: after ∧
          before.length = time ∧
          quittingFractionalEndpointPrefixRoot root moves time =
            quittingFractionalEndpointMoves before root ∧
          quittingFractionalEndpointPrefixRoot root moves (time + 1) =
            move.apply
              (quittingFractionalEndpointPrefixRoot root moves time) ∧
          η / (8 * M) < move.weight := by
  obtain ⟨time, htime, hdrop | hcharge⟩ :=
    exists_prefix_excess_or_outsiderTransfer_or_blockerDrop
      reward minimum root continuation moves owner hrootOwner houtsider
        hη hgap hstart hend hminimum
  · obtain ⟨before, move, after, hsplit, hlength, hbefore, hafter⟩ :=
      exists_fractionalEndpointPrefixEdge root moves time htime
    have hmoveMem : move ∈ moves := by
      rw [hsplit]
      simp
    have hmoveOwner : move.who ≠ owner := houtsider move hmoveMem
    have hdrop' : η / 2 <
        quittingAtomicBlockerBalance reward
            (quittingFractionalEndpointPrefixRoot root moves time) owner -
          quittingAtomicBlockerBalance reward
            (move.apply
              (quittingFractionalEndpointPrefixRoot root moves time)) owner := by
      rwa [← hafter]
    have hweight := weight_gt_gap_div_eight_mul_of_atomicBlockerDrop
      reward (quittingFractionalEndpointPrefixRoot root moves time) owner move
        hmoveOwner hM hreward hpunish hdrop'
    exact Or.inr ⟨time, before, move, after, htime, hsplit, hlength,
      hbefore, hafter, hweight⟩
  · left
    refine ⟨time, htime, ?_⟩
    exact hcharge

end GameTheory
