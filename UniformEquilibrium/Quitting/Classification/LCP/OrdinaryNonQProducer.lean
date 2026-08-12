/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.Gate
import UniformEquilibrium.Quitting.Classification.LCP.IsolatedEndpointProducer
import UniformEquilibrium.Quitting.Classification.LCP.LaterLayerAbnormal
import UniformEquilibrium.Quitting.Classification.ThreePlayer.AnalyticPacket

/-!
# The ordinary non-Q producer

This file formalizes the auxiliary discounted-game argument for the corrected
normal core.  A right-hand side with no projective LCP solution is extended by
a positive value off the core and used as the affine live anchor of a shifted
quitting game.  An all-Continue analytic endpoint produces an anchored
projective singleton packet.  Its positive singleton support either lies in
the corrected normal core, where it restricts to the forbidden LCP solution,
or is a single abnormal column; the latter is closed by the two-hazard
nonnegative-column theorem.

The remaining absorbing-endpoint case is treated strategically below.  No
matrix-classification implication is assumed.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Filter Set Topology
open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## A generic all-Continue analytic alternative -/

/-- A projective packet together with analytic provenance for each positive
singleton coordinate. -/
structure QuittingGermSupportedProjectivePacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame reward).AnalyticBellmanGerm) where
  packet : QuittingProjectiveSingletonPacket reward
  positive_eventuallyActive : ∀ owner, 0 < packet.singleton owner →
    ¬∀ᶠ t in 𝓝[>] (0 : ℝ), quittingGermQuitRate g owner t = 0

/-- A positive limiting normalized share cannot come from an analytically
absent coordinate. -/
theorem not_eventually_quitRate_zero_of_positive_share
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (owner : ι)
    (htotal : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < ∑ other, quittingGermQuitRate g other t)
    {share : ℝ}
    (hshare : Tendsto
      (fun t => quittingGermQuitRate g owner t /
        ∑ other, quittingGermQuitRate g other t)
      (𝓝[>] (0 : ℝ)) (𝓝 share))
    (hpositive : 0 < share) :
    ¬∀ᶠ t in 𝓝[>] (0 : ℝ), quittingGermQuitRate g owner t = 0 := by
  intro hzero
  have hzeroShare : Tendsto
      (fun t => quittingGermQuitRate g owner t /
        ∑ other, quittingGermQuitRate g other t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hzero, htotal] with t hz ht
    simp [hz]
  have : share = 0 := tendsto_nhds_unique hshare hzeroShare
  linarith

/-- At an all-Continue endpoint, an analytic quitting-game Bellman germ gives
either the zero-solo branch or a normalized projective singleton packet. -/
theorem quittingGerm_allContinue_zeroSolo_or_supportedProjectivePacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1) :
    IsQuittingZeroSolo reward ∨
      Nonempty (QuittingGermSupportedProjectivePacket reward g) := by
  classical
  by_cases hzero : IsQuittingZeroSolo reward
  · exact Or.inl hzero
  · obtain ⟨m, leading, horder, hleadingNonneg, hleadingSumPos, _hsupport,
      htotal, hshare, hsmall, _hmatchingLimit, hbig⟩ :=
        quittingGermLeadingOrderNormalization_of_not_isQuittingZeroSolo
          g hzero
    have hm : 1 ≤ m :=
      one_le_quittingGerm_leadingOrder_of_endpoint_allContinue
        g hcontinue horder
    have hne : ∃ owner,
        ¬∀ᶠ t in 𝓝[>] (0 : ℝ), quittingGermQuitRate g owner t = 0 :=
      exists_not_eventually_quittingGermQuitRate_eq_zero_of_not_isQuittingZeroSolo
        g hzero
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
      have hzero' : IsQuittingZeroSolo reward := by
        intro who
        have hsolo :=
          quittingGerm_solo_le_endpointValue_of_endpoint_allContinue
            g hcontinue who
        have hvalueWho := congrFun hvalueZero who
        simp only [Pi.zero_apply] at hvalueWho
        rw [hvalueWho] at hsolo
        exact hsolo
      exact Or.inl hzero'
    · have hmatchingOrder :
          Math.familyAnalyticOrder (quittingGermQuitRate g) =
            g.ramification := by
        rw [horder]
        exact_mod_cast hmatching.symm
      obtain ⟨matchingData⟩ :=
        exists_quittingGermMatchingLeadingData reward g hne hmatchingOrder
      let packet := matchingData.toProjectiveSingletonPacket
      refine Or.inr ⟨⟨packet, ?_⟩⟩
      intro owner hpositive
      have hden : 0 < 1 + ∑ other, matchingData.leading other := by
        linarith [matchingData.leading_sum_pos]
      have hleading : 0 < matchingData.leading owner := by
        change 0 < matchingData.leading owner /
          (1 + ∑ other, matchingData.leading other) at hpositive
        rcases div_pos_iff.mp hpositive with hbothPositive | hbothNegative
        · exact hbothPositive.1
        · linarith [hden, hbothNegative.2]
      exact not_eventually_quitRate_zero_of_positive_share
        g owner matchingData.eventually_total_pos
        (matchingData.share_tendsto owner)
        (div_pos hleading matchingData.leading_sum_pos)
    · let hfastData : QuittingGermFastLeadingData reward g :=
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
      refine Or.inr ⟨⟨packet, ?_⟩⟩
      intro owner hpositive
      exact not_eventually_quitRate_zero_of_positive_share
        g owner hfastData.eventually_total_pos
        (hfastData.share_tendsto owner) hpositive

/-- Packet-only projection of the provenance-preserving alternative. -/
theorem quittingGerm_allContinue_zeroSolo_or_projectivePacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1) :
    IsQuittingZeroSolo reward ∨
      Nonempty (QuittingProjectiveSingletonPacket reward) := by
  rcases quittingGerm_allContinue_zeroSolo_or_supportedProjectivePacket
      reward g hcontinue with hzero | hsupported
  · exact Or.inl hzero
  · exact Or.inr ⟨hsupported.some.packet⟩

/-! ## Translating a shifted packet back to an anchored packet -/

/-- A zero-anchor packet for the reward table shifted by `anchor` is exactly
an `anchor`-cemetery packet for the original reward table. -/
def anchoredPacketOfShiftedPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : Payoff ι)
    (packet : QuittingProjectiveSingletonPacket
      (quittingRewardShift reward anchor)) :
    QuittingAnchoredProjectiveSingletonPacket reward where
  anchor := anchor
  cemetery := packet.cemetery
  singleton := packet.singleton
  value := quittingPayoffUnshift anchor packet.value
  cemetery_nonneg := packet.cemetery_nonneg
  singleton_nonneg := packet.singleton_nonneg
  total := packet.total
  value_eq_anchored_mix := by
    intro who
    rw [quittingPayoffUnshift_apply, packet.value_eq_singleton_mix]
    simp_rw [quittingRewardShift_apply, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    have hsum : ∑ owner, packet.singleton owner = 1 - packet.cemetery := by
      linarith [packet.total]
    rw [hsum]
    ring
  solo_le_value := by
    intro who
    have h := packet.solo_le_value who
    simpa [quittingRewardShift_apply, quittingPayoffUnshift_apply, add_comm] using
      (add_le_add_right h (anchor who))
  positive_singleton_pins := by
    intro who hpositive
    have h := packet.positive_singleton_pins who hpositive
    simpa [quittingRewardShift_apply, quittingPayoffUnshift_apply, add_comm] using
      congrArg (fun x => x + anchor who) h

omit [Fintype ι] [DecidableEq ι] in
/-- Shifting by the solo baseline plus `q` makes the anchored LCP direction
definitionally equal to `q`. -/
theorem quittingAnchoredProjectiveLCPDirection_baseline_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (q : ι → ℝ) (who : ι) :
    quittingAnchoredProjectiveLCPDirection reward
        (fun player => quittingSoloBaseline reward player + q player) who =
      q who := by
  simp [quittingAnchoredProjectiveLCPDirection, quittingSoloBaseline]

/-- Convert the analytic packet of the `solo baseline + q` shifted table
directly to a projective solution of the original normalized singleton matrix
with right-hand side `q`. -/
def projectiveLCPSolutionOfBaselineShiftedPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (q : ι → ℝ)
    (packet : QuittingProjectiveSingletonPacket
      (quittingRewardShift reward
        (fun who => quittingSoloBaseline reward who + q who))) :
    ProjectiveLCPSolution (normalizedSoloMatrix reward) q := by
  let anchored := anchoredPacketOfShiftedPacket reward
    (fun who => quittingSoloBaseline reward who + q who) packet
  refine
    { cemetery := packet.cemetery
      singleton := packet.singleton
      cemetery_nonneg := packet.cemetery_nonneg
      singleton_nonneg := packet.singleton_nonneg
      total := packet.total
      residual_nonneg := ?_
      complementary := ?_ }
  · intro who
    rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
    have hslack :=
      quittingAnchoredProjectiveSingletonPacket_slack_nonneg
        reward anchored who
    rw [quittingAnchoredProjectiveSingletonPacket_balance] at hslack
    simpa [anchored, anchoredPacketOfShiftedPacket,
      quittingAnchoredProjectiveLCPDirection_baseline_add] using hslack
  · intro who
    rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
    have hcomplementary :=
      quittingAnchoredProjectiveSingletonPacket_complementary
        reward anchored who
    rw [quittingAnchoredProjectiveSingletonPacket_balance] at hcomplementary
    simpa [anchored, anchoredPacketOfShiftedPacket,
      quittingAnchoredProjectiveLCPDirection_baseline_add] using hcomplementary

@[simp] theorem projectiveLCPSolutionOfBaselineShiftedPacket_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (q : ι → ℝ)
    (packet : QuittingProjectiveSingletonPacket
      (quittingRewardShift reward
        (fun who => quittingSoloBaseline reward who + q who))) :
    (projectiveLCPSolutionOfBaselineShiftedPacket reward q packet).singleton =
      packet.singleton := by
  rfl

/-! ## Generic absorbing endpoint compiler -/

/-- If an absorbing shifted analytic endpoint contracts every player's fixed
opponents, translation back by an arbitrary anchor gives an ordinary uniform
equilibrium payoff of the original table.  No punishment-specific property
of the anchor is used. -/
theorem isUniformEquilibriumPayoff_of_shiftedGerm_absorbingEndpoint_contracts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : Payoff ι)
    (g : (quittingGame (quittingRewardShift reward anchor)).AnalyticBellmanGerm)
    (habsorbs : quittingStationaryContinueMass (g.endpointProfile none) < 1)
    (hcontracts : ∀ who,
      quittingStationaryFixedOpponentsContinueMass
        (g.endpointProfile none) who < 1) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingPayoffUnshift anchor (quittingGermValue g 0)) := by
  let root : ι → PMF Bool := g.endpointProfile none
  let target := quittingPayoffUnshift anchor (quittingGermValue g 0)
  have hfixedShift := quittingGerm_endpoint_fixedPoint g
  have hfixed : target = quittingRootSuccessorPayoff reward target root := by
    exact quittingRootFixedPoint_unshift reward anchor
      (quittingGermValue g 0) root hfixedShift
  have hnashShift := quittingGerm_endpoint_endpointNash g
  have hnashEndpoint : IsεQuittingRootEndpointNash reward target 0 root :=
    (isεQuittingRootEndpointNash_zero_shift_iff reward anchor
      (quittingGermValue g 0) root).mp hnashShift
  have hnash : IsεQuittingRootNash reward target 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward target root).mp hnashEndpoint
  let cycle : Fin 1 → ι → PMF Bool := fun _ => root
  let value : Fin 1 → Payoff ι := fun _ => target
  apply isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle
    reward cycle value 0
  · intro phase
    simpa [cycle, value, finRotate] using hfixed
  · intro phase
    simpa [cycle, value, finRotate] using hnash
  · simpa [cycle] using habsorbs
  · intro who
    exact Or.inl (by simpa [cycle] using hcontracts who)

/-- Two distinct players with positive quit probability make every player's
fixed opponents contract. -/
theorem fixedOpponents_contract_of_two_positive
    (root : ι → PMF Bool)
    (htwo : ∃ first second, first ≠ second ∧
      0 < (root first true).toReal ∧ 0 < (root second true).toReal) :
    ∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1 := by
  intro who
  obtain ⟨first, second, hne, hfirst, hsecond⟩ := htwo
  have hopponentContracts : ∀ other, other ≠ who →
      0 < (root other true).toReal →
      quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    intro other hother hpositive
    by_contra hnot
    have hle : quittingStationaryFixedOpponentsContinueMass root who ≤ 1 :=
      quittingStationaryContinueMass_le_one
        (Function.update root who (PMF.pure false))
    have hmass : quittingStationaryFixedOpponentsContinueMass root who = 1 :=
      le_antisymm hle (not_lt.mp hnot)
    have hpure :=
      opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
        root who hmass other hother
    have hzero : (root other true).toReal = 0 := by rw [hpure]; simp
    linarith
  by_cases hfirstWho : first = who
  · exact hopponentContracts second (by
      intro hsecondWho
      exact hne (hfirstWho.trans hsecondWho.symm)) hsecond
  · exact hopponentContracts first hfirstWho hfirst

/-- Membership in the corrected normal core supplies a distinct first-layer
blocker. -/
theorem exists_blocker_of_mem_normalCore
    (M : ι → ι → ℝ) {owner : ι} (howner : owner ∈ normalCore M) :
    ∃ blocker, blocker ≠ owner ∧ M owner blocker ≤ 0 := by
  have hlevel : owner ∈ normalLayer M (0 + 1) :=
    (mem_normalCore M owner).1 howner 1
  obtain ⟨_, blocker, _, hne, hentry⟩ :=
    (mem_normalLayer_succ M 0 owner).1 hlevel
  exact ⟨blocker, hne, hentry⟩

/-- A shifted analytic endpoint supported by one positive owner is closed by
the isolated-endpoint repair as soon as one distinct nonpositive singleton
column is exposed.  This is the exact strategic consumer needed from the
one-step opponent-leading normalization; full normal-core membership is not
required. -/
theorem exists_uniformEquilibriumPayoff_of_shiftedGerm_isolatedEndpoint_of_blocker
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : Payoff ι)
    (g : (quittingGame (quittingRewardShift reward anchor)).AnalyticBellmanGerm)
    (owner : ι)
    (howner : 0 < ((g.endpointProfile none owner) true).toReal)
    (hother : ∀ other, other ≠ owner →
      g.endpointProfile none other = PMF.pure false)
    (blocker : ι) (hne : blocker ≠ owner)
    (hblockerMatrix : normalizedSoloMatrix reward owner blocker ≤ 0) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let root : ι → PMF Bool := g.endpointProfile none
  let hazard : PMF Bool := root owner
  let shiftedValue : Payoff ι := quittingGermValue g 0
  let target : Payoff ι := quittingPayoffUnshift anchor shiftedValue
  have hroot : root = quittingSoloStationaryRoot owner hazard := by
    exact eq_quittingSoloStationaryRoot_of_others_continue hother
  have hhazard : 0 < (hazard true).toReal := howner
  have habsorbs : quittingStationaryContinueMass root < 1 := by
    rw [hroot, quittingStationaryContinueMass_solo]
    have hsum := quittingRoot_continueProbability_add_quitProbability
      (fun _ : Unit => hazard) ()
    linarith
  have hfixedShift := quittingGerm_endpoint_fixedPoint g
  have hfixed : target = quittingRootSuccessorPayoff reward target root :=
    quittingRootFixedPoint_unshift reward anchor shiftedValue root hfixedShift
  have hactual := quittingTerminalPayoff_stationary_eq_of_fixedPoint
    reward root target habsorbs hfixed
  have htarget : target = quittingSoloReward reward owner := by
    funext who
    have hactualWho := congrFun hactual who
    rw [hroot, quittingTerminalPayoff_soloStationary
      reward owner who hazard hhazard] at hactualWho
    exact hactualWho.symm
  have hnashShift := quittingGerm_endpoint_endpointNash g
  have hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard) := by
    have hnashOriginal : IsεQuittingRootEndpointNash reward target 0 root :=
      (isεQuittingRootEndpointNash_zero_shift_iff
        reward anchor shiftedValue root).mp hnashShift
    simpa [hroot, htarget] using hnashOriginal
  have hblocker : quittingSoloReward reward blocker owner ≤
      quittingSoloReward reward owner owner := by
    rw [normalizedSoloMatrix_eq_projectiveLCPMatrix] at hblockerMatrix
    unfold quittingProjectiveLCPMatrix at hblockerMatrix
    simpa [quittingSoloReward, quittingProjectiveSingletonTerminal] using
      hblockerMatrix
  exact exists_uniformEquilibriumPayoff_of_isolatedEndpoint
    reward hne hazard hhazard hnash hblocker

/-- A shifted analytic endpoint supported by one positive normal owner is
closed by the isolated-endpoint blocker repair. -/
theorem exists_uniformEquilibriumPayoff_of_shiftedGerm_isolatedNormalEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : Payoff ι)
    (g : (quittingGame (quittingRewardShift reward anchor)).AnalyticBellmanGerm)
    (owner : ι)
    (howner : 0 < ((g.endpointProfile none owner) true).toReal)
    (hother : ∀ other, other ≠ owner →
      g.endpointProfile none other = PMF.pure false)
    (hnormal : owner ∈ normalCore (normalizedSoloMatrix reward)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨blocker, hne, hblockerMatrix⟩ :=
    exists_blocker_of_mem_normalCore
      (normalizedSoloMatrix reward) hnormal
  exact
    exists_uniformEquilibriumPayoff_of_shiftedGerm_isolatedEndpoint_of_blocker
      reward anchor g owner howner hother blocker hne hblockerMatrix

/-! ## Restricting an anchored LCP packet to the corrected core -/

/-- Extend a right-hand side on the corrected normal core by the fixed
strictly positive value `1` off the core. -/
def extendNormalDirection (M : ι → ι → ℝ)
    (q : normalCore M → ℝ) : ι → ℝ :=
  fun who => if hwho : who ∈ normalCore M then q ⟨who, hwho⟩ else 1

@[simp] theorem extendNormalDirection_of_mem
    (M : ι → ι → ℝ) (q : normalCore M → ℝ)
    {who : ι} (hwho : who ∈ normalCore M) :
    extendNormalDirection M q who = q ⟨who, hwho⟩ := by
  simp [extendNormalDirection, hwho]

@[simp] theorem extendNormalDirection_of_notMem
    (M : ι → ι → ℝ) (q : normalCore M → ℝ)
    {who : ι} (hwho : who ∉ normalCore M) :
    extendNormalDirection M q who = 1 := by
  simp [extendNormalDirection, hwho]

/-- If a projective LCP solution for the positive off-core extension has two
distinct positive singleton coordinates, every positive coordinate belongs
to the corrected normal core. -/
theorem positive_singleton_mem_normalCore_of_two_positive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (q : normalCore (normalizedSoloMatrix reward) → ℝ)
    (solution : ProjectiveLCPSolution (normalizedSoloMatrix reward)
      (extendNormalDirection (normalizedSoloMatrix reward) q))
    (htwo : ∃ first second,
      first ≠ second ∧ 0 < solution.singleton first ∧
        0 < solution.singleton second)
    {owner : ι} (howner : 0 < solution.singleton owner) :
    owner ∈ normalCore (normalizedSoloMatrix reward) := by
  classical
  let M := normalizedSoloMatrix reward
  have hlevels : ∀ n : ℕ, ∀ who : ι,
      0 < solution.singleton who → who ∈ normalLayer M n := by
    intro n
    induction n with
    | zero =>
        intro who _
        simp [normalLayer]
    | succ n ih =>
        intro who hwho
        by_cases hcore : who ∈ normalCore M
        · exact (mem_normalCore M who).1 hcore (n + 1)
        · have hqpos : 0 < extendNormalDirection M q who := by
            rw [extendNormalDirection_of_notMem M q hcore]
            norm_num
          have hresidualZero :
              solution.cemetery * extendNormalDirection M q who +
                  ∑ other, solution.singleton other * M who other = 0 := by
            rcases mul_eq_zero.mp (solution.complementary who) with hzero | hzero
            · exact False.elim ((ne_of_gt hwho) hzero)
            · exact hzero
          have hother : ∃ other,
              0 < solution.singleton other ∧ other ≠ who := by
            obtain ⟨first, second, hne, hfirst, hsecond⟩ := htwo
            by_cases hfirstWho : first = who
            · exact ⟨second, hsecond, by
                intro hsecondWho
                exact hne (hfirstWho.trans hsecondWho.symm)⟩
            · exact ⟨first, hfirst, hfirstWho⟩
          obtain ⟨other, hotherPos, hotherNe⟩ := hother
          have hwitness : ∃ blocker,
              0 < solution.singleton blocker ∧ blocker ≠ who ∧
                M who blocker ≤ 0 := by
            by_contra hnone
            push Not at hnone
            have htermNonneg : ∀ blocker,
                0 ≤ solution.singleton blocker * M who blocker := by
              intro blocker
              by_cases hweight : solution.singleton blocker = 0
              · simp [hweight]
              · have hweightPos : 0 < solution.singleton blocker :=
                  lt_of_le_of_ne (solution.singleton_nonneg blocker)
                    (Ne.symm hweight)
                by_cases hsame : blocker = who
                · subst blocker
                  simp [M, normalizedSoloMatrix_diagonal]
                · exact mul_nonneg hweightPos.le
                    (hnone blocker hweightPos hsame).le
            have hotherTerm :
                0 < solution.singleton other * M who other := by
              exact mul_pos hotherPos
                (hnone other hotherPos hotherNe)
            have hsumPos :
                0 < ∑ blocker,
                    solution.singleton blocker * M who blocker := by
              exact Finset.sum_pos' (fun blocker _ => htermNonneg blocker)
                ⟨other, Finset.mem_univ other, hotherTerm⟩
            have hcemeteryTerm :
                0 ≤ solution.cemetery * extendNormalDirection M q who :=
              mul_nonneg solution.cemetery_nonneg hqpos.le
            linarith
          obtain ⟨blocker, hblockerPos, hblockerNe, hentry⟩ := hwitness
          exact (mem_normalLayer_succ M n who).2
            ⟨ih who hwho, blocker, ih blocker hblockerPos,
              hblockerNe, hentry⟩
  exact (mem_normalCore _ _).2 (fun n => hlevels n owner howner)

/-- Restrict a projective solution whose positive singleton support lies in
the corrected normal core to the principal normal-player matrix. -/
def restrictProjectiveLCPSolutionToNormalCore
    (M : ι → ι → ℝ) (q : normalCore M → ℝ)
    (solution : ProjectiveLCPSolution M (extendNormalDirection M q))
    (hsupport : ∀ who, 0 < solution.singleton who → who ∈ normalCore M) :
    ProjectiveLCPSolution (normalPlayerMatrix M) q := by
  classical
  have hzeroOff : ∀ who, who ∉ normalCore M → solution.singleton who = 0 := by
    intro who hwho
    by_contra hne
    have hpos : 0 < solution.singleton who :=
      lt_of_le_of_ne (solution.singleton_nonneg who) (Ne.symm hne)
    exact hwho (hsupport who hpos)
  have hsumRestrict (f : ι → ℝ)
      (hoff : ∀ who, who ∉ normalCore M → f who = 0) :
      (∑ who, f who) = ∑ who : normalCore M, f who.1 := by
    calc
      (∑ who, f who) = ∑ who ∈ normalCore M, f who := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro who _ hwho
        exact hoff who hwho
      _ = ∑ who : normalCore M, f who.1 :=
        Finset.sum_subtype (normalCore M) (fun _ => Iff.rfl) f
  refine
    { cemetery := solution.cemetery
      singleton := fun who => solution.singleton who.1
      cemetery_nonneg := solution.cemetery_nonneg
      singleton_nonneg := fun who => solution.singleton_nonneg who.1
      total := ?_
      residual_nonneg := ?_
      complementary := ?_ }
  · calc
      solution.cemetery + ∑ who : normalCore M, solution.singleton who.1 =
          solution.cemetery + ∑ who, solution.singleton who := by
            rw [hsumRestrict solution.singleton hzeroOff]
      _ = 1 := solution.total
  · intro who
    have h := solution.residual_nonneg who.1
    rw [extendNormalDirection_of_mem M q who.property] at h
    change 0 ≤ solution.cemetery * q who +
      ∑ owner : normalCore M,
        solution.singleton owner.1 * M who.1 owner.1
    calc
      0 ≤ solution.cemetery * q who +
          ∑ owner, solution.singleton owner * M who.1 owner := h
      _ = solution.cemetery * q who +
          ∑ owner : normalCore M,
            solution.singleton owner.1 * M who.1 owner.1 := by
          congr 1
          exact hsumRestrict
            (fun owner => solution.singleton owner * M who.1 owner)
            (fun owner howner => by rw [hzeroOff owner howner, zero_mul])
  · intro who
    have h := solution.complementary who.1
    rw [extendNormalDirection_of_mem M q who.property] at h
    change solution.singleton who.1 *
      (solution.cemetery * q who +
        ∑ owner : normalCore M,
          solution.singleton owner.1 * M who.1 owner.1) = 0
    rw [← hsumRestrict
      (fun owner => solution.singleton owner * M who.1 owner)
      (fun owner howner => by rw [hzeroOff owner howner, zero_mul])]
    exact h

end QuittingLCPClassification
end GameTheory
