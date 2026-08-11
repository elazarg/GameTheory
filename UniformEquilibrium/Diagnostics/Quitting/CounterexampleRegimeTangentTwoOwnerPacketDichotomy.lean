/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerPacketEdge

/-!
# Exact-edge versus tight-gate dichotomy for two-owner tangent packets

The exact two-owner packet ray has a complete local strict-cell consumer. Its
Bellman-eliminated continuation is a rational function of the hazard scale
and converges to the packet boundary. Therefore strict punishment-floor and
upper-box slack persist for all sufficiently small scales. Strict inactive
singleton slack likewise makes every outsider Nash regression negative near
zero. Combining these facts with the exact packet-edge theorem produces a
positive-charge Nash--Bellman edge at every sufficiently small positive
scale.

The complementary cells are kept honest:

* if an active positive-tangent coordinate satisfies
  `boundary = quittingPunishmentValue`, its continuation lies strictly below
  the punishment floor at every positive scale. This is a genuine obstruction
  to this exact ray. It is not itself a punishment realization: the quitting
  min--max theorem identifies an infimum and explicitly does not assert that
  the infimum is attained;
* if an inactive owner satisfies `singleton solo = boundary`, its outsider
  regression starts at zero. Pair and higher coalition coefficients decide
  its sign and are not constrained by the packet equations;
* a tight upper box is recorded as a third physical boundary rather than
  silently perturbed away.

The final dichotomy says that either the physical cell is strict and supplies
nearby positive-charge exact edges, or one of these gates is tight. No branch
constructs a return, lasso, punishment plan, or solved cycle.
-/

noncomputable section

namespace GameTheory

open Finset Filter Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingChargeTangentPacket

/-- Hazard-side rational continuation, defined for every real scale. -/
def twoOwnerContinuationRegression
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (who : ι) : ℝ :=
  (packet.boundary who -
    ∑ S : Finset ι,
      coalitionMass (packet.twoOwnerHazardAt first second t) S *
        quittingProjectiveCoalitionReward reward S who) /
    continueMass (packet.twoOwnerHazardAt first second t)

theorem twoOwnerBellmanContinuation_eq_continuationRegression
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (who : ι) :
    quittingTwoOwnerBellmanContinuation reward packet.boundary
        (packet.twoOwnerRootAt first second t ht0 ht1) who =
      packet.twoOwnerContinuationRegression first second t who := by
  unfold quittingTwoOwnerBellmanContinuation twoOwnerContinuationRegression
  rw [quittingRootAbsorbingContribution_eq_sum_coalitionMass]
  have hrate : (fun owner =>
      ((packet.twoOwnerRootAt first second t ht0 ht1 owner) true).toReal) =
      packet.twoOwnerHazardAt first second t := by
    funext owner
    change hazardOfRoot (packet.twoOwnerRootAt first second t ht0 ht1) owner = _
    rw [packet.hazardOfRoot_twoOwnerRootAt first second t ht0 ht1]
  rw [hrate]
  unfold twoOwnerRootAt
  rw [quittingStationaryContinueMass_rootOfHazard]

theorem continuousAt_twoOwnerContinuationRegression
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι) (hne : first ≠ second) :
    ContinuousAt (fun t : ℝ =>
      packet.twoOwnerContinuationRegression first second t who) 0 := by
  have hcoordinate : ∀ owner, Continuous (fun t : ℝ =>
      packet.twoOwnerHazardAt first second t owner) := by
    intro owner
    by_cases hownerFirst : owner = first
    · subst owner
      simp only [twoOwnerHazardAt, quittingTwoOwnerHazard_first]
      fun_prop
    · by_cases hownerSecond : owner = second
      · subst owner
        simp only [twoOwnerHazardAt,
          quittingTwoOwnerHazard_second first second _ _ hne]
        fun_prop
      · have hzero : (fun t : ℝ =>
            packet.twoOwnerHazardAt first second t owner) = fun _ => 0 := by
          funext t
          exact quittingTwoOwnerHazard_eq_zero_of_ne first second owner
            (t * packet.mass first) (t * packet.mass second)
            hownerFirst hownerSecond
        rw [hzero]
        fun_prop
  have habsorbing : Continuous (fun t : ℝ =>
      ∑ S : Finset ι,
        coalitionMass (packet.twoOwnerHazardAt first second t) S *
          quittingProjectiveCoalitionReward reward S who) := by
    apply continuous_finsetSum
    intro S hS
    apply Continuous.mul
    · unfold coalitionMass
      apply Continuous.mul
      · apply continuous_finsetProd
        intro owner howner
        exact hcoordinate owner
      · apply continuous_finsetProd
        intro owner howner
        exact continuous_const.sub (hcoordinate owner)
    · fun_prop
  have hcontinue : Continuous (fun t : ℝ =>
      continueMass (packet.twoOwnerHazardAt first second t)) := by
    unfold continueMass
    apply continuous_finsetProd
    intro owner howner
    exact continuous_const.sub (hcoordinate owner)
  have hcontinueZero : continueMass
      (packet.twoOwnerHazardAt first second 0) = 1 := by
    rw [twoOwnerHazardAt,
      continueMass_twoOwner first second
        (0 * packet.mass first) (0 * packet.mass second) hne]
    norm_num
  unfold twoOwnerContinuationRegression
  apply ContinuousAt.div
  · exact continuousAt_const.sub habsorbing.continuousAt
  · exact hcontinue.continuousAt
  · rw [hcontinueZero]
    norm_num

theorem twoOwnerContinuationRegression_zero
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι) (hne : first ≠ second) :
    packet.twoOwnerContinuationRegression first second 0 who =
      packet.boundary who := by
  rw [← packet.twoOwnerBellmanContinuation_eq_continuationRegression
    first second 0 (by norm_num) (by norm_num) who]
  let root := packet.twoOwnerRootAt first second 0 (by norm_num) (by norm_num)
  have hmass : quittingStationaryContinueMass root = 1 := by
    unfold root twoOwnerRootAt
    rw [quittingStationaryContinueMass_rootOfHazard,
      twoOwnerHazardAt,
      continueMass_twoOwner first second
        (0 * packet.mass first) (0 * packet.mass second) hne]
    norm_num
  have habsorbing :=
    quittingRootAbsorbingContribution_eq_zero_of_continueMass_eq_one
      reward root hmass who
  unfold quittingTwoOwnerBellmanContinuation
  rw [habsorbing, hmass]
  ring

theorem eventually_twoOwnerContinuationRegression_mem_strictBox
    (packet : QuittingChargeTangentPacket reward)
    (floor : Payoff ι) (upper : ℝ) (first second : ι)
    (hne : first ≠ second)
    (hfloor : ∀ who, floor who < packet.boundary who)
    (hupper : ∀ who, packet.boundary who < upper) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ who,
      floor who < packet.twoOwnerContinuationRegression first second t who ∧
      packet.twoOwnerContinuationRegression first second t who < upper := by
  rw [Filter.eventually_all]
  intro who
  have hzero := packet.twoOwnerContinuationRegression_zero first second who hne
  have hlower : ∀ᶠ t in 𝓝 (0 : ℝ),
      floor who < packet.twoOwnerContinuationRegression first second t who :=
    continuousAt_const.eventually_lt
      (packet.continuousAt_twoOwnerContinuationRegression first second who hne)
      (by simpa [hzero] using hfloor who)
  have hupper' : ∀ᶠ t in 𝓝 (0 : ℝ),
      packet.twoOwnerContinuationRegression first second t who < upper :=
    (packet.continuousAt_twoOwnerContinuationRegression first second who hne).eventually_lt
      continuousAt_const (by simpa [hzero] using hupper who)
  filter_upwards [hlower, hupper'] with t hlt hut
  exact ⟨hlt, hut⟩

/-- A strict physical cell around the packet boundary produces exact
positive-charge Nash--Bellman edges at every sufficiently small positive
scale. -/
theorem eventually_exists_positiveChargeExactEdge_of_strictPhysicalCell
    (packet : QuittingChargeTangentPacket reward)
    (floor : Payoff ι) (upper : ℝ) (first second : ι)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first) (hsecond : 0 < packet.mass second)
    (houtsideMass : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst : quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond : quittingActivePairCompatibilityResidual packet second = 0)
    (hfloor : ∀ who, floor who < packet.boundary who)
    (hupper : ∀ who, packet.boundary who < upper)
    (houtsideSolo : ∀ who, who ≠ first → who ≠ second →
      reward (quittingSingletonTerminal who) who < packet.boundary who) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∃ root : ι → PMF Bool, ∃ continuation : Payoff ι,
        hazardOfRoot root = packet.twoOwnerHazardAt first second t ∧
        0 < quittingRootAbsorptionMass root ∧
        ∀ tailRoot : QuittingRootSimplex ι,
          IsQuittingNashBellmanEdge reward
            (packet.boundary, quittingFrozenRootLiftSimplex root)
            (continuation, tailRoot) := by
  have hbox := packet.eventually_twoOwnerContinuationRegression_mem_strictBox
    floor upper first second hne hfloor hupper
  have houtside :=
    packet.eventually_twoOwnerOutsiderGainRegression_neg_of_solo_lt_boundary
      first second houtsideSolo
  have htlt : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 :=
    continuousAt_id.eventually_lt continuousAt_const zero_lt_one
  filter_upwards [hbox.filter_mono nhdsWithin_le_nhds,
    houtside.filter_mono nhdsWithin_le_nhds,
    htlt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t hboxAt houtsideAt htlt htpos
  have ht0 : 0 < t := htpos
  let root := packet.twoOwnerRootAt first second t ht0.le htlt.le
  let continuation :=
    quittingTwoOwnerBellmanContinuation reward packet.boundary root
  have hsurvival : quittingStationaryContinueMass root ≠ 0 := by
    unfold root twoOwnerRootAt
    rw [quittingStationaryContinueMass_rootOfHazard,
      twoOwnerHazardAt,
      continueMass_twoOwner first second
        (t * packet.mass first) (t * packet.mass second) hne]
    have hfirstLt : t * packet.mass first < 1 := by
      nlinarith [packet.mass_nonneg first, packet.twoOwner_mass_le_one first]
    have hsecondLt : t * packet.mass second < 1 := by
      nlinarith [packet.mass_nonneg second, packet.twoOwner_mass_le_one second]
    exact mul_ne_zero (by linarith) (by linarith)
  have hfloorAt : ∀ who, floor who ≤ continuation who := by
    intro who
    change floor who ≤ quittingTwoOwnerBellmanContinuation reward
      packet.boundary root who
    rw [packet.twoOwnerBellmanContinuation_eq_continuationRegression
      first second t ht0.le htlt.le who]
    exact (hboxAt who).1.le
  have hupperAt : ∀ who, continuation who ≤ upper := by
    intro who
    change quittingTwoOwnerBellmanContinuation reward packet.boundary root who ≤ upper
    rw [packet.twoOwnerBellmanContinuation_eq_continuationRegression
      first second t ht0.le htlt.le who]
    exact (hboxAt who).2.le
  have houtsideGain : ∀ who, who ≠ first → who ≠ second →
      gainValue (weightOfReward reward)
        (packet.twoOwnerHazardAt first second t) who (continuation who) ≤ 0 := by
    intro who hwhoFirst hwhoSecond
    change gainValue (weightOfReward reward)
      (packet.twoOwnerHazardAt first second t) who
      (quittingTwoOwnerBellmanContinuation reward packet.boundary root who) ≤ 0
    rw [packet.gainValue_twoOwnerBellmanContinuationAt_outside_eq_regression
      first second who t ht0.le htlt.le hwhoFirst hwhoSecond hsurvival]
    exact (houtsideAt who hwhoFirst hwhoSecond).le
  refine ⟨root, continuation, ?_, ?_, ?_⟩
  · exact packet.hazardOfRoot_twoOwnerRootAt first second t ht0.le htlt.le
  · unfold root twoOwnerRootAt
    rw [quittingRootAbsorptionMass_rootOfHazard,
      twoOwnerHazardAt,
      continueMass_twoOwner first second
        (t * packet.mass first) (t * packet.mass second) hne]
    have hp : 0 < t * packet.mass first := mul_pos ht0 hfirst
    have hq : 0 < t * packet.mass second := mul_pos ht0 hsecond
    have hpOne : t * packet.mass first < 1 := by
      nlinarith [packet.mass_nonneg first, packet.twoOwner_mass_le_one first]
    have hqOne : t * packet.mass second < 1 := by
      nlinarith [packet.mass_nonneg second, packet.twoOwner_mass_le_one second]
    rw [show 1 - (1 - t * packet.mass first) *
        (1 - t * packet.mass second) =
      t * packet.mass first * (1 - t * packet.mass second) +
        t * packet.mass second by ring]
    positivity
  · intro tailRoot
    exact packet.isQuittingNashBellmanEdge_twoOwnerAt floor upper first second
      t ht0 htlt hne hfirst hsecond houtsideMass hcompatFirst hcompatSecond
      houtsideGain hfloorAt hupperAt tailRoot

/-- A positive active tangent at a boundary coordinate equal to its
punishment value blocks the exact two-owner ray at every positive scale.
This is a floor obstruction, not a punishment-realization theorem: the
min--max infimum need not be attained. -/
theorem punishmentFloor_obstructs_twoOwnerRay_of_tangent_pos
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first) (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst : quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond : quittingActivePairCompatibilityResidual packet second = 0)
    (hfirst_lt : t * packet.mass first < 1)
    (hsecond_lt : t * packet.mass second < 1)
    (hsurvival : quittingStationaryContinueMass
      (packet.twoOwnerRootAt first second t ht0.le ht1) ≠ 0)
    (htangent : 0 < packet.tangent first)
    (htight : packet.boundary first = quittingPunishmentValue reward first) :
    ¬ quittingPunishmentValue reward first ≤
      quittingTwoOwnerBellmanContinuation reward packet.boundary
        (packet.twoOwnerRootAt first second t ht0.le ht1) first := by
  exact packet.not_floor_le_twoOwnerBellmanContinuationAt_first_of_tangent_pos
    (fun who => quittingPunishmentValue reward who) first second t ht0 ht1 hne
    hfirst hsecond houtside hcompatFirst hcompatSecond hfirst_lt hsecond_lt
    hsurvival htangent htight.symm

/-- On a tight inactive singleton row, the outsider Nash gate starts exactly
at zero and is thereafter decided by the finite outsider regression. Packet
data impose no sign on its pair and higher coefficients. -/
theorem tightOutsiderNashGate_eq_regression
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hwhoFirst : who ≠ first) (hwhoSecond : who ≠ second)
    (hsurvival : quittingStationaryContinueMass
      (packet.twoOwnerRootAt first second t ht0 ht1) ≠ 0)
    (htight : reward (quittingSingletonTerminal who) who =
      packet.boundary who) :
    packet.twoOwnerOutsiderGainRegression first second 0 who = 0 ∧
      (gainValue (weightOfReward reward)
          (packet.twoOwnerHazardAt first second t) who
          (quittingTwoOwnerBellmanContinuation reward packet.boundary
            (packet.twoOwnerRootAt first second t ht0 ht1) who) ≤ 0 ↔
        packet.twoOwnerOutsiderGainRegression first second t who ≤ 0) := by
  constructor
  · rw [packet.twoOwnerOutsiderGainRegression_zero first second who, htight]
    ring
  · rw [packet.gainValue_twoOwnerBellmanContinuationAt_outside_eq_regression
      first second who t ht0 ht1 hwhoFirst hwhoSecond hsurvival]

/-- **Exact-edge/tight-gate dichotomy.**  Under the packet's non-strict
physical inequalities, either the entire cell is strict and supplies
positive-charge exact edges near zero, or one of the three physical gates is
tight. The equality branches are named obstructions, not return or
punishment-realization claims. -/
theorem positiveChargeExactEdge_or_tightPhysicalGate
    (packet : QuittingChargeTangentPacket reward)
    (upper : ℝ) (first second : ι)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first) (hsecond : 0 < packet.mass second)
    (houtsideMass : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst : quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond : quittingActivePairCompatibilityResidual packet second = 0)
    (hboundaryUpper : ∀ who, packet.boundary who ≤ upper) :
    (∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∃ root : ι → PMF Bool, ∃ continuation : Payoff ι,
        hazardOfRoot root = packet.twoOwnerHazardAt first second t ∧
        0 < quittingRootAbsorptionMass root ∧
        ∀ tailRoot : QuittingRootSimplex ι,
          IsQuittingNashBellmanEdge reward
            (packet.boundary, quittingFrozenRootLiftSimplex root)
            (continuation, tailRoot)) ∨
      (∃ who, packet.boundary who = quittingPunishmentValue reward who) ∨
      (∃ who, who ≠ first ∧ who ≠ second ∧
        reward (quittingSingletonTerminal who) who = packet.boundary who) ∨
      ∃ who, packet.boundary who = upper := by
  by_cases hfloorStrict : ∀ who,
      quittingPunishmentValue reward who < packet.boundary who
  · by_cases hupperStrict : ∀ who, packet.boundary who < upper
    · by_cases houtsideStrict : ∀ who, who ≠ first → who ≠ second →
        reward (quittingSingletonTerminal who) who < packet.boundary who
      · exact Or.inl <|
          packet.eventually_exists_positiveChargeExactEdge_of_strictPhysicalCell
            (fun who => quittingPunishmentValue reward who) upper first second
            hne hfirst hsecond houtsideMass hcompatFirst hcompatSecond
            hfloorStrict hupperStrict houtsideStrict
      · push Not at houtsideStrict
        obtain ⟨who, hwhoFirst, hwhoSecond, hnot⟩ := houtsideStrict
        have hle := packet.solo_le_boundary who
        have heq : reward (quittingSingletonTerminal who) who =
            packet.boundary who :=
          le_antisymm hle hnot
        exact Or.inr <| Or.inr <| Or.inl
          ⟨who, hwhoFirst, hwhoSecond, heq⟩
    · push Not at hupperStrict
      obtain ⟨who, hnot⟩ := hupperStrict
      have heq : packet.boundary who = upper :=
        le_antisymm (hboundaryUpper who) hnot
      exact Or.inr <| Or.inr <| Or.inr ⟨who, heq⟩
  · push Not at hfloorStrict
    obtain ⟨who, hnot⟩ := hfloorStrict
    have heq : packet.boundary who = quittingPunishmentValue reward who :=
      le_antisymm hnot (packet.punishment_le_boundary who)
    exact Or.inr <| Or.inl ⟨who, heq⟩

end QuittingChargeTangentPacket

end GameTheory
