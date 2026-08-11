/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerOutsiderJet

/-!
# Exact edge or positive tight-outsider jet

The exact quadratic expansion turns the last local equality gate on a
compatible two-owner packet into a finite lexicographic sign test.  A
singleton-tight inactive row is eventually harmless when its linear
coefficient is negative, or when its linear coefficient vanishes and its
quadratic coefficient is nonpositive.  The complementary cases are exactly a
positive linear coefficient, or zero linear coefficient followed by a
positive quadratic coefficient.

After recentering the auxiliary continuation floor and upper box, all harmless
outsider rows can be consumed simultaneously.  Therefore the local producer
alternative sharpens to:

* every sufficiently small positive scale supplies a positive-charge exact
  Nash--Bellman edge; or
* a singleton-tight inactive owner has a positive lexicographic outsider jet.

This is a finite support-entry pivot.  It does not construct the enlarged
support root or a chronological return.
-/

noncomputable section

namespace GameTheory

open Finset Filter Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingChargeTangentPacket

/-- The finite support-entry sign remaining at a singleton-tight outsider:
positive linear response, or a vanished linear response followed by positive
quadratic response. -/
def HasPositiveTwoOwnerOutsiderJet
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι) : Prop :=
  0 < packet.twoOwnerOutsiderLinearCoefficient first second who ∨
    (packet.twoOwnerOutsiderLinearCoefficient first second who = 0 ∧
      0 < packet.twoOwnerOutsiderQuadraticCoefficient first second who)

/-- A negative linear outsider coefficient dominates the quadratic term at
all sufficiently small positive scales. -/
theorem eventually_twoOwnerOutsiderGainRegression_neg_of_tight_of_linear_neg
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι)
    (hne : first ≠ second)
    (hwhoFirst : who ≠ first) (hwhoSecond : who ≠ second)
    (htight : reward (quittingSingletonTerminal who) who =
      packet.boundary who)
    (hlinear : packet.twoOwnerOutsiderLinearCoefficient first second who < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      packet.twoOwnerOutsiderGainRegression first second t who < 0 := by
  let linear := packet.twoOwnerOutsiderLinearCoefficient first second who
  let quadratic := packet.twoOwnerOutsiderQuadraticCoefficient first second who
  have hcontinuous : Continuous (fun t : ℝ => linear + t * quadratic) := by
    fun_prop
  have hzero : linear + (0 : ℝ) * quadratic < 0 := by
    simpa [linear] using hlinear
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), linear + t * quadratic < 0 :=
    hcontinuous.continuousAt.eventually_lt continuousAt_const hzero
  filter_upwards [hevent.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t hjet ht
  have ht0 : 0 < t := ht
  rw [packet.twoOwnerOutsiderGainRegression_eq_t_mul_jet_of_tight
    first second who t hne hwhoFirst hwhoSecond htight]
  exact mul_neg_of_pos_of_neg ht0 hjet

/-- With zero linear coefficient and nonpositive quadratic coefficient, a
tight outsider is Nash-admissible at every nonnegative scale. -/
theorem twoOwnerOutsiderGainRegression_nonpos_of_tight_of_linear_zero_of_quadratic_nonpos
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι) (t : ℝ)
    (hne : first ≠ second)
    (hwhoFirst : who ≠ first) (hwhoSecond : who ≠ second)
    (htight : reward (quittingSingletonTerminal who) who =
      packet.boundary who)
    (ht0 : 0 ≤ t)
    (hlinear : packet.twoOwnerOutsiderLinearCoefficient first second who = 0)
    (hquadratic : packet.twoOwnerOutsiderQuadraticCoefficient first second who ≤ 0) :
    packet.twoOwnerOutsiderGainRegression first second t who ≤ 0 := by
  rw [packet.twoOwnerOutsiderGainRegression_eq_t_mul_jet_of_tight
    first second who t hne hwhoFirst hwhoSecond htight, hlinear]
  calc
    t * (0 + t * packet.twoOwnerOutsiderQuadraticCoefficient first second who) =
        (t * t) * packet.twoOwnerOutsiderQuadraticCoefficient first second who := by
      ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ht0 ht0) hquadratic

/-- A positive linear coefficient makes the tight outsider strictly
profitable at all sufficiently small positive scales. -/
theorem eventually_twoOwnerOutsiderGainRegression_pos_of_tight_of_linear_pos
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι)
    (hne : first ≠ second)
    (hwhoFirst : who ≠ first) (hwhoSecond : who ≠ second)
    (htight : reward (quittingSingletonTerminal who) who =
      packet.boundary who)
    (hlinear : 0 < packet.twoOwnerOutsiderLinearCoefficient first second who) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < packet.twoOwnerOutsiderGainRegression first second t who := by
  let linear := packet.twoOwnerOutsiderLinearCoefficient first second who
  let quadratic := packet.twoOwnerOutsiderQuadraticCoefficient first second who
  have hcontinuous : Continuous (fun t : ℝ => linear + t * quadratic) := by
    fun_prop
  have hzero : 0 < linear + (0 : ℝ) * quadratic := by
    simpa [linear] using hlinear
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < linear + t * quadratic :=
    continuousAt_const.eventually_lt hcontinuous.continuousAt hzero
  filter_upwards [hevent.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t hjet ht
  have ht0 : 0 < t := ht
  rw [packet.twoOwnerOutsiderGainRegression_eq_t_mul_jet_of_tight
    first second who t hne hwhoFirst hwhoSecond htight]
  exact mul_pos ht0 hjet

/-- If the linear coefficient vanishes and the quadratic coefficient is
positive, every positive scale makes the tight outsider strictly profitable. -/
theorem twoOwnerOutsiderGainRegression_pos_of_tight_of_linear_zero_of_quadratic_pos
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι) (t : ℝ)
    (hne : first ≠ second)
    (hwhoFirst : who ≠ first) (hwhoSecond : who ≠ second)
    (htight : reward (quittingSingletonTerminal who) who =
      packet.boundary who)
    (ht0 : 0 < t)
    (hlinear : packet.twoOwnerOutsiderLinearCoefficient first second who = 0)
    (hquadratic : 0 < packet.twoOwnerOutsiderQuadraticCoefficient first second who) :
    0 < packet.twoOwnerOutsiderGainRegression first second t who := by
  rw [packet.twoOwnerOutsiderGainRegression_eq_t_mul_jet_of_tight
    first second who t hne hwhoFirst hwhoSecond htight, hlinear]
  have hsq : 0 < t * t := mul_pos ht0 ht0
  calc
    0 < (t * t) * packet.twoOwnerOutsiderQuadraticCoefficient first second who :=
      mul_pos hsq hquadratic
    _ = t * (0 + t *
        packet.twoOwnerOutsiderQuadraticCoefficient first second who) := by
      ring

/-- If no singleton-tight outsider has a positive lexicographic jet, every
inactive Nash regression is nonpositive at all sufficiently small positive
scales, simultaneously over the finite player set. -/
theorem eventually_twoOwnerOutsiderGainRegression_nonpos_of_noPositiveTightJet
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι)
    (hne : first ≠ second)
    (hnoPositive : ∀ who, who ≠ first → who ≠ second →
      reward (quittingSingletonTerminal who) who = packet.boundary who →
      ¬ packet.HasPositiveTwoOwnerOutsiderJet first second who) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ who, who ≠ first → who ≠ second →
      packet.twoOwnerOutsiderGainRegression first second t who ≤ 0 := by
  rw [Filter.eventually_all]
  intro who
  by_cases hwhoFirstEq : who = first
  · exact Filter.Eventually.of_forall fun _ hwhoFirst _ =>
      (hwhoFirst hwhoFirstEq).elim
  · by_cases hwhoSecondEq : who = second
    · exact Filter.Eventually.of_forall fun _ _ hwhoSecond =>
        (hwhoSecond hwhoSecondEq).elim
    · have hsoloLe := packet.solo_le_boundary who
      by_cases hsoloStrict :
          reward (quittingSingletonTerminal who) who < packet.boundary who
      · have hzero :
            packet.twoOwnerOutsiderGainRegression first second 0 who < 0 := by
          rw [packet.twoOwnerOutsiderGainRegression_zero first second who]
          exact sub_neg.mpr hsoloStrict
        have hevent : ∀ᶠ t in 𝓝 (0 : ℝ),
            packet.twoOwnerOutsiderGainRegression first second t who < 0 :=
          (packet.continuous_twoOwnerOutsiderGainRegression
            first second who).continuousAt.eventually_lt continuousAt_const hzero
        filter_upwards [hevent.filter_mono nhdsWithin_le_nhds] with t ht
        exact fun _ _ => ht.le
      · have htight : reward (quittingSingletonTerminal who) who =
            packet.boundary who :=
          le_antisymm hsoloLe (le_of_not_gt hsoloStrict)
        have hnoJet := hnoPositive who hwhoFirstEq hwhoSecondEq htight
        by_cases hlinearNeg :
            packet.twoOwnerOutsiderLinearCoefficient first second who < 0
        · have hevent :=
            packet.eventually_twoOwnerOutsiderGainRegression_neg_of_tight_of_linear_neg
              first second who hne hwhoFirstEq hwhoSecondEq htight hlinearNeg
          filter_upwards [hevent] with t ht
          exact fun _ _ => ht.le
        · have hlinearLe :
              packet.twoOwnerOutsiderLinearCoefficient first second who ≤ 0 := by
            exact le_of_not_gt fun hlinearPos => hnoJet (Or.inl hlinearPos)
          have hlinearEq :
              packet.twoOwnerOutsiderLinearCoefficient first second who = 0 :=
            le_antisymm hlinearLe (le_of_not_gt hlinearNeg)
          have hquadraticLe :
              packet.twoOwnerOutsiderQuadraticCoefficient first second who ≤ 0 := by
            exact le_of_not_gt fun hquadraticPos =>
              hnoJet (Or.inr ⟨hlinearEq, hquadraticPos⟩)
          filter_upwards [self_mem_nhdsWithin] with t ht
          have ht0 : 0 ≤ t := (show 0 < t from ht).le
          exact fun _ _ =>
            packet.twoOwnerOutsiderGainRegression_nonpos_of_tight_of_linear_zero_of_quadratic_nonpos
              first second who t hne hwhoFirstEq hwhoSecondEq htight ht0
                hlinearEq hquadraticLe

/-- Absence of a positive tight-outsider jet consumes every remaining local
Nash gate.  Artificial bounds centered around the packet boundary discharge
the auxiliary continuation floor and box, which do not occur in the exact
edge conclusion. -/
theorem eventually_exists_positiveChargeExactEdge_of_noPositiveTightOutsiderJet
    (packet : QuittingChargeTangentPacket reward)
    (upper : ℝ) (first second : ι)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first) (hsecond : 0 < packet.mass second)
    (houtsideMass : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst : quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond : quittingActivePairCompatibilityResidual packet second = 0)
    (hboundaryUpper : ∀ who, packet.boundary who ≤ upper)
    (hnoPositive : ∀ who, who ≠ first → who ≠ second →
      reward (quittingSingletonTerminal who) who = packet.boundary who →
      ¬ packet.HasPositiveTwoOwnerOutsiderJet first second who) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∃ root : ι → PMF Bool, ∃ continuation : Payoff ι,
        hazardOfRoot root = packet.twoOwnerHazardAt first second t ∧
        0 < quittingRootAbsorptionMass root ∧
        ∀ tailRoot : QuittingRootSimplex ι,
          IsQuittingNashBellmanEdge reward
            (packet.boundary, quittingFrozenRootLiftSimplex root)
            (continuation, tailRoot) := by
  let floor : Payoff ι := fun who => packet.boundary who - 1
  let enlargedUpper : ℝ := upper + 1
  have hfloor : ∀ who, floor who < packet.boundary who := by
    intro who
    dsimp [floor]
    linarith
  have hupper : ∀ who, packet.boundary who < enlargedUpper := by
    intro who
    dsimp [enlargedUpper]
    linarith [hboundaryUpper who]
  have hbox := packet.eventually_twoOwnerContinuationRegression_mem_strictBox
    floor enlargedUpper first second hne hfloor hupper
  have houtside :=
    packet.eventually_twoOwnerOutsiderGainRegression_nonpos_of_noPositiveTightJet
      first second hne hnoPositive
  have htlt : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 :=
    continuousAt_id.eventually_lt continuousAt_const zero_lt_one
  filter_upwards [hbox.filter_mono nhdsWithin_le_nhds, houtside,
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
  have hupperAt : ∀ who, continuation who ≤ enlargedUpper := by
    intro who
    change quittingTwoOwnerBellmanContinuation reward packet.boundary root who ≤
      enlargedUpper
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
    exact houtsideAt who hwhoFirst hwhoSecond
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
    exact packet.isQuittingNashBellmanEdge_twoOwnerAt floor enlargedUpper
      first second t ht0 htlt hne hfirst hsecond houtsideMass
      hcompatFirst hcompatSecond houtsideGain hfloorAt hupperAt tailRoot

/-- **Exact-edge/positive-jet dichotomy.**  For a compatible literal
 two-owner packet, all sufficiently small positive scales produce exact
 positive-charge Nash--Bellman edges unless a singleton-tight inactive owner
 has a positive lexicographic quadratic jet. -/
theorem positiveChargeExactEdge_or_positiveTightOutsiderJet
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
      ∃ who, who ≠ first ∧ who ≠ second ∧
        reward (quittingSingletonTerminal who) who = packet.boundary who ∧
        packet.HasPositiveTwoOwnerOutsiderJet first second who := by
  by_cases hpivot : ∃ who, who ≠ first ∧ who ≠ second ∧
      reward (quittingSingletonTerminal who) who = packet.boundary who ∧
      packet.HasPositiveTwoOwnerOutsiderJet first second who
  · exact Or.inr hpivot
  · apply Or.inl
    apply packet.eventually_exists_positiveChargeExactEdge_of_noPositiveTightOutsiderJet
      upper first second hne hfirst hsecond houtsideMass hcompatFirst
        hcompatSecond hboundaryUpper
    intro who hwhoFirst hwhoSecond htight hjet
    exact hpivot ⟨who, hwhoFirst, hwhoSecond, htight, hjet⟩

end QuittingChargeTangentPacket

end GameTheory
