/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerExactRoot

/-!
# Exact packet edges on the compatible two-owner ray

A compatible charge-tangent packet whose positive-mass support consists of
two owners selects the exact hazard ray

`p_first = t * mass first`,  `p_second = t * mass second`.

For every `0 < t < 1`, both hazards are automatically positive and subunit
and joint survival is positive. Compatibility kills both directed pair-join
effects, so the exact two-owner root module closes the active Bellman and
mixing rows without a second-order construction.

The remaining gates split sharply:

* active continuation is exactly
  `boundary_i - t * tangent_i / (1 - t * mass_j)`; hence a nonnegative
  tangent makes the upper gate automatic when the boundary is in the box,
  while a tight floor and positive tangent fail at every positive scale;
* an inactive owner's gain is the finite forced-Quit regression
  `sigmaValue(t) - boundary`. Strict singleton slack makes this negative for
  all sufficiently small scales. At equality, its pair and higher coalition
  coefficients remain an independent sign test;
* inactive continuation floor/box gates are not consequences of the packet
  equations. They remain explicit in the exact-edge theorem (strict boundary
  slack can be handled by ordinary continuity; tight gates need their own
  finite regression).

The capstone produces one exact Nash--Bellman edge only. It does not construct
a return, lasso, or cycle.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Finset Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingChargeTangentPacket

theorem twoOwner_mass_add
    (packet : QuittingChargeTangentPacket reward) (first second : ι)
    (hne : first ≠ second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0) :
    packet.mass first + packet.mass second = 1 := by
  calc
    packet.mass first + packet.mass second =
        packet.mass second + packet.mass first := add_comm _ _
    _ = (∑ owner ∈ Finset.univ.erase first, packet.mass owner) +
        packet.mass first := by
      congr 1
      symm
      apply Finset.sum_eq_single second
      · intro owner howner hownerSecond
        exact houtside owner (Finset.mem_erase.mp howner).1 hownerSecond
      · intro hsecond
        exact (hsecond (by simp [hne.symm])).elim
    _ = ∑ owner, packet.mass owner :=
      Finset.sum_erase_add _ _ (Finset.mem_univ first)
    _ = 1 := packet.mass_sum

theorem twoOwner_mass_le_one
    (packet : QuittingChargeTangentPacket reward) (owner : ι) :
    packet.mass owner ≤ 1 := by
  rw [← packet.mass_sum]
  exact Finset.single_le_sum (fun other _ => packet.mass_nonneg other)
    (Finset.mem_univ owner)

/-- The exact two-owner hazard ray selected by a tangent packet. -/
def twoOwnerHazardAt
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) : ι → ℝ :=
  quittingTwoOwnerHazard first second
    (t * packet.mass first) (t * packet.mass second)

theorem twoOwnerHazardAt_nonneg
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht : 0 ≤ t) :
    ∀ owner, 0 ≤ packet.twoOwnerHazardAt first second t owner := by
  intro owner
  by_cases hfirst : owner = first
  · subst owner
    simp [twoOwnerHazardAt, mul_nonneg ht (packet.mass_nonneg first)]
  · by_cases hsecond : owner = second
    · subst owner
      rw [twoOwnerHazardAt,
        quittingTwoOwnerHazard_second first second _ _ (Ne.symm hfirst)]
      exact mul_nonneg ht (packet.mass_nonneg second)
    · simp [twoOwnerHazardAt,
        quittingTwoOwnerHazard_eq_zero_of_ne first second owner _ _
          hfirst hsecond]

theorem twoOwnerHazardAt_le_one
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht1 : t ≤ 1) :
    ∀ owner, packet.twoOwnerHazardAt first second t owner ≤ 1 := by
  intro owner
  by_cases hfirst : owner = first
  · subst owner
    simp only [twoOwnerHazardAt, quittingTwoOwnerHazard_first]
    exact mul_le_one₀ ht1 (packet.mass_nonneg first)
      (packet.twoOwner_mass_le_one first)
  · by_cases hsecond : owner = second
    · subst owner
      simp only [twoOwnerHazardAt]
      rw [quittingTwoOwnerHazard_second first second _ _ (Ne.symm hfirst)]
      exact mul_le_one₀ ht1 (packet.mass_nonneg second)
        (packet.twoOwner_mass_le_one second)
    · rw [twoOwnerHazardAt,
        quittingTwoOwnerHazard_eq_zero_of_ne first second owner _ _ hfirst hsecond]
      norm_num

/-- The product root on the packet's exact two-owner hazard ray. -/
def twoOwnerRootAt
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ι → PMF Bool :=
  rootOfHazard (packet.twoOwnerHazardAt first second t)
    (packet.twoOwnerHazardAt_nonneg first second t ht0)
    (packet.twoOwnerHazardAt_le_one first second t ht1)

@[simp] theorem hazardOfRoot_twoOwnerRootAt
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    hazardOfRoot (packet.twoOwnerRootAt first second t ht0 ht1) =
      packet.twoOwnerHazardAt first second t := by
  exact hazardOfRoot_rootOfHazard _ _ _

theorem twoOwnerHazardAt_active_pos_lt_one
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (hne : first ≠ second)
    (hfirst : 0 < packet.mass first) (hsecond : 0 < packet.mass second)
    (ht0 : 0 < t) (ht1 : t < 1) :
    0 < packet.twoOwnerHazardAt first second t first ∧
      packet.twoOwnerHazardAt first second t first < 1 ∧
    0 < packet.twoOwnerHazardAt first second t second ∧
      packet.twoOwnerHazardAt first second t second < 1 := by
  simp only [twoOwnerHazardAt, quittingTwoOwnerHazard_first,
    quittingTwoOwnerHazard_second first second _ _ hne]
  have hfirst_le := packet.twoOwner_mass_le_one first
  have hsecond_le := packet.twoOwner_mass_le_one second
  constructor
  · positivity
  constructor
  · nlinarith [packet.mass_nonneg first]
  constructor
  · positivity
  · nlinarith [packet.mass_nonneg second]

/-- On an exact two-owner support, the first tangent coordinate is the other
owner's mass times its singleton displacement from the boundary. -/
theorem tangent_eq_second_mass_mul_singleton_sub_boundary
    (packet : QuittingChargeTangentPacket reward) (first second : ι)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0) :
    packet.tangent first = packet.mass second *
      (reward (quittingSingletonTerminal second) first -
        packet.boundary first) := by
  have hmixture : quittingSingletonMixture reward packet.mass first =
      packet.mass first * reward (quittingSingletonTerminal first) first +
        packet.mass second * reward (quittingSingletonTerminal second) first := by
    unfold quittingSingletonMixture
    calc
      (∑ owner, packet.mass owner *
          reward (quittingSingletonTerminal owner) first) =
          (∑ owner ∈ Finset.univ.erase first, packet.mass owner *
            reward (quittingSingletonTerminal owner) first) +
            packet.mass first *
              reward (quittingSingletonTerminal first) first := by
        symm
        exact Finset.sum_erase_add _ _ (Finset.mem_univ first)
      _ = packet.mass second *
            reward (quittingSingletonTerminal second) first +
          packet.mass first *
            reward (quittingSingletonTerminal first) first := by
        congr 1
        apply Finset.sum_eq_single second
        · intro owner howner hownerSecond
          rw [houtside owner (Finset.mem_erase.mp howner).1 hownerSecond]
          simp
        · intro hsecond
          exact (hsecond (by simp [hne.symm])).elim
      _ = _ := add_comm _ _
  rw [packet.tangent_eq first, hmixture,
    packet.positive_mass_pins_boundary first hfirst]
  have hmass := packet.twoOwner_mass_add first second hne houtside
  have hmfirst : packet.mass first = 1 - packet.mass second := by linarith
  rw [hmfirst]
  ring

/-- Symmetric tangent formula for the second owner. -/
theorem tangent_eq_first_mass_mul_singleton_sub_boundary
    (packet : QuittingChargeTangentPacket reward) (first second : ι)
    (hne : first ≠ second)
    (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0) :
    packet.tangent second = packet.mass first *
      (reward (quittingSingletonTerminal first) second -
        packet.boundary second) := by
  exact packet.tangent_eq_second_mass_mul_singleton_sub_boundary
    second first hne.symm hsecond
      (fun owner hownerSecond hownerFirst =>
        houtside owner hownerFirst hownerSecond)

/-- Exact active continuation regression along the packet hazard ray. -/
theorem twoOwnerBellmanContinuationAt_active_formula
    (packet : QuittingChargeTangentPacket reward) (first second : ι)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first)
    (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst : quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond : quittingActivePairCompatibilityResidual packet second = 0)
    (hfirst_lt : t * packet.mass first < 1)
    (hsecond_lt : t * packet.mass second < 1)
    (hsurvival : quittingStationaryContinueMass
      (packet.twoOwnerRootAt first second t ht0 ht1) ≠ 0) :
    quittingTwoOwnerBellmanContinuation reward packet.boundary
        (packet.twoOwnerRootAt first second t ht0 ht1) first =
      packet.boundary first -
        t * packet.tangent first / (1 - t * packet.mass second) ∧
    quittingTwoOwnerBellmanContinuation reward packet.boundary
        (packet.twoOwnerRootAt first second t ht0 ht1) second =
      packet.boundary second -
        t * packet.tangent second / (1 - t * packet.mass first) := by
  have hjoinFirst :=
    packet.pairJoinEffect_eq_zero_of_twoOwnerSupport_compatible_first
      first second hne hfirst hsecond houtside hcompatFirst
  have hjoinSecond :=
    packet.pairJoinEffect_eq_zero_of_twoOwnerSupport_compatible_second
      first second hne hfirst hsecond houtside hcompatSecond
  have hformula := twoOwnerBellmanContinuation_active_formula
    (reward := reward) packet.boundary
      (packet.twoOwnerRootAt first second t ht0 ht1) first second
      (t * packet.mass first) (t * packet.mass second) hne
      (packet.hazardOfRoot_twoOwnerRootAt first second t ht0 ht1)
      hfirst_lt hsecond_lt hsurvival
      (packet.positive_mass_pins_boundary first hfirst)
      (packet.positive_mass_pins_boundary second hsecond)
      hjoinFirst hjoinSecond
  rw [packet.tangent_eq_second_mass_mul_singleton_sub_boundary
      first second hne hfirst houtside,
    packet.tangent_eq_first_mass_mul_singleton_sub_boundary
      first second hne hsecond houtside]
  constructor
  · rw [hformula.1]
    have hdenom : 1 - t * packet.mass second ≠ 0 := by linarith
    field_simp [hdenom]
    ring
  · rw [hformula.2]
    have hdenom : 1 - t * packet.mass first ≠ 0 := by linarith
    field_simp [hdenom]
    ring

/-- The first active floor gate is exactly one scalar regression inequality. -/
theorem floor_le_twoOwnerBellmanContinuationAt_first_iff
    (packet : QuittingChargeTangentPacket reward) (floor : Payoff ι)
    (first second : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first) (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst : quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond : quittingActivePairCompatibilityResidual packet second = 0)
    (hfirst_lt : t * packet.mass first < 1)
    (hsecond_lt : t * packet.mass second < 1)
    (hsurvival : quittingStationaryContinueMass
      (packet.twoOwnerRootAt first second t ht0 ht1) ≠ 0) :
    floor first ≤ quittingTwoOwnerBellmanContinuation reward packet.boundary
        (packet.twoOwnerRootAt first second t ht0 ht1) first ↔
      t * packet.tangent first ≤
        (packet.boundary first - floor first) *
          (1 - t * packet.mass second) := by
  rw [(packet.twoOwnerBellmanContinuationAt_active_formula first second t ht0
    ht1 hne hfirst hsecond houtside hcompatFirst hcompatSecond hfirst_lt
    hsecond_lt hsurvival).1]
  have hdenom : 0 < 1 - t * packet.mass second := by linarith
  constructor
  · intro hgate
    apply (div_le_iff₀ hdenom).mp
    linarith
  · intro hregression
    have hdiv := (div_le_iff₀ hdenom).mpr hregression
    linarith

/-- Strict active floor slack makes the exact scalar floor regression hold at
all sufficiently small scales. No tangent sign is needed for this local
statement. -/
theorem eventually_twoOwnerActiveFloorRegression_first_of_lt
    (packet : QuittingChargeTangentPacket reward) (floor : Payoff ι)
    (first second : ι)
    (hstrict : floor first < packet.boundary first) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      t * packet.tangent first ≤
        (packet.boundary first - floor first) *
          (1 - t * packet.mass second) := by
  have hleft : Continuous (fun t : ℝ => t * packet.tangent first) := by
    fun_prop
  have hright : Continuous (fun t : ℝ =>
      (packet.boundary first - floor first) *
        (1 - t * packet.mass second)) := by
    fun_prop
  have hzero : (0 : ℝ) * packet.tangent first <
      (packet.boundary first - floor first) *
        (1 - (0 : ℝ) * packet.mass second) := by
    simpa using sub_pos.mpr hstrict
  have hevent := hleft.continuousAt.eventually_lt hright.continuousAt hzero
  filter_upwards [hevent] with t ht
  exact ht.le

/-- A tight active floor and a positive tangent are incompatible with every
positive point of the exact two-owner ray. -/
theorem not_floor_le_twoOwnerBellmanContinuationAt_first_of_tangent_pos
    (packet : QuittingChargeTangentPacket reward) (floor : Payoff ι)
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
    (htight : floor first = packet.boundary first) :
    ¬ floor first ≤ quittingTwoOwnerBellmanContinuation reward packet.boundary
        (packet.twoOwnerRootAt first second t ht0.le ht1) first := by
  rw [packet.floor_le_twoOwnerBellmanContinuationAt_first_iff floor first second
    t ht0.le ht1 hne hfirst hsecond houtside hcompatFirst hcompatSecond
    hfirst_lt hsecond_lt hsurvival, htight]
  simp only [sub_self, zero_mul]
  exact not_le_of_gt (mul_pos ht0 htangent)

/-- Nonnegative active tangent makes the continuation move downward, so an
upper box already containing the boundary is automatic. -/
theorem twoOwnerBellmanContinuationAt_first_le_upper
    (packet : QuittingChargeTangentPacket reward) (upper : ℝ)
    (first second : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first) (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst : quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond : quittingActivePairCompatibilityResidual packet second = 0)
    (hfirst_lt : t * packet.mass first < 1)
    (hsecond_lt : t * packet.mass second < 1)
    (hsurvival : quittingStationaryContinueMass
      (packet.twoOwnerRootAt first second t ht0 ht1) ≠ 0)
    (htangent : 0 ≤ packet.tangent first)
    (hboundary : packet.boundary first ≤ upper) :
    quittingTwoOwnerBellmanContinuation reward packet.boundary
        (packet.twoOwnerRootAt first second t ht0 ht1) first ≤ upper := by
  rw [(packet.twoOwnerBellmanContinuationAt_active_formula first second t ht0
    ht1 hne hfirst hsecond houtside hcompatFirst hcompatSecond hfirst_lt
    hsecond_lt hsurvival).1]
  have hdenom : 0 < 1 - t * packet.mass second := by linarith
  have hquotient : 0 ≤ t * packet.tangent first /
      (1 - t * packet.mass second) := div_nonneg (mul_nonneg ht0 htangent) hdenom.le
  linarith

/-- The finite outsider regression along the two-owner packet ray. It is the
forced-Quit polynomial minus the fixed boundary coordinate. -/
def twoOwnerOutsiderGainRegression
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (who : ι) : ℝ :=
  sigmaValue (weightOfReward reward)
      (packet.twoOwnerHazardAt first second t) who - packet.boundary who

/-- Bellman elimination makes every inactive owner's Continue endpoint equal
the boundary, so its exact Nash gate is precisely the finite regression. -/
theorem gainValue_twoOwnerBellmanContinuationAt_outside_eq_regression
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hwhoFirst : who ≠ first) (hwhoSecond : who ≠ second)
    (hsurvival : quittingStationaryContinueMass
      (packet.twoOwnerRootAt first second t ht0 ht1) ≠ 0) :
    gainValue (weightOfReward reward)
        (packet.twoOwnerHazardAt first second t) who
        (quittingTwoOwnerBellmanContinuation reward packet.boundary
          (packet.twoOwnerRootAt first second t ht0 ht1) who) =
      packet.twoOwnerOutsiderGainRegression first second t who := by
  let root := packet.twoOwnerRootAt first second t ht0 ht1
  let continuation :=
    quittingTwoOwnerBellmanContinuation reward packet.boundary root
  have hbellman : packet.boundary =
      quittingRootSuccessorPayoff reward continuation root :=
    boundary_eq_successor_twoOwnerBellmanContinuation
      (reward := reward) packet.boundary root hsurvival
  have htrue : (root who true).toReal = 0 := by
    change hazardOfRoot root who = 0
    rw [packet.hazardOfRoot_twoOwnerRootAt first second t ht0 ht1]
    exact quittingTwoOwnerHazard_eq_zero_of_ne first second who
      (t * packet.mass first) (t * packet.mass second) hwhoFirst hwhoSecond
  have hfalse : (root who false).toReal = 1 := by
    have hprob := quittingRoot_continueProbability_add_quitProbability root who
    linarith
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix
    reward continuation root who
  rw [← congrFun hbellman who, htrue, hfalse] at hmix
  have hcontinue : quittingRootContinuePayoff reward continuation root who =
      packet.boundary who := by simpa using hmix.symm
  unfold twoOwnerOutsiderGainRegression
  rw [← packet.hazardOfRoot_twoOwnerRootAt first second t ht0 ht1]
  change gainValue (weightOfReward reward) (hazardOfRoot root) who
      (continuation who) =
    sigmaValue (weightOfReward reward) (hazardOfRoot root) who -
      packet.boundary who
  rw [← quittingRootEndpointDifference_eq_gainValue]
  unfold quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_eq_sigmaValue, hcontinue]

/-- At the all-Continue endpoint, the outsider regression is exactly the
singleton solo slack already present in the packet. -/
theorem twoOwnerOutsiderGainRegression_zero
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι) :
    packet.twoOwnerOutsiderGainRegression first second 0 who =
      reward (quittingSingletonTerminal who) who - packet.boundary who := by
  have hsigmaZero : sigmaValue (weightOfReward reward) (fun _ : ι => 0) who =
      reward (quittingSingletonTerminal who) who := by
    let term : Finset ι → ℝ := fun J =>
      (∏ j ∈ J, (0 : ℝ)) *
        (∏ j ∈ Finset.univ.erase who \ J, (1 - (0 : ℝ))) *
          weightOfReward reward (insert who J) who
    unfold sigmaValue
    change (∑ J ∈ (Finset.univ.erase who).powerset, term J) = _
    have hemptyValue : term ∅ =
        reward (quittingSingletonTerminal who) who := by
      simp [term, weightOfReward, quittingSingletonTerminal]
    rw [← hemptyValue]
    apply Finset.sum_eq_single (∅ : Finset ι)
    · intro J hJ hJempty
      have hnonempty : J.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hJempty
      obtain ⟨owner, howner⟩ := hnonempty
      have hprod : (∏ j ∈ J, (0 : ℝ)) = 0 :=
        Finset.prod_eq_zero howner rfl
      change (∏ j ∈ J, (0 : ℝ)) *
        (∏ j ∈ Finset.univ.erase who \ J, (1 - (0 : ℝ))) *
          weightOfReward reward (insert who J) who = 0
      rw [hprod]
      ring
    · intro hempty
      exact (hempty (Finset.empty_mem_powerset _)).elim
  unfold twoOwnerOutsiderGainRegression twoOwnerHazardAt
  have hzero : quittingTwoOwnerHazard first second
      (0 * packet.mass first) (0 * packet.mass second) = fun _ : ι => 0 := by
    funext owner
    simp [quittingTwoOwnerHazard, quittingTwoOwnerLeadingVariation]
  rw [hzero, hsigmaZero]

/-- The outsider regression is a finite polynomial in the scale. -/
theorem continuous_twoOwnerOutsiderGainRegression
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι) :
    Continuous (fun t : ℝ =>
      packet.twoOwnerOutsiderGainRegression first second t who) := by
  have hcoordinate : ∀ owner, Continuous (fun t : ℝ =>
      packet.twoOwnerHazardAt first second t owner) := by
    intro owner
    by_cases hfirst : owner = first
    · subst owner
      simp only [twoOwnerHazardAt, quittingTwoOwnerHazard_first]
      fun_prop
    · by_cases hsecond : owner = second
      · subst owner
        have hne : first ≠ second := Ne.symm hfirst
        simp only [twoOwnerHazardAt,
          quittingTwoOwnerHazard_second first second _ _ hne]
        fun_prop
      · have hzero : (fun t : ℝ =>
            packet.twoOwnerHazardAt first second t owner) = fun _ => 0 := by
          funext t
          exact quittingTwoOwnerHazard_eq_zero_of_ne first second owner
            (t * packet.mass first) (t * packet.mass second) hfirst hsecond
        rw [hzero]
        fun_prop
  unfold twoOwnerOutsiderGainRegression sigmaValue twoOwnerHazardAt
  apply Continuous.sub
  · apply continuous_finsetSum
    intro J hJ
    apply Continuous.mul
    · apply Continuous.mul
      · apply continuous_finsetProd
        intro owner howner
        exact hcoordinate owner
      · apply continuous_finsetProd
        intro owner howner
        exact continuous_const.sub (hcoordinate owner)
    · fun_prop
  · fun_prop

/-- Strict singleton outsider slack persists for every outsider at all
sufficiently small scales. Tight singleton rows are not covered: their
linear/quadratic regression coefficients decide the sign. -/
theorem eventually_twoOwnerOutsiderGainRegression_neg_of_solo_lt_boundary
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι)
    (hstrict : ∀ who, who ≠ first → who ≠ second →
      reward (quittingSingletonTerminal who) who < packet.boundary who) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ who, who ≠ first → who ≠ second →
      packet.twoOwnerOutsiderGainRegression first second t who < 0 := by
  rw [Filter.eventually_all]
  intro who
  by_cases hwhoFirst : who = first
  · exact Filter.Eventually.of_forall fun _ hneFirst _ =>
      (hneFirst hwhoFirst).elim
  · by_cases hwhoSecond : who = second
    · exact Filter.Eventually.of_forall fun _ _ hneSecond =>
        (hneSecond hwhoSecond).elim
    · have hzero : packet.twoOwnerOutsiderGainRegression first second 0 who < 0 := by
        rw [packet.twoOwnerOutsiderGainRegression_zero first second who]
        exact sub_neg.mpr (hstrict who hwhoFirst hwhoSecond)
      have hevent : ∀ᶠ t in 𝓝 (0 : ℝ),
          packet.twoOwnerOutsiderGainRegression first second t who < 0 :=
        (packet.continuous_twoOwnerOutsiderGainRegression
          first second who).continuousAt.eventually_lt continuousAt_const hzero
      filter_upwards [hevent] with t ht
      exact fun _ _ => ht

/-- A compatible exact-two packet produces one exact edge at every supplied
positive subunit scale once the outsider and continuation admissibility gates
are verified. -/
theorem isQuittingNashBellmanEdge_twoOwnerAt
    (packet : QuittingChargeTangentPacket reward)
    (floor : Payoff ι) (upper : ℝ) (first second : ι)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first)
    (hsecond : 0 < packet.mass second)
    (houtsideMass : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst : quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond : quittingActivePairCompatibilityResidual packet second = 0)
    (houtsideGain : ∀ who, who ≠ first → who ≠ second →
      gainValue (weightOfReward reward)
        (packet.twoOwnerHazardAt first second t) who
        (quittingTwoOwnerBellmanContinuation reward packet.boundary
          (packet.twoOwnerRootAt first second t ht0.le ht1.le) who) ≤ 0)
    (hfloor : ∀ who, floor who ≤
      quittingTwoOwnerBellmanContinuation reward packet.boundary
        (packet.twoOwnerRootAt first second t ht0.le ht1.le) who)
    (hupper : ∀ who,
      quittingTwoOwnerBellmanContinuation reward packet.boundary
          (packet.twoOwnerRootAt first second t ht0.le ht1.le) who ≤ upper)
    (tailRoot : QuittingRootSimplex ι) :
    IsQuittingNashBellmanEdge reward
      (packet.boundary, quittingFrozenRootLiftSimplex
        (packet.twoOwnerRootAt first second t ht0.le ht1.le))
      (quittingTwoOwnerBellmanContinuation reward packet.boundary
        (packet.twoOwnerRootAt first second t ht0.le ht1.le), tailRoot) := by
  have hsurvival : quittingStationaryContinueMass
      (packet.twoOwnerRootAt first second t ht0.le ht1.le) ≠ 0 := by
    unfold twoOwnerRootAt
    rw [quittingStationaryContinueMass_rootOfHazard,
      twoOwnerHazardAt,
      continueMass_twoOwner first second
        (t * packet.mass first) (t * packet.mass second) hne]
    have hf : 0 < 1 - t * packet.mass first := by
      nlinarith [packet.mass_nonneg first, packet.twoOwner_mass_le_one first]
    have hs : 0 < 1 - t * packet.mass second := by
      nlinarith [packet.mass_nonneg second, packet.twoOwner_mass_le_one second]
    exact mul_ne_zero hf.ne' hs.ne'
  have hfirstPos : 0 < t * packet.mass first := mul_pos ht0 hfirst
  have hsecondPos : 0 < t * packet.mass second := mul_pos ht0 hsecond
  have hfirstLt : t * packet.mass first < 1 := by
    nlinarith [packet.mass_nonneg first, packet.twoOwner_mass_le_one first]
  have hsecondLt : t * packet.mass second < 1 := by
    nlinarith [packet.mass_nonneg second, packet.twoOwner_mass_le_one second]
  apply isQuittingNashBellmanEdge_twoOwner_of_pairJoin_zero
    packet.boundary floor upper
      (packet.twoOwnerRootAt first second t ht0.le ht1.le)
      first second (t * packet.mass first) (t * packet.mass second) hne
      (packet.hazardOfRoot_twoOwnerRootAt first second t ht0.le ht1.le)
      hfirstPos hfirstLt hsecondPos hsecondLt hsurvival
      (packet.positive_mass_pins_boundary first hfirst)
      (packet.positive_mass_pins_boundary second hsecond)
  · exact packet.pairJoinEffect_eq_zero_of_twoOwnerSupport_compatible_first
      first second hne hfirst hsecond houtsideMass hcompatFirst
  · exact packet.pairJoinEffect_eq_zero_of_twoOwnerSupport_compatible_second
      first second hne hfirst hsecond houtsideMass hcompatSecond
  · simpa using houtsideGain
  · exact hfloor
  · exact hupper

end QuittingChargeTangentPacket

end GameTheory
