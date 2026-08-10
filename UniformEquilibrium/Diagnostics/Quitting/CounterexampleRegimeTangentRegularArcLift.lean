/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentMixingCompatibility
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentAnchoredProjectiveLCP
import UniformEquilibrium.Quitting.Projective.AnalyticPacket
import Math.AnalyticImplicitFunction

/-!
# Regular first-blow-up lifting of charge tangent packets

The raw Nash--Bellman variety is necessarily singular at the all-Continue
root: its active mixing equations lose their rate dependence there.  The
correct regular object is the first radial blow-up

`hazard = t * leading`,

`continuation = boundary + t * drift`.

This module removes the common factor `t` exactly from both equation classes.
The resulting Bellman residual retains every quitting coalition, and the
mixing residual retains every pair and higher opponent coalition.  At the
exceptional divisor `t = 0`, a charge tangent packet solves all Bellman rows
with

`leading = scale * mass`, `drift = -scale * tangent`.

The remaining active equations are the pair compatibilities

`tangent_i + Σ_{j ≠ i} mass_j * (r_i({i,j}) - r_i({j})) = 0`.

On active support this is equivalently the clean pair-join condition

`Σ_{j ≠ i} mass_j * (r_i({i,j}) - r_i({i})) = 0`.

For a declared support, the full finite equality system also sets every
off-support leading coefficient to zero.  It is a polynomial map.  If its
derivative at the packet point is surjective and its kernel contains a
direction with positive radial coordinate, the existing analytic implicit-
function theorem constructs a positive analytic arc.  Strict physical signs
may be carried in an arbitrary open neighborhood.  A separate decoder proves
that every physical zero on this arc is an exact undiscounted Nash--Bellman
root.

This is an abstract regular-lift interface.  For the literal ungauged chart
at a compatible packet, `CounterexampleRegimeTangentSupportTransversality`
proves that the projective scale line is a nonzero radial-zero kernel and
that derivative surjectivity is incompatible with any positive-radial kernel
direction.  A projective gauge or radial-parameter formulation is therefore
needed before this interface can produce an arc.  No lifting, Puiseux
resolution, or arbitrary-player conclusion is asserted here.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Finset Filter Set Topology Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

omit [Fintype ι] in
/-- Nonempty subsets of a fixed finite carrier split into its singleton
subsets and its subsets of cardinality at least two. -/
theorem sum_powerset_erase_empty_eq_sum_singleton_add_sum_card_ge_two
    (base : Finset ι) (f : Finset ι → ℝ) :
    ∑ S ∈ base.powerset.erase (∅ : Finset ι), f S =
      (∑ owner ∈ base, f {owner}) +
        ∑ S ∈ (base.powerset.filter fun S => 2 ≤ S.card), f S := by
  let nonempty := base.powerset.erase (∅ : Finset ι)
  let multiple := nonempty.filter fun S => 2 ≤ S.card
  let single := nonempty.filter fun S => ¬2 ≤ S.card
  have hsplit :
      (∑ S ∈ multiple, f S) + (∑ S ∈ single, f S) =
        ∑ S ∈ nonempty, f S := by
    simpa [multiple, single] using
      (Finset.sum_filter_add_sum_filter_not nonempty
        (fun S : Finset ι => 2 ≤ S.card) f)
  have hmultiple :
      multiple = base.powerset.filter (fun S => 2 ≤ S.card) := by
    ext S
    simp only [multiple, nonempty, Finset.mem_filter, Finset.mem_erase,
      Finset.mem_powerset]
    constructor
    · exact fun h => ⟨h.1.2, h.2⟩
    · rintro ⟨hsubset, hcard⟩
      exact ⟨⟨fun hzero => by simp [hzero] at hcard, hsubset⟩, hcard⟩
  have hsingle :
      single = base.image (fun owner : ι => ({owner} : Finset ι)) := by
    ext S
    simp only [single, nonempty, Finset.mem_filter, Finset.mem_erase,
      Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨⟨hne, hsubset⟩, hsmall⟩
      have hpos : 0 < S.card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hne)
      have hcard : S.card = 1 := by omega
      obtain ⟨owner, howner⟩ := Finset.card_eq_one.mp hcard
      refine ⟨owner, ?_, howner.symm⟩
      exact hsubset (by rw [howner]; simp)
    · rintro ⟨owner, howner, rfl⟩
      simp [howner]
  have hsingleSum :
      ∑ S ∈ single, f S = ∑ owner ∈ base, f {owner} := by
    rw [hsingle, Finset.sum_image]
    intro first _ second _ heq
    simpa using heq
  rw [← hsplit, hmultiple, hsingleSum]
  ring

/-- Hazards on a first blow-up chart: `x = t a`. -/
def quittingBlowupHazard (t : ℝ) (a : ι → ℝ) : ι → ℝ :=
  fun owner ↦ t * a owner

/-- The coalition mass with its common radial factor `t` removed.  This is
only used for nonempty coalitions. -/
def quittingBlowupCoalitionSlope (t : ℝ) (a : ι → ℝ)
    (S : Finset ι) : ℝ :=
  t ^ (S.card - 1) * (∏ owner ∈ S, a owner) *
    ∏ owner ∈ Finset.univ \ S, (1 - t * a owner)

theorem t_mul_quittingBlowupCoalitionSlope
    (t : ℝ) (a : ι → ℝ) (S : Finset ι) (hS : S.Nonempty) :
    t * quittingBlowupCoalitionSlope t a S =
      coalitionMass (quittingBlowupHazard t a) S := by
  have hcard : 1 ≤ S.card := Finset.one_le_card.mpr hS
  have hpow : t * t ^ (S.card - 1) = t ^ S.card := by
    calc
      t * t ^ (S.card - 1) = t ^ 1 * t ^ (S.card - 1) := by simp
      _ = t ^ (1 + (S.card - 1)) := by rw [← pow_add]
      _ = t ^ S.card := by congr 1; omega
  unfold quittingBlowupCoalitionSlope coalitionMass quittingBlowupHazard
  rw [Finset.compl_eq_univ_sdiff]
  have hprod : (∏ owner ∈ S, t * a owner) =
      t ^ S.card * ∏ owner ∈ S, a owner := by
    simp_rw [Finset.prod_mul_distrib]
    simp
  rw [hprod]
  calc
    t * ((t ^ (S.card - 1) * ∏ owner ∈ S, a owner) *
        ∏ owner ∈ Finset.univ \ S, (1 - t * a owner)) =
      (t * t ^ (S.card - 1)) * (∏ owner ∈ S, a owner) *
        ∏ owner ∈ Finset.univ \ S, (1 - t * a owner) := by ring
    _ = (t ^ S.card * ∏ owner ∈ S, a owner) *
        ∏ owner ∈ Finset.univ \ S, (1 - t * a owner) := by rw [hpow]

/-- Bellman consistency on the first blow-up chart after removing the common
radial factor.  Collision and all higher coalitions remain in the finite sum. -/
def quittingBellmanBlowupResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (boundary : Payoff ι) (t : ℝ) (a u : ι → ℝ) (who : ι) : ℝ :=
  continueMass (quittingBlowupHazard t a) * u who +
    ∑ S ∈ Finset.univ.erase (∅ : Finset ι),
      quittingBlowupCoalitionSlope t a S *
        (weightOfReward reward S who - boundary who)

/-- Exact factorization of the undiscounted Bellman equation on the blow-up
chart. -/
theorem t_mul_quittingBellmanBlowupResidual
    (boundary : Payoff ι) (t : ℝ) (a u : ι → ℝ) (who : ι) :
    t * quittingBellmanBlowupResidual reward boundary t a u who =
      continueMass (quittingBlowupHazard t a) *
          (boundary who + t * u who) +
        (∑ S ∈ Finset.univ.erase (∅ : Finset ι),
          coalitionMass (quittingBlowupHazard t a) S *
            weightOfReward reward S who) - boundary who := by
  unfold quittingBellmanBlowupResidual
  rw [mul_add, Finset.mul_sum]
  have hslope : ∀ S ∈ Finset.univ.erase (∅ : Finset ι),
      t * (quittingBlowupCoalitionSlope t a S *
        (weightOfReward reward S who - boundary who)) =
      coalitionMass (quittingBlowupHazard t a) S *
        (weightOfReward reward S who - boundary who) := by
    intro S hS
    rw [← mul_assoc, t_mul_quittingBlowupCoalitionSlope]
    exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1
  have hsum :
      (∑ S ∈ Finset.univ.erase (∅ : Finset ι),
        t * (quittingBlowupCoalitionSlope t a S *
          (weightOfReward reward S who - boundary who))) =
      ∑ S ∈ Finset.univ.erase (∅ : Finset ι),
        coalitionMass (quittingBlowupHazard t a) S *
          (weightOfReward reward S who - boundary who) :=
    Finset.sum_congr rfl hslope
  rw [hsum]
  have hmass := sum_coalitionMass_nonempty (quittingBlowupHazard t a)
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass]
  ring

/-- The first-order singleton Bellman residual at the exceptional divisor. -/
def quittingBellmanFirstOrderResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (boundary : Payoff ι) (a u : ι → ℝ) (who : ι) : ℝ :=
  u who + ∑ owner, a owner *
    (reward (quittingSingletonTerminal owner) who - boundary who)

theorem quittingBellmanBlowupResidual_zero
    (boundary : Payoff ι) (a u : ι → ℝ) (who : ι) :
    quittingBellmanBlowupResidual reward boundary 0 a u who =
      quittingBellmanFirstOrderResidual reward boundary a u who := by
  rw [quittingBellmanBlowupResidual,
    sum_nonemptyFinset_eq_sum_singleton_add_sum_card_ge_two]
  have hmultiple :
      (∑ S ∈ (Finset.univ.filter fun S : Finset ι => 2 ≤ S.card),
        quittingBlowupCoalitionSlope 0 a S *
          (weightOfReward reward S who - boundary who)) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    have hcard : 0 < S.card - 1 := by
      have := (Finset.mem_filter.mp hS).2
      omega
    simp [quittingBlowupCoalitionSlope, zero_pow hcard.ne']
  rw [hmultiple, add_zero]
  simp [quittingBlowupHazard, continueMass,
    quittingBlowupCoalitionSlope, quittingBellmanFirstOrderResidual,
    weightOfReward_singleton]

/-- Opponent-coalition mass with the common radial factor removed. -/
def quittingBlowupOpponentCoalitionSlope (t : ℝ) (a : ι → ℝ)
    (who : ι) (J : Finset ι) : ℝ :=
  t ^ (J.card - 1) * (∏ owner ∈ J, a owner) *
    ∏ owner ∈ Finset.univ.erase who \ J, (1 - t * a owner)

theorem t_mul_quittingBlowupOpponentCoalitionSlope
    (t : ℝ) (a : ι → ℝ) (who : ι) (J : Finset ι)
    (hJ : J.Nonempty) :
    t * quittingBlowupOpponentCoalitionSlope t a who J =
      (∏ owner ∈ J, quittingBlowupHazard t a owner) *
        ∏ owner ∈ Finset.univ.erase who \ J,
          (1 - quittingBlowupHazard t a owner) := by
  have hcard : 1 ≤ J.card := Finset.one_le_card.mpr hJ
  have hpow : t * t ^ (J.card - 1) = t ^ J.card := by
    calc
      t * t ^ (J.card - 1) = t ^ 1 * t ^ (J.card - 1) := by simp
      _ = t ^ (1 + (J.card - 1)) := by rw [← pow_add]
      _ = t ^ J.card := by congr 1; omega
  unfold quittingBlowupOpponentCoalitionSlope quittingBlowupHazard
  have hprod : (∏ owner ∈ J, t * a owner) =
      t ^ J.card * ∏ owner ∈ J, a owner := by
    simp_rw [Finset.prod_mul_distrib]
    simp
  rw [hprod]
  calc
    t * ((t ^ (J.card - 1) * ∏ owner ∈ J, a owner) *
        ∏ owner ∈ Finset.univ.erase who \ J, (1 - t * a owner)) =
      (t * t ^ (J.card - 1)) * (∏ owner ∈ J, a owner) *
        ∏ owner ∈ Finset.univ.erase who \ J, (1 - t * a owner) := by ring
    _ = (t ^ J.card * ∏ owner ∈ J, a owner) *
        ∏ owner ∈ Finset.univ.erase who \ J, (1 - t * a owner) := by rw [hpow]

/-- Active mixing on the first blow-up chart after removing its common radial
factor.  Every pair and higher opponent coalition remains explicit. -/
def quittingMixingBlowupResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (t : ℝ) (a u : ι → ℝ) (who : ι) : ℝ :=
  (∑ J ∈ (Finset.univ.erase who).powerset.erase (∅ : Finset ι),
    quittingBlowupOpponentCoalitionSlope t a who J *
      (weightOfReward reward (insert who J) who -
        weightOfReward reward J who)) -
    continueMassExcl (quittingBlowupHazard t a) who * u who

/-- Pair-level compatibility left on the exceptional divisor by active
mixing. -/
def quittingMixingFirstOrderResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (a u : ι → ℝ) (who : ι) : ℝ :=
  (∑ other ∈ Finset.univ.erase who,
    a other *
      (weightOfReward reward ({who, other} : Finset ι) who -
        weightOfReward reward ({other} : Finset ι) who)) - u who

theorem quittingMixingBlowupResidual_zero
    (a u : ι → ℝ) (who : ι) :
    quittingMixingBlowupResidual reward 0 a u who =
      quittingMixingFirstOrderResidual reward a u who := by
  rw [quittingMixingBlowupResidual,
    sum_powerset_erase_empty_eq_sum_singleton_add_sum_card_ge_two]
  have hmultiple :
      (∑ J ∈ ((Finset.univ.erase who).powerset.filter
          fun J : Finset ι => 2 ≤ J.card),
        quittingBlowupOpponentCoalitionSlope 0 a who J *
          (weightOfReward reward (insert who J) who -
            weightOfReward reward J who)) = 0 := by
    apply Finset.sum_eq_zero
    intro J hJ
    have hcard : 0 < J.card - 1 := by
      have := (Finset.mem_filter.mp hJ).2
      omega
    simp [quittingBlowupOpponentCoalitionSlope, zero_pow hcard.ne']
  rw [hmultiple, add_zero]
  simp [quittingBlowupOpponentCoalitionSlope, quittingBlowupHazard,
    continueMassExcl, quittingMixingFirstOrderResidual]

/-- Exact factorization of the active mixing gain, assuming the exceptional-
divisor boundary is pinned to the owner's singleton reward. -/
theorem t_mul_quittingMixingBlowupResidual
    (boundary : Payoff ι) (t : ℝ) (a u : ι → ℝ) (who : ι)
    (hpin : boundary who = reward (quittingSingletonTerminal who) who) :
    t * quittingMixingBlowupResidual reward t a u who =
      gainValue (weightOfReward reward) (quittingBlowupHazard t a) who
        (boundary who + t * u who) := by
  let opponents := Finset.univ.erase who
  let nonempty := opponents.powerset.erase (∅ : Finset ι)
  have hempty : (∅ : Finset ι) ∈ opponents.powerset :=
    Finset.empty_mem_powerset _
  have hslope : ∀ J ∈ nonempty,
      t * (quittingBlowupOpponentCoalitionSlope t a who J *
        (weightOfReward reward (insert who J) who -
          weightOfReward reward J who)) =
      ((∏ owner ∈ J, quittingBlowupHazard t a owner) *
        ∏ owner ∈ opponents \ J,
          (1 - quittingBlowupHazard t a owner)) *
        (weightOfReward reward (insert who J) who -
          weightOfReward reward J who) := by
    intro J hJ
    rw [← mul_assoc, t_mul_quittingBlowupOpponentCoalitionSlope]
    exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hJ).1
  unfold quittingMixingBlowupResidual gainValue gammaValue sigmaValue
    excludedValue
  rw [mul_sub, Finset.mul_sum]
  have hsum :
      (∑ J ∈ nonempty,
        t * (quittingBlowupOpponentCoalitionSlope t a who J *
          (weightOfReward reward (insert who J) who -
            weightOfReward reward J who))) =
      ∑ J ∈ nonempty,
        ((∏ owner ∈ J, quittingBlowupHazard t a owner) *
          ∏ owner ∈ opponents \ J,
            (1 - quittingBlowupHazard t a owner)) *
          (weightOfReward reward (insert who J) who -
            weightOfReward reward J who) :=
    Finset.sum_congr rfl hslope
  rw [hsum]
  change _ =
    (∑ J ∈ opponents.powerset,
      (∏ owner ∈ J, quittingBlowupHazard t a owner) *
        (∏ owner ∈ opponents \ J,
          (1 - quittingBlowupHazard t a owner)) *
        weightOfReward reward (insert who J) who) -
      ((∑ J ∈ nonempty,
        (∏ owner ∈ J, quittingBlowupHazard t a owner) *
          (∏ owner ∈ opponents \ J,
            (1 - quittingBlowupHazard t a owner)) *
          weightOfReward reward J who) +
        continueMassExcl (quittingBlowupHazard t a) who *
          (boundary who + t * u who))
  rw [← Finset.add_sum_erase opponents.powerset
    (fun J ↦
      (∏ owner ∈ J, quittingBlowupHazard t a owner) *
        (∏ owner ∈ opponents \ J,
          (1 - quittingBlowupHazard t a owner)) *
        weightOfReward reward (insert who J) who) hempty]
  simp only [nonempty]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp [opponents, continueMassExcl, hpin, weightOfReward,
    quittingSingletonTerminal]
  ring

namespace QuittingChargeTangentPacket

/-- Leading hazard coefficient represented by a tangent packet at radial
scale `scale`. -/
def blowupLeading (packet : QuittingChargeTangentPacket reward)
    (scale : ℝ) : ι → ℝ :=
  fun owner ↦ scale * packet.mass owner

/-- First continuation drift forced by Bellman consistency. -/
def blowupContinuationDrift
    (packet : QuittingChargeTangentPacket reward) (scale : ℝ) : ι → ℝ :=
  fun who ↦ -scale * packet.tangent who

/-- The leading hazard coefficient at scale `(1-c)/c` is the anchored
singleton coordinate divided projectively by cemetery mass. -/
theorem anchored_cemetery_mul_blowupLeading
    (packet : QuittingChargeTangentPacket reward) (cemetery : ℝ)
    (hcemetery_pos : 0 < cemetery) (hcemetery_le_one : cemetery ≤ 1)
    (owner : ι) :
    cemetery * packet.blowupLeading ((1 - cemetery) / cemetery) owner =
      (packet.toAnchoredProjectiveSingletonPacket cemetery hcemetery_pos
        hcemetery_le_one).singleton owner := by
  rw [toAnchoredProjectiveSingletonPacket_singleton]
  unfold blowupLeading
  field_simp

/-- The anchored cemetery payoff is the unit-radial extrapolation of the
blown-up continuation drift at the matching projective scale. -/
theorem anchored_anchor_eq_boundary_add_blowupContinuationDrift
    (packet : QuittingChargeTangentPacket reward) (cemetery : ℝ)
    (hcemetery_pos : 0 < cemetery) (hcemetery_le_one : cemetery ≤ 1)
    (who : ι) :
    (packet.toAnchoredProjectiveSingletonPacket cemetery hcemetery_pos
        hcemetery_le_one).anchor who =
      packet.boundary who +
        packet.blowupContinuationDrift ((1 - cemetery) / cemetery) who := by
  rw [toAnchoredProjectiveSingletonPacket_anchor]
  unfold blowupContinuationDrift
  ring

/-- The packet tangent identity is exactly the exceptional-divisor Bellman
equation. -/
theorem bellmanFirstOrderResidual_eq_zero
    (packet : QuittingChargeTangentPacket reward) (scale : ℝ) (who : ι) :
    quittingBellmanFirstOrderResidual reward packet.boundary
      (packet.blowupLeading scale)
      (packet.blowupContinuationDrift scale) who = 0 := by
  unfold quittingBellmanFirstOrderResidual blowupLeading
    blowupContinuationDrift
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have hsum :
      (∑ owner, packet.mass owner *
        (reward (quittingSingletonTerminal owner) who -
          packet.boundary who)) = packet.tangent who := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, packet.mass_sum, one_mul]
    exact packet.tangent_eq who |>.symm
  rw [hsum]
  ring

/-- At the packet base point, the blown-up active-mixing residual is precisely
the radial scale times the canonical pair-compatibility residual. -/
theorem mixingFirstOrderResidual_eq_scale_mul_activePairCompatibilityResidual
    (packet : QuittingChargeTangentPacket reward) (scale : ℝ) (who : ι) :
    quittingMixingFirstOrderResidual reward
        (packet.blowupLeading scale)
        (packet.blowupContinuationDrift scale) who =
      scale * quittingActivePairCompatibilityResidual packet who := by
  unfold quittingMixingFirstOrderResidual blowupLeading
    blowupContinuationDrift quittingActivePairCompatibilityResidual
    quittingActiveMixingCollisionIncrement
  have hsum :
      (∑ other ∈ Finset.univ.erase who,
        packet.mass other *
          (weightOfReward reward ({who, other} : Finset ι) who -
            weightOfReward reward ({other} : Finset ι) who)) =
      ∑ other ∈ Finset.univ.erase who,
        packet.mass other *
          (reward (quittingPairJoinTerminal who other) who -
            reward (quittingSingletonTerminal other) who) := by
    apply Finset.sum_congr rfl
    intro other hother
    congr 1
    simp [weightOfReward, quittingPairJoinTerminal,
      quittingSingletonTerminal]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hsum]
  ring

/-- On active support, the canonical collapse rewrites the packet-base
mixing residual as the mass-weighted pair-join row. -/
theorem mixingFirstOrderResidual_eq_scale_mul_sum_pairJoinEffect
    (packet : QuittingChargeTangentPacket reward) (scale : ℝ) (who : ι)
    (hmass : 0 < packet.mass who) :
    quittingMixingFirstOrderResidual reward
        (packet.blowupLeading scale)
        (packet.blowupContinuationDrift scale) who =
      scale * ∑ owner ∈ Finset.univ.erase who,
        packet.mass owner *
          quittingActiveMixingPairJoinEffect reward who owner := by
  rw [packet.mixingFirstOrderResidual_eq_scale_mul_activePairCompatibilityResidual,
    packet.activePairCompatibilityResidual_eq_sum_pairJoinEffect who hmass]

/-- At nonzero radial scale, first-order active mixing holds exactly when the
pair compatibility vanishes. -/
theorem mixingFirstOrderResidual_eq_zero_iff
    (packet : QuittingChargeTangentPacket reward) (scale : ℝ)
    (hscale : scale ≠ 0) (who : ι) :
    quittingMixingFirstOrderResidual reward
        (packet.blowupLeading scale)
        (packet.blowupContinuationDrift scale) who = 0 ↔
      quittingActivePairCompatibilityResidual packet who = 0 := by
  rw [packet.mixingFirstOrderResidual_eq_scale_mul_activePairCompatibilityResidual]
  exact mul_eq_zero.trans (or_iff_right hscale)

end QuittingChargeTangentPacket

/-! ## Thin regular-locus lift -/

/-- Ambient first-blow-up coordinates: radial scale, leading hazards, and
continuation drift. -/
abbrev QuittingBlowupPoint (ι : Type) :=
  ℝ × ((ι → ℝ) × (ι → ℝ))

/-- Equality rows of one fixed support chart: Bellman, active mixing, and
zero leading rate off the declared support. -/
abbrev QuittingBlowupEqRow (ι : Type) (support : Finset ι) :=
  Sum ι (Sum {who : ι // who ∈ support} {who : ι // who ∉ support})

/-- Exact polynomial first-blow-up equality map for one declared support. -/
def quittingSupportBlowupResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (boundary : Payoff ι) (support : Finset ι)
    (point : QuittingBlowupPoint ι) :
    QuittingBlowupEqRow ι support → ℝ
  | Sum.inl who =>
      quittingBellmanBlowupResidual reward boundary point.1
        point.2.1 point.2.2 who
  | Sum.inr (Sum.inl owner) =>
      quittingMixingBlowupResidual reward point.1 point.2.1 point.2.2 owner
  | Sum.inr (Sum.inr outsider) => point.2.1 outsider

/-- The distinguished radial coordinate of the blow-up chart. -/
def quittingBlowupRadialCoordinate :
    QuittingBlowupPoint ι →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ((ι → ℝ) × (ι → ℝ))

namespace QuittingChargeTangentPacket

/-- Exceptional-divisor point represented by the packet at a supplied
nonzero projective scale. -/
def blowupBasePoint (packet : QuittingChargeTangentPacket reward)
    (scale : ℝ) : QuittingBlowupPoint ι :=
  (0, packet.blowupLeading scale, packet.blowupContinuationDrift scale)

/-- The packet is a zero of the full support-chart blow-up system exactly
after imposing the new pair-compatibility equations on its declared active
support. -/
theorem supportBlowupResidual_basePoint_eq_zero
    (packet : QuittingChargeTangentPacket reward) (scale : ℝ)
    (support : Finset ι)
    (hsupport : ∀ who, who ∈ support ↔ 0 < packet.mass who)
    (hcompat : ∀ who ∈ support,
      quittingActivePairCompatibilityResidual packet who = 0) :
    quittingSupportBlowupResidual reward packet.boundary support
      (packet.blowupBasePoint scale) = 0 := by
  funext row
  rcases row with who | owner | outsider
  · rw [quittingSupportBlowupResidual, blowupBasePoint,
      quittingBellmanBlowupResidual_zero]
    exact packet.bellmanFirstOrderResidual_eq_zero scale who
  · rw [quittingSupportBlowupResidual, blowupBasePoint,
      quittingMixingBlowupResidual_zero,
      packet.mixingFirstOrderResidual_eq_scale_mul_activePairCompatibilityResidual,
      hcompat owner owner.property, mul_zero]
    rfl
  · change scale * packet.mass outsider = 0
    have hnotpos : ¬0 < packet.mass outsider := by
      intro hpos
      exact outsider.property ((hsupport outsider).mpr hpos)
    have hzero : packet.mass outsider = 0 :=
      le_antisymm (le_of_not_gt hnotpos) (packet.mass_nonneg outsider)
    rw [hzero, mul_zero]

end QuittingChargeTangentPacket

/-- The support blow-up residual is a finite polynomial map and hence real
analytic at every point. -/
theorem analyticAt_quittingSupportBlowupResidual
    (boundary : Payoff ι) (support : Finset ι)
    (point : QuittingBlowupPoint ι) :
    AnalyticAt ℝ
      (quittingSupportBlowupResidual reward boundary support) point := by
  have hradial : AnalyticAt ℝ
      (fun p : QuittingBlowupPoint ι => p.1) point := analyticAt_fst
  have hpair : AnalyticAt ℝ
      (fun p : QuittingBlowupPoint ι => p.2) point := analyticAt_snd
  have hleading : AnalyticAt ℝ
      (fun p : QuittingBlowupPoint ι => p.2.1) point :=
    analyticAt_fst.comp_of_eq hpair rfl
  have hdrift : AnalyticAt ℝ
      (fun p : QuittingBlowupPoint ι => p.2.2) point :=
    analyticAt_snd.comp_of_eq hpair rfl
  have hleading_apply : ∀ owner, AnalyticAt ℝ
      (fun p : QuittingBlowupPoint ι => p.2.1 owner) point := by
    intro owner
    exact (ContinuousLinearMap.proj owner).analyticAt _ |>.comp_of_eq
      hleading rfl
  have hdrift_apply : ∀ who, AnalyticAt ℝ
      (fun p : QuittingBlowupPoint ι => p.2.2 who) point := by
    intro who
    exact (ContinuousLinearMap.proj who).analyticAt _ |>.comp_of_eq
      hdrift rfl
  have hhazard : ∀ owner, AnalyticAt ℝ
      (fun p : QuittingBlowupPoint ι => p.1 * p.2.1 owner) point :=
    fun owner => hradial.mul (hleading_apply owner)
  have hcontinue : AnalyticAt ℝ
      (fun p : QuittingBlowupPoint ι =>
        ∏ owner, (1 - p.1 * p.2.1 owner)) point :=
    Finset.univ.analyticAt_fun_prod fun owner _ =>
      analyticAt_const.sub (hhazard owner)
  have hslope : ∀ S : Finset ι, AnalyticAt ℝ
      (fun p : QuittingBlowupPoint ι =>
        (p.1 ^ (S.card - 1) * ∏ owner ∈ S, p.2.1 owner) *
          ∏ owner ∈ Finset.univ \ S,
            (1 - p.1 * p.2.1 owner)) point := by
    intro S
    exact (hradial.pow _ |>.mul
      (S.analyticAt_fun_prod fun owner _ => hleading_apply owner)).mul
        ((Finset.univ \ S).analyticAt_fun_prod fun owner _ =>
          analyticAt_const.sub (hhazard owner))
  have hopponentSlope : ∀ who (J : Finset ι), AnalyticAt ℝ
      (fun p : QuittingBlowupPoint ι =>
        (p.1 ^ (J.card - 1) * ∏ owner ∈ J, p.2.1 owner) *
          ∏ owner ∈ Finset.univ.erase who \ J,
            (1 - p.1 * p.2.1 owner)) point := by
    intro who J
    exact (hradial.pow _ |>.mul
      (J.analyticAt_fun_prod fun owner _ => hleading_apply owner)).mul
        ((Finset.univ.erase who \ J).analyticAt_fun_prod fun owner _ =>
          analyticAt_const.sub (hhazard owner))
  rw [analyticAt_pi_iff]
  intro row
  rcases row with who | owner | outsider
  · simp only [quittingSupportBlowupResidual,
      quittingBellmanBlowupResidual, quittingBlowupCoalitionSlope,
      quittingBlowupHazard, continueMass]
    exact hcontinue.mul (hdrift_apply who) |>.add
      ((Finset.univ.erase (∅ : Finset ι)).analyticAt_fun_sum fun S _ =>
        (hslope S).mul analyticAt_const)
  · simp only [quittingSupportBlowupResidual,
      quittingMixingBlowupResidual, quittingBlowupOpponentCoalitionSlope,
      quittingBlowupHazard, continueMassExcl]
    exact (((Finset.univ.erase (owner : ι)).powerset.erase
      (∅ : Finset ι)).analyticAt_fun_sum fun J _ =>
        (hopponentSlope owner J).mul analyticAt_const).sub
      (((Finset.univ.erase (owner : ι)).analyticAt_fun_prod fun other _ =>
        analyticAt_const.sub (hhazard other)).mul (hdrift_apply owner))
  · exact hleading_apply outsider

/-- A positive physical zero of the support blow-up system decodes to an
actual exact undiscounted Nash--Bellman root.  The outsider sign is kept as
an explicit strict-cell input; zero outsider slack is a separate singular
boundary problem. -/
theorem isNashBellmanRoot_of_supportBlowupResidual_eq_zero
    (packet : QuittingChargeTangentPacket reward) (support : Finset ι)
    (point : QuittingBlowupPoint ι)
    (hresidual : quittingSupportBlowupResidual reward packet.boundary support
      point = 0)
    (hpacketActive : ∀ who ∈ support, 0 < packet.mass who)
    (hhazard_nonneg : ∀ who,
      0 ≤ quittingBlowupHazard point.1 point.2.1 who)
    (hhazard_lt_one : ∀ who,
      quittingBlowupHazard point.1 point.2.1 who < 1)
    (houtside : ∀ who ∉ support,
      gainValue (weightOfReward reward)
        (quittingBlowupHazard point.1 point.2.1) who
        (packet.boundary who + point.1 * point.2.2 who) < 0) :
    let hazard := quittingBlowupHazard point.1 point.2.1
    let continuation : Payoff ι :=
      fun who ↦ packet.boundary who + point.1 * point.2.2 who
    let root := rootOfHazard hazard hhazard_nonneg
      (fun who ↦ (hhazard_lt_one who).le)
    packet.boundary = quittingRootSuccessorPayoff reward continuation root ∧
      IsεQuittingRootEndpointNash reward continuation 0 root := by
  let hazard := quittingBlowupHazard point.1 point.2.1
  let continuation : Payoff ι :=
    fun who ↦ packet.boundary who + point.1 * point.2.2 who
  let root := rootOfHazard hazard hhazard_nonneg
    (fun who ↦ (hhazard_lt_one who).le)
  have hrootHazard : hazardOfRoot root = hazard := by
    exact hazardOfRoot_rootOfHazard hazard hhazard_nonneg
      (fun who ↦ (hhazard_lt_one who).le)
  have hbellman : packet.boundary =
      quittingRootSuccessorPayoff reward continuation root := by
    funext who
    have hrow := congrFun hresidual (Sum.inl who)
    change quittingBellmanBlowupResidual reward packet.boundary point.1
      point.2.1 point.2.2 who = 0 at hrow
    have hfactor := t_mul_quittingBellmanBlowupResidual
      (reward := reward) packet.boundary point.1 point.2.1 point.2.2 who
    rw [hrow, mul_zero] at hfactor
    have habsorbing :
        (∑ S ∈ Finset.univ.erase (∅ : Finset ι),
          coalitionMass hazard S * weightOfReward reward S who) =
        quittingRootAbsorbingContribution reward root who := by
      rw [quittingRootAbsorbingContribution_eq_sum_coalitionMass]
      have hrate :
          (fun owner => (root owner true).toReal) = hazard := by
        change hazardOfRoot root = hazard
        exact hrootHazard
      rw [hrate]
      let f := (fun S : Finset ι =>
          coalitionMass (fun owner => (root owner true).toReal) S *
            quittingProjectiveCoalitionReward reward S who)
      have hsplit := Finset.add_sum_erase Finset.univ f
        (Finset.mem_univ (∅ : Finset ι))
      have hempty : f ∅ = 0 := by
        simp [f, quittingProjectiveCoalitionReward]
      rw [hempty, zero_add] at hsplit
      simpa only [f, hrate, quittingProjectiveCoalitionReward,
        weightOfReward] using hsplit
    have hcontinue : quittingStationaryContinueMass root =
        continueMass hazard := by
      rw [quittingStationaryContinueMass_eq_prod_continueProbability]
      unfold continueMass
      apply Finset.prod_congr rfl
      intro owner _
      have hsum := quittingRoot_continueProbability_add_quitProbability root owner
      have hquit : (root owner true).toReal = hazard owner := by
        exact congrFun hrootHazard owner
      linarith
    rw [quittingRootSuccessorPayoff_apply_eq_affine, hcontinue,
      ← habsorbing]
    change packet.boundary who = _
    linarith
  refine ⟨hbellman, ?_⟩
  rw [← isExactRowComplementary_hazardOfRoot_iff reward continuation root,
    hrootHazard]
  intro who
  by_cases hwho : who ∈ support
  · have hrow := congrFun hresidual
      (Sum.inr (Sum.inl ⟨who, hwho⟩))
    change quittingMixingBlowupResidual reward point.1 point.2.1
      point.2.2 who = 0 at hrow
    have hpin : packet.boundary who =
        reward (quittingSingletonTerminal who) who :=
      packet.positive_mass_pins_boundary who (hpacketActive who hwho)
    have hfactor := t_mul_quittingMixingBlowupResidual
      (reward := reward) packet.boundary point.1 point.2.1 point.2.2 who hpin
    rw [hrow, mul_zero] at hfactor
    change (0 < hazard who → 0 ≤ gainValue (weightOfReward reward)
      hazard who (continuation who)) ∧
      (hazard who < 1 → gainValue (weightOfReward reward)
        hazard who (continuation who) ≤ 0)
    exact ⟨fun _ ↦ hfactor.le, fun _ ↦ hfactor.ge⟩
  · have hrow := congrFun hresidual
      (Sum.inr (Sum.inr ⟨who, hwho⟩))
    change point.2.1 who = 0 at hrow
    have hzero : hazard who = 0 := by simp [hazard, quittingBlowupHazard, hrow]
    exact ⟨fun hpositive ↦ by simp [hzero] at hpositive,
      fun _ ↦ (houtside who hwho).le⟩

namespace QuittingChargeTangentPacket

/-- **Regular first-blow-up arc lift.**  Pair compatibility places the packet
on the exceptional-divisor equality locus.  If the derivative of that exact
finite polynomial system is surjective and has a kernel direction pointing
outward in the radial coordinate, the repository's analytic implicit-function
theorem constructs an actual positive analytic equality arc.  `U` carries
strict outsider, floor, upper-box, and positivity signs; only signs strict at
the base point may be placed there.

For the literal compatible ungauged chart, the later transversality theorem
shows that the two displayed regularity premises cannot hold together.  This
theorem remains the exact analytic consumer for a future gauged chart; it is
not itself a compatible-packet producer. -/
theorem hasPositiveRadialAnalyticArcAt_of_regular_supportBlowup
    (packet : QuittingChargeTangentPacket reward) (scale : ℝ)
    (support : Finset ι)
    (hsupport : ∀ who, who ∈ support ↔ 0 < packet.mass who)
    (hcompat : ∀ who ∈ support,
      quittingActivePairCompatibilityResidual packet who = 0)
    (U : Set (QuittingBlowupPoint ι))
    (hU : U ∈ 𝓝 (packet.blowupBasePoint scale))
    (hsurj :
      (fderiv ℝ (quittingSupportBlowupResidual reward packet.boundary support)
        (packet.blowupBasePoint scale)).range = ⊤)
    (direction :
      (fderiv ℝ (quittingSupportBlowupResidual reward packet.boundary support)
        (packet.blowupBasePoint scale)).ker)
    (hdirection : 0 < quittingBlowupRadialCoordinate direction.1) :
    Math.HasPositiveCoordinateAnalyticArcAt
      ({point | quittingSupportBlowupResidual reward packet.boundary support
          point = 0} ∩ U)
      quittingBlowupRadialCoordinate (packet.blowupBasePoint scale) := by
  let residual := quittingSupportBlowupResidual reward packet.boundary support
  let base := packet.blowupBasePoint scale
  have hanalytic : AnalyticAt ℝ residual base :=
    analyticAt_quittingSupportBlowupResidual packet.boundary support base
  have hderiv : HasStrictFDerivAt residual (fderiv ℝ residual base) base :=
    hanalytic.hasStrictFDerivAt
  have hbase : residual base = 0 :=
    packet.supportBlowupResidual_basePoint_eq_zero scale support
      hsupport hcompat
  have hcoordinate : quittingBlowupRadialCoordinate base = 0 := rfl
  have harc := Math.hasPositiveCoordinateAnalyticArcAt_regularLevel_of_analytic
    hderiv hanalytic hsurj direction hdirection hcoordinate hU
  simpa [residual, base, hbase] using harc

end QuittingChargeTangentPacket

end GameTheory
