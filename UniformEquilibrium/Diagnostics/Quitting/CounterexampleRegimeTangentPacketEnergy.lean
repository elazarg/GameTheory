/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacket
import UniformEquilibrium.Quitting.Classification.SingletonPacketEnergy

/-!
# Energy consequences of an active-positive tangent packet

After the negative-coordinate tangent branch has been excluded, a charge-
tangent packet is canonically a normalized singleton-source packet: its
boundary is the packet target and its tangent is the coordinatewise delivery
surplus.  Thus a positive tangent carried by positive mass makes the existing
singleton packet energy strictly positive.  The energy theorem then supplies
a distinct positive-mass pair with positive reciprocal singleton effect.

This is the complete finite singleton-level handoff, not a product-root
realization.  The Boolean Möbius expansion of a product root also contains
the actual collision rewards, the continuation value, and all pair and higher
coalition coefficients.  Nothing here controls those terms or proves the
on-support equalities and off-support inequalities needed to enlarge support.
In particular, the concrete residue in
`LocalMechanismResidueWitness` shows that reciprocal singleton information
need not produce a two-owner root.  No chronological return, punishment-
admissible cycle, or equilibrium compiler is inferred.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingChargeTangentPacket

/-- Once every tangent coordinate is nonnegative, the boundary of a charge-
tangent packet is a normalized singleton-source target. -/
def toNormalizedSingletonSourcePacket
    (packet : QuittingChargeTangentPacket reward)
    (htangent : ∀ who, 0 ≤ packet.tangent who) :
    QuittingNormalizedSingletonSourcePacket reward where
  mass := packet.mass
  target := packet.boundary
  mass_nonneg := packet.mass_nonneg
  mass_sum := packet.mass_sum
  mix_ge_target := by
    intro who
    have h := htangent who
    rw [packet.tangent_eq who] at h
    linarith
  solo_le_target := packet.solo_le_boundary
  punishment_le_target := packet.punishment_le_boundary
  positive_mass_pins_target := packet.positive_mass_pins_boundary

@[simp]
theorem toNormalizedSingletonSourcePacket_mass
    (packet : QuittingChargeTangentPacket reward)
    (htangent : ∀ who, 0 ≤ packet.tangent who) :
    (packet.toNormalizedSingletonSourcePacket htangent).mass = packet.mass :=
  rfl

@[simp]
theorem toNormalizedSingletonSourcePacket_target
    (packet : QuittingChargeTangentPacket reward)
    (htangent : ∀ who, 0 ≤ packet.tangent who) :
    (packet.toNormalizedSingletonSourcePacket htangent).target =
      packet.boundary :=
  rfl

/-- The adapted packet's weighted delivery surplus is exactly its mass-
weighted tangent motion. -/
theorem weightedSurplus_toNormalizedSingletonSourcePacket_eq
    (packet : QuittingChargeTangentPacket reward)
    (htangent : ∀ who, 0 ≤ packet.tangent who) :
    quittingPacketWeightedSurplus
        (packet.toNormalizedSingletonSourcePacket htangent) =
      ∑ who, packet.mass who * packet.tangent who := by
  unfold quittingPacketWeightedSurplus
  apply Finset.sum_congr rfl
  intro who _
  change packet.mass who *
      (quittingSingletonMixture reward packet.mass who -
        packet.boundary who) =
    packet.mass who * packet.tangent who
  rw [packet.tangent_eq who]

/-- A positive tangent at a positive-mass owner is paid by a distinct
positive-mass singleton owner with a strictly positive directed solo effect.
This conclusion does not require nonnegativity of the other tangent
coordinates. -/
theorem exists_supported_outsider_pos_soloEffect
    (packet : QuittingChargeTangentPacket reward) (owner : ι)
    (hmass : 0 < packet.mass owner)
    (htangent : 0 < packet.tangent owner) :
    ∃ other, other ≠ owner ∧ 0 < packet.mass other ∧
      0 < quittingSingletonSoloEffect reward owner other := by
  have haverage :
      0 < ∑ other, packet.mass other *
        quittingSingletonSoloEffect reward owner other := by
    rw [sum_mass_mul_quittingSingletonSoloEffect_eq
      reward packet.mass packet.mass_sum owner]
    have htangent' := htangent
    rw [packet.tangent_eq owner,
      packet.positive_mass_pins_boundary owner hmass] at htangent'
    exact htangent'
  by_contra hno
  push Not at hno
  have hnonpos :
      (∑ other, packet.mass other *
        quittingSingletonSoloEffect reward owner other) ≤ 0 := by
    apply Finset.sum_nonpos
    intro other _
    by_cases heq : other = owner
    · subst other
      simp
    by_cases hother : 0 < packet.mass other
    · exact mul_nonpos_of_nonneg_of_nonpos
        (packet.mass_nonneg other) (hno other heq hother)
    · have hzero : packet.mass other = 0 :=
        le_antisymm (le_of_not_gt hother) (packet.mass_nonneg other)
      simp [hzero]
  linarith

/-- **Active-positive reciprocal-pair restriction.**  If all tangent
coordinates are nonnegative and one positive tangent is carried by positive
mass, two distinct positive-mass owners have positive reciprocal singleton
effect.  This is a packet-energy conclusion, not an exact-root compiler. -/
theorem exists_supported_pair_pos_reciprocalSoloEffect
    (packet : QuittingChargeTangentPacket reward)
    (htangent : ∀ who, 0 ≤ packet.tangent who)
    (active : ι) (hmass : 0 < packet.mass active)
    (hactive : 0 < packet.tangent active) :
    ∃ who owner,
      0 < packet.mass who ∧ 0 < packet.mass owner ∧ who ≠ owner ∧
        0 < quittingSingletonSoloEffect reward who owner +
          quittingSingletonSoloEffect reward owner who := by
  have hterm : 0 < packet.mass active * packet.tangent active :=
    mul_pos hmass hactive
  have hsum : 0 < ∑ who, packet.mass who * packet.tangent who :=
    hterm.trans_le <| Finset.single_le_sum
      (fun who _ => mul_nonneg (packet.mass_nonneg who) (htangent who))
      (Finset.mem_univ active)
  have hsurplus :
      0 < quittingPacketWeightedSurplus
        (packet.toNormalizedSingletonSourcePacket htangent) := by
    rwa [packet.weightedSurplus_toNormalizedSingletonSourcePacket_eq htangent]
  have henergy :
      0 < quittingSingletonPacketQuadraticEnergy reward packet.mass := by
    rw [quittingPacketWeightedSurplus_eq_quadraticForm] at hsurplus
    simpa only [toNormalizedSingletonSourcePacket_mass] using hsurplus
  exact exists_supported_pair_pos_reciprocalSoloEffect_of_energy_pos
    reward packet.mass packet.mass_nonneg henergy

end QuittingChargeTangentPacket

end GameTheory
