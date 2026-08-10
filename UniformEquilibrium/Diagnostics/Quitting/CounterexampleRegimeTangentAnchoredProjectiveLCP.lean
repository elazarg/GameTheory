/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacket
import UniformEquilibrium.Quitting.Projective.AnchoredSingletonLCP

/-!
# Tangent packets as anchored projective LCP packets

A charge-normalized tangent packet already has the exact affine identity
needed by the repository's anchored projective singleton LCP.  For any
cemetery weight `c ∈ (0, 1]`, assign singleton weight
`(1 - c) * mass owner`, retain `boundary` as the value, and use the anchor

`boundary - ((1 - c) / c) * tangent`.

The tangent identity makes the anchored mixture equation exact.  On an
active owner, the anchored LCP direction is the negative rescaled tangent;
in particular an active positive tangent gives a strictly negative direction
for `c < 1`.

This is an algebraic bridge into the existing projective LCP coordinates.  It
does not construct a simultaneous quit-rate root, a resolved projective chart,
or the real/Puiseux arc required by `QuittingResolvedProjectiveChartInterface`.
Collision and higher-coalition terms belong to that unresolved lifting step,
not to the singleton first-event identity proved here.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingChargeTangentPacket

/-- Rebase a charge tangent packet as an anchored projective singleton packet
at any strictly positive cemetery weight at most one. -/
def toAnchoredProjectiveSingletonPacket
    (packet : QuittingChargeTangentPacket reward) (cemetery : ℝ)
    (hcemetery_pos : 0 < cemetery) (hcemetery_le_one : cemetery ≤ 1) :
    QuittingAnchoredProjectiveSingletonPacket reward where
  anchor := fun who ↦ packet.boundary who -
    ((1 - cemetery) / cemetery) * packet.tangent who
  cemetery := cemetery
  singleton := fun owner ↦ (1 - cemetery) * packet.mass owner
  value := packet.boundary
  cemetery_nonneg := hcemetery_pos.le
  singleton_nonneg := fun owner ↦
    mul_nonneg (sub_nonneg.mpr hcemetery_le_one) (packet.mass_nonneg owner)
  total := by
    rw [← Finset.mul_sum, packet.mass_sum]
    ring
  value_eq_anchored_mix := by
    intro who
    have hterminal : ∀ owner : ι,
        quittingProjectiveSingletonTerminal owner =
          quittingSingletonTerminal owner := by
      intro owner
      apply Subtype.ext
      rfl
    simp_rw [hterminal, mul_assoc]
    rw [← Finset.mul_sum]
    change packet.boundary who = cemetery *
        (packet.boundary who - (1 - cemetery) / cemetery * packet.tangent who) +
      (1 - cemetery) * quittingSingletonMixture reward packet.mass who
    rw [packet.tangent_eq who]
    field_simp
    ring
  solo_le_value := by
    intro who
    simpa [quittingProjectiveSingletonTerminal, quittingSingletonTerminal]
      using packet.solo_le_boundary who
  positive_singleton_pins := by
    intro owner hpositive
    have hmass : 0 < packet.mass owner := by
      have hfactor : 0 ≤ 1 - cemetery := sub_nonneg.mpr hcemetery_le_one
      nlinarith [packet.mass_nonneg owner]
    simpa [quittingProjectiveSingletonTerminal, quittingSingletonTerminal]
      using packet.positive_mass_pins_boundary owner hmass

@[simp] theorem toAnchoredProjectiveSingletonPacket_anchor
    (packet : QuittingChargeTangentPacket reward) (cemetery : ℝ)
    (hcemetery_pos : 0 < cemetery) (hcemetery_le_one : cemetery ≤ 1)
    (who : ι) :
    (packet.toAnchoredProjectiveSingletonPacket cemetery hcemetery_pos
      hcemetery_le_one).anchor who = packet.boundary who -
        ((1 - cemetery) / cemetery) * packet.tangent who := rfl

@[simp] theorem toAnchoredProjectiveSingletonPacket_singleton
    (packet : QuittingChargeTangentPacket reward) (cemetery : ℝ)
    (hcemetery_pos : 0 < cemetery) (hcemetery_le_one : cemetery ≤ 1)
    (owner : ι) :
    (packet.toAnchoredProjectiveSingletonPacket cemetery hcemetery_pos
      hcemetery_le_one).singleton owner =
        (1 - cemetery) * packet.mass owner := rfl

/-- On the active support, the artificial anchored direction is exactly the
negative rescaled tangent. -/
theorem anchoredProjectiveLCPDirection_eq
    (packet : QuittingChargeTangentPacket reward) (cemetery : ℝ)
    (hcemetery_pos : 0 < cemetery) (hcemetery_le_one : cemetery ≤ 1)
    (owner : ι) (hmass : 0 < packet.mass owner) :
    quittingAnchoredProjectiveLCPDirection reward
        (packet.toAnchoredProjectiveSingletonPacket cemetery hcemetery_pos
          hcemetery_le_one).anchor owner =
      -((1 - cemetery) / cemetery) * packet.tangent owner := by
  rw [quittingAnchoredProjectiveLCPDirection,
    toAnchoredProjectiveSingletonPacket_anchor]
  have hterminal : quittingProjectiveSingletonTerminal owner =
      quittingSingletonTerminal owner := by
    apply Subtype.ext
    rfl
  rw [hterminal, ← packet.positive_mass_pins_boundary owner hmass]
  ring

/-- A positive tangent on an active owner becomes a strictly negative
anchored projective LCP direction at every nondegenerate cemetery weight. -/
theorem anchoredProjectiveLCPDirection_neg
    (packet : QuittingChargeTangentPacket reward) (cemetery : ℝ)
    (hcemetery_pos : 0 < cemetery) (hcemetery_lt_one : cemetery < 1)
    (owner : ι) (hmass : 0 < packet.mass owner)
    (htangent : 0 < packet.tangent owner) :
    quittingAnchoredProjectiveLCPDirection reward
        (packet.toAnchoredProjectiveSingletonPacket cemetery hcemetery_pos
          hcemetery_lt_one.le).anchor owner < 0 := by
  rw [packet.anchoredProjectiveLCPDirection_eq cemetery hcemetery_pos
    hcemetery_lt_one.le owner hmass]
  have hscale : 0 < (1 - cemetery) / cemetery :=
    div_pos (sub_pos.mpr hcemetery_lt_one) hcemetery_pos
  nlinarith [mul_pos hscale htangent]

end QuittingChargeTangentPacket

end GameTheory
