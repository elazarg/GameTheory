/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketDefect
import UniformEquilibrium.Quitting.Classification.SingletonPacketEnergy

/-!
# Refusal duality and reciprocal pairs in a counterexample packet

For a normalized singleton source packet with no full-mass atom, conditioning
away each owner's atom converts its weighted refusal gain into exactly that
owner's weighted delivery surplus.  Summing therefore recovers the same
quadratic solo-effect energy as the packet complementarity equations.

The compact packet defect used by a counterexample regime is bounded above by
this total energy.  Its strict positivity consequently forces two distinct
positive-mass owners whose reciprocal solo effects have positive sum.

This is a finite packet restriction.  It neither identifies packet mass with
a late-tail occupation law nor realizes the positive reciprocal pair as a
charged Bellman path.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Mass-weighted gain from conditioning each owner out of the singleton
delivery.  Its energy identity is used when every packet atom has mass below
one. -/
def quittingPacketWeightedRefusalSurplus
    (packet : QuittingNormalizedSingletonSourcePacket reward) : ℝ :=
  ∑ owner, (1 - packet.mass owner) *
    (quittingSingletonRefusalValue reward packet.mass owner owner -
      quittingSingletonMixture reward packet.mass owner)

namespace QuittingNormalizedSingletonSourcePacket

/-- On a proper atom, the weighted refusal gain is exactly the weighted
packet surplus.  Zero-mass atoms are included; only a full-mass denominator
is excluded. -/
theorem one_sub_mass_mul_refusal_sub_mixture_eq_mass_mul_surplus
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (owner : ι) (hmass : packet.mass owner < 1) :
    (1 - packet.mass owner) *
        (quittingSingletonRefusalValue reward packet.mass owner owner -
          quittingSingletonMixture reward packet.mass owner) =
      packet.mass owner *
        (quittingSingletonMixture reward packet.mass owner -
          packet.target owner) := by
  have hsplit := packet.singletonMixture_eq_mass_mul_add_refusal hmass owner
  have hcomplement := packet.mass_mul_target_sub_solo_eq_zero owner
  have hfirst :
      (1 - packet.mass owner) *
          (quittingSingletonRefusalValue reward packet.mass owner owner -
            quittingSingletonMixture reward packet.mass owner) =
        packet.mass owner *
          (quittingSingletonMixture reward packet.mass owner -
            reward (quittingSingletonTerminal owner) owner) := by
    rw [hsplit]
    ring
  have htargetSolo :
      packet.mass owner * packet.target owner =
        packet.mass owner *
          reward (quittingSingletonTerminal owner) owner := by
    rw [mul_sub] at hcomplement
    linarith
  rw [hfirst]
  calc
    packet.mass owner *
        (quittingSingletonMixture reward packet.mass owner -
          reward (quittingSingletonTerminal owner) owner) =
      packet.mass owner *
          quittingSingletonMixture reward packet.mass owner -
        packet.mass owner *
          reward (quittingSingletonTerminal owner) owner := by ring
    _ = packet.mass owner *
          quittingSingletonMixture reward packet.mass owner -
        packet.mass owner * packet.target owner := by rw [htargetSolo]
    _ = packet.mass owner *
        (quittingSingletonMixture reward packet.mass owner -
          packet.target owner) := by ring

end QuittingNormalizedSingletonSourcePacket

/-- **Aggregate refusal-energy identity.**  If every packet atom is proper,
the total weighted refusal surplus is the solo-effect quadratic form. -/
theorem quittingPacketWeightedRefusal_eq_quadraticForm
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hmass : ∀ owner, packet.mass owner < 1) :
    quittingPacketWeightedRefusalSurplus packet =
      quittingSingletonPacketQuadraticEnergy reward packet.mass := by
  classical
  calc
    quittingPacketWeightedRefusalSurplus packet =
        quittingPacketWeightedSurplus packet := by
      unfold quittingPacketWeightedRefusalSurplus
        quittingPacketWeightedSurplus
      apply Finset.sum_congr rfl
      intro owner _
      exact packet.one_sub_mass_mul_refusal_sub_mixture_eq_mass_mul_surplus
        owner (hmass owner)
    _ = quittingSingletonPacketQuadraticEnergy reward packet.mass :=
      quittingPacketWeightedSurplus_eq_quadraticForm packet

/-- The maximum coordinate packet defect is at most the sum of all weighted
coordinate surpluses. -/
theorem quittingNormalizedSingletonPacketDefect_le_weightedSurplus
    [Nonempty ι]
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    quittingNormalizedSingletonPacketDefect reward
        (packet.mass, packet.target) ≤
      quittingPacketWeightedSurplus packet := by
  classical
  obtain ⟨owner, _, howner⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty
    (fun who => packet.mass who *
      (quittingSingletonMixture reward packet.mass who - packet.target who))
  rw [quittingNormalizedSingletonPacketDefect, howner]
  unfold quittingPacketWeightedSurplus
  exact Finset.single_le_sum
    (fun who _ => packet.mass_mul_surplus_nonneg who)
    (Finset.mem_univ owner)

/-- A positive normalized packet defect forces a positive reciprocal-synergy
pair in the positive support of that packet. -/
theorem exists_supported_pair_pos_reciprocalSurplus_of_packetDefect_pos
    [Nonempty ι]
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hdefect : 0 < quittingNormalizedSingletonPacketDefect reward
      (packet.mass, packet.target)) :
    ∃ who owner,
      0 < packet.mass who ∧ 0 < packet.mass owner ∧ who ≠ owner ∧
        0 < quittingSingletonSoloEffect reward who owner +
          quittingSingletonSoloEffect reward owner who := by
  have hsurplus : 0 < quittingPacketWeightedSurplus packet :=
    hdefect.trans_le
      (quittingNormalizedSingletonPacketDefect_le_weightedSurplus packet)
  have henergy :
      0 < quittingSingletonPacketQuadraticEnergy reward packet.mass := by
    rwa [quittingPacketWeightedSurplus_eq_quadraticForm] at hsurplus
  exact exists_supported_pair_pos_reciprocalSoloEffect_of_energy_pos
    reward packet.mass packet.mass_nonneg henergy

namespace QuittingCounterexampleRegime

/-- No normalized singleton packet of a counterexample regime has a full-mass
atom.  A strict-surplus atom supplies positive mass away from every putative
full atom. -/
theorem normalizedSingletonPacket_mass_lt_one
    (regime : QuittingCounterexampleRegime reward) [Nonempty ι]
    (packet : QuittingNormalizedSingletonSourcePacket reward) (owner : ι) :
    packet.mass owner < 1 := by
  obtain ⟨selected, hselected, hselectedLt, -, -⟩ :=
    regime.exists_active_strictSingletonRefusal packet
  by_cases heq : owner = selected
  · simpa [heq] using hselectedLt
  · have hmem : owner ∈ (Finset.univ.erase selected : Finset ι) := by
      exact Finset.mem_erase.mpr ⟨heq, Finset.mem_univ owner⟩
    have hownerLe : packet.mass owner ≤
        ∑ other ∈ (Finset.univ.erase selected : Finset ι),
          packet.mass other :=
      Finset.single_le_sum
        (fun other _ => packet.mass_nonneg other) hmem
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset ι)) (f := packet.mass)
      (a := selected) (Finset.mem_univ selected)
    rw [packet.mass_sum] at hsplit
    linarith

/-- In a counterexample regime the aggregate weighted refusal identity is
automatic: strict packet surplus rules out every full-mass denominator. -/
theorem packetWeightedRefusal_eq_quadraticForm
    (regime : QuittingCounterexampleRegime reward) [Nonempty ι]
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    quittingPacketWeightedRefusalSurplus packet =
      quittingSingletonPacketQuadraticEnergy reward packet.mass :=
  quittingPacketWeightedRefusal_eq_quadraticForm packet
    (regime.normalizedSingletonPacket_mass_lt_one packet)

/-- **Positive reciprocal pair restriction.**  Every normalized singleton
packet of a counterexample regime contains two distinct positive-mass owners
whose reciprocal solo effects have positive sum. -/
theorem exists_supported_pair_pos_reciprocalSoloEffect
    (regime : QuittingCounterexampleRegime reward) [Nonempty ι]
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∃ who owner,
      0 < packet.mass who ∧ 0 < packet.mass owner ∧ who ≠ owner ∧
        0 < quittingSingletonSoloEffect reward who owner +
          quittingSingletonSoloEffect reward owner who := by
  obtain ⟨active, hactive, hstrict⟩ :=
    regime.exists_active_strictSingletonSurplus packet
  have hterm : 0 < packet.mass active *
      (quittingSingletonMixture reward packet.mass active -
        packet.target active) :=
    mul_pos hactive (sub_pos.mpr hstrict)
  have htermLe : packet.mass active *
      (quittingSingletonMixture reward packet.mass active -
        packet.target active) ≤ quittingPacketWeightedSurplus packet := by
    unfold quittingPacketWeightedSurplus
    exact Finset.single_le_sum
      (fun who _ => packet.mass_mul_surplus_nonneg who)
      (Finset.mem_univ active)
  have henergy :
      0 < quittingSingletonPacketQuadraticEnergy reward packet.mass := by
    rw [← quittingPacketWeightedSurplus_eq_quadraticForm packet]
    exact hterm.trans_le htermLe
  exact exists_supported_pair_pos_reciprocalSoloEffect_of_energy_pos
    reward packet.mass packet.mass_nonneg henergy

end QuittingCounterexampleRegime

end GameTheory
