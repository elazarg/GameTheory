/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacket
import UniformEquilibrium.Quitting.Classification.ThreePlayer.SingletonMixtureCompiler

/-!
# The forced source packet has a strict refusal direction

A normalized singleton source packet supplies a probability distribution on
singleton exits and a target below the delivered singleton mixture.  Under a
counterexample regime this packet cannot be complementary on its support:
the face-circulation compiler would otherwise produce a uniform-equilibrium
payoff.  Consequently some positive-mass owner is strictly overpaid by the
mixture relative to its pinned solo target.

Conditioning the singleton delivery on that owner not being selected turns
the same strict surplus into a literal refusal advantage.  Thus the finite
analytic packet already contains one of the payoff escapes that can obstruct
a periodically restarted late window.  This is a finite source statement;
it does not assert that the selected packet is the asymptotic delivery law of
the optimized exact-debt tail.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Singleton delivery to `who`, conditioned on the selected singleton owner
being different from `owner`.  The definition is used only when
`mass owner < 1`. -/
def quittingSingletonRefusalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ) (owner who : ι) : ℝ :=
  (∑ other ∈ (Finset.univ.erase owner : Finset ι),
      mass other * reward (quittingSingletonTerminal other) who) /
    (1 - mass owner)

namespace QuittingNormalizedSingletonSourcePacket

/-- A packet mass is at most one. -/
theorem mass_le_one
    (packet : QuittingNormalizedSingletonSourcePacket reward) (owner : ι) :
    packet.mass owner ≤ 1 := by
  rw [← packet.mass_sum]
  exact single_le_sum (fun other _ ↦ packet.mass_nonneg other)
    (mem_univ owner)

/-- Split the singleton mixture into the owner's atom and all other atoms. -/
theorem singletonMixture_eq_owner_add_erase
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (owner who : ι) :
    quittingSingletonMixture reward packet.mass who =
      packet.mass owner * reward (quittingSingletonTerminal owner) who +
        ∑ other ∈ (Finset.univ.erase owner : Finset ι),
          packet.mass other * reward (quittingSingletonTerminal other) who := by
  unfold quittingSingletonMixture
  rw [← sum_erase_add _ _ (mem_univ owner)]
  ac_rfl

/-- If an atom has full mass, the singleton mixture is exactly its reward
vector. -/
theorem singletonMixture_eq_singleton_of_mass_eq_one
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {owner : ι} (hmass : packet.mass owner = 1) (who : ι) :
    quittingSingletonMixture reward packet.mass who =
      reward (quittingSingletonTerminal owner) who := by
  have heraseMass :
      ∑ other ∈ (Finset.univ.erase owner : Finset ι), packet.mass other = 0 := by
    have hsplit := sum_erase_add
      (s := (Finset.univ : Finset ι)) (f := packet.mass)
      (a := owner) (mem_univ owner)
    rw [packet.mass_sum, hmass] at hsplit
    linarith
  have hzero : ∀ other ∈ (Finset.univ.erase owner : Finset ι),
      packet.mass other = 0 := by
    intro other hother
    apply le_antisymm
    · have hle : packet.mass other ≤
          ∑ player ∈ (Finset.univ.erase owner : Finset ι),
            packet.mass player :=
        single_le_sum (fun player _ ↦ packet.mass_nonneg player) hother
      simpa [heraseMass] using hle
    · exact packet.mass_nonneg other
  have hweightedZero :
      ∑ other ∈ (Finset.univ.erase owner : Finset ι),
        packet.mass other * reward (quittingSingletonTerminal other) who = 0 := by
    apply sum_eq_zero
    intro other hother
    rw [hzero other hother, zero_mul]
  rw [packet.singletonMixture_eq_owner_add_erase owner who, hmass]
  rw [hweightedZero]
  ring

/-- For a non-full atom, the singleton mixture is the affine combination of
its singleton reward and its conditional refusal value. -/
theorem singletonMixture_eq_mass_mul_add_refusal
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {owner : ι} (hmass : packet.mass owner < 1) (who : ι) :
    quittingSingletonMixture reward packet.mass who =
      packet.mass owner * reward (quittingSingletonTerminal owner) who +
        (1 - packet.mass owner) *
          quittingSingletonRefusalValue reward packet.mass owner who := by
  rw [packet.singletonMixture_eq_owner_add_erase owner who]
  unfold quittingSingletonRefusalValue
  rw [mul_comm (1 - packet.mass owner),
    div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hmass))]

/-- Exact refusal amplification on a pinned active atom.  The gain from
refusing relative to the original singleton mixture is its source surplus
multiplied by the odds of the refused atom. -/
theorem refusal_sub_mixture_eq_mass_div_mul_surplus
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {owner : ι} (howner : 0 < packet.mass owner)
    (hmass : packet.mass owner < 1) :
    quittingSingletonRefusalValue reward packet.mass owner owner -
        quittingSingletonMixture reward packet.mass owner =
      packet.mass owner / (1 - packet.mass owner) *
        (quittingSingletonMixture reward packet.mass owner -
          packet.target owner) := by
  have hpinned := packet.positive_mass_pins_target owner howner
  rw [packet.singletonMixture_eq_owner_add_erase owner owner, hpinned]
  unfold quittingSingletonRefusalValue
  field_simp [sub_ne_zero.mpr (ne_of_gt hmass)]
  ring

end QuittingNormalizedSingletonSourcePacket

namespace QuittingCounterexampleRegime

/-- **Strict packet surplus.**  The packet forced by a counterexample regime
has an active owner whose delivered singleton mixture strictly exceeds its
pinned target.  Otherwise it is a complementary singleton mixture and the
existing circulation compiler produces a uniform-equilibrium payoff. -/
theorem exists_active_strictSingletonSurplus
    (regime : QuittingCounterexampleRegime reward) [Nonempty ι]
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∃ owner, 0 < packet.mass owner ∧
      packet.target owner <
        quittingSingletonMixture reward packet.mass owner := by
  by_contra hstrict
  push Not at hstrict
  have hactive : ∀ owner, 0 < packet.mass owner →
      quittingSingletonMixture reward packet.mass owner =
        reward (quittingSingletonTerminal owner) owner := by
    intro owner howner
    have heq : packet.target owner =
        quittingSingletonMixture reward packet.mass owner :=
      le_antisymm (packet.mix_ge_target owner)
        (hstrict owner howner)
    rw [← heq, packet.positive_mass_pins_target owner howner]
  obtain ⟨payoff, hpayoff⟩ :=
    exists_uniformEquilibriumPayoff_of_complementarySingletonMixture
      reward packet.mass packet.target packet.mass_nonneg packet.mass_sum
        packet.mix_ge_target hactive packet.solo_le_target
        packet.punishment_le_target
  exact regime.not_exists_uniformEquilibriumPayoff ⟨payoff, hpayoff⟩

/-- **Strict packet refusal.**  One positive-mass owner strictly prefers the
singleton delivery conditioned on refusing its own prescribed atom to both
the packet target and the unconditioned delivery.  The selected atom
necessarily has mass strictly below one. -/
theorem exists_active_strictSingletonRefusal
    (regime : QuittingCounterexampleRegime reward) [Nonempty ι]
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∃ owner, 0 < packet.mass owner ∧ packet.mass owner < 1 ∧
      packet.target owner < quittingSingletonMixture reward packet.mass owner ∧
      quittingSingletonMixture reward packet.mass owner <
        quittingSingletonRefusalValue reward packet.mass owner owner := by
  obtain ⟨owner, howner, hsurplus⟩ :=
    regime.exists_active_strictSingletonSurplus packet
  have hmass : packet.mass owner < 1 := by
    apply lt_of_le_of_ne (packet.mass_le_one owner)
    intro heq
    rw [packet.singletonMixture_eq_singleton_of_mass_eq_one heq owner,
      ← packet.positive_mass_pins_target owner howner] at hsurplus
    exact (lt_irrefl _ hsurplus)
  have hpinned := packet.positive_mass_pins_target owner howner
  have hsplit := packet.singletonMixture_eq_mass_mul_add_refusal hmass owner
  rw [← hpinned] at hsplit
  refine ⟨owner, howner, hmass, hsurplus, ?_⟩
  nlinarith

end QuittingCounterexampleRegime

end GameTheory
