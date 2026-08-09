/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacket
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeToggles

/-!
# Finite support consequences of the forced singleton packet

The normalized singleton source packet carried by a quitting counterexample
has two useful finite consequences.  First, every supported owner in a
nonsingleton support weakly prefers the singleton exit of some other supported
owner to its own pinned target.  Choosing such successors produces the finite
directed support graph on which later circulation or support-enlargement
arguments may operate.  This weak graph is not itself an equilibrium
compiler: outsider inequalities and equality strata remain separate.

Second, the counterexample's terminal margin reaches the packet twice: some
target coordinate is at least the margin, and a positive-mass singleton atom
already pays some coordinate at least that margin.  This is the direct finite
bridge between behavioral exploitability and the analytic packet.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingNormalizedSingletonSourcePacket

/-- The finite support of the packet's normalized singleton mass. -/
def support (packet : QuittingNormalizedSingletonSourcePacket reward) : Finset ι :=
  Finset.univ.filter fun owner => 0 < packet.mass owner

@[simp] theorem mem_support_iff
    (packet : QuittingNormalizedSingletonSourcePacket reward) (owner : ι) :
    owner ∈ packet.support ↔ 0 < packet.mass owner := by
  simp [support]

/-- Mass vanishes away from the positive support. -/
theorem mass_eq_zero_of_notMem_support
    (packet : QuittingNormalizedSingletonSourcePacket reward) {owner : ι}
    (howner : owner ∉ packet.support) :
    packet.mass owner = 0 := by
  have hnot : ¬ 0 < packet.mass owner := by
    simpa [mem_support_iff] using howner
  exact le_antisymm (le_of_not_gt hnot) (packet.mass_nonneg owner)

/-- The positive support retains all of the normalized mass. -/
theorem sum_support_mass
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∑ owner ∈ packet.support, packet.mass owner = 1 := by
  rw [← packet.mass_sum]
  apply Finset.sum_subset (Finset.subset_univ packet.support)
  intro owner _ howner
  exact packet.mass_eq_zero_of_notMem_support howner

/-- The support is nonempty because its nonnegative masses sum to one. -/
theorem support_nonempty
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    packet.support.Nonempty := by
  by_contra hempty
  have hsum := packet.sum_support_mass
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hsum
  simp at hsum

/-- Restricting a weighted singleton row to the positive support changes
nothing. -/
theorem sum_support_mul_singletonReward
    (packet : QuittingNormalizedSingletonSourcePacket reward) (who : ι) :
    ∑ owner ∈ packet.support,
        packet.mass owner * reward (quittingSingletonTerminal owner) who =
      quittingSingletonMixture reward packet.mass who := by
  unfold quittingSingletonMixture
  apply Finset.sum_subset (Finset.subset_univ packet.support)
  intro owner _ howner
  rw [packet.mass_eq_zero_of_notMem_support howner, zero_mul]

/-- Every supported row of a nonsingleton packet has a distinct supported
successor whose singleton outcome weakly beats that row's pinned target. -/
theorem exists_nonnegative_offDiagonal_on_support
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupport : packet.support.Nontrivial)
    {owner : ι} (howner : owner ∈ packet.support) :
    ∃ other ∈ packet.support, other ≠ owner ∧
      packet.target owner ≤
        reward (quittingSingletonTerminal other) owner := by
  have hownerMass : 0 < packet.mass owner :=
    (packet.mem_support_iff owner).mp howner
  have hpinned := packet.positive_mass_pins_target owner hownerMass
  have herase : (packet.support.erase owner).Nonempty :=
    hsupport.erase_nonempty
  have hweighted :
      ∑ other ∈ packet.support.erase owner,
          packet.mass other * packet.target owner ≤
        ∑ other ∈ packet.support.erase owner,
          packet.mass other *
            reward (quittingSingletonTerminal other) owner := by
    have hmix := packet.mix_ge_target owner
    rw [← packet.sum_support_mul_singletonReward owner] at hmix
    have hmassSplit := Finset.sum_erase_add
      (s := packet.support) (f := packet.mass) howner
    have hrewardSplit := Finset.sum_erase_add
      (s := packet.support)
      (f := fun other => packet.mass other *
        reward (quittingSingletonTerminal other) owner) howner
    have hmassSum := packet.sum_support_mass
    rw [hmassSum] at hmassSplit
    rw [← hpinned] at hrewardSplit
    rw [← Finset.sum_mul]
    have htargetSplit :
        packet.target owner =
          (∑ other ∈ packet.support.erase owner, packet.mass other) *
              packet.target owner +
            packet.mass owner * packet.target owner := by
      rw [← add_mul, hmassSplit, one_mul]
    calc
      (∑ other ∈ packet.support.erase owner, packet.mass other) *
            packet.target owner =
          packet.target owner - packet.mass owner * packet.target owner := by
            linarith
      _ ≤ (∑ other ∈ packet.support,
              packet.mass other *
                reward (quittingSingletonTerminal other) owner) -
            packet.mass owner * packet.target owner :=
          sub_le_sub_right hmix _
      _ = ∑ other ∈ packet.support.erase owner,
            packet.mass other *
              reward (quittingSingletonTerminal other) owner := by
          linarith
  obtain ⟨other, hother, hle⟩ :=
    Finset.exists_le_of_sum_le herase hweighted
  have hotherSupport : other ∈ packet.support :=
    Finset.mem_of_mem_erase hother
  have hotherNe : other ≠ owner := Finset.ne_of_mem_erase hother
  have hotherMass : 0 < packet.mass other :=
    (packet.mem_support_iff other).mp hotherSupport
  refine ⟨other, hotherSupport, hotherNe, ?_⟩
  exact le_of_mul_le_mul_left hle hotherMass

/-- Packet support is either a singleton or carries the successor relation
needed to choose a weak directed support cycle.  The pointwise form avoids
installing an arbitrary choice as canonical packet data. -/
theorem support_singleton_or_successors
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    (∃ owner, packet.support = {owner}) ∨
      ∀ owner ∈ packet.support,
        ∃ other ∈ packet.support, other ≠ owner ∧
          packet.target owner ≤
            reward (quittingSingletonTerminal other) owner := by
  by_cases hs : packet.support.Nontrivial
  · exact Or.inr fun owner howner =>
      packet.exists_nonnegative_offDiagonal_on_support
        hs howner
  · obtain ⟨owner, howner⟩ := packet.support_nonempty
    refine Or.inl ⟨owner, Finset.ext fun other => ?_⟩
    constructor
    · intro hother
      have : other = owner := by
        by_contra hne
        exact hs ⟨other, hother, owner, howner, hne⟩
      simp [this]
    · intro heq
      have hother : other = owner := by simpa using heq
      rw [hother]
      exact howner

/-- A chosen weak-preference successor on a nontrivial packet support.  The
definition is deliberately local to the packet graph; no strategic meaning
is assigned to the arbitrary choice. -/
noncomputable def weakPreferenceSuccessor
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupport : packet.support.Nontrivial) (owner : ι) : ι :=
  if howner : owner ∈ packet.support then
    Classical.choose
      (packet.exists_nonnegative_offDiagonal_on_support hsupport howner)
  else packet.support_nonempty.choose

theorem weakPreferenceSuccessor_mem
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupport : packet.support.Nontrivial) (owner : ι) :
    packet.weakPreferenceSuccessor hsupport owner ∈ packet.support := by
  by_cases howner : owner ∈ packet.support
  · simp only [weakPreferenceSuccessor, dif_pos howner]
    exact (Classical.choose_spec
      (packet.exists_nonnegative_offDiagonal_on_support hsupport howner)).1
  · simp only [weakPreferenceSuccessor, dif_neg howner]
    exact packet.support_nonempty.choose_spec

theorem weakPreferenceSuccessor_ne
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupport : packet.support.Nontrivial)
    {owner : ι} (howner : owner ∈ packet.support) :
    packet.weakPreferenceSuccessor hsupport owner ≠ owner := by
  simp only [weakPreferenceSuccessor, dif_pos howner]
  exact (Classical.choose_spec
    (packet.exists_nonnegative_offDiagonal_on_support hsupport howner)).2.1

theorem target_le_weakPreferenceSuccessor_reward
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupport : packet.support.Nontrivial)
    {owner : ι} (howner : owner ∈ packet.support) :
    packet.target owner ≤ reward
      (quittingSingletonTerminal
        (packet.weakPreferenceSuccessor hsupport owner)) owner := by
  simp only [weakPreferenceSuccessor, dif_pos howner]
  exact (Classical.choose_spec
    (packet.exists_nonnegative_offDiagonal_on_support hsupport howner)).2.2

/-- A nonsingleton packet support contains a finite closed orbit of weak
singleton preferences.  The returned interval is a closed directed walk;
one may erase repetitions to obtain a simple directed cycle.  Keeping the
orbit form avoids adding a separate finite-graph representation merely for
this consequence. -/
theorem exists_weakPreferenceClosedOrbit
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupport : packet.support.Nontrivial) :
    ∃ start stop : ℕ, start < stop ∧
      let successor := packet.weakPreferenceSuccessor hsupport
      let seed := packet.support_nonempty.choose
      (successor^[start]) seed = (successor^[stop]) seed ∧
      (∀ time,
        (successor^[time]) seed ∈ packet.support ∧
        successor ((successor^[time]) seed) ≠ (successor^[time]) seed ∧
        packet.target ((successor^[time]) seed) ≤
          reward (quittingSingletonTerminal
            (successor ((successor^[time]) seed)))
            ((successor^[time]) seed)) := by
  let successor := packet.weakPreferenceSuccessor hsupport
  let seed := packet.support_nonempty.choose
  have horbitMem : ∀ time, (successor^[time]) seed ∈ packet.support := by
    intro time
    induction time with
    | zero => exact packet.support_nonempty.choose_spec
    | succ time ih =>
        rw [Function.iterate_succ_apply']
        exact packet.weakPreferenceSuccessor_mem hsupport _
  obtain ⟨first, second, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun time : ℕ => (successor^[time]) seed)
  have hedge : ∀ time,
      successor ((successor^[time]) seed) ≠ (successor^[time]) seed ∧
        packet.target ((successor^[time]) seed) ≤
          reward (quittingSingletonTerminal
            (successor ((successor^[time]) seed)))
            ((successor^[time]) seed) := by
    intro time
    exact ⟨packet.weakPreferenceSuccessor_ne hsupport (horbitMem time),
      packet.target_le_weakPreferenceSuccessor_reward hsupport
        (horbitMem time)⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨first, second, hlt, heq, ?_⟩
    intro time
    exact ⟨horbitMem time, hedge time⟩
  · refine ⟨second, first, hgt, heq.symm, ?_⟩
    intro time
    exact ⟨horbitMem time, hedge time⟩

end QuittingNormalizedSingletonSourcePacket

namespace QuittingCounterexampleRegime

/-- The terminal margin is visible in a coordinate of every forced packet's
target. -/
theorem exists_terminalGap_le_packetTarget
    (regime : QuittingCounterexampleRegime reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∃ who, regime.terminalGap ≤ packet.target who := by
  obtain ⟨who, hgap⟩ := regime.exists_terminalGap_le_soloReward
  exact ⟨who, hgap.trans (packet.solo_le_target who)⟩

/-- A positive-mass singleton atom of every forced packet pays some player at
least the counterexample's terminal margin. -/
theorem exists_supportedSingleton_terminalGap
    (regime : QuittingCounterexampleRegime reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∃ who owner, 0 < packet.mass owner ∧
      regime.terminalGap ≤
        reward (quittingSingletonTerminal owner) who := by
  obtain ⟨who, hgap⟩ := regime.exists_terminalGap_le_packetTarget packet
  have hweighted :
      ∑ owner ∈ packet.support,
          packet.mass owner * regime.terminalGap ≤
        ∑ owner ∈ packet.support,
          packet.mass owner *
            reward (quittingSingletonTerminal owner) who := by
    rw [← Finset.sum_mul, packet.sum_support_mass,
      packet.sum_support_mul_singletonReward]
    simpa using hgap.trans (packet.mix_ge_target who)
  obtain ⟨owner, howner, hle⟩ :=
    Finset.exists_le_of_sum_le packet.support_nonempty hweighted
  have hmass : 0 < packet.mass owner :=
    (packet.mem_support_iff owner).mp howner
  refine ⟨who, owner, hmass, ?_⟩
  exact le_of_mul_le_mul_left hle hmass

end QuittingCounterexampleRegime

end GameTheory
