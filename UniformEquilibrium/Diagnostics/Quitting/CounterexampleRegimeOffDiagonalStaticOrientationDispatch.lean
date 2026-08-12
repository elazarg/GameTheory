/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOffDiagonalAtomSequenceDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNegativeVertexGerm
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlayerDeletion

/-!
# Static dispatch for the off-diagonal atom frontier

The singleton terminal orientation in the fixed-label rectangle frontier is
not an additional analytic seam.  Its owner satisfies the universal
counterexample-regime singleton restriction.  A strict incoming or outgoing
coalition toggle feeds the existing unstable-atomic-row theorem; otherwise
the owner has positive punishment value or can be deleted while preserving
the exact terminal exploitability gap.

After this handoff, a rectangle terminal has one of only four genuinely
different static orientations: it omits the observer, it is a strategically
dispatched observer singleton, it is an observer-containing collision with
strictly negative observer reward, or it is the already consumed positive
marked collision.  In particular the apparent zero-reward orientation is
impossible: the fixed positive atom forces both a nonzero reward and a strict
terminal-mass polarity.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A positive absorbing terminal-payoff atom has exactly the expected signed
mass polarity.  This is the complete static information present in an atom:
positive reward pairs with increased first-profile mass, and negative reward
pairs with decreased first-profile mass. -/
theorem positive_quittingTerminalPayoffDifferenceAtom_iff_signedMassPolarity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (terminal : {S : Finset ι // S.Nonempty}) :
    0 < quittingTerminalPayoffDifferenceAtom reward first second observer
        (some terminal) ↔
      (0 < reward terminal observer ∧
          quittingTerminalOutcomeMass reward second (some terminal) <
            quittingTerminalOutcomeMass reward first (some terminal)) ∨
        (reward terminal observer < 0 ∧
          quittingTerminalOutcomeMass reward first (some terminal) <
            quittingTerminalOutcomeMass reward second (some terminal)) := by
  unfold quittingTerminalPayoffDifferenceAtom
  simp only [quittingTerminalOutcomeReward]
  rw [mul_pos_iff]
  constructor
  · rintro (⟨hmass, hreward⟩ | ⟨hmass, hreward⟩)
    · exact Or.inl ⟨hreward, sub_pos.mp hmass⟩
    · exact Or.inr ⟨hreward, sub_neg.mp hmass⟩
  · rintro (⟨hreward, hmass⟩ | ⟨hreward, hmass⟩)
    · exact Or.inl ⟨sub_pos.mpr hmass, hreward⟩
    · exact Or.inr ⟨sub_neg.mpr hmass, hreward⟩

/-- A strict coalition insertion toggle together with the literal unstable
pure atomic row supplied by the positive terminal exploitability floor. -/
def HasQuittingStaticAtomicToggleHandoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ (owner : ι) (quitters : Finset ι) (hquitters : quitters.Nonempty),
    owner ∉ quitters ∧
      reward ⟨quitters, hquitters⟩ owner <
        reward
          ⟨insert owner quitters,
            Finset.insert_nonempty owner quitters⟩ owner ∧
      ∃ who, who ≠ owner ∧ ∃ deviation : PMF Bool,
        quittingRootExpectedPayoff reward 0
            (Function.update
              (QuittingSureSetOwnerRepair.quittingPureSetRoot
                (insert owner quitters)) who deviation) who >
          quittingRootExpectedPayoff reward 0
            (QuittingSureSetOwnerRepair.quittingPureSetRoot
              (insert owner quitters)) who

/-- Exact descent of the same terminal exploitability floor after deleting
one player. -/
def HasQuittingExactPlayerDeletionAtGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (gap : ℝ) : Prop :=
  Nonempty (QuittingDeletedPlayer owner) ∧
    HasTerminalExploitabilityGap
      (quittingDeletePlayerReward reward owner) gap ∧
    Fintype.card (QuittingDeletedPlayer owner) < Fintype.card ι

/-- The game-facing output attached to an observer singleton. -/
def HasQuittingSingletonStaticStrategicDispatch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (gap : ℝ) : Prop :=
  HasQuittingStaticAtomicToggleHandoff reward ∨
    0 < quittingPunishmentValue reward owner ∨
    HasQuittingExactPlayerDeletionAtGap reward owner gap

namespace QuittingCounterexampleRegime

/-- **Universal singleton static handoff.**  Every player in a counterexample
regime supplies an unstable atomic toggle row, a positive punishment value,
or an exact smaller-player counterexample with the same exploitability gap.

For an incoming singleton joiner, the atomic row is the pure pair consisting
of the singleton owner and the joiner.  For the no-incoming-join branch, the
standard singleton punishment moat gives either positive punishment or the
existing toggle/deletion dispatcher. -/
theorem singletonStaticStrategicDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) (owner : ι) :
    HasQuittingSingletonStaticStrategicDispatch reward owner
      regime.terminalGap := by
  classical
  rcases regime.strictJoiner_or_soloReward_lt_punishmentValue owner with
    hincoming | hsolo
  · left
    obtain ⟨joiner, hjoinerNe, hstrict⟩ := hincoming
    let quitters : Finset ι := {owner}
    have hquitters : quitters.Nonempty := by
      simp [quitters]
    have hjoiner : joiner ∉ quitters := by
      simp [quitters, hjoinerNe]
    have htoggle : reward ⟨quitters, hquitters⟩ joiner <
        reward
          ⟨insert joiner quitters,
            Finset.insert_nonempty joiner quitters⟩ joiner := by
      simpa [quitters, quittingSoloReward,
        quittingSingletonCollisionReward, Finset.pair_comm] using hstrict
    exact ⟨joiner, quitters, hquitters, hjoiner, htoggle,
      exists_outsider_atomicDeviation_of_strict_ownerToggle reward
        regime.terminalGap_pos regime.terminalExploitability joiner quitters
        hquitters hjoiner htoggle⟩
  · by_cases hchi : 0 < quittingPunishmentValue reward owner
    · exact Or.inr (Or.inl hchi)
    · have hchiLe : quittingPunishmentValue reward owner ≤ 0 :=
        le_of_not_gt hchi
      have hdispatch := exists_strict_owner_toggle_or_exact_playerDeletion
        reward owner regime.terminalGap_pos regime.terminalExploitability
          (by simpa [quittingSoloReward, quittingSingletonTerminal] using hsolo)
          hchiLe
      rcases strictToggle_or_playerDeletion_to_atomicHandoff reward
          regime.terminalGap_pos regime.terminalExploitability owner hdispatch
        with hatomic | hdelete
      · obtain ⟨quitters, hquitters, howner, htoggle, hatomic⟩ := hatomic
        exact Or.inl
          ⟨owner, quitters, hquitters, howner, htoggle, hatomic⟩
      · exact Or.inr (Or.inr hdelete)

end QuittingCounterexampleRegime

/-! ## Prescribed-atom orientation -/

/-- Every prescribed atom in the fixed-label sequence is positive. -/
theorem QuittingStoppingLawPrescribedAtomSequence.atom_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawPrescribedAtomSequence frontier) (n : ℕ) :
    0 < quittingTerminalPayoffDifferenceAtom reward
      (frontier.profiles (frontier.subseq (packet.rank n)))
      (Function.update
        (frontier.profiles (frontier.subseq (packet.rank n))) packet.mover.1
        (frontier.bestResponse packet.mover
          (frontier.subseq (packet.rank n))))
      packet.observer (some packet.terminal) := by
  have hbound := packet.atom_bound n
  have hcard : 0 < (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
    positivity
  have hproduct : 0 <
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (frontier.profiles (frontier.subseq (packet.rank n)))
          (Function.update
            (frontier.profiles (frontier.subseq (packet.rank n)))
            packet.mover.1
            (frontier.bestResponse packet.mover
              (frontier.subseq (packet.rank n))))
          packet.observer (some packet.terminal) :=
    (div_pos packet.charge_pos (by norm_num)).trans_le hbound
  rw [mul_comm] at hproduct
  exact pos_of_mul_pos_left hproduct hcard.le

/-- The prescribed branch has a fixed nonzero reward sign and the opposite
strict mass orientation at every rank.  This is sharp but not yet a strategic
certificate: it still compares two mover deviations rather than either one
against the prescribed baseline. -/
theorem QuittingStoppingLawPrescribedAtomSequence.signedMassPolarity
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawPrescribedAtomSequence frontier) (n : ℕ) :
    (0 < reward packet.terminal packet.observer ∧
        quittingTerminalOutcomeMass reward
            (Function.update
              (frontier.profiles (frontier.subseq (packet.rank n)))
              packet.mover.1
              (frontier.bestResponse packet.mover
                (frontier.subseq (packet.rank n))))
            (some packet.terminal) <
          quittingTerminalOutcomeMass reward
            (frontier.profiles (frontier.subseq (packet.rank n)))
            (some packet.terminal)) ∨
      (reward packet.terminal packet.observer < 0 ∧
        quittingTerminalOutcomeMass reward
            (frontier.profiles (frontier.subseq (packet.rank n)))
            (some packet.terminal) <
          quittingTerminalOutcomeMass reward
            (Function.update
              (frontier.profiles (frontier.subseq (packet.rank n)))
              packet.mover.1
              (frontier.bestResponse packet.mover
                (frontier.subseq (packet.rank n))))
            (some packet.terminal)) := by
  exact
    (positive_quittingTerminalPayoffDifferenceAtom_iff_signedMassPolarity
      reward (frontier.profiles (frontier.subseq (packet.rank n)))
      (Function.update
        (frontier.profiles (frontier.subseq (packet.rank n))) packet.mover.1
        (frontier.bestResponse packet.mover
          (frontier.subseq (packet.rank n))))
      packet.observer packet.terminal).1 (packet.atom_pos n)

/-! ## Rectangle orientation refinement -/

/-- The fixed rectangle terminal is an observer singleton and its table
owner has already been routed to a strategic consumer. -/
def HasQuittingStoppingLawSingletonStrategicOrientation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) : Prop :=
  packet.observer ∈ packet.terminal.val ∧
    packet.terminal.val.card = 1 ∧
    HasQuittingSingletonStaticStrategicDispatch reward packet.observer
      regime.terminalGap

/-- The remaining non-marked collision orientation.  The reward is strictly,
not merely weakly, negative. -/
def HasQuittingStoppingLawNegativeTargetCollision
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) : Prop :=
  packet.observer ∈ packet.terminal.val ∧
    1 < packet.terminal.val.card ∧
    reward packet.terminal packet.observer < 0

/-- Every fixed rectangle atom in the packet is strictly positive. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.atom_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) :
    0 < quittingTerminalPayoffDifferenceAtom reward
      (Function.update
        (Function.update
          (frontier.profiles (frontier.subseq (packet.rank n))) packet.mover.1
          (frontier.bestResponse packet.mover
            (frontier.subseq (packet.rank n))))
        packet.observer
        (quittingPureTimeBehaviorStrategy reward packet.observer
          (packet.quitTime n)))
      (Function.update
        (Function.update
          (frontier.profiles (frontier.subseq (packet.rank n))) packet.mover.1
          (frontier.profiles (frontier.subseq (packet.rank n)) packet.mover.1))
        packet.observer
        (quittingPureTimeBehaviorStrategy reward packet.observer
          (packet.quitTime n)))
      packet.observer (some packet.terminal) := by
  have hbound := packet.atom_bound n
  have hcard : 0 < (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
    positivity
  have hproduct : 0 <
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (Function.update
            (Function.update
              (frontier.profiles (frontier.subseq (packet.rank n)))
              packet.mover.1
              (frontier.bestResponse packet.mover
                (frontier.subseq (packet.rank n))))
            packet.observer
            (quittingPureTimeBehaviorStrategy reward packet.observer
              (packet.quitTime n)))
          (Function.update
            (Function.update
              (frontier.profiles (frontier.subseq (packet.rank n)))
              packet.mover.1
              (frontier.profiles (frontier.subseq (packet.rank n))
                packet.mover.1))
            packet.observer
            (quittingPureTimeBehaviorStrategy reward packet.observer
              (packet.quitTime n)))
          packet.observer (some packet.terminal) :=
    (div_pos packet.charge_pos (by norm_num)).trans_le hbound
  rw [mul_comm] at hproduct
  exact pos_of_mul_pos_left hproduct hcard.le

/-- A weakly nonpositive observer reward on a positive fixed rectangle atom
is necessarily strictly negative, and the target mover continuation strictly
reduces the mass of that same terminal coalition. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.negativeReward_massPolarity
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) (hreward : reward packet.terminal packet.observer ≤ 0) :
    reward packet.terminal packet.observer < 0 ∧
      quittingTerminalOutcomeMass reward
          (Function.update
            (Function.update
              (frontier.profiles (frontier.subseq (packet.rank n)))
              packet.mover.1
              (frontier.bestResponse packet.mover
                (frontier.subseq (packet.rank n))))
            packet.observer
            (quittingPureTimeBehaviorStrategy reward packet.observer
              (packet.quitTime n)))
          (some packet.terminal) <
        quittingTerminalOutcomeMass reward
          (Function.update
            (Function.update
              (frontier.profiles (frontier.subseq (packet.rank n)))
              packet.mover.1
              (frontier.profiles (frontier.subseq (packet.rank n))
                packet.mover.1))
            packet.observer
            (quittingPureTimeBehaviorStrategy reward packet.observer
              (packet.quitTime n)))
          (some packet.terminal) := by
  let targetProfile := Function.update
    (Function.update
      (frontier.profiles (frontier.subseq (packet.rank n))) packet.mover.1
      (frontier.bestResponse packet.mover
        (frontier.subseq (packet.rank n))))
    packet.observer
    (quittingPureTimeBehaviorStrategy reward packet.observer
      (packet.quitTime n))
  let sourceProfile := Function.update
    (Function.update
      (frontier.profiles (frontier.subseq (packet.rank n))) packet.mover.1
      (frontier.profiles (frontier.subseq (packet.rank n)) packet.mover.1))
    packet.observer
    (quittingPureTimeBehaviorStrategy reward packet.observer
      (packet.quitTime n))
  have hatom : 0 < quittingTerminalPayoffDifferenceAtom reward targetProfile
      sourceProfile packet.observer (some packet.terminal) := by
    simpa only [targetProfile, sourceProfile] using packet.atom_pos n
  have hrewardStrict : reward packet.terminal packet.observer < 0 := by
    rcases lt_or_eq_of_le hreward with hlt | heq
    · exact hlt
    · unfold quittingTerminalPayoffDifferenceAtom at hatom
      simp only [quittingTerminalOutcomeReward] at hatom
      rw [heq, mul_zero] at hatom
      exact False.elim (lt_irrefl 0 hatom)
  refine ⟨hrewardStrict, ?_⟩
  by_contra hnot
  have hmass : quittingTerminalOutcomeMass reward sourceProfile
        (some packet.terminal) ≤
      quittingTerminalOutcomeMass reward targetProfile
        (some packet.terminal) := le_of_not_gt hnot
  have hnonpos :
      (quittingTerminalOutcomeMass reward targetProfile
          (some packet.terminal) -
        quittingTerminalOutcomeMass reward sourceProfile
          (some packet.terminal)) *
          reward packet.terminal packet.observer ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hmass) hreward
  unfold quittingTerminalPayoffDifferenceAtom at hatom
  simp only [quittingTerminalOutcomeReward] at hatom
  exact (not_lt_of_ge hnonpos) hatom

/-- **Sharp refinement of the three open rectangle orientations.**  The
singleton branch is routed to an existing strategic consumer.  The only
unconsumed static cases are observer absence and a strictly negative
observer-containing collision. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.refineOpenOrientation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hopen : HasQuittingStoppingLawOpenRectangleOrientation packet) :
    packet.observer ∉ packet.terminal.val ∨
      HasQuittingStoppingLawSingletonStrategicOrientation packet ∨
      HasQuittingStoppingLawNegativeTargetCollision packet := by
  classical
  by_cases hobserver : packet.observer ∈ packet.terminal.val
  · by_cases hsingleton : packet.terminal.val.card = 1
    · exact Or.inr (Or.inl
        ⟨hobserver, hsingleton,
          regime.singletonStaticStrategicDispatch packet.observer⟩)
    · right
      right
      have hcardPos : 0 < packet.terminal.val.card :=
        Finset.card_pos.mpr packet.terminal.property
      have hcollision : 1 < packet.terminal.val.card := by omega
      have hreward : reward packet.terminal packet.observer ≤ 0 := by
        rcases hopen with habsent | hsingleton' | hreward
        · exact False.elim (habsent hobserver)
        · exact False.elim (hsingleton hsingleton')
        · exact hreward
      exact ⟨hobserver, hcollision,
        (packet.negativeReward_massPolarity 0 hreward).1⟩
  · exact Or.inl hobserver

/-- **Exhaustive static frontier after the singleton handoff.**  The former
three-way open rectangle branch has been reduced to observer absence or a
strictly negative collision, plus the named singleton strategic dispatch.
The positive collision remains connected to the marked-tail consumer. -/
theorem QuittingCounterexampleStoppingLawFrontier.exists_prescribed_or_staticRectangleDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    Nonempty (QuittingStoppingLawPrescribedAtomSequence frontier) ∨
      ∃ packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier,
        packet.observer ∉ packet.terminal.val ∨
          HasQuittingStoppingLawSingletonStrategicOrientation packet ∨
          HasQuittingStoppingLawNegativeTargetCollision packet ∨
          HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch packet
            ((packet.charge / 4) /
              ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
                quittingRewardBound reward)) := by
  classical
  rcases frontier.exists_prescribedAtomSequence_or_openRectangleOrientation_or_markedTailDispatch
      with hprescribed | ⟨packet, hopen | hmarked⟩
  · exact Or.inl hprescribed
  · refine Or.inr ⟨packet, ?_⟩
    rcases packet.refineOpenOrientation hopen with habsent | hsingleton |
      hnegative
    · exact Or.inl habsent
    · exact Or.inr (Or.inl hsingleton)
    · exact Or.inr (Or.inr (Or.inl hnegative))
  · exact Or.inr ⟨packet, Or.inr (Or.inr (Or.inr hmarked))⟩

end GameTheory
