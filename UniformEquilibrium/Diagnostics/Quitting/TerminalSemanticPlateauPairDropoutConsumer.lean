/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauFractionalResetDropout
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNegativeVertexGerm

/-!
# Consuming the pair-to-singleton fractional-reset dropout

The literal pair-to-singleton crossing produced by a finite fractional reset
word lands on a positive-mass singleton cylinder.  In a quitting
counterexample that singleton has only two honest table-level outcomes.

* Its owner's singleton reward lies below the negated counterexample gap.  If
  there is no strict singleton joiner, the negative-vertex theorem also puts
  the punishment value strictly above that reward.
* A distinct outsider strictly gains by joining the singleton.  Making that
  outsider pure Quit routes the positive singleton cylinder to a positive
  overlapping pair cylinder.

The capstone retains the literal reset prefix, the roots immediately before
and after the dropout, both positive routed masses, and the exact pair and
singleton identities.  The final outsider update is a static pure endpoint
replacement.  It is not asserted to be a Nash root, a Bellman successor, or
the next move of the fractional-reset word.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleRegime

/-- A positive-mass singleton in a counterexample either belongs to the
negative punishment-moat branch or admits a literal positive-mass
overlapping-pair replacement by a strict outsider joiner.

When the singleton reward lies above the negated counterexample gap, the
join improvement retains the full quantitative terminal-gap margin.  In the
lower singleton stratum the selected joiner, if present, is only asserted to
be strict; otherwise the negative-vertex punishment moat is returned. -/
theorem negativeMoat_or_positive_pairReplacement
    (regime : QuittingCounterexampleRegime reward)
    (owner : ι) (root : ι → PMF Bool)
    (hmass : 0 < quittingRootCoalitionMass root ({owner} : Finset ι)) :
    (quittingSoloReward reward owner owner ≤ -regime.terminalGap ∧
        quittingSoloReward reward owner owner <
          quittingPunishmentValue reward owner) ∨
      ∃ outsider, outsider ≠ owner ∧
        quittingSoloReward reward owner outsider <
          quittingSingletonCollisionReward reward owner outsider ∧
        (-regime.terminalGap < quittingSoloReward reward owner owner →
          quittingSoloReward reward owner outsider + regime.terminalGap ≤
            quittingSingletonCollisionReward reward owner outsider) ∧
        0 < quittingRootCoalitionMass
          (Function.update root outsider (PMF.pure true))
          ({owner, outsider} : Finset ι) := by
  have routedMassPos : ∀ outsider, outsider ≠ owner →
      0 < quittingRootCoalitionMass
        (Function.update root outsider (PMF.pure true))
        ({owner, outsider} : Finset ι) := by
    intro outsider hne
    have hroute := quittingRootCoalitionMass_le_pureEndpointRouted
      root ({owner} : Finset ι) outsider true
    have hrouted :
        quittingPureEndpointRoutedCoalition ({owner} : Finset ι)
            outsider true = {owner, outsider} := by
      ext player
      simp [or_comm]
    rw [hrouted] at hroute
    exact hmass.trans_le hroute
  by_cases hnegative :
      quittingSoloReward reward owner owner ≤ -regime.terminalGap
  · rcases regime.strictJoiner_or_soloReward_lt_punishmentValue owner with
      hjoin | hmoat
    · obtain ⟨outsider, hne, hstrict⟩ := hjoin
      exact Or.inr ⟨outsider, hne, hstrict, by
        intro habove
        linarith, routedMassPos outsider hne⟩
    · exact Or.inl ⟨hnegative, hmoat⟩
  · have habove : -regime.terminalGap <
        quittingSoloReward reward owner owner := lt_of_not_ge hnegative
    obtain ⟨outsider, hne, hmargin⟩ := regime.exists_collision_gain habove
    exact Or.inr ⟨outsider, hne, by
      linarith [regime.terminalGap_pos], fun _ => hmargin,
      routedMassPos outsider hne⟩

end QuittingCounterexampleRegime

/-! ## The literal dropout consumer -/

/-- **Pair dropout to negative vertex or overlapping pair replacement.**

Suppose a finite fractional endpoint word Nashifies a positive collision
cylinder over a positive-debt minimum terminal-semantic tail.  At the
resulting pair-to-singleton dropout, retain the actual prefix root, the pure
member-Continue update, and positive mass on both cylinders.  The surviving
singleton then either enters the quantitatively negative punishment-moat
branch or has a strict outsider joiner whose literal pure-Quit update carries
positive mass on an overlapping pair.

The outsider update is only a static, table-certified endpoint replacement;
no chronological or Bellman compatibility is claimed. -/
theorem QuittingCounterexampleRegime.exists_negativeMoat_or_pairReplacement_of_dropout
    (regime : QuittingCounterexampleRegime reward)
    (minimum : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (moves : List (QuittingFractionalEndpointMove ι))
    (terminal : {S : Finset ι // S.Nonempty}) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hcollision : 1 < terminal.val.card)
    (hmass : 0 < quittingRootCoalitionMass root terminal.val)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hfinalDefect : quittingRootTotalNashDefect reward minimum.1
      (quittingFractionalEndpointMoves moves root) = 0) :
    ∃ before move after beforeRoot afterRoot beforeCoalition afterCoalition
        owner,
      moves = before ++ move :: after ∧
        beforeRoot = quittingFractionalEndpointMoves before root ∧
        afterRoot = move.apply beforeRoot ∧
        beforeCoalition =
          quittingFractionalEndpointTrackedCoalition before terminal.val ∧
        afterCoalition = move.nextTrackedCoalition beforeCoalition ∧
        move.weight = 1 ∧ move.who ∈ beforeCoalition ∧
        move.action = false ∧
        beforeCoalition.card = 2 ∧
        afterCoalition = beforeCoalition.erase move.who ∧
        afterCoalition = {owner} ∧
        beforeCoalition = insert move.who {owner} ∧
        move.who ≠ owner ∧
        afterRoot = Function.update beforeRoot move.who (PMF.pure false) ∧
        0 < quittingRootCoalitionMass beforeRoot beforeCoalition ∧
        0 < quittingRootCoalitionMass afterRoot afterCoalition ∧
        ((quittingSoloReward reward owner owner ≤ -regime.terminalGap ∧
            quittingSoloReward reward owner owner <
              quittingPunishmentValue reward owner) ∨
          ∃ outsider replacementRoot replacementCoalition,
            outsider ≠ owner ∧
              replacementRoot =
                Function.update afterRoot outsider (PMF.pure true) ∧
              replacementCoalition = insert outsider afterCoalition ∧
              replacementCoalition = {owner, outsider} ∧
              afterCoalition ⊂ replacementCoalition ∧
              replacementCoalition.card = 2 ∧
              quittingSoloReward reward owner outsider <
                quittingSingletonCollisionReward reward owner outsider ∧
              (-regime.terminalGap <
                    quittingSoloReward reward owner owner →
                quittingSoloReward reward owner outsider +
                    regime.terminalGap ≤
                  quittingSingletonCollisionReward reward owner outsider) ∧
              0 < quittingRootCoalitionMass replacementRoot
                replacementCoalition) := by
  obtain ⟨before, move, after, beforeCoalition, afterCoalition,
      hsplit, hbeforeCoalition, hafterCoalition, hfull, hmember, hcontinue,
      hbeforeCard, hafterErase, hafterCard, hbeforeMass, hafterMass⟩ :=
    exists_positive_pair_to_singleton_dropout_of_finalDefect_eq_zero
      reward minimum root moves terminal hM hreward hminimumCarrier hminimum
        hcollision hmass hminimumDebt hfinalDefect
  obtain ⟨owner, hsingleton⟩ := Finset.card_eq_one.mp hafterCard
  let beforeRoot := quittingFractionalEndpointMoves before root
  let afterRoot := move.apply beforeRoot
  have hbeforePair : beforeCoalition = insert move.who {owner} := by
    calc
      beforeCoalition = insert move.who (beforeCoalition.erase move.who) :=
        (Finset.insert_erase hmember).symm
      _ = insert move.who afterCoalition := by rw [← hafterErase]
      _ = insert move.who {owner} := by rw [hsingleton]
  have hdropperNe : move.who ≠ owner := by
    have hnotAfter : move.who ∉ afterCoalition := by
      rw [hafterErase]
      simp
    rw [hsingleton] at hnotAfter
    simpa using hnotAfter
  have hafterRootUpdate :
      afterRoot = Function.update beforeRoot move.who (PMF.pure false) := by
    rw [show afterRoot = move.apply beforeRoot by rfl]
    simpa [hcontinue] using
      move.apply_eq_update_pure_of_weight_eq_one beforeRoot hfull
  have hbeforeMass' :
      0 < quittingRootCoalitionMass beforeRoot beforeCoalition := by
    simpa [beforeRoot] using hbeforeMass
  have hafterMass' :
      0 < quittingRootCoalitionMass afterRoot afterCoalition := by
    simpa [afterRoot, beforeRoot] using hafterMass
  have hsingletonMass :
      0 < quittingRootCoalitionMass afterRoot ({owner} : Finset ι) := by
    simpa [hsingleton] using hafterMass'
  rcases regime.negativeMoat_or_positive_pairReplacement owner afterRoot
      hsingletonMass with hnegative | hreplacement
  · exact ⟨before, move, after, beforeRoot, afterRoot, beforeCoalition,
      afterCoalition, owner, hsplit, rfl, rfl, hbeforeCoalition,
      hafterCoalition, hfull, hmember, hcontinue, hbeforeCard, hafterErase,
      hsingleton, hbeforePair, hdropperNe, hafterRootUpdate, hbeforeMass',
      hafterMass', Or.inl hnegative⟩
  · obtain ⟨outsider, houtsiderNe, hstrict, hmargin, hreplacedMass⟩ :=
      hreplacement
    let replacementRoot :=
      Function.update afterRoot outsider (PMF.pure true)
    let replacementCoalition := insert outsider afterCoalition
    have hreplacementPair : replacementCoalition = {owner, outsider} := by
      dsimp [replacementCoalition]
      rw [hsingleton]
      ext player
      simp [or_comm]
    have hreplacementCard : replacementCoalition.card = 2 := by
      rw [hreplacementPair]
      exact Finset.card_pair houtsiderNe.symm
    have hproper : afterCoalition ⊂ replacementCoalition := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · exact Finset.subset_insert outsider afterCoalition
      · intro heq
        have hcardEq := congrArg Finset.card heq
        rw [hafterCard, hreplacementCard] at hcardEq
        omega
    have hreplacedMass' :
        0 < quittingRootCoalitionMass replacementRoot
          replacementCoalition := by
      simpa [replacementRoot, hreplacementPair] using hreplacedMass
    exact ⟨before, move, after, beforeRoot, afterRoot, beforeCoalition,
      afterCoalition, owner, hsplit, rfl, rfl, hbeforeCoalition,
      hafterCoalition, hfull, hmember, hcontinue, hbeforeCard, hafterErase,
      hsingleton, hbeforePair, hdropperNe, hafterRootUpdate, hbeforeMass',
      hafterMass', Or.inr ⟨outsider, replacementRoot,
        replacementCoalition, houtsiderNe, rfl, rfl, hreplacementPair,
        hproper, hreplacementCard, hstrict, hmargin, hreplacedMass'⟩⟩

end GameTheory
