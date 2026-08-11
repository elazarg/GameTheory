/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauFractionalResetFloor

/-!
# Tracking collision support through finite fractional resets

Strictly fractional endpoint moves retain the tracked coalition.
A unit-weight move instead routes it across the corresponding Boolean-cube
edge.  Iterating this literal rule gives a positive-mass coalition at the
final product root.

Against a positive-debt minimum tail, zero final total Nash defect forbids
that final coalition from remaining a collision.  Since one routed endpoint
move changes coalition cardinality by at most one, every such finite reset
attempt must contain an exact transition

`two-player collision -> singleton`

at a unit-weight member-Continue move.  The theorem retains the actual root
before the move, the actual pure-updated root after it, and positive mass on
both routed cylinders.  It makes no return, recurrence, or chronology claim.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A strict fractional move keeps the tracked coalition; a full move routes
it to agree with the new pure endpoint. -/
def QuittingFractionalEndpointMove.nextTrackedCoalition
    (move : QuittingFractionalEndpointMove ι) (coalition : Finset ι) :
    Finset ι :=
  if move.weight = 1 then
    quittingPureEndpointRoutedCoalition coalition move.who move.action
  else coalition

/-- Coalition obtained by following the literal routing rule through a
finite reset list. -/
def quittingFractionalEndpointTrackedCoalition :
    List (QuittingFractionalEndpointMove ι) → Finset ι → Finset ι
  | [], coalition => coalition
  | move :: moves, coalition =>
      quittingFractionalEndpointTrackedCoalition moves
        (move.nextTrackedCoalition coalition)

/-- One move preserves positive mass on its tracked coalition.  Strict moves
use the positive `1 - weight` retention factor; full moves use exact pure
endpoint routing. -/
theorem QuittingFractionalEndpointMove.coalitionMass_pos_nextTracked
    (move : QuittingFractionalEndpointMove ι)
    (root : ι → PMF Bool) (coalition : Finset ι)
    (hmass : 0 < quittingRootCoalitionMass root coalition) :
    0 < quittingRootCoalitionMass (move.apply root)
      (move.nextTrackedCoalition coalition) := by
  by_cases hfull : move.weight = 1
  · have hroute := quittingRootCoalitionMass_le_pureEndpointRouted
      root coalition move.who move.action
    have happly := move.apply_eq_update_pure_of_weight_eq_one root hfull
    rw [happly] at *
    simpa [QuittingFractionalEndpointMove.nextTrackedCoalition, hfull] using
      hmass.trans_le hroute
  · have hstrict : move.weight < 1 :=
      lt_of_le_of_ne move.weight_le_one hfull
    have hretain :=
      one_sub_mul_quittingRootCoalitionMass_le_partialEndpointRoot
        root move.who move.action move.weight move.weight_nonneg
          move.weight_le_one coalition
    have hpositive : 0 < (1 - move.weight) *
        quittingRootCoalitionMass root coalition :=
      mul_pos (sub_pos.mpr hstrict) hmass
    simpa [QuittingFractionalEndpointMove.nextTrackedCoalition, hfull,
      QuittingFractionalEndpointMove.apply] using
        hpositive.trans_le hretain

/-- Positive coalition mass survives along the entire tracked finite route. -/
theorem quittingFractionalEndpointTrackedCoalition_mass_pos
    (moves : List (QuittingFractionalEndpointMove ι))
    (root : ι → PMF Bool) (coalition : Finset ι)
    (hmass : 0 < quittingRootCoalitionMass root coalition) :
    0 < quittingRootCoalitionMass
      (quittingFractionalEndpointMoves moves root)
      (quittingFractionalEndpointTrackedCoalition moves coalition) := by
  induction moves generalizing root coalition with
  | nil => simpa [quittingFractionalEndpointMoves,
      quittingFractionalEndpointTrackedCoalition] using hmass
  | cons move moves ih =>
      rw [quittingFractionalEndpointMoves,
        quittingFractionalEndpointTrackedCoalition]
      exact ih (root := move.apply root)
        (coalition := move.nextTrackedCoalition coalition)
        (move.coalitionMass_pos_nextTracked root coalition hmass)

/-! ## The unique downward cardinal crossing -/

omit [Fintype ι] in
/-- If one routed step starts above singleton cardinality and ends at or
below it, then it is exactly a full member-Continue dropout from cardinality
two to cardinality one. -/
theorem QuittingFractionalEndpointMove.pair_dropout_of_card_crossing
    (move : QuittingFractionalEndpointMove ι) (coalition : Finset ι)
    (hbefore : 1 < coalition.card)
    (hafter : ¬ 1 < (move.nextTrackedCoalition coalition).card) :
    move.weight = 1 ∧ move.who ∈ coalition ∧ move.action = false ∧
      coalition.card = 2 ∧
      (move.nextTrackedCoalition coalition).card = 1 := by
  by_cases hfull : move.weight = 1
  · by_cases hmem : move.who ∈ coalition
    · cases haction : move.action
      · have hnext : move.nextTrackedCoalition coalition =
            coalition.erase move.who := by
          simp [QuittingFractionalEndpointMove.nextTrackedCoalition,
            hfull, haction]
        have hcard := Finset.card_erase_of_mem hmem
        have hcoalitionCard : coalition.card = 2 := by
          rw [hnext, hcard] at hafter
          omega
        have hnextCard : (move.nextTrackedCoalition coalition).card = 1 := by
          rw [hnext, hcard, hcoalitionCard]
        exact ⟨hfull, hmem, rfl, hcoalitionCard, hnextCard⟩
      · have hnext : move.nextTrackedCoalition coalition = coalition := by
          simp [QuittingFractionalEndpointMove.nextTrackedCoalition,
            hfull, haction, hmem]
        rw [hnext] at hafter
        exact (hafter hbefore).elim
    · cases haction : move.action
      · have hnext : move.nextTrackedCoalition coalition = coalition := by
          simp [QuittingFractionalEndpointMove.nextTrackedCoalition,
            hfull, haction, hmem]
        rw [hnext] at hafter
        exact (hafter hbefore).elim
      · have hnext : move.nextTrackedCoalition coalition =
            insert move.who coalition := by
          simp [QuittingFractionalEndpointMove.nextTrackedCoalition,
            hfull, haction]
        have hsubset : coalition ⊆ insert move.who coalition :=
          Finset.subset_insert move.who coalition
        have hcardLe : coalition.card ≤ (insert move.who coalition).card :=
          Finset.card_le_card hsubset
        rw [hnext] at hafter
        exact (hafter (hbefore.trans_le hcardLe)).elim
  · have hnext : move.nextTrackedCoalition coalition = coalition := by
      simp [QuittingFractionalEndpointMove.nextTrackedCoalition, hfull]
    rw [hnext] at hafter
    exact (hafter hbefore).elim

omit [Fintype ι] in
/-- A finite tracked coalition path which starts above singleton cardinality
and ends at or below it contains an exact pair-to-singleton full dropout. -/
theorem exists_pair_dropout_of_fractionalEndpointTracked_card_crossing
    (moves : List (QuittingFractionalEndpointMove ι))
    (coalition : Finset ι)
    (hstart : 1 < coalition.card)
    (hfinal : ¬ 1 <
      (quittingFractionalEndpointTrackedCoalition moves coalition).card) :
    ∃ before move after beforeCoalition afterCoalition,
      moves = before ++ move :: after ∧
        beforeCoalition =
          quittingFractionalEndpointTrackedCoalition before coalition ∧
        afterCoalition = move.nextTrackedCoalition beforeCoalition ∧
        move.weight = 1 ∧ move.who ∈ beforeCoalition ∧
        move.action = false ∧ beforeCoalition.card = 2 ∧
        afterCoalition.card = 1 := by
  induction moves generalizing coalition with
  | nil =>
      simp [quittingFractionalEndpointTrackedCoalition] at hfinal
      omega
  | cons first moves ih =>
      let next := first.nextTrackedCoalition coalition
      by_cases hnext : 1 < next.card
      · have htailFinal : ¬ 1 <
          (quittingFractionalEndpointTrackedCoalition moves next).card := by
          simpa [quittingFractionalEndpointTrackedCoalition, next] using hfinal
        obtain ⟨before, move, after, beforeCoalition, afterCoalition,
            hsplit, hbeforeCoalition, hafterCoalition, hfull, hmem,
            haction, hbeforeCard, hafterCard⟩ :=
          ih next hnext htailFinal
        refine ⟨first :: before, move, after, beforeCoalition,
          afterCoalition, ?_, ?_, hafterCoalition, hfull, hmem, haction,
          hbeforeCard, hafterCard⟩
        · simp [hsplit]
        · rw [hbeforeCoalition]
          simp [quittingFractionalEndpointTrackedCoalition, next]
      · have hcross := first.pair_dropout_of_card_crossing
          coalition hstart hnext
        exact ⟨[], first, moves, coalition,
          first.nextTrackedCoalition coalition, by simp,
          by simp [quittingFractionalEndpointTrackedCoalition], rfl,
          hcross.1, hcross.2.1, hcross.2.2.1,
          hcross.2.2.2.1, hcross.2.2.2.2⟩

/-! ## Minimum-tail consumer -/

/-- **Every zero-defect finite reset attempt crosses a pair dropout.**

Starting from any positive collision cylinder over a positive-debt minimum
tail, track the cylinder through strict retention and full pure routing.  If
the final product root has zero total Nash defect, the final tracked cylinder
cannot still be a collision.  Consequently some full move drops a member of
an exact two-player collision, producing a positive singleton cylinder.

The roots and masses immediately before and after that move are the literal
ones generated by the reset prefix.  The remaining suffix is unconstrained. -/
theorem exists_positive_pair_to_singleton_dropout_of_finalDefect_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
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
    ∃ before move after beforeCoalition afterCoalition,
      moves = before ++ move :: after ∧
        beforeCoalition =
          quittingFractionalEndpointTrackedCoalition before terminal.val ∧
        afterCoalition = move.nextTrackedCoalition beforeCoalition ∧
        move.weight = 1 ∧ move.who ∈ beforeCoalition ∧
        move.action = false ∧ beforeCoalition.card = 2 ∧
        afterCoalition = beforeCoalition.erase move.who ∧
        afterCoalition.card = 1 ∧
        0 < quittingRootCoalitionMass
          (quittingFractionalEndpointMoves before root) beforeCoalition ∧
        0 < quittingRootCoalitionMass
          (move.apply (quittingFractionalEndpointMoves before root))
            afterCoalition := by
  let finalCoalition :=
    quittingFractionalEndpointTrackedCoalition moves terminal.val
  have hfinalMass : 0 < quittingRootCoalitionMass
      (quittingFractionalEndpointMoves moves root) finalCoalition := by
    exact quittingFractionalEndpointTrackedCoalition_mass_pos
      moves root terminal.val hmass
  have hfinalNotCollision : ¬ 1 < finalCoalition.card := by
    intro hfinalCollision
    let finalTerminal : {S : Finset ι // S.Nonempty} :=
      ⟨finalCoalition, Finset.card_pos.mp (by omega)⟩
    have hfloor :=
      quittingRootCoalitionMass_mul_minimumDebt_le_tailExcess_add_defect
        reward minimum minimum
          (quittingFractionalEndpointMoves moves root) finalTerminal
          hM hreward hminimumCarrier hminimum hminimumCarrier
          hfinalCollision
    have hleft : 0 < quittingRootCoalitionMass
        (quittingFractionalEndpointMoves moves root) finalCoalition *
          quittingTerminalSemanticDebtSum minimum :=
      mul_pos hfinalMass hminimumDebt
    change quittingRootCoalitionMass
        (quittingFractionalEndpointMoves moves root) finalCoalition *
          quittingTerminalSemanticDebtSum minimum ≤ _ at hfloor
    rw [hfinalDefect] at hfloor
    norm_num at hfloor
    linarith
  obtain ⟨before, move, after, beforeCoalition, afterCoalition,
      hsplit, hbeforeCoalition, hafterCoalition, hfull, hmem, haction,
      hbeforeCard, hafterCard⟩ :=
    exists_pair_dropout_of_fractionalEndpointTracked_card_crossing
      moves terminal.val hcollision hfinalNotCollision
  have hbeforeMass : 0 < quittingRootCoalitionMass
      (quittingFractionalEndpointMoves before root) beforeCoalition := by
    rw [hbeforeCoalition]
    exact quittingFractionalEndpointTrackedCoalition_mass_pos
      before root terminal.val hmass
  have hafterMass : 0 < quittingRootCoalitionMass
      (move.apply (quittingFractionalEndpointMoves before root))
        afterCoalition := by
    rw [hafterCoalition]
    exact move.coalitionMass_pos_nextTracked
      (quittingFractionalEndpointMoves before root) beforeCoalition hbeforeMass
  have hafterErase : afterCoalition = beforeCoalition.erase move.who := by
    rw [hafterCoalition]
    simp [QuittingFractionalEndpointMove.nextTrackedCoalition,
      hfull, haction]
  exact ⟨before, move, after, beforeCoalition, afterCoalition,
    hsplit, hbeforeCoalition, hafterCoalition, hfull, hmem, haction,
    hbeforeCard, hafterErase, hafterCard, hbeforeMass, hafterMass⟩

end GameTheory
