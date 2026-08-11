/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectStratification

/-!
# The defect floor under finitely many fractional resets

Fractional endpoint moves retain terminal incidence, but this does not let a
simplex-valued family of resets evade the minimum-plateau charge.  This file
records the exact finite obstruction.

For an arbitrary finite list of coordinatewise endpoint moves, let

`retention = prod (1 - lambda)`.

Every old collision atom survives with at least this factor.  Against a
minimum terminal-semantic tail, the surviving collision forces

`retention * collisionMass * minimumDebt <= finalTotalNashDefect`.

More generally, shifted-tail excess is the only additional payment.  Thus a
finite simultaneous or sequential fractional reset with positive retention
cannot Nashify a positive collision above a positive debt floor.  Any local
defect consumed on the moved coordinates must reappear on other coordinates;
the cross-player transfer is forced by the same exact killed-debt charge.

The endpoint actions below are arbitrary.  In particular the theorem applies
to best-endpoint moves, recomputed best endpoints, and simplex-weighted
mixtures without choosing a privileged player.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Finite coordinatewise fractional moves -/

/-- One legal fractional move of one Boolean marginal toward a pure endpoint. -/
structure QuittingFractionalEndpointMove (ι : Type) where
  who : ι
  action : Bool
  weight : ℝ
  weight_nonneg : 0 ≤ weight
  weight_le_one : weight ≤ 1

/-- Apply one fractional endpoint move to a product root. -/
def QuittingFractionalEndpointMove.apply
    (move : QuittingFractionalEndpointMove ι) (root : ι → PMF Bool) :
    ι → PMF Bool :=
  quittingPartialEndpointRoot root move.who move.action move.weight
    move.weight_nonneg move.weight_le_one

/-- Apply a finite list of fractional endpoint moves in order. -/
def quittingFractionalEndpointMoves :
    List (QuittingFractionalEndpointMove ι) → (ι → PMF Bool) → ι → PMF Bool
  | [], root => root
  | move :: moves, root =>
      quittingFractionalEndpointMoves moves (move.apply root)

/-- Fraction of every old coalition atom guaranteed to survive all moves. -/
def quittingFractionalEndpointRetention :
    List (QuittingFractionalEndpointMove ι) → ℝ
  | [] => 1
  | move :: moves =>
      (1 - move.weight) * quittingFractionalEndpointRetention moves

omit [Fintype ι] [DecidableEq ι] in
theorem quittingFractionalEndpointRetention_nonneg
    (moves : List (QuittingFractionalEndpointMove ι)) :
    0 ≤ quittingFractionalEndpointRetention moves := by
  induction moves with
  | nil => simp [quittingFractionalEndpointRetention]
  | cons move moves ih =>
      rw [quittingFractionalEndpointRetention]
      exact mul_nonneg (sub_nonneg.mpr move.weight_le_one) ih

omit [Fintype ι] [DecidableEq ι] in
theorem quittingFractionalEndpointRetention_pos
    (moves : List (QuittingFractionalEndpointMove ι))
    (hstrict : ∀ move ∈ moves, move.weight < 1) :
    0 < quittingFractionalEndpointRetention moves := by
  induction moves with
  | nil => simp [quittingFractionalEndpointRetention]
  | cons move moves ih =>
      rw [quittingFractionalEndpointRetention]
      apply mul_pos (sub_pos.mpr (hstrict move (by simp)))
      exact ih fun later hlater => hstrict later (by simp [hlater])

omit [Fintype ι] [DecidableEq ι] in
/-- A zero retention product has a first full move.  Every preceding move has
strictly subunit weight. -/
theorem exists_first_full_fractionalEndpointMove_of_retention_eq_zero
    (moves : List (QuittingFractionalEndpointMove ι))
    (hzero : quittingFractionalEndpointRetention moves = 0) :
    ∃ before move after,
      moves = before ++ move :: after ∧
        (∀ prior ∈ before, prior.weight < 1) ∧ move.weight = 1 := by
  induction moves with
  | nil => simp [quittingFractionalEndpointRetention] at hzero
  | cons move moves ih =>
      by_cases hfull : move.weight = 1
      · exact ⟨[], move, moves, by simp, by simp, hfull⟩
      · have hfactor : 1 - move.weight ≠ 0 := by
          intro hfactor
          apply hfull
          linarith
        have htailZero : quittingFractionalEndpointRetention moves = 0 := by
          apply (mul_eq_zero.mp ?_).resolve_left hfactor
          simpa [quittingFractionalEndpointRetention] using hzero
        obtain ⟨before, first, after, hsplit, hbefore, hfirst⟩ :=
          ih htailZero
        refine ⟨move :: before, first, after, ?_, ?_, hfirst⟩
        · simp [hsplit]
        · intro prior hprior
          simp only [List.mem_cons] at hprior
          rcases hprior with hprior | hprior
          · subst prior
            exact lt_of_le_of_ne move.weight_le_one hfull
          · exact hbefore prior hprior

omit [Fintype ι] in
/-- A unit-weight fractional endpoint move is exactly the corresponding pure
coordinate update. -/
theorem QuittingFractionalEndpointMove.apply_eq_update_pure_of_weight_eq_one
    (move : QuittingFractionalEndpointMove ι) (root : ι → PMF Bool)
    (hfull : move.weight = 1) :
    move.apply root = Function.update root move.who (PMF.pure move.action) := by
  funext player
  by_cases hplayer : player = move.who
  · subst player
    rw [Function.update_self]
    unfold QuittingFractionalEndpointMove.apply
      quittingPartialEndpointRoot
    rw [Function.update_self]
    apply PMF.ext
    intro endpoint
    apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top _ endpoint) (PMF.apply_ne_top _ endpoint)).mp
    cases endpoint
    · rw [quittingPartialEndpointMarginal_false_toReal]
      simp [hfull]
    · rw [quittingPartialEndpointMarginal_true_toReal]
      simp [hfull]
  · unfold QuittingFractionalEndpointMove.apply
      quittingPartialEndpointRoot
    rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]

/-- Every exact root coalition retains the product of the unmoved fractions
through an arbitrary finite list of coordinatewise endpoint moves. -/
theorem quittingFractionalEndpointRetention_mul_coalitionMass_le
    (moves : List (QuittingFractionalEndpointMove ι))
    (root : ι → PMF Bool) (coalition : Finset ι) :
    quittingFractionalEndpointRetention moves *
        quittingRootCoalitionMass root coalition ≤
      quittingRootCoalitionMass
        (quittingFractionalEndpointMoves moves root) coalition := by
  induction moves generalizing root with
  | nil => simp [quittingFractionalEndpointRetention,
      quittingFractionalEndpointMoves]
  | cons move moves ih =>
      have hone :=
        one_sub_mul_quittingRootCoalitionMass_le_partialEndpointRoot
          root move.who move.action move.weight move.weight_nonneg
            move.weight_le_one coalition
      have hscaled := mul_le_mul_of_nonneg_left hone
        (quittingFractionalEndpointRetention_nonneg moves)
      have htail := ih (root := move.apply root)
      rw [quittingFractionalEndpointRetention,
        quittingFractionalEndpointMoves]
      change (1 - move.weight) *
          quittingFractionalEndpointRetention moves *
            quittingRootCoalitionMass root coalition ≤ _
      rw [mul_assoc, mul_left_comm (1 - move.weight)]
      exact hscaled.trans htail

/-! ## The minimum-tail charge -/

/-- A collision at an arbitrary product root is paid by shifted-tail excess
or by the root's total Nash defect.  This is the direct root-level form of the
marked-tail localization inequality. -/
theorem quittingRootCoalitionMass_mul_minimumDebt_le_tailExcess_add_defect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum tail : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (terminal : {S : Finset ι // S.Nonempty}) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward)
    (hcollision : 1 < terminal.val.card) :
    quittingRootCoalitionMass root terminal.val *
        quittingTerminalSemanticDebtSum minimum ≤
      (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        quittingRootTotalNashDefect reward tail.1 root := by
  have htailDebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward htail
  have htailMin : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum tail := hminimum tail htail
  have hcoalitionNonneg :
      0 ≤ quittingRootCoalitionMass root terminal.val :=
    MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
      root terminal.val
  have hminimumToTail :
      quittingRootCoalitionMass root terminal.val *
          quittingTerminalSemanticDebtSum minimum ≤
        quittingRootCoalitionMass root terminal.val *
          quittingTerminalSemanticDebtSum tail :=
    mul_le_mul_of_nonneg_left htailMin hcoalitionNonneg
  have hcoordinate : ∀ who,
      quittingRootCoalitionMass root terminal.val *
          quittingTerminalSemanticDebt tail who ≤
        quittingRootOpponentAbsorptionMass root who *
          quittingTerminalSemanticDebt tail who := by
    intro who
    obtain ⟨other, hother, hne⟩ :=
      terminal.val.exists_mem_ne hcollision who
    exact mul_le_mul_of_nonneg_right
      (quittingRootCoalitionMass_le_opponentAbsorptionMass_of_other_mem
        root terminal.val who other hother hne)
      (htailDebt who)
  have hsum := Finset.sum_le_sum fun who (_ : who ∈ Finset.univ) =>
    hcoordinate who
  have hcoalitionToCharge :
      quittingRootCoalitionMass root terminal.val *
          quittingTerminalSemanticDebtSum tail ≤
        ∑ who, quittingRootOpponentAbsorptionMass root who *
          quittingTerminalSemanticDebt tail who := by
    unfold quittingTerminalSemanticDebtSum
    simpa [Finset.mul_sum] using hsum
  have hcharge :=
    minimumTerminalSemantic_sum_opponentAbsorption_charge_le_excess_add_defect
      reward minimum tail root hM hreward hminimumCarrier hminimum htail
  exact hminimumToTail.trans (hcoalitionToCharge.trans hcharge)

/-- **Finite fractional-reset floor.**  After any finite family of
coordinatewise fractional endpoint moves, retained collision mass times the
minimum debt remains a lower bound for shifted-tail excess plus the final
root's total Nash defect. -/
theorem fractionalEndpointMoves_collisionDebt_le_tailExcess_add_defect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum tail : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (moves : List (QuittingFractionalEndpointMove ι))
    (terminal : {S : Finset ι // S.Nonempty}) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward)
    (hcollision : 1 < terminal.val.card) :
    quittingFractionalEndpointRetention moves *
        quittingRootCoalitionMass root terminal.val *
          quittingTerminalSemanticDebtSum minimum ≤
      (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        quittingRootTotalNashDefect reward tail.1
          (quittingFractionalEndpointMoves moves root) := by
  have hminimumNonneg : 0 ≤ quittingTerminalSemanticDebtSum minimum := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hM hreward hminimumCarrier who
  have hretention :=
    quittingFractionalEndpointRetention_mul_coalitionMass_le
      moves root terminal.val
  have hscaled := mul_le_mul_of_nonneg_right hretention hminimumNonneg
  have hfinal :=
    quittingRootCoalitionMass_mul_minimumDebt_le_tailExcess_add_defect
      reward minimum tail (quittingFractionalEndpointMoves moves root)
        terminal hM hreward hminimumCarrier hminimum htail hcollision
  exact (by simpa [mul_assoc] using hscaled.trans hfinal)

/-- On the minimum fiber itself, a finite positive-retention perturbation of
a positive collision cannot have zero total Nash defect.  This is the exact
cross-player cancellation no-go for simultaneous fractional Nashification. -/
theorem fractionalEndpointMoves_totalNashDefect_pos_of_positiveRetention
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
    (hretention : 0 < quittingFractionalEndpointRetention moves)
    (hmass : 0 < quittingRootCoalitionMass root terminal.val)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum) :
    0 < quittingRootTotalNashDefect reward minimum.1
      (quittingFractionalEndpointMoves moves root) := by
  have hfloor :=
    fractionalEndpointMoves_collisionDebt_le_tailExcess_add_defect
      reward minimum minimum root moves terminal hM hreward hminimumCarrier
        hminimum hminimumCarrier hcollision
  have hleft : 0 < quittingFractionalEndpointRetention moves *
      quittingRootCoalitionMass root terminal.val *
        quittingTerminalSemanticDebtSum minimum :=
    mul_pos (mul_pos hretention hmass) hminimumDebt
  norm_num at hfloor
  exact hleft.trans_le hfloor

/-! ## The first full-move stratum -/

/-- **Finite-strata alternative.**

Suppose a finite fractional reset list takes a positive collision over a
positive minimum debt to zero final total Nash defect.  Then the list has a
first full move.  Every earlier weight is strictly below one, so the original
coalition still has positive mass immediately before that move.  The full
move routes this positive mass, without loss, to the same coalition or its
one-player Boolean toggle.

No assertion is made about what the later suffix does to the routed mass or
about chronological recurrence. -/
theorem exists_first_full_move_routes_positive_collision_of_finalDefect_eq_zero
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
    ∃ before move after,
      moves = before ++ move :: after ∧
        (∀ prior ∈ before, prior.weight < 1) ∧
        move.weight = 1 ∧
        0 < quittingRootCoalitionMass
          (quittingFractionalEndpointMoves before root) terminal.val ∧
        let routed := quittingPureEndpointRoutedCoalition
          terminal.val move.who move.action
        0 < quittingRootCoalitionMass
          (move.apply (quittingFractionalEndpointMoves before root)) routed ∧
        quittingRootCoalitionMass
            (quittingFractionalEndpointMoves before root) terminal.val ≤
          quittingRootCoalitionMass
            (move.apply (quittingFractionalEndpointMoves before root)) routed ∧
        ((move.who ∈ terminal.val ∧ move.action = true ∧
              routed = terminal.val) ∨
          (move.who ∈ terminal.val ∧ move.action = false ∧
              routed = terminal.val.erase move.who) ∨
          (move.who ∉ terminal.val ∧ move.action = true ∧
              routed = insert move.who terminal.val) ∨
          (move.who ∉ terminal.val ∧ move.action = false ∧
              routed = terminal.val)) := by
  have hretentionZero : quittingFractionalEndpointRetention moves = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hretention
      have hpositive :=
        fractionalEndpointMoves_totalNashDefect_pos_of_positiveRetention
          reward minimum root moves terminal hM hreward hminimumCarrier
            hminimum hcollision hretention hmass hminimumDebt
      rw [hfinalDefect] at hpositive
      exact lt_irrefl 0 hpositive
    · exact quittingFractionalEndpointRetention_nonneg moves
  obtain ⟨before, move, after, hsplit, hbeforeStrict, hfull⟩ :=
    exists_first_full_fractionalEndpointMove_of_retention_eq_zero
      moves hretentionZero
  have hbeforeRetention : 0 < quittingFractionalEndpointRetention before :=
    quittingFractionalEndpointRetention_pos before hbeforeStrict
  have hbeforeLower :=
    quittingFractionalEndpointRetention_mul_coalitionMass_le
      before root terminal.val
  have hbeforeMass : 0 < quittingRootCoalitionMass
      (quittingFractionalEndpointMoves before root) terminal.val :=
    (mul_pos hbeforeRetention hmass).trans_le hbeforeLower
  let beforeRoot := quittingFractionalEndpointMoves before root
  let routed := quittingPureEndpointRoutedCoalition
    terminal.val move.who move.action
  have hroutePure : quittingRootCoalitionMass beforeRoot terminal.val ≤
      quittingRootCoalitionMass
        (Function.update beforeRoot move.who (PMF.pure move.action)) routed :=
    quittingRootCoalitionMass_le_pureEndpointRouted
      beforeRoot terminal.val move.who move.action
  have hmoveRoot : move.apply beforeRoot =
      Function.update beforeRoot move.who (PMF.pure move.action) :=
    move.apply_eq_update_pure_of_weight_eq_one beforeRoot hfull
  have hroute : quittingRootCoalitionMass beforeRoot terminal.val ≤
      quittingRootCoalitionMass (move.apply beforeRoot) routed := by
    rwa [hmoveRoot]
  have hbeforeMass' : 0 < quittingRootCoalitionMass beforeRoot terminal.val := by
    simpa only [beforeRoot] using hbeforeMass
  have hroutedPositive :
      0 < quittingRootCoalitionMass (move.apply beforeRoot) routed :=
    hbeforeMass'.trans_le hroute
  have hroutingClass :=
    quittingPureEndpointRoutedCoalition_four_way
      terminal.val move.who move.action
  exact ⟨before, move, after, hsplit, hbeforeStrict, hfull,
    by simpa only [beforeRoot] using hbeforeMass,
    by simpa only [beforeRoot, routed] using hroutedPositive,
    by simpa only [beforeRoot, routed] using hroute,
    by simpa only [routed] using hroutingClass⟩

end GameTheory
