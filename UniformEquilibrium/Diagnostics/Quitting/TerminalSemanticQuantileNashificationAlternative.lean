/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumDebtSimplex
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCapNashDebtSupport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionDiffuseClockBridge

/-!
# The exact-Nash alternative for a singletonized diffuse clock

The diffuse deleted-clock bridge reduces every surviving fixed coalition to
one opponent singleton.  Exact Nashification cannot then preserve that clock
at a generic positive minimum state.  Positive mass on the fixed singleton
forces its player to be the unique quitting owner of a solo root and exposes
the corresponding debt-vertex/zero-slack gate.  Away from that gate the
singleton mass of every exact Nash root is zero.

Thus a quantile-block construction has a sharp alternative at every exact
minimum state: it either loses the calibrated clock, or it has already entered
the solo debt-gate geometry.  No averaging or independent replacement of the
literal terminal continuation is used here.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- Quantitative version of the singleton-clock alternative above a minimum.
If an exact Nash root retains `clockFloor` mass on one prescribed singleton,
then that player's complementary debt is paid by the total debt excess.  The
same excess pays the whole collision mass.  Hence a fixed positive quantile
block along near-minimizers can survive Nashification only by converging to a
debt vertex, while collision disappears. -/
theorem exactNash_preservedSingletonClock_mul_complementDebt_le_excess
    (base pair : QuittingTerminalSemanticPair iota)
    (root : iota → PMF Bool) (owner : iota) (clockFloor : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hclock : clockFloor ≤ quittingRootCoalitionMass root {owner}) :
    clockFloor *
          (quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebt pair owner) ≤
        quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebtSum base ∧
      quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root ≤
        quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebtSum base := by
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hcomplement : ∀ who,
      0 ≤ quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebt pair who := by
    intro who
    apply sub_nonneg.mpr
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ => hdebtNonneg player) (Finset.mem_univ who)
  have htermsNonneg : ∀ who ∈ (Finset.univ : Finset iota),
      0 ≤ quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebt pair who) := by
    intro who _
    exact mul_nonneg
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {who})
      (hcomplement who)
  have hsumNonneg : 0 ≤ ∑ who,
      quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebt pair who) :=
    Finset.sum_nonneg htermsNonneg
  have hpairDebtNonneg : 0 ≤ quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ => hdebtNonneg who
  have hcollisionNonneg : 0 ≤
      quittingTerminalSemanticDebtSum pair *
        quittingRootCollisionMass root :=
    mul_nonneg hpairDebtNonneg (quittingRootCollisionMass_nonneg root)
  have hbudget := terminalSemantic_exactNash_nearMinimum_support_budget
    (reward := reward) base pair root hM hreward hminimum hpair hnash
  constructor
  · calc
      clockFloor *
            (quittingTerminalSemanticDebtSum pair -
              quittingTerminalSemanticDebt pair owner) ≤
          quittingRootCoalitionMass root {owner} *
            (quittingTerminalSemanticDebtSum pair -
              quittingTerminalSemanticDebt pair owner) :=
        mul_le_mul_of_nonneg_right hclock (hcomplement owner)
      _ ≤ ∑ who, quittingRootCoalitionMass root {who} *
            (quittingTerminalSemanticDebtSum pair -
              quittingTerminalSemanticDebt pair who) :=
        Finset.single_le_sum htermsNonneg (Finset.mem_univ owner)
      _ ≤ quittingTerminalSemanticDebtSum pair *
              quittingRootCollisionMass root +
            ∑ who, quittingRootCoalitionMass root {who} *
              (quittingTerminalSemanticDebtSum pair -
                quittingTerminalSemanticDebt pair who) :=
        le_add_of_nonneg_left hcollisionNonneg
      _ ≤ quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebtSum base := hbudget
  · exact (le_add_of_nonneg_right hsumNonneg).trans hbudget

/-- An exact Nash root which preserves positive mass on a prescribed
singleton at a positive minimum state is necessarily a solo debt-gate root
owned by that singleton player. -/
theorem minimumTerminalSemantic_exactNash_preservingSingletonClock_is_debtGateSolo
    (pair : QuittingTerminalSemanticPair iota)
    (root : iota → PMF Bool) (owner : iota) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hclock : 0 < quittingRootCoalitionMass root {owner}) :
    IsMinimumTerminalSemanticDebtGate reward pair owner ∧
      0 < (root owner true).toReal ∧
      ∀ other, other ≠ owner → root other = PMF.pure false := by
  have hgate := minimumTerminalSemantic_debtGate_of_singletonMass_pos
    (reward := reward) pair root hM hreward hpair hminimum hpositive hnash
      owner hclock
  have hquit : 0 < (root owner true).toReal :=
    QuittingFiniteRootWindow.quitProbability_pos_of_singletonCoalitionMass_pos
      root owner hclock
  refine ⟨hgate, hquit, ?_⟩
  intro other hne
  exact pmf_eq_pure_false_of_apply_true_toReal_eq_zero
    (root other)
    (quittingTerminalSemantic_minimum_positiveDebt_opponents_quit_eq_zero
      reward pair root hM hreward hpair hminimum hnash
        (hgate.1.symm ▸ hpositive) hne)

/-- Contrapositive producer fence: away from the prescribed debt gate, exact
Nashification annihilates the singleton clock that the quantile construction
would need to preserve. -/
theorem minimumTerminalSemantic_exactNash_singletonClock_eq_zero_of_not_debtGate
    (pair : QuittingTerminalSemanticPair iota)
    (root : iota → PMF Bool) (owner : iota) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hnoGate : ¬ IsMinimumTerminalSemanticDebtGate reward pair owner) :
    quittingRootCoalitionMass root {owner} = 0 := by
  have hnonneg : 0 ≤ quittingRootCoalitionMass root {owner} :=
    MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {owner}
  apply le_antisymm
  · by_contra hnot
    have hclock : 0 < quittingRootCoalitionMass root {owner} :=
      lt_of_not_ge hnot
    exact hnoGate
      (minimumTerminalSemantic_exactNash_preservingSingletonClock_is_debtGateSolo
        (reward := reward) pair root owner hM hreward hpair hminimum
          hpositive hnash hclock).1
  · exact hnonneg

/-- Packet-facing capstone.  After diffuse deleted-clock singletonization, an
exact Nash row preserving positive mass on the packet's fixed label is
already the solo debt-gate alternative. -/
theorem
    QuittingReprojectionDiffuseDeletedWindowPacket.exactNash_preservingTerminalClock_is_debtGateSolo
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {marked : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ} {lower : ℝ}
    (packet : QuittingReprojectionDiffuseDeletedWindowPacket
      reward profiles marked terminal cutoff scale lower)
    (owner : iota) (howner : owner ∈ terminal.val) (hne : owner ≠ marked)
    (pair : QuittingTerminalSemanticPair iota)
    (root : iota → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hclock : 0 < quittingRootCoalitionMass root terminal.val) :
    IsMinimumTerminalSemanticDebtGate reward pair owner ∧
      0 < (root owner true).toReal ∧
      ∀ other, other ≠ owner → root other = PMF.pure false := by
  have hterminal : terminal.val = {owner} :=
    packet.terminal_eq_singleton owner howner hne
  rw [hterminal] at hclock
  exact
    minimumTerminalSemantic_exactNash_preservingSingletonClock_is_debtGateSolo
      (reward := reward) pair root owner hM hreward hpair hminimum hpositive
        hnash hclock

end GameTheory
