/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLiteralSourceReturnNoGo
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPartialResetTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport

/-!
# Paid own-strategy transport of terminal debt

Changing one player's behavior while keeping every opponent fixed preserves
that player's all-behavior best-response envelope.  Consequently the change
in prescribed payoff is exactly the decrease in that player's terminal debt.
This gives the bounded potential underlying changed-root and changed-tail
transport: a positive reached-row ticket can be paid only by a decrease of
the marked debt or by the transported profile's residual best-response error.

The second part records the exact one-row decomposition of that residual.
For an arbitrary semantic pair and root, prefixed debt is the cap-coordinate
Nash defect of the root plus joint survival times the tail debt.  No Nash
hypothesis is used.

The opponent-aware surcharge identities are maintenance API: they localize
best-response-envelope drift as hidden continuation-option debt and state the
sharp residual/reserve condition for a paid inequality.  They do not prove
that arbitrary opponent changes satisfy that condition, and hence are not a
closure of the opponent-changing frontier branch.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- For an arbitrary profile transport, debt plus prescribed-payoff gain
equals old debt plus best-response-envelope drift.  This is the exact signed
term that disappears under a fixed-opponent own-strategy update. -/
theorem quittingTerminalSemanticDebt_add_payoffGain_eq_add_envelopeDrift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) who +
        (quittingTerminalPayoff reward target who -
          quittingTerminalPayoff reward source who) =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) who +
        (quittingContinuationBestResponseValue reward target who -
          quittingContinuationBestResponseValue reward source who) := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  ring

/-- The hidden continuation-option surcharge at one semantic prefix row:
the increase in the best pure endpoint when the literal prescribed tail is
replaced by the coordinatewise behavioral cap. -/
def quittingRootContinuationOptionSurcharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  max (quittingRootQuitPayoff reward pair.2 root who)
      (quittingRootContinuePayoff reward pair.2 root who) -
    max (quittingRootQuitPayoff reward pair.1 root who)
      (quittingRootContinuePayoff reward pair.1 root who)

/-- Replacing a literal continuation by its semantic cap cannot decrease the
best pure endpoint. -/
theorem quittingRootContinuationOptionSurcharge_nonneg_of_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    0 ≤ quittingRootContinuationOptionSurcharge reward pair root who := by
  have hdebt := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
    reward hM hreward hpair who
  have htail : pair.1 who ≤ pair.2 who := by
    unfold quittingTerminalSemanticDebt at hdebt
    linarith
  have hquit : quittingRootQuitPayoff reward pair.1 root who =
      quittingRootQuitPayoff reward pair.2 root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward pair.1 pair.2 root who
  have hcontinue : quittingRootContinuePayoff reward pair.1 root who ≤
      quittingRootContinuePayoff reward pair.2 root who := by
    let roots : ℕ → ι → PMF Bool := fun _ => root
    rw [show root = roots 0 by rfl,
      quittingRootContinuePayoff_eq_fixedOpponents,
      quittingRootContinuePayoff_eq_fixedOpponents]
    have hmul := mul_le_mul_of_nonneg_left htail
      (quittingFixedOpponentsContinueMass_nonneg roots who 0)
    linarith
  unfold quittingRootContinuationOptionSurcharge
  rw [hquit]
  exact sub_nonneg.mpr (max_le (le_max_left _ _) (hcontinue.trans (le_max_right _ _)))

/-- Exact literal-error plus hidden-surcharge decomposition.  This is a
localization of the opponent-change obstruction, not a bound on it. -/
theorem quittingTerminalSemanticDebt_prefix_eq_literalDefect_add_surcharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingRootCoordinateNashDefect reward pair.1 root who +
        quittingRootContinuationOptionSurcharge reward pair root who := by
  have hquit : quittingRootQuitPayoff reward pair.1 root who =
      quittingRootQuitPayoff reward pair.2 root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward pair.1 pair.2 root who
  have hcontinue : quittingRootContinuePayoff reward
      (Function.update pair.1 who (pair.2 who)) root who =
        quittingRootContinuePayoff reward pair.2 root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
    quittingRootCoordinateNashDefect
    quittingRootContinuationOptionSurcharge
  dsimp only
  rw [hquit, hcontinue]
  ring

/-- For the debt potential and the displayed row-error account, the residual
reserve hypothesis is exactly equivalent to the desired paid-transport
inequality. -/
theorem gain_le_potentialDrop_add_error_iff_residual_le_reserve
    (gain sourcePotential targetPotential error residual : ℝ)
    (hsplit : targetPotential = error + residual) :
    gain ≤ sourcePotential - targetPotential + error ↔
      residual ≤ sourcePotential - gain := by
  rw [hsplit]
  constructor <;> intro h <;> linarith

/-- **Minimum-fiber barrier for paid residuals.**  If the source potential is
globally minimal among admissible outputs, an exact `target = error + residual`
account together with the paid-residual condition can only hold after the
row-error account has already spent the whole gain.  In particular, this is
an obstruction theorem: it does not produce the paid-residual hypothesis. -/
theorem gain_le_error_of_minimumFiber_and_paid_residual
    (gain minimum sourcePotential targetPotential error residual : ℝ)
    (hsource : sourcePotential = minimum)
    (htarget : minimum ≤ targetPotential)
    (hsplit : targetPotential = error + residual)
    (hpaid : residual ≤ sourcePotential - gain) :
    gain ≤ error := by
  linarith

/-- The fundamental minimum-fiber invariant behind the preceding gain
statement: residual debt can decrease below the minimum only by at most the
amount entered in the explicit error ledger.  This uses no proposed gain or
paid-transport condition. -/
theorem residualDischarge_le_error_of_minimumFiber
    (minimum targetPotential error residual : ℝ)
    (htarget : minimum ≤ targetPotential)
    (hsplit : targetPotential = error + residual) :
    minimum - residual ≤ error := by
  linarith

/-- An exact target on or above the minimum fiber cannot discharge any
strictly positive charge from its residual ledger.  This is the direct
operation-class no-go obtained by specializing the error ledger to zero. -/
theorem not_residual_le_minimum_sub_charge_of_exact_minimumFiber
    (minimum targetPotential residual charge : ℝ)
    (hcharge : 0 < charge)
    (htarget : minimum ≤ targetPotential)
    (hexact : targetPotential = residual) :
    ¬ residual ≤ minimum - charge := by
  intro hpaid
  linarith

/-- Exact slack identity for a claimed residual discharge `charge`.  If the
target is above the minimum or the claimed residual bound has positive
slack, the error ledger exceeds the charge by exactly those two slacks. -/
theorem error_sub_charge_eq_minimumExcess_add_residualSlack
    (minimum targetPotential error residual charge : ℝ)
    (hsplit : targetPotential = error + residual) :
    error - charge =
      (targetPotential - minimum) + (minimum - charge - residual) := by
  rw [hsplit]
  ring

/-- Near the minimum fiber, a paid residual reduction can spend at most the
source's pre-existing excess before the rest of its charge becomes error. -/
theorem charge_sub_excess_le_error_of_nearMinimum_paid_residual
    (minimum sourcePotential targetPotential error residual charge excess : ℝ)
    (hsource : sourcePotential = minimum + excess)
    (htarget : minimum ≤ targetPotential)
    (hsplit : targetPotential = error + residual)
    (hpaid : residual ≤ sourcePotential - charge) :
    charge - excess ≤ error := by
  linarith

/-- A decrease of a proper-subset debt potential at a globally minimal
total-debt source is paid by an equal increase in the complementary debt.
Thus changing the tracked subset can move debt between players but cannot
create a decrease of total debt. -/
theorem complementPotential_increase_of_totalMinimum_and_subsetDrop
    (sourceSelected sourceComplement targetSelected targetComplement charge : ℝ)
    (htotal : sourceSelected + sourceComplement ≤
      targetSelected + targetComplement)
    (hdrop : targetSelected ≤ sourceSelected - charge) :
    sourceComplement + charge ≤ targetComplement := by
  linarith

/-- Updating only `who` changes terminal debt by exactly the negative of the
prescribed-payoff change.  This is the fixed-opponent potential identity. -/
theorem quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (strategy : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile who strategy)) who =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who -
        (quittingTerminalPayoff reward
            (Function.update profile who strategy) who -
          quittingTerminalPayoff reward profile who) := by
  change quittingContinuationBestResponseValue reward
        (Function.update profile who strategy) who -
        quittingTerminalPayoff reward
          (Function.update profile who strategy) who =
      (quittingContinuationBestResponseValue reward profile who -
        quittingTerminalPayoff reward profile who) -
      (quittingTerminalPayoff reward
          (Function.update profile who strategy) who -
        quittingTerminalPayoff reward profile who)
  rw [quittingContinuationBestResponseValue_update_self]
  ring

/-- Equivalent telescoping form of fixed-opponent debt transport. -/
theorem quittingTerminalSemanticDebt_update_self_add_payoffGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (strategy : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile who strategy)) who +
        (quittingTerminalPayoff reward
            (Function.update profile who strategy) who -
          quittingTerminalPayoff reward profile who) =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
  rw [quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain]
  ring

/-- A source ticket bounded by the marked player's source debt is paid by
the marked debt drop plus the transported profile's residual debt.  The
transport may replace the player's entire behavior strategy, hence includes
root-only, tail-only, and simultaneous root-and-tail changes, while every
opponent stays literal. -/
theorem gain_le_debtDrop_add_residual_of_update_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (strategy : (quittingGame reward).BehaviorStrategy who)
    (gain : ℝ)
    (hgain : gain ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who) :
    gain ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile who strategy)) who +
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile who strategy)) who := by
  linarith

/-- If the transported own strategy is within `error` of the unchanged
best-response envelope, the only unpaid amount in the potential account is
at most `error`. -/
theorem gain_le_debtDrop_add_error_of_update_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (strategy : (quittingGame reward).BehaviorStrategy who)
    (gain error : ℝ)
    (hgain : gain ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who)
    (hcap : quittingContinuationBestResponseValue reward profile who ≤
      quittingTerminalPayoff reward
        (Function.update profile who strategy) who + error) :
    gain ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile who strategy)) who + error := by
  have hresidual : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile who strategy)) who ≤ error := by
    change quittingContinuationBestResponseValue reward
        (Function.update profile who strategy) who -
          quittingTerminalPayoff reward
            (Function.update profile who strategy) who ≤ error
    rw [quittingContinuationBestResponseValue_update_self]
    linarith
  have hpaid := gain_le_debtDrop_add_residual_of_update_self
    reward profile who strategy gain hgain
  linarith

/-- Under a uniform reward bound, the marked debt is a bounded nonnegative
potential, with range contained in `[0, 2M]`. -/
theorem quittingTerminalSemanticDebt_mem_Icc_zero_two_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who ∈
      Set.Icc 0 (2 * M) := by
  constructor
  · exact quittingTerminalDeviationDebt_nonneg reward profile who hM hreward
  · unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    have hbest := abs_quittingContinuationBestResponseValue_le
      reward profile who hM hreward
    have hpayoff := abs_quittingTerminalPayoff_le
      reward profile who hM hreward
    have hbestUpper := le_of_abs_le hbest
    have hpayoffLower := neg_le_of_abs_le hpayoff
    linarith

/-- **Exact arbitrary-root cap decomposition.**  Prefix debt is the root's
coordinate Nash defect against the tail cap plus joint Continue mass times
the tail debt.  This is the exact root-error plus tail-error account used by
paid root-or-tail transport. -/
theorem quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingRootCoordinateNashDefect reward pair.2 root who +
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who := by
  have hquit : quittingRootQuitPayoff reward pair.1 root who =
      quittingRootQuitPayoff reward pair.2 root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward pair.1 pair.2 root who
  have hcontinue :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        quittingRootContinuePayoff reward pair.2 root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp
  have hsuccessor := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    reward pair.2 pair.1 root who
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
    quittingRootCoordinateNashDefect
  dsimp only
  rw [hquit, hcontinue]
  linarith

/-- **Maximal one-step transport/prefix account.**  Relative to an arbitrary
source semantic state, a changed root and changed tail pay through prescribed
payoff gain, minus cap-envelope drift, plus the changed root's cap defect and
survival-weighted tail debt.  Fixed-opponent own-strategy transport is the
special case in which the envelope-drift term vanishes. -/
theorem quittingTerminalSemanticDebt_eq_payoffGain_sub_envelopeDrift_add_capDefect_add_liveTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source tail : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingTerminalSemanticDebt source who =
      ((quittingTerminalSemanticPrefix reward root tail).1 who -
          source.1 who) -
        ((quittingTerminalSemanticPrefix reward root tail).2 who -
          source.2 who) +
      quittingRootCoordinateNashDefect reward tail.2 root who +
      quittingStationaryContinueMass root *
        quittingTerminalSemanticDebt tail who := by
  have hprefix :=
    quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul
      reward tail root who
  unfold quittingTerminalSemanticDebt at hprefix ⊢
  linarith

/-- Literal specialization of the exact cap-error recursion. -/
theorem quittingTerminalDeviationDebt_rootThenContinuation_eq_capDefect_add_continueMass_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward root continuation) who =
      quittingRootCoordinateNashDefect reward
          (fun player =>
            quittingContinuationBestResponseValue reward continuation player)
          root who +
        quittingStationaryContinueMass root *
          quittingTerminalDeviationDebt reward continuation who := by
  have hpair := quittingTerminalSemanticPair_rootThenContinuation
    reward root continuation hM hreward
  have hdecomp :=
    quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul
      reward (quittingTerminalSemanticPair reward continuation) root who
  rw [← hpair] at hdecomp
  exact hdecomp

end GameTheory

#print axioms GameTheory.quittingTerminalSemanticDebt_add_payoffGain_eq_add_envelopeDrift
#print axioms GameTheory.quittingRootContinuationOptionSurcharge_nonneg_of_mem_carrier
#print axioms GameTheory.quittingTerminalSemanticDebt_prefix_eq_literalDefect_add_surcharge
#print axioms GameTheory.gain_le_potentialDrop_add_error_iff_residual_le_reserve
#print axioms GameTheory.gain_le_error_of_minimumFiber_and_paid_residual
#print axioms GameTheory.residualDischarge_le_error_of_minimumFiber
#print axioms GameTheory.not_residual_le_minimum_sub_charge_of_exact_minimumFiber
#print axioms GameTheory.error_sub_charge_eq_minimumExcess_add_residualSlack
#print axioms GameTheory.charge_sub_excess_le_error_of_nearMinimum_paid_residual
#print axioms GameTheory.complementPotential_increase_of_totalMinimum_and_subsetDrop
#print axioms GameTheory.quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
#print axioms GameTheory.gain_le_debtDrop_add_error_of_update_self
#print axioms GameTheory.quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul
#print axioms
  GameTheory.quittingTerminalSemanticDebt_eq_payoffGain_sub_envelopeDrift_add_capDefect_add_liveTail
