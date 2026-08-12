/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawDebtConvexity
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDebtTransfer

/-!
# A minimum-debt consumer for a counterfactual reset square

The positive off-diagonal stopping-law slope raises an observer's debt at the
full mover-reset endpoint.  If one then installs an observer response whose
debt is small, global minimum provenance has a quantitative consequence.
Either the first endpoint is separated from the minimum fiber, or the second
reset transfers a fixed amount of debt to a third coordinate.

This is a literal `2 x 2` square of behavior profiles.  The two replacements
commute, and the second edge uses the actual observer response selected at the
mover-reset endpoint.  No comparison between unrelated deviations is called
a strategic gain.

The result does not close the counterexample frontier: the separated first
endpoint still needs the reset-face/surface-tension consumer, while the
second-transfer branch needs a recurrence or deletion compiler.  It does
show that the pure externality regression cannot survive positive global
minimum provenance together with a near-minimal first reset target.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A positive normalized debt slope on a stopping-law mixture forces at
least the same observer-debt increase at the full reset endpoint. -/
theorem stoppingLawSlope_le_fullEndpoint_observerDebtChange
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda charge : ℝ) (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hslope : lambda * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (profile mover) target lambda hlambda0.le hlambda1))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer) :
    charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer := by
  have hchord := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward profile mover observer (profile mover) target lambda hlambda0.le
      hlambda1 hM hreward
  rw [Function.update_eq_self] at hchord
  have hscaled : lambda * charge ≤ lambda *
      (quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer) := by
    nlinarith
  nlinarith

/-- Exact opposite-face accounting for an actual self update. -/
theorem sum_opponent_debtChange_update_eq_totalChange_add_debtDecrease
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (strategy : (quittingGame reward).BehaviorStrategy who) :
    let source := quittingTerminalSemanticPair reward profile
    let target := quittingTerminalSemanticPair reward
      (Function.update profile who strategy)
    (∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target other) =
      (quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum source) +
        (quittingTerminalSemanticDebt source who -
          quittingTerminalSemanticDebt target who) := by
  dsimp only
  let source := quittingTerminalSemanticPair reward profile
  let target := quittingTerminalSemanticPair reward
    (Function.update profile who strategy)
  change (∑ other ∈ Finset.univ.erase who,
      quittingTerminalSemanticDebtChange source target other) =
    (quittingTerminalSemanticDebtSum target -
        quittingTerminalSemanticDebtSum source) +
      (quittingTerminalSemanticDebt source who -
        quittingTerminalSemanticDebt target who)
  have hsum := Finset.sum_erase_add Finset.univ
    (fun player => quittingTerminalSemanticDebtChange source target player)
    (Finset.mem_univ who)
  have htotal : (∑ player,
      quittingTerminalSemanticDebtChange source target player) =
      quittingTerminalSemanticDebtSum target -
        quittingTerminalSemanticDebtSum source := by
    unfold quittingTerminalSemanticDebtChange
      quittingTerminalSemanticDebtSum
    rw [Finset.sum_sub_distrib]
  rw [htotal] at hsum
  have hwho : quittingTerminalSemanticDebtChange source target who =
      quittingTerminalSemanticDebt target who -
        quittingTerminalSemanticDebt source who := rfl
  rw [hwho] at hsum
  linarith

/-- **Minimum reset-square alternative.**

Let `first` be the full mover reset and `both` the result of subsequently
installing the observer's selected response.  A positive stopping-law slope
gives the observer at least `charge` debt at `first`, up to its nonnegative
source debt.  If the response leaves at most `charge / 4` observer debt, then
either:

* `first` lies at least `charge / 2` above the global minimum; or
* the literal observer edge `first -> both` transfers more than
  `charge / 4` in aggregate to the opposite face, and one fixed opponent
  receives at least its finite-player average.

The conclusion also records that the two reset orders have the same literal
endpoint. -/
theorem positiveMinimum_counterfactualResetSquare_excess_or_secondTransfer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : mover ≠ observer)
    (moverTarget : (quittingGame reward).BehaviorStrategy mover)
    (observerResponse : (quittingGame reward).BehaviorStrategy observer)
    (lambda charge error : ℝ)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (hcharge : 0 < charge) (herror : error ≤ charge / 4)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hslope : lambda * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (profile mover) moverTarget lambda hlambda0.le hlambda1)))
          observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer)
    (hresponse : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update (Function.update profile mover moverTarget) observer
          observerResponse)) observer ≤ error) :
    let first := Function.update profile mover moverTarget
    let observerFirst := Function.update profile observer observerResponse
    let both := Function.update first observer observerResponse
    both = Function.update observerFirst mover moverTarget ∧
      (charge / 2 ≤
          quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward first) -
            quittingTerminalSemanticDebtSum minimum ∨
        ∃ recipient ∈ Finset.univ.erase observer,
          charge / 4 /
              ((Finset.univ.erase observer).card : ℝ) <
            quittingTerminalSemanticDebtChange
              (quittingTerminalSemanticPair reward first)
              (quittingTerminalSemanticPair reward both) recipient) := by
  dsimp only
  let first := Function.update profile mover moverTarget
  let observerFirst := Function.update profile observer observerResponse
  let both := Function.update first observer observerResponse
  have hcommute : both = Function.update observerFirst mover moverTarget := by
    dsimp only [both, observerFirst, first]
    exact Function.update_comm hne _ _ profile
  refine ⟨hcommute, ?_⟩
  let sourcePair := quittingTerminalSemanticPair reward profile
  let firstPair := quittingTerminalSemanticPair reward first
  let bothPair := quittingTerminalSemanticPair reward both
  have hendpointSlope : charge ≤
      quittingTerminalSemanticDebt firstPair observer -
        quittingTerminalSemanticDebt sourcePair observer := by
    dsimp only [firstPair, sourcePair, first]
    exact stoppingLawSlope_le_fullEndpoint_observerDebtChange
      reward profile mover observer moverTarget lambda charge hlambda0
        hlambda1 hM hreward hslope
  have hsourceMem : sourcePair ∈ quittingTerminalSemanticCarrier reward := by
    exact quittingTerminalSemanticPair_mem_carrier reward profile
  have hsourceNonneg : 0 ≤
      quittingTerminalSemanticDebt sourcePair observer :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hM hreward
      hsourceMem observer
  have hfirstDebt : charge ≤
      quittingTerminalSemanticDebt firstPair observer := by
    linarith
  by_cases hexcess : charge / 2 ≤
      quittingTerminalSemanticDebtSum firstPair -
        quittingTerminalSemanticDebtSum minimum
  · exact Or.inl hexcess
  · right
    have hbothMem : bothPair ∈ quittingTerminalSemanticCarrier reward := by
      exact quittingTerminalSemanticPair_mem_carrier reward both
    have hbothFloor : quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum bothPair :=
      hminimum bothPair hbothMem
    have haccount :=
      sum_opponent_debtChange_update_eq_totalChange_add_debtDecrease
        reward first observer observerResponse
    change (∑ other ∈ Finset.univ.erase observer,
        quittingTerminalSemanticDebtChange firstPair bothPair other) = _
      at haccount
    have htransfer : charge / 4 <
        ∑ other ∈ Finset.univ.erase observer,
          quittingTerminalSemanticDebtChange firstPair bothPair other := by
      rw [haccount]
      have hexcessLt :
          quittingTerminalSemanticDebtSum firstPair -
              quittingTerminalSemanticDebtSum minimum < charge / 2 :=
        lt_of_not_ge hexcess
      linarith
    let opponents := Finset.univ.erase observer
    have hmoverMem : mover ∈ opponents := by
      exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ mover⟩
    have hopponents : opponents.Nonempty := ⟨mover, hmoverMem⟩
    have hcardPos : 0 < (opponents.card : ℝ) := by
      exact_mod_cast hopponents.card_pos
    by_contra hnot
    push Not at hnot
    have hsumLe : (∑ recipient ∈ opponents,
        quittingTerminalSemanticDebtChange firstPair bothPair recipient) ≤
        ∑ _recipient ∈ opponents,
          charge / 4 / (opponents.card : ℝ) := by
      exact Finset.sum_le_sum fun recipient hrecipient =>
        hnot recipient hrecipient
    have hconstant : (∑ _recipient ∈ opponents,
        charge / 4 / (opponents.card : ℝ)) = charge / 4 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [hconstant] at hsumLe
    have htransfer' : charge / 4 <
        ∑ other ∈ opponents,
          quittingTerminalSemanticDebtChange firstPair bothPair other := by
      simpa only [opponents] using htransfer
    linarith

/-- If the first reset target is already within `charge / 2` of the minimum
fiber, only the quantitative second-transfer branch remains. -/
theorem positiveMinimum_counterfactualResetSquare_secondTransfer_of_nearFirst
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : mover ≠ observer)
    (moverTarget : (quittingGame reward).BehaviorStrategy mover)
    (observerResponse : (quittingGame reward).BehaviorStrategy observer)
    (lambda charge error : ℝ)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (hcharge : 0 < charge) (herror : error ≤ charge / 4)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hslope : lambda * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (profile mover) moverTarget lambda hlambda0.le hlambda1)))
          observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer)
    (hresponse : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update (Function.update profile mover moverTarget) observer
          observerResponse)) observer ≤ error)
    (hnearFirst :
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update profile mover moverTarget)) -
        quittingTerminalSemanticDebtSum minimum < charge / 2) :
    ∃ recipient ∈ Finset.univ.erase observer,
      charge / 4 / ((Finset.univ.erase observer).card : ℝ) <
        quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward
            (Function.update profile mover moverTarget))
          (quittingTerminalSemanticPair reward
            (Function.update (Function.update profile mover moverTarget)
              observer observerResponse)) recipient := by
  have hsquare :=
    positiveMinimum_counterfactualResetSquare_excess_or_secondTransfer
      reward minimum profile mover observer hne moverTarget observerResponse
      lambda charge error hlambda0 hlambda1 hcharge herror hM hreward
      hminimum hslope hresponse
  rcases hsquare.2 with hexcess | htransfer
  · linarith
  · exact htransfer

/-- If instead the common double-reset endpoint is near the minimum fiber,
the separated-first-endpoint branch becomes quantitative total-debt descent
along the observer's literal response edge. -/
theorem positiveMinimum_counterfactualResetSquare_descent_or_secondTransfer_of_nearBoth
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : mover ≠ observer)
    (moverTarget : (quittingGame reward).BehaviorStrategy mover)
    (observerResponse : (quittingGame reward).BehaviorStrategy observer)
    (lambda charge error nearError : ℝ)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (hcharge : 0 < charge) (herror : error ≤ charge / 4)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hslope : lambda * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (profile mover) moverTarget lambda hlambda0.le hlambda1)))
          observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer)
    (hresponse : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update (Function.update profile mover moverTarget) observer
          observerResponse)) observer ≤ error)
    (hnearBoth : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (Function.update (Function.update profile mover moverTarget) observer
          observerResponse)) ≤
        quittingTerminalSemanticDebtSum minimum + nearError) :
    charge / 2 - nearError ≤
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (Function.update profile mover moverTarget)) -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (Function.update (Function.update profile mover moverTarget)
                observer observerResponse)) ∨
      ∃ recipient ∈ Finset.univ.erase observer,
        charge / 4 / ((Finset.univ.erase observer).card : ℝ) <
          quittingTerminalSemanticDebtChange
            (quittingTerminalSemanticPair reward
              (Function.update profile mover moverTarget))
            (quittingTerminalSemanticPair reward
              (Function.update (Function.update profile mover moverTarget)
                observer observerResponse)) recipient := by
  have hsquare :=
    positiveMinimum_counterfactualResetSquare_excess_or_secondTransfer
      reward minimum profile mover observer hne moverTarget observerResponse
      lambda charge error hlambda0 hlambda1 hcharge herror hM hreward
      hminimum hslope hresponse
  rcases hsquare.2 with hexcess | htransfer
  · exact Or.inl (by linarith)
  · exact Or.inr htransfer

end GameTheory
