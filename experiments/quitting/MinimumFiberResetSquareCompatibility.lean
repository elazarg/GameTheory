/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import experiments.quitting.MinimumFiberResetSquareSourceMatchNoGo
import experiments.quitting.Q182EndpointRecipientAtomInterfaceNoGo
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawTransferBalanceRegression

/-!
# A positive common-fiber reset square with opposite parallel signs

The conditional hypotheses in
`minimumFiber_resetSquare_sourceMismatch_eq_opponentTransport` are jointly
realizable by a literal finite quitting game.  In the two-player table below,
the four pure stationary quitter sets form a commuting reset square.  Every
vertex has total terminal-semantic debt exactly one, while the observer gains
one on the target-side reset edge and loses one on the parallel source-side
edge.

This is a local compatibility witness, not a counterexample to uniform
equilibrium existence.  Since the game has two players, its attainable
semantic carrier cannot have a positive global debt minimum.  Thus positive
*global-minimum provenance*, rather than equality on one positive fiber, is
the only part of the corrected Q186 compatibility problem not realized here.
-/

noncomputable section

namespace GameTheory
namespace MinimumFiberResetSquareCompatibility

open StochasticGame Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

abbrev Player := Bool
abbrev mover : Player := false
abbrev observer : Player := true

/-- The rows are

* `{observer} -> (0,1)`;
* `{mover} -> (-1,1)`; and
* `{mover, observer} -> (1,0)`.

The empty quitter set has the quitting-game cemetery payoff `(0,0)`. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who =>
    if terminal.val = {observer} then
      if who = mover then 0 else 1
    else if terminal.val = {mover} then
      if who = mover then -1 else 1
    else if who = mover then 1 else 0

theorem reward_bound (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : |reward terminal who| ≤ 1 := by
  unfold reward
  split_ifs <;> norm_num

def source : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot {observer})

def first : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward
    (quittingPureSetRoot {mover, observer})

def observerFirst : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot ∅)

def both : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot {mover})

def moverTarget : (quittingGame reward).BehaviorStrategy mover :=
  first mover

def observerResponse : (quittingGame reward).BehaviorStrategy observer :=
  observerFirst observer

theorem update_source_mover :
    Function.update source mover moverTarget = first := by
  funext who time history
  cases who <;>
    simp [source, first, moverTarget, quittingStationaryProfile,
      StochasticGame.stationaryBehaviorProfile, quittingPureSetRoot,
      quittingSetAction, mover, observer]

theorem update_source_observer :
    Function.update source observer observerResponse = observerFirst := by
  funext who time history
  cases who <;>
    simp [source, observerFirst, observerResponse,
      quittingStationaryProfile, StochasticGame.stationaryBehaviorProfile,
      quittingPureSetRoot, quittingSetAction, observer]

theorem update_first_observer :
    Function.update first observer observerResponse = both := by
  funext who time history
  cases who <;>
    simp [first, observerFirst, both, observerResponse,
      quittingStationaryProfile, StochasticGame.stationaryBehaviorProfile,
      quittingPureSetRoot, quittingSetAction, mover, observer]

theorem update_observerFirst_mover :
    Function.update observerFirst mover moverTarget = both := by
  funext who time history
  cases who <;>
    simp [first, observerFirst, both, moverTarget,
      quittingStationaryProfile, StochasticGame.stationaryBehaviorProfile,
      quittingPureSetRoot, quittingSetAction, mover, observer]

theorem source_totalDebt : quittingTerminalDebtSum reward source = 1 := by
  unfold quittingTerminalDebtSum
  rw [Fintype.sum_bool]
  change
    quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward source)
        true +
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source) false = 1
  rw [source,
    quittingTerminalSemanticDebt_pureSetRoot_eq reward {observer} false
      (by norm_num) reward_bound,
    quittingTerminalSemanticDebt_pureSetRoot_eq reward {observer} true
      (by norm_num) reward_bound]
  norm_num [quittingSetReward, reward, mover, observer, Finset.ext_iff]

theorem first_totalDebt : quittingTerminalDebtSum reward first = 1 := by
  unfold quittingTerminalDebtSum
  rw [Fintype.sum_bool]
  change
    quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward first)
        true +
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward first) false = 1
  rw [first,
    quittingTerminalSemanticDebt_pureSetRoot_eq reward {mover, observer} false
      (by norm_num) reward_bound,
    quittingTerminalSemanticDebt_pureSetRoot_eq reward {mover, observer} true
      (by norm_num) reward_bound]
  norm_num [quittingSetReward, reward, mover, observer, Finset.ext_iff,
    show ({mover, observer} : Finset Player).Nontrivial by decide]

theorem observerFirst_totalDebt :
    quittingTerminalDebtSum reward observerFirst = 1 := by
  unfold quittingTerminalDebtSum
  rw [Fintype.sum_bool]
  change
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward observerFirst) true +
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward observerFirst) false = 1
  rw [observerFirst,
    quittingTerminalSemanticDebt_pureSetRoot_eq reward ∅ false
      (by norm_num) reward_bound,
    quittingTerminalSemanticDebt_pureSetRoot_eq reward ∅ true
      (by norm_num) reward_bound]
  norm_num [quittingSetReward, reward, mover, observer, Finset.ext_iff]

theorem both_totalDebt : quittingTerminalDebtSum reward both = 1 := by
  unfold quittingTerminalDebtSum
  rw [Fintype.sum_bool]
  change
    quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward both)
        true +
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward both) false = 1
  rw [both,
    quittingTerminalSemanticDebt_pureSetRoot_eq reward {mover} false
      (by norm_num) reward_bound,
    quittingTerminalSemanticDebt_pureSetRoot_eq reward {mover} true
      (by norm_num) reward_bound]
  norm_num [quittingSetReward, reward, mover, observer, Finset.ext_iff]

theorem target_observer_gain_eq_one :
    quittingTerminalPayoff reward
          (Function.update first observer observerResponse) observer -
        quittingTerminalPayoff reward first observer = 1 := by
  rw [update_first_observer, both, first,
    quittingTerminalPayoff_pureSetRoot,
    quittingTerminalPayoff_pureSetRoot]
  norm_num [quittingSetReward, reward, mover, observer, Finset.ext_iff]

theorem source_observer_gain_eq_neg_one :
    quittingTerminalPayoff reward
          (Function.update source observer observerResponse) observer -
        quittingTerminalPayoff reward source observer = -1 := by
  rw [update_source_observer, observerFirst, source,
    quittingTerminalPayoff_pureSetRoot,
    quittingTerminalPayoff_pureSetRoot]
  norm_num [quittingSetReward, reward, mover, observer, Finset.ext_iff]

/-- **Strict local compatibility for the corrected Q186 hypotheses.** -/
theorem positiveCommonFiber_signedSourceMismatch :
    Function.update source mover moverTarget = first ∧
      Function.update source observer observerResponse = observerFirst ∧
      Function.update first observer observerResponse = both ∧
      Function.update observerFirst mover moverTarget = both ∧
      quittingTerminalDebtSum reward source = 1 ∧
      quittingTerminalDebtSum reward first = 1 ∧
      quittingTerminalDebtSum reward observerFirst = 1 ∧
      quittingTerminalDebtSum reward both = 1 ∧
      0 < quittingTerminalPayoff reward
            (Function.update first observer observerResponse) observer -
          quittingTerminalPayoff reward first observer ∧
      quittingTerminalPayoff reward
            (Function.update source observer observerResponse) observer -
          quittingTerminalPayoff reward source observer ≤ 0 := by
  refine ⟨update_source_mover, update_source_observer,
    update_first_observer, update_observerFirst_mover, source_totalDebt,
    first_totalDebt, observerFirst_totalDebt, both_totalDebt, ?_, ?_⟩
  · rw [target_observer_gain_eq_one]
    norm_num
  · rw [source_observer_gain_eq_neg_one]
    norm_num

/-- The common positive fiber is not the positive global-minimum fiber.
Indeed no two-player quitting table can have such a minimum. -/
theorem not_exists_positive_globalSemanticDebtMinimum :
    ¬∃ minimum : QuittingTerminalSemanticPair Player,
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalSemanticDebtSum minimum := by
  rintro ⟨minimum, hminimum, hpositive⟩
  have hno := no_uniformPayoff_of_positive_globalSemanticDebtMinimum
    reward minimum hminimum hpositive
  exact hno
    (quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_two
      (by decide) reward)

end MinimumFiberResetSquareCompatibility
end GameTheory
