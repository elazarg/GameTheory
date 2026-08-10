/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeReachableCarryTelescope
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalPacketSimpleFallbackCounterexample

/-!
# Nonpositive punishment does not erase the zero-boundary terminal cap

The terminal state in the intrinsic finite-chain carry telescope has exact
aggregate debt

`sum_i max(0, r_i({i}))`.

It is tempting to expect a coordinatewise nonpositive behavioral punishment
vector to make this terminal debt vanish.  The existing two-player terminal
packet regression disproves that implication.  Both players can be punished
to a nonpositive value by explicit stationary opponent rows, while player
one's positive-singleton terminal cap is exactly one.

This finite regression does not instantiate a counterexample regime and does
not compute its global admissible charge capacity.  Its role is narrower: it
shows that the automatic zero-cap closure of the terminal carry gate is a
strict subclass of `punishmentValue ≤ 0`; a quantitative incoming-path or
same-state capacity premise is still genuinely required.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

namespace QuittingNonpositiveFloorTerminalCapRegression

open QuittingTerminalPacketSimpleFallbackCounterexample

/-- The existing finite two-player table has coordinatewise nonpositive
behavioral punishment values. -/
theorem punishmentValue_nonpos (who : Bool) :
    quittingPunishmentValue reward who ≤ 0 := by
  let halfRoot := approximateRoot (1 / 2) (by norm_num) (by norm_num)
  have hcap := quittingPunishmentValue_le_stationaryUnilateralCap
    reward who halfRoot
  cases who with
  | false =>
      rw [show halfRoot = approximateRoot (1 / 2)
          (by norm_num) (by norm_num) by rfl,
        unilateralCap_approximateRoot_false] at hcap
      exact hcap.trans (by norm_num)
  | true =>
      rw [show halfRoot = approximateRoot (1 / 2)
          (by norm_num) (by norm_num) by rfl,
        unilateralCap_approximateRoot_true (hapositive := by norm_num)] at hcap
      exact hcap.trans (by norm_num)

/-- Nevertheless player one's exact zero-boundary terminal cap is positive. -/
theorem positive_terminalCap :
    0 < quittingPositiveSingletonDebtCap reward false := by
  rw [positiveSingletonDebtCap_false]
  norm_num

/-- Hence nonpositive punishment does not imply the cap-zero premise that
automatically closes the intrinsic finite-chain carry telescope. -/
theorem not_terminalCap_eq_zero_of_punishmentValue_nonpos :
    (∀ who : Bool, quittingPunishmentValue reward who ≤ 0) ∧
      ¬ (∀ who : Bool,
        quittingPositiveSingletonDebtCap reward who = 0) := by
  refine ⟨punishmentValue_nonpos, ?_⟩
  intro hzero
  have := hzero false
  rw [positiveSingletonDebtCap_false] at this
  norm_num at this

end QuittingNonpositiveFloorTerminalCapRegression

end GameTheory
