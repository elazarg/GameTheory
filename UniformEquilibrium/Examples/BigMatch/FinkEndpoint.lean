/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import UniformEquilibrium.Examples.BigMatch.Fink

/-!
# The Big Match endpoint for corrected Fink selection

This file contains the formal reduction from the local discounted live-value
calculation to failure of the global corrected-calendar selection principle.
The coordinate calculation itself is deliberately kept separate.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace BigMatch

open Filter

/-- If discounted Bellman equilibria have the classical Big Match live value,
then no fast corrected Fink selection exists. -/
theorem not_hasFastFinkCorrectedCalendarSelection_of_halfLiveValue
    (hhalf : HasHalfLiveValueForDiscountedBellmanEquilibria) :
    ¬ game.HasFastFinkCorrectedCalendarSelection := by
  intro hselection
  have hpay : ∀ s a who, |game.stagePayoff s a who| ≤ (1 : ℝ) := by
    intro s a who
    cases s <;> cases who <;>
      simp only [payoff, Bool.false_eq_true, if_false, if_true]
    all_goals simp only [reward]
    all_goals try split <;> norm_num
    all_goals norm_num
  obtain ⟨β, z, zlim, hβ0, hβ1, R, hfix, _hβlim, hz,
      hclose, hselect⟩ := hselection 1 (by norm_num) hpay
  let target : Payoff Player :=
    fun who => if who then -(1 / 2 : ℝ) else (1 / 2 : ℝ)
  have hvalue : ∀ n, game.finkValue (z n) .live = target := by
    intro n
    apply hhalf (β n) (game.finkProfile (z n)) (game.finkValue (z n))
      (hβ0 n) (hβ1 n)
    exact game.isDiscountedStationaryBellmanEq_of_finkMap_fixedPoint
      (β n) 1 (hβ0 n) (hβ1 n).le hpay (z n) (hfix n)
  have hlimit : game.finkValue zlim .live = target := by
    funext who
    have ht := game.tendsto_finkValue_apply hz State.live who
    have heq : (fun n => game.finkValue (z n) State.live who) =
        fun _ => target who := by
      funext n
      exact congrFun (hvalue n) who
    rw [heq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hsched :=
    game.isUniformScheduledMarkovEquilibriumPayoff_of_indexedFinkFixedPoints_correctedTarget
      State.live β 1 hβ0 hβ1 hpay z (game.finkValue zlim)
        (fun s who => game.abs_finkValue_le zlim s who)
        R fastFinkValueError hfix hclose hselect
  apply not_isUniformScheduledMarkovEquilibriumPayoff_half
  simpa only [hlimit, target] using hsched

/-- The Big Match refutes fast corrected Fink calendar selection. -/
theorem not_hasFastFinkCorrectedCalendarSelection :
    ¬ game.HasFastFinkCorrectedCalendarSelection :=
  not_hasFastFinkCorrectedCalendarSelection_of_halfLiveValue
    hasHalfLiveValueForDiscountedBellmanEquilibria

end BigMatch
end StochasticGame
end GameTheory
