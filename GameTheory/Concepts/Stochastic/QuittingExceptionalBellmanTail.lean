/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingBellmanTelescope

/-!
# Finite exceptional-clock Bellman tail

The exceptional branch has two independent finite survival coordinates:
`π`, the opponents' survival probability, and `α`, the prescribed player's
own survival probability.  This file keeps both coordinates.  In particular,
it does not discard the own-never atom `π * R * α` and makes no infinite-tail
closure claim.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

/-- The two finite exceptional-tail estimates imply the corrected cap-gap
bound, including the own-never atom. -/
theorem exceptionalBellmanGap_le_of_prescribed_and_cap_bounds
    (prescribed cap opponentSurvival ownSurvival soloReward bound : ℝ)
    (hprescribed :
      |prescribed - opponentSurvival * soloReward * (1 - ownSurvival)| ≤
        bound * (1 - opponentSurvival))
    (hcap :
      cap ≤ opponentSurvival * soloReward +
        bound * (1 - opponentSurvival)) :
    cap - prescribed ≤
      opponentSurvival * soloReward * ownSurvival +
        2 * bound * (1 - opponentSurvival) := by
  rw [abs_le] at hprescribed
  nlinarith

end GameTheory
