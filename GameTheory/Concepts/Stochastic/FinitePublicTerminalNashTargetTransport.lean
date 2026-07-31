/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FiniteChildTargetAlternative
import GameTheory.Concepts.Stochastic.FinitePublicTerminalNashSystem

/-!
# Target transport from a finite public terminal Nash system

Backward Nash selection on a finite public-history tree produces an
endogenous root payoff.  The actual prescribed terminal-history law is a
lottery whose expected whole payoff vector is exactly that root payoff.
Consequently, when the public state space is finite, the root payoff belongs
to the convex hull of the terminal-history payoff vectors.

This does not identify the endogenous root payoff with an externally
prescribed analytic target, nor does it turn terminal histories into legal
lower-rank continuation children.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace FinitePublicTerminalNashSystem

open Math.Probability

variable {ι : Type} {G : StochasticGame ι}
  [Fintype ι] [DecidableEq ι]
  [Finite G.State]
  [∀ who, Fintype (G.Act who)]
  [∀ who, Nonempty (G.Act who)]
  {fuel : ℕ}

/-- The prescribed terminal-history law is an operational lottery realizing
the endogenous backward-Nash root payoff coordinatewise. -/
theorem rootPayoff_isFiniteChildTargetLottery
    (obstacle : G.Hist fuel → Payoff ι)
    (initial : G.State) :
    IsFiniteChildTargetLottery obstacle
      (rootPayoff (G := G) obstacle initial) := by
  refine
    ⟨G.histDist (profile (G := G) obstacle) initial fuel, ?_⟩
  intro who
  exact expect_obstacle_profile_eq_root obstacle initial who

/-- For finite public state spaces, the endogenous backward-Nash root payoff
lies in the convex hull of the terminal-history payoff vectors. -/
theorem rootPayoff_isFiniteChildTargetTransportable
    (obstacle : G.Hist fuel → Payoff ι)
    (initial : G.State) :
    IsFiniteChildTargetTransportable obstacle
      (rootPayoff (G := G) obstacle initial) :=
  (isFiniteChildTargetTransportable_iff_lottery
    obstacle (rootPayoff (G := G) obstacle initial)).2
      (rootPayoff_isFiniteChildTargetLottery obstacle initial)

end FinitePublicTerminalNashSystem
end StochasticGame
end GameTheory
