/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Classification.AnalyticWaist

/-!
# Every counterexample regime carries a normalized singleton source packet

The analytic waist theorem states that a finite quitting game either has a
uniform-equilibrium payoff or exports a normalized singleton source packet.
A counterexample regime refutes the first branch outright, so the packet is
forced: any counterexample reward table comes equipped with simplex weights
over its players and a target payoff vector satisfying the source
inequality, the punishment and singleton floors, and diagonal
complementarity on the support.

This adds a finite semialgebraic necessary condition to the regime: the
packet's constraints are finitely many polynomial equalities and
inequalities in the reward table and the packet data, so search code can
reject a candidate table by proving the packet system infeasible.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleRegime

/-- **Forced analytic packet.**  A counterexample regime refutes the uniform
branch of the analytic waist, so the reward table exports a normalized
singleton source packet. -/
theorem nonempty_normalizedSingletonSourcePacket
    (regime : QuittingCounterexampleRegime reward) :
    Nonempty (QuittingNormalizedSingletonSourcePacket reward) := by
  rcases quittingGame_uniformPayoff_or_normalizedSingletonSourcePacket
      reward with hpayoff | hpacket
  · exact absurd hpayoff regime.not_exists_uniformEquilibriumPayoff
  · exact hpacket

end QuittingCounterexampleRegime

end GameTheory
