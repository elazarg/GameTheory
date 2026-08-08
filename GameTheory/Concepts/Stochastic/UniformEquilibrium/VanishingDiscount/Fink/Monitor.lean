/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Fink.Obstruction
import Math.ProbabilityMassFunction.Monitoring

/-!
# Fink transition-monitor adapter

The generic coordinate-monitor and anytime-learning API lives in
`Math.ProbabilityMassFunction.Monitoring`. This file connects that API to
normalized Fink tangent obstructions.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability
open Filter


namespace NormalizedFinkSupportTangentObstructionFlow

/-- Pair-valued form of the transition-visible monitor certificate, matching the action type of
    the anytime coordinate-monitor learner. -/
theorem exists_pureDeviationCoordinateMonitor_spec
    (G : StochasticGame ι)
    [Fintype G.State] [DecidableEq G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who)
    (hkernel :
      G.finkPureDeviationStateKernel z s who d ≠
        G.finkStateKernel z s) :
    ∃ monitor : PMFCoordinateMonitor G.State,
      expect (G.finkStateKernel z s)
          (pmfCoordinateTestScore
            (G.finkStateKernel z s) monitor.1 monitor.2) = 0 ∧
        0 <
          expect (G.finkPureDeviationStateKernel z s who d)
            (pmfCoordinateTestScore
              (G.finkStateKernel z s) monitor.1 monitor.2) ∧
        ∀ x,
          |pmfCoordinateTestScore
            (G.finkStateKernel z s) monitor.1 monitor.2 x| ≤ 1 := by
  obtain ⟨t, positive, hbaseline, hpositive, hbound⟩ :=
    exists_pureDeviationCoordinateTestScore_spec G z s who d hkernel
  exact ⟨(t, positive), hbaseline, hpositive, hbound⟩

end NormalizedFinkSupportTangentObstructionFlow

end StochasticGame
end GameTheory
