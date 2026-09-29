/-
Analytic consumer for finite exact-potential fictitious-play convergence.

The imported hostile trace has a strictly positive first gain and a nonzero
first potential increment, so these asymptotic conclusions are not witnessed
only by a stationary equilibrium path.
-/

import GameTheory.Analysis.FictitiousPlayPotential
import GameTheory.Tests.FictitiousPlayPotential

noncomputable section

namespace GameTheory.Analysis.FictitiousPlayPotentialTest

open Filter
open Tests.FictitiousPlayPotential

theorem improvement_tendsto_zero :
    Tendsto (fun t : ℕ =>
      game.mixedImprovement (game.form.empiricalBelief history (t + 1)))
      atTop (nhds 0) :=
  UtilityGame.IsExactPotential.mixedImprovement_empiricalBelief_tendsto_zero
    (G := game) exactPotential isFictitiousPlay

/-- The nonstationary hostile path eventually satisfies every positive-error
approximate Nash condition. -/
theorem eventually_isεNash {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop,
      IsεNash game.form.mixed game.utility ε
        (game.form.empiricalBelief history (t + 1)) :=
  UtilityGame.IsExactPotential.eventually_isεNash_of_isFictitiousPlay
    (G := game) exactPotential isFictitiousPlay hε

end GameTheory.Analysis.FictitiousPlayPotentialTest
