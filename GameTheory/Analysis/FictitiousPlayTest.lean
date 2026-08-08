/-
Analytic consumer of the finite fictitious-play fixture.

The Core test already separates nonconstant empirical-law arithmetic from the
constant best-response trajectory.  This file checks that the latter passes
through the shared finite-law convergence interface and the public
limit-to-Nash theorem.
-/

import GameTheory.Analysis.Learning
import GameTheory.Tests.FictitiousPlay

noncomputable section

namespace GameTheory.Tests.FictitiousPlay

/-- Every coordinate of the constant history's empirical belief converges to
the corresponding pure mixed strategy. -/
theorem constant_empiricalBelief_converges (who : Fin 2) :
    Analysis.FinDistConvergesPointwise
      (fun t => game.empiricalBelief constantHistory (t + 1) who)
      (game.form.purify coordinated who) := by
  have hsequence :
      (fun t => game.empiricalBelief constantHistory (t + 1) who) =
        fun _ => game.form.purify coordinated who := by
    funext t
    exact congrFun (constant_empiricalBelief t) who
  rw [hsequence]
  exact Analysis.finDistConvergesPointwise_const _

/-- The analytic theorem returns the sole canonical mixed Nash predicate on
the concrete fictitious-play trajectory. -/
theorem constant_limit_isNash :
    IsNash game.form.mixed (euPreference game.utility)
      (game.form.purify coordinated) :=
  UtilityGame.IsFictitiousPlay.limit_isNash
    (G := game) constant_isFictitiousPlay constant_empiricalBelief_converges

end GameTheory.Tests.FictitiousPlay
