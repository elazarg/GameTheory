/-
# Multiplicative-weights self-play test

The Core-owned learning test supplies a discriminating finite coordination
game.  This Analysis-owned test is the only place where that fixture reaches
the opt-in exponential-weights bridge.
-/

import GameTheory.Analysis.Learning
import GameTheory.Tests.Learning

noncomputable section

namespace GameTheory.Tests.Learning

open Probability

/-- The quantitative bridge is non-vacuous on the concrete two-player game:
for every positive tolerance, its finite multiplicative-weights trajectory
exhibits a canonical approximate CCE law. -/
theorem multiplicativeWeights_selfPlay_api {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ law : FinDist (Profile signature),
      game.IsεCoarseCorrelatedEq epsilon law := by
  apply game.mwSelfPlay_exists_isεCoarseCorrelatedEq_of_pos
    (lo := fun _ => 0) (width := 1) (L := Real.log 2)
    (by norm_num)
  · intro who outcome
    simp only [utility]
    split <;> norm_num
  · intro who
    simp
  · exact hepsilon

end GameTheory.Tests.Learning
