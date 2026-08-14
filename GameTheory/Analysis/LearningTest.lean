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
      IsεCoarseCorrelatedEq game.form game.utility epsilon law := by
  apply game.mwSelfPlay_exists_isεCoarseCorrelatedEq_of_pos
    (lo := fun _ => 0) (width := 1) (L := Real.log 2)
    (by norm_num)
  · intro who outcome
    simp only [utility]
    split <;> norm_num
  · intro who
    simp
  · exact hepsilon

/-- At horizon four, the same concrete game consumes the closed-form
square-root rate with the exact common log-cardinality bound `log 2`. -/
theorem multiplicativeWeights_selfPlay_sqrt_rate_four :
    IsεCoarseCorrelatedEq game.form game.utility
      (1 * (2 * Real.sqrt (Real.log 2 * 4)) / 4)
      (game.form.timeAverage fun round : Fin 4 =>
        FinDist.pi
          (game.mwProfile (Real.sqrt (Real.log 2 / 4))
            (fun _ => 0) 1 (round : ℕ))) := by
  apply game.mwSelfPlay_timeAverage_isεCoarseCorrelatedEq_sqrt
    (lo := fun _ => 0) (width := 1) (L := Real.log 2) 4
  · exact Real.log_pos (by norm_num)
  · calc
      Real.log 2 ≤ (2 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num)
      _ ≤ 4 := by norm_num
  · norm_num
  · intro who outcome
    simp only [utility]
    split <;> norm_num
  · intro who
    simp

/-- The positive-log tuning premise rules out the meaningless zero-horizon
specialization. -/
theorem logTwo_not_bounded_by_zero : ¬ Real.log 2 ≤ (0 : ℝ) :=
  not_le_of_gt (Real.log_pos (by norm_num))

end GameTheory.Tests.Learning
