/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import GameTheory.Concepts.SolutionConcepts

/-!
# GameTheory.Concepts.CorrelatedEqProperties

Structural properties of correlated and coarse correlated equilibria.

Provides:
- `IsCorrelatedEq.toCoarseCorrelatedEq` -- every CE is a CCE
-/

namespace GameTheory

open Math.Probability
namespace KernelGame

variable {ι : Type} [DecidableEq ι] {G : KernelGame ι}

/-- Every correlated equilibrium is a coarse correlated equilibrium.

A constant deviation `fun _ => s'` is a special case of a recommendation-dependent
deviation, so the CE condition (which quantifies over all deviations) implies the
CCE condition (which only considers constant deviations). The two deviation
distributions are definitionally equal: `unilateralDeviation G who (fun _ => s') σ` reduces
to `Function.update σ who s'`. -/
theorem IsCorrelatedEq.toCoarseCorrelatedEq {μ : PMF (Profile G)}
    (hce : G.IsCorrelatedEq μ) : G.IsCoarseCorrelatedEq μ := by
  intro who s'
  exact hce who (fun _ => s')

end KernelGame
end GameTheory
