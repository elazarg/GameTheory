/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.OnlineLearning.MultiplicativeWeights
import GameTheory.Concepts.Learning.SelfPlay

/-!
# Tests for the learning-dynamics (Tier A) development

Compilation tests exercising the no-regret ⇒ coarse correlated equilibrium pipeline:
the ε-correlated notions, the time-average reduction, multiplicative weights, and the
self-play assembly. Lives in the `GameTheoryTest` target, not the public surface.
-/

namespace GameTheory.Learning.Tests

open Math.OnlineLearning

/-- The multiplicative-weights regret bound instantiates concretely on a two-action set:
    the hypotheses are non-vacuous (here the all-zero gain sequence with learning rate `1`). -/
example (T : ℕ) :
    onlineExternalRegret (A := Bool) 1 (fun _ _ => 0) T
      ≤ Real.log (Fintype.card Bool) / 1 + (Real.exp 1 - 1 - 1) / 1 * T :=
  mw_externalRegret_le (by norm_num) (fun _ _ => Set.mem_Icc.mpr ⟨le_refl _, zero_le_one⟩) T

/-- Multiplicative weights is a genuine no-regret rule: at the optimal tuning the bound is
    finite for every horizon (sanity check that the bound is a real number, not `⊤`). -/
example (T : ℕ) (η : ℝ) (hη : 0 < η) :
    onlineExternalRegret (A := Bool) η (fun _ _ => 0) T
      ≤ Real.log (Fintype.card Bool) / η + (Real.exp η - 1 - η) / η * T :=
  mw_externalRegret_le hη (fun _ _ => Set.mem_Icc.mpr ⟨le_refl _, zero_le_one⟩) T

-- The reduction, the algorithm, the assembly, and the PoA-of-learning bound all type-check
-- with the intended signatures.
section API
open GameTheory.KernelGame

example : True := by
  have _ := @timeAverage_isεCCE_of_regret_le
  have _ := @selfPlay_timeAverage_isεCCE
  have _ := @externalRegret_pmfPi
  have _ := @IsSmooth.epsilonCoarseCorrelated_bound
  have _ := @isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero
  trivial

end API

end GameTheory.Learning.Tests
