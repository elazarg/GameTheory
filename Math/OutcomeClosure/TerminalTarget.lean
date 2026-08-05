/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.OutcomeClosure
import Math.Probability

/-!
# Distributional target transport for outcome-closure value processes

Distributional outcome closure transports every coordinate of a terminal
target map: reading a target through the observation map of a finite value
process at any horizon past its rank agrees with reading it under the
process's limiting value law.
-/

noncomputable section

namespace Math
namespace OutcomeClosure
namespace ValueProcess

open Math.Probability

variable {S Ω Player : Type*}

/-- Distributional outcome closure transports every coordinate of a
terminal target map. -/
theorem expect_terminalTarget_eq
    (R : ValueProcess S Ω) (terminalTarget : Ω → Player → ℝ)
    (n : ℕ) (s : S) (hn : R.rank s ≤ n) (who : Player) :
    expect (R.run n s)
        (fun terminal => terminalTarget (R.observe terminal) who) =
      expect (R.value s) (fun outcome => terminalTarget outcome who) := by
  calc
    expect (R.run n s)
        (fun terminal => terminalTarget (R.observe terminal) who) =
      expect (PMF.map R.observe (R.run n s))
        (fun outcome => terminalTarget outcome who) := by
          symm
          exact expect_map R.observe (R.run n s)
            (fun outcome => terminalTarget outcome who)
    _ = expect (R.value s)
        (fun outcome => terminalTarget outcome who) := by
          rw [R.map_observe_run_eq_value n s hn]

end ValueProcess
end OutcomeClosure
end Math
