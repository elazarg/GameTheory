/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import Math.PMFProduct

/-!
# Math.Tests

Compilation validation entrypoint for project-local math infrastructure.
-/

namespace Math.Tests

open Math.Probability
open Math.PMFProduct

noncomputable section

example : expect (PMF.pure true) (fun b => if b then (3 : ℝ) else 0) = 3 := by
  simp

example :
    Kernel.comp (Kernel.id Bool) (Kernel.ofFun not) = Kernel.ofFun not := by
  simp

example (σ : Bool → Bool) :
    pmfPi (fun i => (PMF.pure (σ i) : PMF Bool)) = PMF.pure σ :=
  pmfPi_pure σ

end

end Math.Tests
