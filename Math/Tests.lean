/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import Math.PMFProduct
import Math.OnlineAlgorithms

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

namespace OnlineAlgorithms

open Math.OnlineAlgorithms

def stopOnTrue : OnlineAlgorithm Bool Unit Bool where
  init := ()
  step _ r := ((), r.bind fun b => if b then some true else none)

example : stopOnTrue.runResult () [false, true, false] = some true := by
  rfl

example : stopOnTrue.runAll () [false, true, true] = [true, true] := by
  rfl

end OnlineAlgorithms

end Math.Tests
