/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.KernelGame

/-!
# GameTheory.Core.Tests

Compilation validation entrypoint for the kernel-game core.
-/

namespace GameTheory.Core.Tests

open Math.Probability

noncomputable section

def boolGame : KernelGame Bool :=
  KernelGame.ofPureEU (fun _ => Bool) (fun σ i => if σ i then (1 : ℝ) else 0)

def trueProfile : KernelGame.Profile boolGame :=
  fun _ => true

example : boolGame.eu trueProfile false = 1 := by
  simp [boolGame, trueProfile]

example :
    boolGame.correlatedOutcome (PMF.pure trueProfile) =
      boolGame.outcomeKernel trueProfile :=
  KernelGame.correlatedOutcome_pure boolGame trueProfile

example : boolGame.outcomeKernel trueProfile = PMF.pure trueProfile :=
  rfl

end

end GameTheory.Core.Tests
