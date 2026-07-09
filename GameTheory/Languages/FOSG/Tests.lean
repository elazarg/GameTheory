/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.FOSG.Basic
import GameTheory.Languages.FOSG.Compile
import GameTheory.Languages.FOSG.Examples
import GameTheory.Languages.FOSG.Theorems

/-!
# GameTheory.Languages.FOSG.Tests

Compilation validation entrypoint for FOSG.

Reader-facing worked examples belong in `GameTheory.Languages.FOSG.Examples`.
-/

namespace GameTheory.FOSG.Tests

open GameTheory.FOSG.Examples

noncomputable section

example : binaryChoice.init = SoloState.start := rfl

example : binaryChoice.terminal (SoloState.done true) := by
  simp [binaryChoice, binaryChoiceTerminal]

example :
    binaryChoiceKernel.Outcome = binaryChoice.History := rfl

example :
    MatchingPennies.kernel.Outcome = MatchingPennies.game.History := rfl

example :
    MatchingPennies.payoff true true MatchingPennies.Player.left = 1 := by
  rfl

example :
    MatchingPennies.payoff true false MatchingPennies.Player.right = 1 := by
  rfl

end

end GameTheory.FOSG.Tests
