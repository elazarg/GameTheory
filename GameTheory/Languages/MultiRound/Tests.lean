/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.MultiRound.Syntax
import GameTheory.Languages.MultiRound.SOS
import GameTheory.Languages.MultiRound.Compile
import GameTheory.Languages.MultiRound.Theorems
import GameTheory.Languages.MultiRound.AbsentMindedDriver

/-!
# GameTheory.Languages.MultiRound.Tests

Compilation/SOS validation entrypoint for MultiRound.

Reader-facing worked examples belong in `GameTheory.Languages.MultiRound.Examples`.
-/

namespace GameTheory.Languages.MultiRound.Tests

open GameTheory.MultiRound

noncomputable section

example : absentMindedProtocol.init = AMDState.atFirst := rfl

example : absentMindedProtocol.rounds.length = 2 := rfl

example :
    (absentMindedProtocol.toKernelGame (fun s _ => absentMindedPayoff s)).Outcome = AMDState := rfl

example :
    absentMindedRound₁.view 0 AMDState.atFirst () = AMDView.intersection := rfl

example :
    absentMindedRound₂.transition AMDState.atSecond
      (fun _ => some AMDAction.exit) = AMDState.tookSecondExit := rfl

example : ¬ absentMindedProtocol.ViewDeterminesRound :=
  absentMindedProtocol_not_viewDeterminesRound

end

end GameTheory.Languages.MultiRound.Tests
