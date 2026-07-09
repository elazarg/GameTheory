/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.MAID.Syntax
import GameTheory.Languages.MAID.SOS
import GameTheory.Languages.MAID.Compile
import GameTheory.Languages.MAID.Examples

/-!
# MAID Tests

Compilation/SOS validation entrypoint for MAID.

Reader-facing worked examples belong in `GameTheory.Languages.MAID.Examples`.
-/

namespace MAID.Tests

open _root_.MAID

noncomputable section

example : (_root_.MAID.tinyKG).Strategy 0 = PlayerStrategy _root_.MAID.tinyStruct 0 := rfl

example (pol : Policy _root_.MAID.tinyStruct) :
    (_root_.MAID.tinyKG).outcomeKernel pol =
      evalAssignDist _root_.MAID.tinyStruct _root_.MAID.tinySem pol := rfl

example :
    (_root_.MAID.tinyOrder).order = [0, 1] := rfl

example :
    (_root_.MAID.tinyStruct).parents 1 = {0} := rfl

end

end MAID.Tests
