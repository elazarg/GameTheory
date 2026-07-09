/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.MAID.Syntax
import GameTheory.Languages.MAID.SOS
import GameTheory.Languages.MAID.FrontierEval
import GameTheory.Languages.MAID.Prefix
import GameTheory.Languages.MAID.Compile
import GameTheory.Languages.MAID.Theorems

/-!
# GameTheory.Languages.MAID

Public entrypoint for the MAID language layer.

The intent is the same as for the other languages:
- `Syntax` and `SOS` present the language natively
- `Compile` targets the generic semantic layer
- `Theorems` remains a thin reduction interface
- `Examples` stays separate from `Tests`
-/
