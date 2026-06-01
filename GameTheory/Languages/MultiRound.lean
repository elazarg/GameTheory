/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.MultiRound.Syntax
import GameTheory.Languages.MultiRound.SOS
import GameTheory.Languages.MultiRound.Compile
import GameTheory.Languages.MultiRound.Theorems

/-!
# GameTheory.Languages.MultiRound

Public entrypoint for the sequential/protocol language layer.

`Syntax` and `SOS` are the source-language presentation; `Compile` and
`Theorems` are the reduction interface to the generic semantic stack.
Reader-facing `Examples` stays separate from compilation `Tests`.
-/
