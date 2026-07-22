/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Syntax
import GameTheory.Languages.OpenGame.Compile
import GameTheory.Languages.OpenGame.Sequential
import GameTheory.Languages.OpenGame.DAG
import GameTheory.Languages.OpenGame.Ownership
import GameTheory.Languages.OpenGame.Deviation
import GameTheory.Languages.OpenGame.FinTensor
import GameTheory.Languages.OpenGame.Theorems
import GameTheory.Languages.OpenGame.Correlation
import GameTheory.Languages.OpenGame.Mixed
import GameTheory.Languages.OpenGame.CoendContext
import GameTheory.Languages.OpenGame.Evolutionary
import GameTheory.Languages.Bridges.OpenGame_EFG
import GameTheory.Languages.Bridges.OpenGame_MAID
import GameTheory.Languages.Bridges.OpenGame_Mixed
import GameTheory.Languages.OpenGame.Examples

/-!
# Open Games

Public entrypoint for compositional deterministic open games and their
context-indexed compilation to `KernelGame`.
-/
