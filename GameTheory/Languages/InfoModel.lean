/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.InfoModel.SemanticForm
import GameTheory.Languages.InfoModel.InfoGame
import GameTheory.Languages.InfoModel.Simulation

/-!
# GameTheory.Languages.InfoModel

Information-model game language: multi-agent state machines with public and
private observation layers, execution dynamics, and the InfoModel lemma library.

`InfoGame` is re-exported as an optional public extension point for packaging a
common-knowledge control specification with an `InfoModel`. The current EFG,
MAID, and MultiRound compilers target `InfoModel` directly.
-/
