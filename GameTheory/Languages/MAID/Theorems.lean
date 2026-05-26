/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.MAID.Syntax
import GameTheory.Languages.MAID.SOS
import GameTheory.Languages.MAID.Compile
import GameTheory.Languages.MAID.CompileObs
import GameTheory.Languages.MAID.Kuhn

/-!
# GameTheory.Languages.MAID.Theorems

Thin public theorem interface for MAID.

This file exposes only reductions from native frontier semantics to the compiled
semantic layer. Substantive game-theoretic ports should land in generic theorem
files and then be re-exported here.
-/
