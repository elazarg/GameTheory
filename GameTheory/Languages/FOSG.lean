/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.FOSG.Basic
import GameTheory.Languages.FOSG.History
import GameTheory.Languages.FOSG.Information
import GameTheory.Languages.FOSG.Strategy
import GameTheory.Languages.FOSG.Values
import GameTheory.Languages.FOSG.Execution
import GameTheory.Languages.FOSG.Compile
import GameTheory.Languages.FOSG.OutcomeClosure
import GameTheory.Languages.FOSG.Serial
import GameTheory.Languages.FOSG.Kuhn
import GameTheory.Languages.FOSG.Theorems

/-!
# GameTheory.Languages.FOSG

Umbrella import for factored-observation stochastic games.

`FOSG.Serial` is included as experimental structural infrastructure. Its
serializer proves construction invariants, but no semantic-preservation or
equilibrium-transport theorem is currently exported; clients needing the
established semantic bridge should use `Languages.Bridges.FOSG.AugmentedEFG`.
-/
