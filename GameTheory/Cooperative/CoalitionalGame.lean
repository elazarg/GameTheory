/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Cooperative.CoalitionalGame.Core
import GameTheory.Cooperative.CoalitionalGame.Shapley
import GameTheory.Cooperative.CoalitionalGame.Banzhaf
import GameTheory.Cooperative.CoalitionalGame.Convex
import GameTheory.Cooperative.CoalitionalGame.Additive
import GameTheory.Cooperative.CoalitionalGame.CostOfStability
import GameTheory.Cooperative.CoalitionalGame.Bondareva

/-!
# Coalitional Games and the Shapley Value

Umbrella module. Split across `CoalitionalGame/`:

- `Core` — the `CoalGame` structure, the core (`IsCore`), and core closure
  under linear game operations.
- `Shapley` — unanimity games and the Shapley value with its uniqueness.
- `Banzhaf` — the Banzhaf power index and simple games.
- `Convex` — convex (supermodular) coalitional games.
- `Additive` — additive games and the 3-player majority worked example.
- `CostOfStability` — the least subsidy that makes the core nonempty.
- `Bondareva` — balancedness and the easy direction of Bondareva–Shapley.
-/
