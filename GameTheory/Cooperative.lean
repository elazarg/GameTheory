/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Cooperative.CoalitionalGame
import GameTheory.Cooperative.Bargaining
import GameTheory.Cooperative.Matching

/-!
# GameTheory.Cooperative

The **cooperative game theory** branch — a separate paradigm from the
rest of `GameTheory`, which formalizes non-cooperative game theory
(strategies, best responses, Nash equilibrium, all built over
`KernelGame`).

The cooperative tradition takes *coalitions*, *feasible payoff sets*, or
*preference rankings* as primitive rather than per-player strategies. As
a consequence, none of the files in this folder go through `KernelGame`
or import `Concepts.Equilibrium.SolutionConcepts` / `Concepts.Existence.NashExistence` / etc.
Apart from the player-index type and `ℝ`, this branch shares no
load-bearing abstractions with the non-cooperative core; it lives under
the same package only for packaging convenience.

Caveat on the word "cooperative": in this library it refers to the
formalism (coalition-value functions, axiomatic solution concepts) and
NOT to "strategic games whose players have aligned interests" — the
latter is *non-cooperative content* in the cooperative-behavior sense
and lives in the strategic branch as `IsTeamGame`, `SymmetricGame`, etc.

- `CoalitionalGame` — TU coalitional games, the Shapley value, Banzhaf
  index, convex (supermodular) games, the core, and worked examples.
- `Bargaining` — Nash bargaining solution for two-player bargaining
  problems.
- `Matching` — two-sided matching markets and Gale-Shapley-style
  stability concepts.
-/
