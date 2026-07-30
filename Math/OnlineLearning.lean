/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Math.OnlineLearning.MultiplicativeWeights
import Math.OnlineLearning.AnytimeMultiplicativeWeights
import Math.OnlineLearning.ContextualMultiplicativeWeights
import Math.OnlineLearning.UniversalCalendar

/-!
# Online learning

Umbrella module. Split across `OnlineLearning/`:

- `MultiplicativeWeights` — the multiplicative-weights (Hedge) algorithm, its
  explicit fixed-rate regret bound, and restartable signed-gain composition.
- `AnytimeMultiplicativeWeights` — a horizon-independent restarted schedule for
  signed gains, with vanishing per-round regret at every sufficiently large horizon.
- `ContextualMultiplicativeWeights` — independent horizon-free local learners
  indexed by revealed contexts, with regret controlled by visitation counts.
- `UniversalCalendar` — a logarithmic scale on the quadratic epoch calendar that
  handles every fixed but unknown polynomial signal order.
-/
