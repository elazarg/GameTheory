import GameTheory.Cooperative.CoalitionalGame
import GameTheory.Cooperative.Bargaining
import GameTheory.Cooperative.Matching

/-!
# GameTheory.Cooperative

Cooperative and non-strategic-form game-theoretic models. These describe
problems whose game-theoretic content is not captured by the strategic
form (simultaneous-move action choices with payoffs), but rather by
coalition values, axiomatic bargaining over feasible payoff sets, or
combinatorial matching markets.

- `CoalitionalGame` — TU coalitional games, the Shapley value, Banzhaf
  index, convex (supermodular) games, the core, and worked examples.
- `Bargaining` — Nash bargaining solution for two-player bargaining
  problems.
- `Matching` — two-sided matching markets and Gale-Shapley-style
  stability concepts.
-/
