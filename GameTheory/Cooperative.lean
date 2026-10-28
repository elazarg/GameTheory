module

/-
# Opt-in cooperative and market-design theories

Foundational coalitional games remain in `GameTheory.Core`.  This root exposes
larger parallel theories whose native objects are not artificial strategic
forms.  It is intentionally absent from the lightweight `GameTheory` umbrella.
-/

public import GameTheory.Core.Coalitional
public import GameTheory.Cooperative.Balancedness
public import GameTheory.Cooperative.Banzhaf
public import GameTheory.Cooperative.Bargaining
public import GameTheory.Cooperative.Convex
public import GameTheory.Cooperative.GaleShapley.Perfect
public import GameTheory.Cooperative.GaleShapley.Optimality
public import GameTheory.Cooperative.GaleShapley.Unmatched
public import GameTheory.Cooperative.GaleShapley.Strategyproof
public import GameTheory.Cooperative.ShapleyShubik

@[expose] public section

namespace GameTheory

end GameTheory
