/-
Scalar-generic finite-set aggregation for knapsack allocations.

This leaf is shared by the executable natural-number solver and the
real-valued mechanism semantics.  It deliberately imports no game semantics.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic

namespace GameTheory.Mechanism.Knapsack

open scoped BigOperators

variable {Agent R : Type} [DecidableEq Agent] [AddCommMonoid R]

/-- Aggregate a scalar quantity over a finite selected allocation. -/
def aggregate (amount : Agent → R) (selected : Finset Agent) : R :=
  ∑ agent ∈ selected, amount agent

/-- Total scalar weight of a finite selected allocation. -/
abbrev load (weight : Agent → R) (selected : Finset Agent) : R :=
  aggregate weight selected

/-- Total scalar value of a finite selected allocation. -/
abbrev welfare (value : Agent → R) (selected : Finset Agent) : R :=
  aggregate value selected

end GameTheory.Mechanism.Knapsack
