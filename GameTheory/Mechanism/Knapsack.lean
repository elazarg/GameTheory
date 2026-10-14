module

/-
# Finite knapsack allocation and mechanism design

Public opt-in surface for scalar-generic aggregation, real finite-allocation
semantics, exact and checked half-approximate natural-number solvers, and the
canonical pivot-normalized VCG mechanism.
-/

public import GameTheory.Mechanism.Knapsack.Basic
public import GameTheory.Mechanism.Knapsack.Algorithm
public import GameTheory.Mechanism.Knapsack.Correctness
public import GameTheory.Mechanism.Knapsack.ExactBridge
public import GameTheory.Mechanism.Knapsack.ApproximationAlgorithm
public import GameTheory.Mechanism.Knapsack.ApproximationCorrectness
public import GameTheory.Mechanism.Knapsack.Approximation
public import GameTheory.Mechanism.Knapsack.Mechanism

@[expose] public section

namespace GameTheory.Mechanism.Knapsack

end GameTheory.Mechanism.Knapsack
