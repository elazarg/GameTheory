import GameTheory.Math.GridRoutedGraph
import Mathlib.Tactic.IntervalCases

/-! Actual grid-pointer controls exercise adjacent switch boxes, displaced
centers, background isolation, known sources and disconnected cycle components. -/

namespace GameTheory.Tests.GridRoutedGraph

open GameTheory.Math.GridWire GameTheory.Math.GridCrossing GameTheory.Math.EndOfLine

private def fixtureS : ℕ → ℕ
  | 0 => 4
  | 1 => 3
  | 2 => 0
  | i => i

private def fixtureP : ℕ → ℕ
  | 0 => 2
  | 3 => 1
  | 4 => 0
  | i => i

private theorem fixtureP_bound : ∀ i, i < 5 → fixtureP i < 5 := by
  intro i hi
  interval_cases i <;> decide

private theorem fixtureS_bound : ∀ i, i < 5 → fixtureS i < 5 := by
  intro i hi
  interval_cases i <;> decide

example : crossingOwners 5 fixtureP fixtureS (12, 3) = some (2, 0) ∧
    crossingOwners 5 fixtureP fixtureS (12, 6) = some (1, 0) := by decide

example : decodeWireNode 5 fixtureP fixtureS (13, 4) = some (.inr (2, (12, 3))) ∧
    decodeWireNode 5 fixtureP fixtureS (11, 2) = some (.inr (0, (12, 3))) ∧
    decodeWireNode 5 fixtureP fixtureS (12, 3) = none ∧
    decodeWireNode 5 fixtureP fixtureS (11, 4) = none := by decide

example : gridRoutedSuccessor 5 fixtureP fixtureS (13, 3) = (13, 4) ∧
    gridRoutedSuccessor 5 fixtureP fixtureS (13, 4) = (12, 4) ∧
    gridRoutedSuccessor 5 fixtureP fixtureS (12, 4) = (12, 5) ∧
    gridRoutedSuccessor 5 fixtureP fixtureS (12, 5) = (13, 5) ∧
    gridRoutedSuccessor 5 fixtureP fixtureS (13, 5) = (13, 6) := by decide

example : gridRoutedPredecessor 5 fixtureP fixtureS (12, 5) = (12, 4) ∧
    gridRoutedPredecessor 5 fixtureP fixtureS (12, 4) = (13, 4) ∧
    gridRoutedPredecessor 5 fixtureP fixtureS (13, 4) = (13, 3) := by decide

example : gridRoutedPredecessor 5 fixtureP fixtureS (vertexPoint 2) = vertexPoint 2 ∧
    gridRoutedSuccessor 5 fixtureP fixtureS (vertexPoint 2) ≠ vertexPoint 2 ∧
    gridRoutedPredecessor 5 fixtureP fixtureS
      (gridRoutedSuccessor 5 fixtureP fixtureS (vertexPoint 2)) = vertexPoint 2 :=
  gridRouted_source (by decide) (by decide) (by decide) (by decide) (by decide)

example (p : ℕ × ℕ) :
    IsEndpoint (gridRoutedPredecessor 5 fixtureP fixtureS)
        (gridRoutedSuccessor 5 fixtureP fixtureS) p ↔
      p = vertexPoint 1 ∨ p = vertexPoint 2 ∨ p = vertexPoint 3 ∨ p = vertexPoint 4 := by
  constructor
  · intro he
    obtain ⟨i, hi, rfl, hend⟩ := gridRouted_endpoint_decodes fixtureP_bound fixtureS_bound he
    have h : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      interval_cases i <;> simp_all [IsEndpoint, HasSuccessor, HasPredecessor, fixtureP, fixtureS]
    rcases h with rfl | rfl | rfl | rfl <;> simp
  · intro h
    rcases h with rfl | rfl | rfl | rfl <;>
      exact (gridRouted_vertex_endpoint_iff (by decide) fixtureP_bound fixtureS_bound).mpr
        (by decide)

private def cycleS : ℕ → ℕ
  | 0 => 1
  | 2 => 3
  | 3 => 2
  | i => i

private def cycleP : ℕ → ℕ
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | i => i

private theorem cycleP_bound : ∀ i, i < 4 → cycleP i < 4 := by
  intro i hi
  interval_cases i <;> decide

private theorem cycleS_bound : ∀ i, i < 4 → cycleS i < 4 := by
  intro i hi
  interval_cases i <;> decide

example (p : ℕ × ℕ) :
    IsEndpoint (gridRoutedPredecessor 4 cycleP cycleS) (gridRoutedSuccessor 4 cycleP cycleS) p ↔
      p = vertexPoint 0 ∨ p = vertexPoint 1 := by
  constructor
  · intro he
    obtain ⟨i, hi, rfl, hend⟩ := gridRouted_endpoint_decodes cycleP_bound cycleS_bound he
    have h : i = 0 ∨ i = 1 := by
      interval_cases i <;> simp_all [IsEndpoint, HasSuccessor, HasPredecessor, cycleP, cycleS]
    rcases h with rfl | rfl <;> simp
  · intro h
    rcases h with rfl | rfl <;>
      exact (gridRouted_vertex_endpoint_iff (by decide) cycleP_bound cycleS_bound).mpr (by decide)

example : crossingOwners 5 (fun i => if i = 4 then 4 else fixtureP i)
    fixtureS (12, 6) = none := by decide

private def downS : ℕ → ℕ
  | 3 => 0
  | 4 => 2
  | i => i

private def downP : ℕ → ℕ
  | 0 => 3
  | 2 => 4
  | i => i

example : crossingOwners 5 downP downS (45, 15) = some (4, 3) ∧
    gridRoutedSuccessor 5 downP downS (46, 15) = (46, 14) ∧
    gridRoutedSuccessor 5 downP downS (46, 14) = (45, 14) ∧
    gridRoutedSuccessor 5 downP downS (45, 16) = (44, 16) ∧
    gridRoutedSuccessor 5 downP downS (44, 16) = (44, 15) := by decide

example : gridRoutedSuccessor 0 fixtureP fixtureS (100, 100) = (100, 100) ∧
    gridRoutedPredecessor 0 fixtureP fixtureS (100, 100) = (100, 100) ∧
    decodeWireNode 5 fixtureP fixtureS (100, 100) = none := by decide

end GameTheory.Tests.GridRoutedGraph
