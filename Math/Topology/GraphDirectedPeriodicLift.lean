/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Topology.GraphDirectedCompactPullback

/-!
# Periodic lifts and common-prefix continuity

In a compact graph-directed pullback system with a common strict contraction,
the unique compatible value path inherits every period of its vertex/edge
code.  Thus a closed combinatorial support word has a closed geometric lift;
there is no hidden aperiodic continuation above a periodic code.

Two compatible lifts whose edge codes share a finite prefix are exponentially
close at its start.  When the two terminal points lie in the same vertex box,
the common finite-box diameter gives a code-independent bound.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Topology

variable {Vertex Edge Point : Type*} [MetricSpace Point]

/-- Two compatible lifts whose edge codes agree for `fuel` steps satisfy the
same contraction estimate over that common prefix. -/
theorem dist_compatiblePullbackPath_le_pow_mul_of_commonPrefix
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex₁ vertex₂ : ℕ → Vertex) (edge₁ edge₂ : ℕ → Edge)
    (hpath₁ : system.IsAdmissiblePath vertex₁ edge₁)
    (hpath₂ : system.IsAdmissiblePath vertex₂ edge₂)
    {contraction : ℝ} (hcontraction0 : 0 ≤ contraction)
    (hcontract : system.IsUniformContraction contraction)
    {value₁ value₂ : ℕ → Point}
    (hvalue₁ : system.IsCompatiblePullbackPath vertex₁ edge₁ value₁)
    (hvalue₂ : system.IsCompatiblePullbackPath vertex₂ edge₂ value₂) :
    ∀ start fuel,
      (∀ offset, offset < fuel →
        edge₁ (start + offset) = edge₂ (start + offset)) →
      dist (value₁ start) (value₂ start) ≤
        contraction ^ fuel *
          dist (value₁ (start + fuel)) (value₂ (start + fuel)) := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp
  | succ fuel ih =>
      intro hedge
      have hedge0 : edge₁ start = edge₂ start := by
        simpa using hedge 0 (Nat.zero_lt_succ fuel)
      have hpoint₁ : value₁ (start + 1) ∈
          system.box (system.target (edge₁ start)) := by
        rw [(hpath₁ start).2]
        exact hvalue₁.1 (start + 1)
      have hpoint₂ : value₂ (start + 1) ∈
          system.box (system.target (edge₁ start)) := by
        rw [hedge0, (hpath₂ start).2]
        exact hvalue₂.1 (start + 1)
      have hone := hcontract (edge₁ start) _ hpoint₁ _ hpoint₂
      have htail := ih (start + 1) (fun offset hoffset ↦ by
        have hcode := hedge (offset + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcode)
      have hscaled := mul_le_mul_of_nonneg_left htail hcontraction0
      calc
        dist (value₁ start) (value₂ start) =
            dist (system.branch (edge₁ start) (value₁ (start + 1)))
              (system.branch (edge₁ start) (value₂ (start + 1))) := by
                rw [hvalue₁.2 start, hvalue₂.2 start, hedge0]
        _ ≤ contraction * dist (value₁ (start + 1))
              (value₂ (start + 1)) := hone
        _ ≤ contraction * (contraction ^ fuel *
              dist (value₁ (start + 1 + fuel))
                (value₂ (start + 1 + fuel))) := hscaled
        _ = contraction ^ fuel.succ *
              dist (value₁ (start + fuel.succ))
                (value₂ (start + fuel.succ)) := by
              rw [pow_succ]
              have hindex : start + 1 + fuel = start + fuel.succ := by omega
              rw [hindex]
              ring

/-- Quantitative continuity of the coding map: a common edge prefix whose
terminal vertices agree gives exponentially close current values. -/
theorem dist_compatiblePullbackPath_le_pow_mul_diameter_of_commonPrefix
    [Fintype Vertex]
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex₁ vertex₂ : ℕ → Vertex) (edge₁ edge₂ : ℕ → Edge)
    (hpath₁ : system.IsAdmissiblePath vertex₁ edge₁)
    (hpath₂ : system.IsAdmissiblePath vertex₂ edge₂)
    {contraction : ℝ} (hcontraction0 : 0 ≤ contraction)
    (hcontract : system.IsUniformContraction contraction)
    {value₁ value₂ : ℕ → Point}
    (hvalue₁ : system.IsCompatiblePullbackPath vertex₁ edge₁ value₁)
    (hvalue₂ : system.IsCompatiblePullbackPath vertex₂ edge₂ value₂)
    (start fuel : ℕ)
    (hedge : ∀ offset, offset < fuel →
      edge₁ (start + offset) = edge₂ (start + offset))
    (hend : vertex₁ (start + fuel) = vertex₂ (start + fuel)) :
    dist (value₁ start) (value₂ start) ≤
      contraction ^ fuel * system.diameterBudget := by
  refine (dist_compatiblePullbackPath_le_pow_mul_of_commonPrefix
    system vertex₁ vertex₂ edge₁ edge₂ hpath₁ hpath₂ hcontraction0 hcontract
      hvalue₁ hvalue₂ start fuel hedge).trans ?_
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hcontraction0 fuel)
  have hmem₁ := hvalue₁.1 (start + fuel)
  rw [hend] at hmem₁
  exact system.dist_le_diameterBudget (vertex₂ (start + fuel))
    hmem₁ (hvalue₂.1 (start + fuel))

/-- A compatible lift of a periodic graph path is periodic under a common
strict contraction. -/
theorem GraphDirectedCompactSystem.compatiblePullbackPath_periodic
    [Finite Vertex]
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (hpath : system.IsAdmissiblePath vertex edge)
    (period : ℕ)
    (hvertex : ∀ time, vertex (time + period) = vertex time)
    (hedge : ∀ time, edge (time + period) = edge time)
    {contraction : ℝ}
    (hcontraction0 : 0 ≤ contraction)
    (hcontraction1 : contraction < 1)
    (hcontract : system.IsUniformContraction contraction)
    {value : ℕ → Point}
    (hvalue : system.IsCompatiblePullbackPath vertex edge value) :
    ∀ time, value (time + period) = value time := by
  let shifted : ℕ → Point := fun time ↦ value (time + period)
  have hshifted : system.IsCompatiblePullbackPath vertex edge shifted := by
    constructor
    · intro time
      have hmem := hvalue.1 (time + period)
      rw [hvertex time] at hmem
      exact hmem
    · intro time
      have heq := hvalue.2 (time + period)
      rw [hedge time] at heq
      have htime : time + period + 1 = time + 1 + period := by omega
      rw [htime] at heq
      exact heq
  have hunique : shifted = value :=
    system.compatiblePullbackPath_unique vertex edge hpath
      hcontraction0 hcontraction1 hcontract hshifted hvalue
  exact fun time ↦ congrFun hunique time

end Topology
end Math
