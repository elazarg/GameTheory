/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Compact graph-directed pullback paths

This file isolates the topological layer of graph-directed quitting
constructions.  A directed system consists of nonempty compact vertex boxes
and continuous edge maps taking the target box into the source box.  Along
every infinite admissible edge path there is a compatible infinite pullback
path.  Existence uses only compactness and box preservation, by intersecting
nested closed sets of finite-prefix solutions.  A common strict contraction
and finitely many vertex boxes make that path unique.

No numerical box inclusion or game-specific Bellman calculation is built
into this abstraction; those remain hypotheses of an application.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter

/-- A graph-directed family of compact boxes and backward branch maps. -/
structure GraphDirectedCompactSystem
    (Vertex Edge Point : Type*) [TopologicalSpace Point] where
  source : Edge → Vertex
  target : Edge → Vertex
  box : Vertex → Set Point
  branch : Edge → Point → Point
  box_nonempty : ∀ vertex, (box vertex).Nonempty
  box_compact : ∀ vertex, IsCompact (box vertex)
  branch_continuousOn : ∀ edge,
    ContinuousOn (branch edge) (box (target edge))
  branch_mapsTo : ∀ edge, Set.MapsTo (branch edge) (box (target edge))
    (box (source edge))

variable {Vertex Edge Point : Type*} [TopologicalSpace Point]

/-- A vertex/edge sequence follows the source and target incidences. -/
def GraphDirectedCompactSystem.IsAdmissiblePath
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge) : Prop :=
  ∀ time,
    system.source (edge time) = vertex time ∧
      system.target (edge time) = vertex (time + 1)

/-- A point sequence stays in its vertex boxes and satisfies every backward
branch equation. -/
def GraphDirectedCompactSystem.IsCompatiblePullbackPath
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (value : ℕ → Point) : Prop :=
  (∀ time, value time ∈ system.box (vertex time)) ∧
    ∀ time, value time = system.branch (edge time) (value (time + 1))

/-- Pull a terminal point backward through `fuel` consecutive edge maps. -/
def graphDirectedIteratedPullback
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (edge : ℕ → Edge) : ℕ → ℕ → Point → Point
  | _, 0, point => point
  | start, fuel + 1, point =>
      system.branch (edge start)
        (graphDirectedIteratedPullback system edge (start + 1) fuel point)

@[simp] theorem graphDirectedIteratedPullback_zero
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (edge : ℕ → Edge) (start : ℕ) (point : Point) :
    graphDirectedIteratedPullback system edge start 0 point = point := by
  rfl

@[simp] theorem graphDirectedIteratedPullback_succ
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (edge : ℕ → Edge) (start fuel : ℕ) (point : Point) :
    graphDirectedIteratedPullback system edge start (fuel + 1) point =
      system.branch (edge start)
        (graphDirectedIteratedPullback system edge (start + 1) fuel point) := by
  rfl

/-- Iterated pullback preserves the boxes along an admissible path. -/
theorem graphDirectedIteratedPullback_mem
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (hpath : system.IsAdmissiblePath vertex edge) :
    ∀ {start fuel : ℕ} {point : Point},
      point ∈ system.box (vertex (start + fuel)) →
        graphDirectedIteratedPullback system edge start fuel point ∈
          system.box (vertex start) := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro point hpoint
      simpa using hpoint
  | succ fuel ih =>
      intro point hpoint
      have hpoint' : point ∈
          system.box (vertex ((start + 1) + fuel)) := by
        have hindex : start + fuel.succ = (start + 1) + fuel := by omega
        rw [← hindex]
        exact hpoint
      have htail := ih (start := start + 1) hpoint'
      have htailTarget :
          graphDirectedIteratedPullback system edge (start + 1) fuel point ∈
            system.box (system.target (edge start)) := by
        rw [(hpath start).2]
        exact htail
      have hout := system.branch_mapsTo (edge start) htailTarget
      rw [(hpath start).1] at hout
      simpa using hout

/-- A canonical chosen point in each nonempty vertex box. -/
def GraphDirectedCompactSystem.center
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : Vertex) : Point :=
  Classical.choose (system.box_nonempty vertex)

@[simp] theorem GraphDirectedCompactSystem.center_mem
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : Vertex) :
    system.center vertex ∈ system.box vertex :=
  Classical.choose_spec (system.box_nonempty vertex)

/-- A finite-prefix solution, obtained by choosing a terminal anchor and
pulling it backward; after the terminal index it uses arbitrary box centers. -/
def graphDirectedPrefixPath
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (horizon : ℕ) (time : ℕ) : Point :=
  if time ≤ horizon then
    graphDirectedIteratedPullback system edge time (horizon - time)
      (system.center (vertex horizon))
  else
    system.center (vertex time)

/-- Every coordinate of the canonical finite-prefix solution lies in its
prescribed vertex box. -/
theorem graphDirectedPrefixPath_mem
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (hpath : system.IsAdmissiblePath vertex edge)
    (horizon time : ℕ) :
    graphDirectedPrefixPath system vertex edge horizon time ∈
      system.box (vertex time) := by
  classical
  unfold graphDirectedPrefixPath
  split_ifs with htime
  · apply graphDirectedIteratedPullback_mem system vertex edge hpath
    have hend : time + (horizon - time) = horizon :=
      Nat.add_sub_of_le htime
    rw [hend]
    exact system.center_mem (vertex horizon)
  · exact system.center_mem (vertex time)

/-- The canonical finite-prefix solution satisfies every branch equation
strictly before its terminal anchor. -/
theorem graphDirectedPrefixPath_compatible
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (horizon time : ℕ) (htime : time < horizon) :
    graphDirectedPrefixPath system vertex edge horizon time =
      system.branch (edge time)
        (graphDirectedPrefixPath system vertex edge horizon (time + 1)) := by
  classical
  have htime0 : time ≤ horizon := htime.le
  have htime1 : time + 1 ≤ horizon := by omega
  unfold graphDirectedPrefixPath
  rw [if_pos htime0, if_pos htime1]
  have hsub : horizon - time = (horizon - (time + 1)) + 1 := by omega
  rw [hsub, graphDirectedIteratedPullback_succ]

/-! ## Compact inverse limit -/

/-- Point sequences which stay in every path box and solve the first
`horizon` branch equations. -/
def graphDirectedPrefixSolutionSet
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (horizon : ℕ) : Set (ℕ → Point) :=
  {value |
    (∀ time, value time ∈ system.box (vertex time)) ∧
      ∀ time : Fin horizon,
        value time = system.branch (edge time) (value (time + 1))}

/-- Every finite-prefix solution set is nonempty. -/
theorem graphDirectedPrefixSolutionSet_nonempty
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (hpath : system.IsAdmissiblePath vertex edge)
    (horizon : ℕ) :
    (graphDirectedPrefixSolutionSet system vertex edge horizon).Nonempty := by
  classical
  refine ⟨graphDirectedPrefixPath system vertex edge horizon, ?_, ?_⟩
  · intro time
    exact graphDirectedPrefixPath_mem system vertex edge hpath horizon time
  · intro time
    exact graphDirectedPrefixPath_compatible system vertex edge horizon time
      time.isLt

/-- Solving one more branch equation only shrinks the prefix solution set. -/
theorem graphDirectedPrefixSolutionSet_succ_subset
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (horizon : ℕ) :
    graphDirectedPrefixSolutionSet system vertex edge (horizon + 1) ⊆
      graphDirectedPrefixSolutionSet system vertex edge horizon := by
  intro value hvalue
  refine ⟨hvalue.1, fun time ↦ ?_⟩
  exact hvalue.2
    ⟨time, lt_trans time.isLt (Nat.lt_succ_self horizon)⟩

/-- Prefix solution sets are closed in the full sequence space. -/
theorem graphDirectedPrefixSolutionSet_isClosed
    [T2Space Point]
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (hpath : system.IsAdmissiblePath vertex edge)
    (horizon : ℕ) :
    IsClosed (graphDirectedPrefixSolutionSet system vertex edge horizon) := by
  let ambient : Set (ℕ → Point) :=
    {value | ∀ time, value time ∈ system.box (vertex time)}
  have hambientCompact : IsCompact ambient := by
    dsimp only [ambient]
    exact isCompact_pi_infinite fun time ↦
      system.box_compact (vertex time)
  have hambientClosed : IsClosed ambient := hambientCompact.isClosed
  have hequationClosed : ∀ time : Fin horizon,
      IsClosed (ambient ∩
        {value : ℕ → Point |
          value time = system.branch (edge time) (value (time + 1))}) := by
    intro time
    let pairMap : (ℕ → Point) → Point × Point :=
      fun value ↦
        (value time, system.branch (edge time) (value (time + 1)))
    have hevalTarget : Set.MapsTo
        (fun value : ℕ → Point ↦ value ((time : ℕ) + 1))
        ambient (system.box (system.target (edge time))) := by
      intro value hvalue
      rw [(hpath time).2]
      exact hvalue ((time : ℕ) + 1)
    have hright : ContinuousOn
        (fun value : ℕ → Point ↦
          system.branch (edge time) (value ((time : ℕ) + 1)))
        ambient :=
      (system.branch_continuousOn (edge time)).comp
        (continuous_apply ((time : ℕ) + 1)).continuousOn hevalTarget
    have hpair : ContinuousOn pairMap ambient :=
      (continuous_apply (time : ℕ)).continuousOn.prodMk hright
    have hdiagonal : IsClosed
        {pair : Point × Point | pair.1 = pair.2} :=
      isClosed_eq continuous_fst continuous_snd
    have hpreimage := hpair.preimage_isClosed_of_isClosed
      hambientClosed hdiagonal
    simpa only [pairMap, Set.preimage_setOf_eq] using hpreimage
  have hclosed : IsClosed
      (ambient ∩ ⋂ time : Fin horizon,
        (ambient ∩
          {value : ℕ → Point |
            value time = system.branch (edge time) (value (time + 1))})) :=
    hambientClosed.inter (isClosed_iInter hequationClosed)
  have heq : graphDirectedPrefixSolutionSet system vertex edge horizon =
      ambient ∩ ⋂ time : Fin horizon,
        (ambient ∩
          {value : ℕ → Point |
            value time = system.branch (edge time) (value (time + 1))}) := by
    ext value
    simp only [graphDirectedPrefixSolutionSet, ambient, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_iInter]
    aesop
  rw [heq]
  exact hclosed

/-- Every prefix solution set is compact as a closed subset of the compact
product of path boxes. -/
theorem graphDirectedPrefixSolutionSet_isCompact
    [T2Space Point]
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (hpath : system.IsAdmissiblePath vertex edge)
    (horizon : ℕ) :
    IsCompact (graphDirectedPrefixSolutionSet system vertex edge horizon) := by
  have hambient : IsCompact
      {value : ℕ → Point |
        ∀ time, value time ∈ system.box (vertex time)} :=
    isCompact_pi_infinite fun time ↦ system.box_compact (vertex time)
  exact hambient.of_isClosed_subset
    (graphDirectedPrefixSolutionSet_isClosed
      system vertex edge hpath horizon)
    (fun _ hvalue ↦ hvalue.1)

/-- Compact inverse-limit existence: every admissible one-sided graph path
has a compatible pullback value path.  No contraction hypothesis is needed. -/
theorem GraphDirectedCompactSystem.exists_compatiblePullbackPath
    [T2Space Point]
    (system : GraphDirectedCompactSystem Vertex Edge Point)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (hpath : system.IsAdmissiblePath vertex edge) :
    ∃ value : ℕ → Point,
      system.IsCompatiblePullbackPath vertex edge value := by
  let prefixSet : ℕ → Set (ℕ → Point) :=
    fun horizon ↦
      graphDirectedPrefixSolutionSet system vertex edge horizon
  have hnested : ∀ horizon,
      prefixSet (horizon + 1) ⊆ prefixSet horizon := by
    intro horizon
    exact graphDirectedPrefixSolutionSet_succ_subset
      system vertex edge horizon
  have hnonempty : ∀ horizon, (prefixSet horizon).Nonempty := by
    intro horizon
    exact graphDirectedPrefixSolutionSet_nonempty
      system vertex edge hpath horizon
  have hcompact0 : IsCompact (prefixSet 0) :=
    graphDirectedPrefixSolutionSet_isCompact system vertex edge hpath 0
  have hclosed : ∀ horizon, IsClosed (prefixSet horizon) := by
    intro horizon
    exact graphDirectedPrefixSolutionSet_isClosed
      system vertex edge hpath horizon
  obtain ⟨value, hvalue⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      prefixSet hnested hnonempty hcompact0 hclosed
  have hprefix : ∀ horizon, value ∈ prefixSet horizon :=
    Set.mem_iInter.mp hvalue
  refine ⟨value, (hprefix 0).1, fun time ↦ ?_⟩
  exact (hprefix (time + 1)).2 ⟨time, Nat.lt_succ_self time⟩

/-! ## Uniqueness under a common contraction -/

section Metric

variable {MetricPoint : Type*} [MetricSpace MetricPoint]

/-- A common contraction factor for all branch maps, only on their certified
target boxes. -/
def GraphDirectedCompactSystem.IsUniformContraction
    (system : GraphDirectedCompactSystem Vertex Edge MetricPoint)
    (contraction : ℝ) : Prop :=
  ∀ edge point₁, point₁ ∈ system.box (system.target edge) →
    ∀ point₂, point₂ ∈ system.box (system.target edge) →
      dist (system.branch edge point₁) (system.branch edge point₂) ≤
        contraction * dist point₁ point₂

/-- A finite family of compact boxes has this canonical common diameter
budget. -/
def GraphDirectedCompactSystem.diameterBudget
    [Fintype Vertex]
    (system : GraphDirectedCompactSystem Vertex Edge MetricPoint) : ℝ :=
  ∑ vertex, Metric.diam (system.box vertex)

/-- Every pair in one vertex box is bounded by the common finite-box diameter
budget. -/
theorem GraphDirectedCompactSystem.dist_le_diameterBudget
    [Fintype Vertex]
    (system : GraphDirectedCompactSystem Vertex Edge MetricPoint)
    (vertex : Vertex) {point₁ point₂ : MetricPoint}
    (hpoint₁ : point₁ ∈ system.box vertex)
    (hpoint₂ : point₂ ∈ system.box vertex) :
    dist point₁ point₂ ≤ system.diameterBudget := by
  classical
  calc
    dist point₁ point₂ ≤ Metric.diam (system.box vertex) :=
      Metric.dist_le_diam_of_mem (system.box_compact vertex).isBounded
        hpoint₁ hpoint₂
    _ ≤ ∑ other, Metric.diam (system.box other) :=
      Finset.single_le_sum
        (fun other _ ↦ Metric.diam_nonneg) (Finset.mem_univ vertex)

/-- Along two compatible paths, iterating the common one-step contraction
gives a power of the contraction factor. -/
theorem dist_compatiblePullbackPath_le_pow_mul
    (system : GraphDirectedCompactSystem Vertex Edge MetricPoint)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (hpath : system.IsAdmissiblePath vertex edge)
    {contraction : ℝ} (hcontraction0 : 0 ≤ contraction)
    (hcontract : system.IsUniformContraction contraction)
    {value₁ value₂ : ℕ → MetricPoint}
    (hvalue₁ : system.IsCompatiblePullbackPath vertex edge value₁)
    (hvalue₂ : system.IsCompatiblePullbackPath vertex edge value₂) :
    ∀ start fuel,
      dist (value₁ start) (value₂ start) ≤
        contraction ^ fuel *
          dist (value₁ (start + fuel)) (value₂ (start + fuel)) := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp
  | succ fuel ih =>
      have hpoint₁ : value₁ (start + 1) ∈
          system.box (system.target (edge start)) := by
        rw [(hpath start).2]
        exact hvalue₁.1 (start + 1)
      have hpoint₂ : value₂ (start + 1) ∈
          system.box (system.target (edge start)) := by
        rw [(hpath start).2]
        exact hvalue₂.1 (start + 1)
      have hone := hcontract (edge start) _ hpoint₁ _ hpoint₂
      have htail := ih (start + 1)
      have hscaled := mul_le_mul_of_nonneg_left htail hcontraction0
      calc
        dist (value₁ start) (value₂ start) =
            dist (system.branch (edge start) (value₁ (start + 1)))
              (system.branch (edge start) (value₂ (start + 1))) := by
                rw [hvalue₁.2 start, hvalue₂.2 start]
        _ ≤ contraction *
            dist (value₁ (start + 1)) (value₂ (start + 1)) := hone
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

/-- A common strict contraction makes the compatible pullback path unique.
Finiteness of the vertex family is used only to obtain a uniform diameter. -/
theorem GraphDirectedCompactSystem.compatiblePullbackPath_unique
    [Finite Vertex]
    (system : GraphDirectedCompactSystem Vertex Edge MetricPoint)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (hpath : system.IsAdmissiblePath vertex edge)
    {contraction : ℝ}
    (hcontraction0 : 0 ≤ contraction)
    (hcontraction1 : contraction < 1)
    (hcontract : system.IsUniformContraction contraction)
    {value₁ value₂ : ℕ → MetricPoint}
    (hvalue₁ : system.IsCompatiblePullbackPath vertex edge value₁)
    (hvalue₂ : system.IsCompatiblePullbackPath vertex edge value₂) :
    value₁ = value₂ := by
  letI := Fintype.ofFinite Vertex
  funext time
  have hiterate := dist_compatiblePullbackPath_le_pow_mul
    system vertex edge hpath hcontraction0 hcontract hvalue₁ hvalue₂
      time
  have hbound : ∀ fuel,
      dist (value₁ time) (value₂ time) ≤
        contraction ^ fuel * system.diameterBudget := by
    intro fuel
    exact (hiterate fuel).trans
      (mul_le_mul_of_nonneg_left
        (system.dist_le_diameterBudget (vertex (time + fuel))
          (hvalue₁.1 (time + fuel)) (hvalue₂.1 (time + fuel)))
        (pow_nonneg hcontraction0 fuel))
  have hpow : Tendsto (fun fuel : ℕ ↦ contraction ^ fuel)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hcontraction0 hcontraction1
  have hlimit : Tendsto
      (fun fuel : ℕ ↦ contraction ^ fuel * system.diameterBudget)
      atTop (nhds 0) := by
    simpa using hpow.mul_const system.diameterBudget
  have hzero : dist (value₁ time) (value₂ time) ≤ 0 :=
    ge_of_tendsto' hlimit hbound
  exact dist_eq_zero.mp (le_antisymm hzero dist_nonneg)

/-- Compact existence and strict contraction uniqueness in one statement. -/
theorem GraphDirectedCompactSystem.existsUnique_compatiblePullbackPath
    [Finite Vertex] [T2Space MetricPoint]
    (system : GraphDirectedCompactSystem Vertex Edge MetricPoint)
    (vertex : ℕ → Vertex) (edge : ℕ → Edge)
    (hpath : system.IsAdmissiblePath vertex edge)
    {contraction : ℝ}
    (hcontraction0 : 0 ≤ contraction)
    (hcontraction1 : contraction < 1)
    (hcontract : system.IsUniformContraction contraction) :
    ∃! value : ℕ → MetricPoint,
      system.IsCompatiblePullbackPath vertex edge value := by
  letI := Fintype.ofFinite Vertex
  obtain ⟨value, hvalue⟩ := system.exists_compatiblePullbackPath
    vertex edge hpath
  exact ⟨value, hvalue, fun other hother ↦
    system.compatiblePullbackPath_unique vertex edge hpath
      hcontraction0 hcontraction1 hcontract hother hvalue⟩

end Metric

end GameTheory
