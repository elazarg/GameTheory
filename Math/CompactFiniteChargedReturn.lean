/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.FiniteChargedReturn
import Mathlib.Topology.MetricSpace.Cover

/-!
# Compact finite charged return

Compactness turns the finite labelled charged-return theorem into a metric
statement with exactly the quantifiers supplied by finite-prefix orbit
producers.

For a requested return radius `r > 0`, take a finite `r / 3`-cover with `m`
centres and require total charge at least `2m`.  Labelling each state by one
cover centre and applying `exists_same_label_with_large_charge_gap` produces
two ordered states at distance less than `r`, separated by charge at least
one.

The finite path may depend on the requested charge threshold.  No diagonal
extraction and no single orbit working for every charge target are required.
-/

noncomputable section

namespace Math

open Set

variable {X : Type*} [PseudoMetricSpace X]

/-- **Compact charged-return threshold.**

For every positive metric radius there is a finite charge threshold such that
any sequence in the compact set whose prefix reaches that threshold contains
a close ordered return carrying raw charge at least one. -/
theorem exists_charge_threshold_for_close_pair_of_compact
    (K : Set X) (hK : IsCompact K)
    (radius : ℝ) (hradius : 0 < radius) :
    ∃ threshold : ℝ, 0 ≤ threshold ∧
      ∀ (state : ℕ → X) (charge : ℕ → ℝ) (horizon : ℕ),
        (∀ time, state time ∈ K) →
        (∀ time, 0 ≤ charge time) →
        (∀ time, charge time ≤ 1) →
        threshold ≤ ∑ time ∈ Finset.range horizon, charge time →
        ∃ first second : ℕ,
          first < second ∧ second ≤ horizon ∧
          dist (state first) (state second) < radius ∧
          1 ≤
            (∑ time ∈ Finset.range second, charge time) -
              ∑ time ∈ Finset.range first, charge time := by
  classical
  let coverRadius : NNReal :=
    ⟨radius / 3, by positivity⟩
  have hcoverRadius : coverRadius ≠ 0 := by
    intro hzero
    have hcoe := congrArg (fun r : NNReal => (r : ℝ)) hzero
    simp only [coverRadius, NNReal.coe_mk, NNReal.coe_zero] at hcoe
    linarith
  obtain ⟨centres, _hcentresK, hcentresFinite, hcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact hcoverRadius hK
  letI : Fintype {point // point ∈ centres} := hcentresFinite.fintype
  have hcoverSubset :
      K ⊆ ⋃ centre ∈ centres,
        Metric.closedBall centre (coverRadius : ℝ) :=
    hcover.subset_iUnion_closedBall
  have hcentre : ∀ point ∈ K,
      ∃ centre : {point // point ∈ centres},
        dist point centre.1 ≤ (coverRadius : ℝ) := by
    intro point hpoint
    have hcovered := hcoverSubset hpoint
    rcases Set.mem_iUnion.mp hcovered with ⟨centre, hcovered⟩
    rcases Set.mem_iUnion.mp hcovered with ⟨hcentreMem, hball⟩
    refine ⟨⟨centre, hcentreMem⟩, ?_⟩
    simpa only [Metric.mem_closedBall] using hball
  let threshold : ℝ :=
    2 * (Fintype.card {point // point ∈ centres} : ℝ)
  refine ⟨threshold, by positivity, ?_⟩
  intro state charge horizon hstate hcharge0 hcharge1 hlarge
  let label : ℕ → {point // point ∈ centres} := fun time =>
    Classical.choose (hcentre (state time) (hstate time))
  have hlabelClose : ∀ time,
      dist (state time) (label time).1 ≤ (coverRadius : ℝ) := by
    intro time
    exact Classical.choose_spec (hcentre (state time) (hstate time))
  have hsame : ∀ first second,
      label first = label second →
        dist (state first) (state second) < radius := by
    intro first second heq
    calc
      dist (state first) (state second) ≤
          dist (state first) (label first).1 +
            dist (label first).1 (state second) :=
        dist_triangle _ _ _
      _ = dist (state first) (label first).1 +
          dist (state second) (label second).1 := by
        rw [heq, dist_comm (label second).1]
      _ ≤ (coverRadius : ℝ) + (coverRadius : ℝ) :=
        add_le_add (hlabelClose first) (hlabelClose second)
      _ < radius := by
        dsimp only [coverRadius]
        linarith
  exact exists_close_pair_with_large_charge_gap_of_finite_labels
    state label radius hsame charge horizon hcharge0 hcharge1
      (by simpa only [threshold] using hlarge)

end Math
