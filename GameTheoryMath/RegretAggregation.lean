/-
# Finite aggregation of local regret bounds

This module contains the game-independent step from finitely many local
regret-vector averages to a bound on a scalar gain that decomposes through
their coordinates.  Protocol semantics are responsible for proving such a
decomposition; this file only supplies the finite-sum geometry.
-/

import GameTheoryMath.OrthantProjection

noncomputable section

namespace GameTheoryMath.RegretAggregation

open Filter GameTheoryMath.OrthantProjection

variable {κ : Type*}
variable {Action : κ → Type*} [∀ site, Fintype (Action site)]

/-- A coefficient in `[0,1]` times one regret coordinate is bounded by that
vector's distance from the nonpositive orthant. -/
theorem weightedCoordinate_le_infDist
    (average : (site : κ) → EuclideanSpace ℝ (Action site))
    (reach : κ → ℝ) (hreach : ∀ site, reach site ∈ Set.Icc 0 1)
    (deviation : (site : κ) → Action site) (site : κ) :
    reach site * (average site).ofLp (deviation site) ≤
      Metric.infDist (average site) nonposOrthant := by
  rcases le_total ((average site).ofLp (deviation site)) 0 with hnonpos | hnonneg
  · exact (mul_nonpos_of_nonneg_of_nonpos (hreach site).1 hnonpos).trans
      Metric.infDist_nonneg
  · calc
      reach site * (average site).ofLp (deviation site) ≤
          1 * (average site).ofLp (deviation site) :=
        mul_le_mul_of_nonneg_right (hreach site).2 hnonneg
      _ = max ((average site).ofLp (deviation site)) 0 := by
        rw [one_mul, max_eq_left hnonneg]
      _ ≤ Metric.infDist (average site) nonposOrthant :=
        positivePart_le_infDist (average site) (deviation site)

/-- Summing finitely many local bounds controls every weighted selection of
one coordinate from each local regret vector. -/
theorem weightedCoordinates_le_sum_infDist
    [Fintype κ]
    (average : (site : κ) → EuclideanSpace ℝ (Action site))
    (reach : κ → ℝ) (hreach : ∀ site, reach site ∈ Set.Icc 0 1)
    (deviation : (site : κ) → Action site) :
    (∑ site, reach site * (average site).ofLp (deviation site)) ≤
      ∑ site, Metric.infDist (average site) nonposOrthant := by
  exact Finset.sum_le_sum fun site _ =>
    weightedCoordinate_le_infDist average reach hreach deviation site

/-- If every instantaneous scalar gain decomposes through the same bounded
reach coefficients, its positive time average is bounded by the sum of the
local average vectors' distances from their nonpositive orthants. -/
theorem positiveAverageGain_le_sum_infDist
    [Fintype κ]
    (instantaneous : ℕ → (site : κ) → EuclideanSpace ℝ (Action site))
    (average : (site : κ) → EuclideanSpace ℝ (Action site))
    (gain : ℕ → ℝ) (reach : κ → ℝ)
    (hreach : ∀ site, reach site ∈ Set.Icc 0 1)
    (deviation : (site : κ) → Action site) (t : ℕ) (ht : 0 < t)
    (haverage : ∀ site,
      (t : ℝ) • average site =
        ∑ round ∈ Finset.range t, instantaneous round site)
    (hgain : ∀ round < t,
      gain round = ∑ site,
        reach site * (instantaneous round site).ofLp (deviation site)) :
    max ((∑ round ∈ Finset.range t, gain round) / (t : ℝ)) 0 ≤
      ∑ site, Metric.infDist (average site) nonposOrthant := by
  have htReal : (0 : ℝ) < t := by exact_mod_cast ht
  have hcoordinate : ∀ site,
      ∑ round ∈ Finset.range t,
          (instantaneous round site).ofLp (deviation site) =
        (t : ℝ) * (average site).ofLp (deviation site) := by
    intro site
    have happly := congrArg
      (fun value : EuclideanSpace ℝ (Action site) =>
        value.ofLp (deviation site)) (haverage site)
    simpa using happly.symm
  have hsum :
      (∑ round ∈ Finset.range t, gain round) =
        ∑ site, reach site *
          ((t : ℝ) * (average site).ofLp (deviation site)) := by
    calc
      (∑ round ∈ Finset.range t, gain round) =
          ∑ round ∈ Finset.range t, ∑ site,
            reach site *
              (instantaneous round site).ofLp (deviation site) := by
        apply Finset.sum_congr rfl
        intro round hround
        exact hgain round (Finset.mem_range.mp hround)
      _ = ∑ site, ∑ round ∈ Finset.range t,
          reach site *
            (instantaneous round site).ofLp (deviation site) := by
        rw [Finset.sum_comm]
      _ = ∑ site, reach site *
          (∑ round ∈ Finset.range t,
            (instantaneous round site).ofLp (deviation site)) := by
        apply Finset.sum_congr rfl
        intro site _
        rw [Finset.mul_sum]
      _ = ∑ site, reach site *
          ((t : ℝ) * (average site).ofLp (deviation site)) := by
        apply Finset.sum_congr rfl
        intro site _
        rw [hcoordinate site]
  have hmean :
      (∑ round ∈ Finset.range t, gain round) / (t : ℝ) =
        ∑ site, reach site * (average site).ofLp (deviation site) := by
    rw [hsum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro site _
    field_simp
  rw [hmean, max_le_iff]
  exact ⟨weightedCoordinates_le_sum_infDist average reach hreach deviation,
    Finset.sum_nonneg fun _ _ => Metric.infDist_nonneg⟩

/-- If every local average approaches its nonpositive orthant, every scalar
gain sequence with the stated finite decomposition has vanishing positive
average gain. -/
theorem positiveAverageGain_tendsto_zero
    [Fintype κ]
    (instantaneous : ℕ → (site : κ) → EuclideanSpace ℝ (Action site))
    (average : (site : κ) → ℕ → EuclideanSpace ℝ (Action site))
    (gain : ℕ → ℝ) (reach : κ → ℝ)
    (hreach : ∀ site, reach site ∈ Set.Icc 0 1)
    (deviation : (site : κ) → Action site)
    (haverage : ∀ site (t : ℕ),
      (t : ℝ) • average site t =
        ∑ round ∈ Finset.range t, instantaneous round site)
    (hgain : ∀ round,
      gain round = ∑ site,
        reach site * (instantaneous round site).ofLp (deviation site))
    (hlocal : ∀ site,
      Tendsto (fun t => Metric.infDist (average site t) nonposOrthant)
        atTop (nhds 0)) :
    Tendsto
      (fun t => max ((∑ round ∈ Finset.range t, gain round) / (t : ℝ)) 0)
      atTop (nhds 0) := by
  have hsum : Tendsto
      (fun t => ∑ site, Metric.infDist (average site t) nonposOrthant)
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ
      (fun site _ => hlocal site)
  have hupper : ∀ t,
      max ((∑ round ∈ Finset.range t, gain round) / (t : ℝ)) 0 ≤
        ∑ site, Metric.infDist (average site t) nonposOrthant := by
    intro t
    cases t with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
          div_zero, max_self]
        exact Finset.sum_nonneg fun _ _ => Metric.infDist_nonneg
    | succ t =>
        apply positiveAverageGain_le_sum_infDist instantaneous
          (fun site => average site (t + 1)) gain reach hreach deviation
          (t + 1) (Nat.succ_pos t)
        · exact fun site => haverage site (t + 1)
        · intro round _
          exact hgain round
  exact squeeze_zero (fun t => le_max_right _ _) hupper hsum

end GameTheoryMath.RegretAggregation
