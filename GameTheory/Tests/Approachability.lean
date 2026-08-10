/-
# Nondegenerate Blackwell approachability fixture

A binary approacher steers a genuinely signed vector payoff toward the
nonpositive orthant.  This discharges the public B-set hypothesis and consumes
the response, finite-time, and convergence entry points directly.
-/

import GameTheoryMath.Approachability

noncomputable section

namespace GameTheory.Tests.Approachability

open GameTheoryMath.Approachability
open scoped InnerProductSpace

/-- The one-dimensional nonpositive orthant. -/
def nonpositiveOrthant : Set ℝ := Set.Iic 0

/-- `true` is the positive action.  The negative action responds to the
opponent with either `-1` or `-2`, so both payoff coordinates are live. -/
def orthantPayoff (approacher opponent : Bool) : ℝ :=
  if approacher then 1 else if opponent then -1 else -2

theorem orthantPayoff_norm_le_two (approacher opponent : Bool) :
    ‖orthantPayoff approacher opponent‖ ≤ 2 := by
  cases approacher <;> cases opponent <;>
    norm_num [orthantPayoff, Real.norm_eq_abs]

private theorem nearest_eq_self_of_nonpositive
    {x π : ℝ} (_hπ : π ∈ nonpositiveOrthant)
    (hnearness : ‖x - π‖ = Metric.infDist x nonpositiveOrthant)
    (hx : x ≤ 0) : π = x := by
  have hinf_le : Metric.infDist x nonpositiveOrthant ≤ dist x x :=
    Metric.infDist_le_dist_of_mem hx
  rw [dist_self] at hinf_le
  have hzero : ‖x - π‖ = 0 := by
    rw [hnearness]
    exact le_antisymm hinf_le Metric.infDist_nonneg
  have hsub : x - π = 0 := norm_eq_zero.mp hzero
  linarith

private theorem nearest_eq_zero_of_positive
    {x π : ℝ} (hπ : π ∈ nonpositiveOrthant)
    (hnearness : ‖x - π‖ = Metric.infDist x nonpositiveOrthant)
    (hx : 0 < x) : π = 0 := by
  have hinf_le : Metric.infDist x nonpositiveOrthant ≤ dist x 0 :=
    Metric.infDist_le_dist_of_mem (show (0 : ℝ) ∈ nonpositiveOrthant by
      show (0 : ℝ) ≤ 0
      exact le_rfl)
  have hpi : π ≤ 0 := hπ
  have hxpi : 0 ≤ x - π := by linarith
  rw [← hnearness, Real.norm_eq_abs, abs_of_nonneg hxpi,
    Real.dist_eq, sub_zero, abs_of_pos hx] at hinf_le
  linarith

/-- The negative action satisfies Blackwell's supporting-halfspace condition
at every nearest point of the nonpositive orthant. -/
theorem nonpositiveOrthant_isBSet :
    ∀ x : ℝ, ∀ π ∈ nonpositiveOrthant,
      ‖x - π‖ = Metric.infDist x nonpositiveOrthant →
        ∃ approacher : Bool, ∀ opponent : Bool,
          inner ℝ (orthantPayoff approacher opponent - π) (x - π) ≤ 0 := by
  intro x π hπ hnearness
  refine ⟨false, ?_⟩
  intro opponent
  by_cases hx : x ≤ 0
  · have hπx := nearest_eq_self_of_nonpositive hπ hnearness hx
    subst π
    simp
  · have hxpos : 0 < x := lt_of_not_ge hx
    have hπ0 := nearest_eq_zero_of_positive hπ hnearness hxpos
    subst π
    cases opponent <;> simp [orthantPayoff] <;> nlinarith

/-- The public response selector is inhabited on a nontrivial B-set. -/
theorem exists_orthant_blackwell_response :
    ∃ br : ℝ → Bool, ∀ qseq : ℕ → Bool, ∀ t : ℕ,
      ∃ π ∈ nonpositiveOrthant,
        ‖avgVec orthantPayoff br qseq t - π‖ =
            Metric.infDist (avgVec orthantPayoff br qseq t) nonpositiveOrthant ∧
          inner ℝ
              (orthantPayoff (br (avgVec orthantPayoff br qseq t)) (qseq t) - π)
              (avgVec orthantPayoff br qseq t - π) ≤ 0 ∧
            ‖orthantPayoff (br (avgVec orthantPayoff br qseq t)) (qseq t) - π‖ ≤
              (3 * 2 : ℝ) := by
  simpa [nonpositiveOrthant] using
    (exists_blackwell_response orthantPayoff nonpositiveOrthant 0
      (show (0 : ℝ) ∈ nonpositiveOrthant by
        show (0 : ℝ) ≤ 0
        exact le_rfl)
      isClosed_Iic (M := 2) (by norm_num) orthantPayoff_norm_le_two
      nonpositiveOrthant_isBSet)

/-- The same orthant fixture reaches the public finite-time estimate. -/
theorem orthant_blackwell_finite_time_bound :
    ∃ br : ℝ → Bool, ∀ qseq : ℕ → Bool, ∀ t : ℕ,
      (t : ℝ) ^ 2 *
          Metric.infDist (avgVec orthantPayoff br qseq t) nonpositiveOrthant ^ 2 ≤
        (t : ℝ) * (3 * 2 : ℝ) ^ 2 := by
  simpa [nonpositiveOrthant] using
    (blackwell_sq_infDist_avg_le orthantPayoff nonpositiveOrthant 0
      (show (0 : ℝ) ∈ nonpositiveOrthant by
        show (0 : ℝ) ≤ 0
        exact le_rfl)
      isClosed_Iic (M := 2) (by norm_num) orthantPayoff_norm_le_two
      nonpositiveOrthant_isBSet)

/-- End-to-end convergence to the nonpositive orthant against every opponent
sequence, through `blackwell_approaches` itself. -/
theorem orthant_blackwell_approaches :
    ∃ br : ℝ → Bool, ∀ qseq : ℕ → Bool,
      Filter.Tendsto
        (fun t =>
          Metric.infDist (avgVec orthantPayoff br qseq t) nonpositiveOrthant)
        Filter.atTop (nhds 0) := by
  exact blackwell_approaches orthantPayoff nonpositiveOrthant
    isClosed_Iic ⟨0, by simp [nonpositiveOrthant]⟩
    (M := 2) (by norm_num) orthantPayoff_norm_le_two
    nonpositiveOrthant_isBSet

end GameTheory.Tests.Approachability
