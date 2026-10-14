module

public import GameTheory.Math.Probability.Bounds

@[expose] public section

/-! # Atomic and finite-support expectations -/
noncomputable section
namespace GameTheory.Math.Probability

open Classical in
/-- A payoff confined to one atom is its value times that atom's probability. -/
theorem expect_ite_eq {α : Type*} (law : PMF α) (a : α) (value : ℝ) :
    expect law (fun actual => if a = actual then value else 0) = (law a).toReal * value := by
  classical
  unfold expect
  rw [tsum_eq_single a]
  · simp
  · intro actual different
    simp [Ne.symm different]

/-- A finite-support prior's expectation is its finite weighted sum. -/
theorem expect_eq_sum_of_support_finite {α : Type*} (law : PMF α)
    (finite : law.support.Finite) (value : α → ℝ) :
    expect law value = ∑ a ∈ finite.toFinset, (law a).toReal * value a := by
  classical
  unfold expect
  rw [tsum_eq_sum]
  intro a absent
  have zero : law a = 0 := (law.apply_eq_zero_iff a).mpr (by simpa only [Set.Finite.mem_toFinset]
    using absent)
  rw [zero, ENNReal.toReal_zero, zero_mul]

end GameTheory.Math.Probability
