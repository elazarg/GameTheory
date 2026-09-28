import GameTheory.Math.Probability.Interaction

/-! # Correlation-sensitive and additive payoffs

Rewarding coordination is not additive, so some recoupling with unchanged
marginals changes its expectation. A payoff that adds a bonus for each
coordinate separately is insensitive to every recoupling.
-/

noncomputable section

namespace GameTheory.Math.Probability.InteractionTest

/-- Reward agreement of the two coordinates. -/
def coordination (outcome : Bool × Bool) : ℝ := if outcome.1 = outcome.2 then 1 else 0

theorem abs_coordination_le (outcome : Bool × Bool) : |coordination outcome| ≤ 1 := by
  unfold coordination
  split_ifs <;> norm_num

theorem coordination_not_additive :
    ¬ ∃ row : Bool → ℝ, ∃ column : Bool → ℝ,
      ∀ outcome, coordination outcome = row outcome.1 + column outcome.2 := by
  rintro ⟨row, column, hrepresentation⟩
  have htt := hrepresentation (true, true)
  have hff := hrepresentation (false, false)
  have htf := hrepresentation (true, false)
  have hft := hrepresentation (false, true)
  simp only [coordination] at htt hff htf hft
  norm_num at htt hff htf hft
  linarith

/-- The characterization is not vacuous: coordination distinguishes two laws
with the same marginals. -/
theorem coordination_sees_correlation :
    ¬ ∀ first second : PMF (Bool × Bool),
      first.map Prod.fst = second.map Prod.fst →
      first.map Prod.snd = second.map Prod.snd →
      expect first coordination (payoffIntegrable_of_bounded _ _ abs_coordination_le) =
        expect second coordination (payoffIntegrable_of_bounded _ _ abs_coordination_le) :=
  fun hpreserves => coordination_not_additive
    ((expect_eq_of_marginals_iff_additive abs_coordination_le).1 hpreserves)

/-- Separate bonuses for each coordinate. -/
def bonuses (outcome : Bool × Bool) : ℝ :=
  (if outcome.1 then 2 else 0) + (if outcome.2 then 3 else 0)

theorem abs_bonuses_le (outcome : Bool × Bool) : |bonuses outcome| ≤ 5 := by
  unfold bonuses
  split_ifs <;> norm_num

theorem bonuses_ignore_correlation (first second : PMF (Bool × Bool))
    (hleft : first.map Prod.fst = second.map Prod.fst)
    (hright : first.map Prod.snd = second.map Prod.snd) :
    expect first bonuses (payoffIntegrable_of_bounded _ _ abs_bonuses_le) =
      expect second bonuses (payoffIntegrable_of_bounded _ _ abs_bonuses_le) :=
  (expect_eq_of_marginals_iff_additive abs_bonuses_le).2
    ⟨fun first => if first then 2 else 0, fun second => if second then 3 else 0,
      fun _ => rfl⟩ first second hleft hright

end GameTheory.Math.Probability.InteractionTest
