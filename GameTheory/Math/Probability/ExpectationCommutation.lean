import GameTheory.Math.Probability.ExpectationAlgebra

/-! # Commuting independent expectations -/
noncomputable section
namespace GameTheory.Math.Probability

/-- The two orders of expectation agree whenever the independent joint payoff is integrable. -/
theorem expect_comm {α β : Type*} (first : PMF α) (second : PMF β) (f : α → β → ℝ)
    (integrable : PayoffIntegrable (bindPairLaw first (fun _ => second)) (fun pair => f pair.1 pair.2)) :
    expect first (fun a => expect second (f a)) =
      expect second (fun b => expect first (fun a => f a b)) := by
  have reversed : PayoffIntegrable (bindPairLaw second (fun _ => first))
      (fun pair => f pair.2 pair.1) := by
    rw [← bindPairLaw_const_map_swap]
    exact (payoffIntegrable_map_iff _ _ _).mpr integrable
  rw [← expect_bindPairLaw_tower first second (fun pair => f pair.1 pair.2) integrable,
    ← expect_bindPairLaw_tower second first (fun pair => f pair.2 pair.1) reversed,
    ← bindPairLaw_const_map_swap, expect_map]
  rfl

end GameTheory.Math.Probability
