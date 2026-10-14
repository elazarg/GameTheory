module

public import GameTheory.Math.Probability.AggregateComparison

@[expose] public section
noncomputable section
namespace GameTheory.Tests.AggregateComparison
open GameTheory.Math.Probability

private def conflictingValue (member action : Bool) : ℝ :=
  if member then (if action then 1 else 0) else (if action then 0 else 1)

/-- An aggregate optimum can leave a member with a profitable deviation when their best actions
  conflict. -/
theorem conflicting_members :
    (∀ alternative : PMF Bool, ∑ member ∈ ({false, true} : Finset Bool),
      (expect alternative (conflictingValue member) -
        expect (PMF.pure false) (conflictingValue member)) ≤ 0) ∧
    0 < expect (PMF.pure true) (conflictingValue true) -
      expect (PMF.pure false) (conflictingValue true) := by
  constructor
  · intro alternative
    have total : expect alternative (conflictingValue false) +
        expect alternative (conflictingValue true) = 1 := by
      rw [← expect_add (payoffIntegrable_of_finite alternative (conflictingValue false))
        (payoffIntegrable_of_finite alternative (conflictingValue true))]
      calc
        _ = expect alternative (fun _ => 1) := by
          apply expect_congr_on_support
          intro action _
          cases action <;> norm_num [conflictingValue]
        _ = 1 := expect_constant _ _
    rw [Finset.sum_pair (by decide)]
    rw [expect_pure, expect_pure]
    have falseValue : conflictingValue false false = 1 := rfl
    have trueValue : conflictingValue true false = 0 := rfl
    rw [falseValue, trueValue]
    linarith
  · norm_num [expect_pure, conflictingValue]

/-- An unbounded action space uses the same common-action bound; only the compared means are
  integrable. -/
theorem infinite_action_bound (current alternative : PMF ℕ) (value : Bool → ℕ → ℝ)
    (best : ℕ) (error tolerance : ℝ)
    (currentIntegrable : ∀ member ∈ ({false, true} : Finset Bool), PayoffIntegrable current (value
      member))
    (nearBest : ∀ member ∈ ({false, true} : Finset Bool), ∀ action,
      value member action ≤ value member best + error)
    (aggregate : ∑ member ∈ ({false, true} : Finset Bool),
      (value member best - expect current (value member)) ≤ tolerance)
    (alternativeIntegrable : PayoffIntegrable alternative (value true)) :
    expect alternative (value true) - expect current (value true) ≤ tolerance + 2 * error := by
  have bound := member_gain_le_of_common_best ({false, true} : Finset Bool) value current
    best error tolerance currentIntegrable nearBest aggregate (by simp : true ∈ ({false, true} :
      Finset Bool))
    alternative alternativeIntegrable
  simpa using bound

end GameTheory.Tests.AggregateComparison
