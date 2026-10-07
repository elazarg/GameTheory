import GameTheory.Core.SatisfiabilityGameReduction

/-! Payoff-threshold controls use a nonconstant satisfying assignment and an
inconsistent pair of clauses. Mixed strategies cannot evade the latter. -/

noncomputable section

namespace GameTheory.Tests.SatisfiabilityGame

open GameTheory.SatisfiabilityGame

def separated : Clauses 2 2 :=
  fun c v b => decide ((c = 0 ∧ v = 0 ∧ b = true) ∨ (c = 1 ∧ v = 1 ∧ b = false))

theorem separated_satisfiable : ∃ τ, Satisfies separated τ := by
  refine ⟨fun v => decide (v = 0), fun c => ?_⟩
  fin_cases c
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩

theorem separated_has_high_payoff_nash :
    ∃ p q, IsNash (game separated).form.mixed (euPreference (game separated).utility)
      (MatrixGame.mixedProfile p q) ∧ 1 ≤ value separated p q ∧ 1 ≤ value separated q p :=
  (satisfiable_iff_exists_nash_threshold separated).mp separated_satisfiable

def contradictory : Clauses 1 2 := fun c _ b => if c = 0 then b else !b

theorem contradictory_unsatisfiable : ¬ ∃ τ, Satisfies contradictory τ := by
  rintro ⟨τ, hτ⟩
  obtain ⟨v, hv⟩ := hτ 0
  obtain ⟨w, hw⟩ := hτ 1
  have hv0 : v = 0 := Subsingleton.elim _ _
  have hw0 : w = 0 := Subsingleton.elim _ _
  subst v
  subst w
  simp [contradictory] at hv hw
  simp [hv] at hw

theorem contradictory_has_no_high_payoff_nash :
    ¬ ∃ p q, IsNash (game contradictory).form.mixed (euPreference (game contradictory).utility)
      (MatrixGame.mixedProfile p q) ∧
      1 ≤ value contradictory p q ∧ 1 ≤ value contradictory q p := by
  rw [← satisfiable_iff_exists_nash_threshold]
  exact contradictory_unsatisfiable

/-- The unsatisfiable control still has a Nash equilibrium: both choose the
fallback and earn zero. Only the payoff-constrained existence question fails. -/
theorem contradictory_fallback_isNash :
    IsNash (game contradictory).form.mixed (euPreference (game contradictory).utility)
      (MatrixGame.mixedProfile (PMF.pure fallback) (PMF.pure fallback)) := by
  apply (SatisfiabilityGame.isNash_iff contradictory _ _).mpr
  have hval : value contradictory (PMF.pure fallback) (PMF.pure fallback) = 0 := by
    rw [value, Math.Probability.bindPairLaw, PMF.pure_bind, PMF.pure_map,
      Math.Probability.expect_pure]
    simp [payoff, payoffInt, fallback]
  rw [hval]
  constructor <;> intro a <;>
    rw [Math.Probability.expect_pure] <;>
    rcases a with ⟨v, b⟩ | (v | (c | u)) <;>
    simp [payoff, payoffInt, fallback]

end GameTheory.Tests.SatisfiabilityGame
