import GameTheory.Core.SatisfiabilityGameCompleteness
import GameTheory.Core.SatisfiabilityGameSoundness
import GameTheory.Core.ConstrainedNash

/-! Satisfiability is equivalent to existence of a high-payoff equilibrium in
the explicitly constructed two-player game. This semantic reduction asserts no
machine runtime bound; encoded polynomial reductions belong to the opt-in layer. -/

noncomputable section

namespace GameTheory.SatisfiabilityGame

open GameTheory.Math.Probability

/-- A formula is satisfiable precisely when its literal/clause game has a mixed
Nash equilibrium giving each player payoff at least one. -/
theorem satisfiable_iff_exists_nash_threshold {n m : ℕ} [NeZero n] (C : Clauses n m) :
    (∃ τ, Satisfies C τ) ↔
      ∃ p q, IsNash (game C).form.mixed (euPreference (game C).utility)
        (MatrixGame.mixedProfile p q) ∧ 1 ≤ value C p q ∧ 1 ≤ value C q p := by
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨assignmentLaw τ, assignmentLaw τ, assignment_isNash C τ hτ,
      (value_assignment C τ).ge, (value_assignment C τ).ge⟩
  · rintro ⟨p, q, h, hp, hq⟩
    exact satisfies_of_nash_threshold C p q h hp hq

/-- Satisfiability is exactly payoff-constrained Nash existence in the canonical
literal/clause game, using the generic utility-game existence predicate. -/
theorem satisfiable_iff_hasNash_threshold {n m : ℕ} [NeZero n] (C : Clauses n m) :
    (∃ τ, Satisfies C τ) ↔ (game C).HasNashWithPayoffAtLeast (fun _ => 1) := by
  rw [satisfiable_iff_exists_nash_threshold, MatrixGame.hasNashWithPayoffAtLeast_iff]
  have hswap (p q : PMF (Action n m)) :
      expect (bindPairLaw p (fun _ => q)) (fun x => payoff C x.2 x.1) = value C q p := by
    rw [value, ← bindPairLaw_const_map_swap p q, expect_map]
    rfl
  constructor
  · rintro ⟨p, q, hnash, hp, hq⟩
    exact ⟨p, q, hnash, hp, by rwa [hswap]⟩
  · rintro ⟨p, q, hnash, hp, hq⟩
    exact ⟨p, q, hnash, hp, by rwa [hswap] at hq⟩

end GameTheory.SatisfiabilityGame
