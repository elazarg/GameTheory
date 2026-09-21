import GameTheory.Math.Probability.FinDist

/-! # Finite-law support and coupling controls

These witnesses retain the zero-probability branch case and refute the claim
that infinitely many prescribed nondegenerate marginals necessarily require
an infinite-support coupling.
-/

noncomputable section

namespace GameTheory.Tests.FinDistExtensions

open GameTheory.Math.Probability

private def coin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

private def sharedCoin : FinDist (ℕ → Bool) := coin.map fun value _ => value

/-- The same sampled coin supplies all countably many marginals. -/
theorem infinite_shared_coin_marginal (index : ℕ) :
    sharedCoin.map (fun assignment => assignment index) = coin := by
  rw [sharedCoin, FinDist.map_comp]
  exact FinDist.map_id coin

/-- The assignment law has only the two constant assignments in its support. -/
theorem infinite_shared_coin_support :
    sharedCoin.support ⊆ {fun _ : ℕ => false, fun _ : ℕ => true} := by
  intro assignment hmem
  rw [sharedCoin, FinDist.support_map] at hmem
  obtain ⟨value, _, rfl⟩ := hmem
  cases value <;> simp

/-- Every one of the infinitely many marginals is nondegenerate. -/
theorem infinite_shared_coin_fair (index : ℕ) :
    (sharedCoin.map (fun assignment => assignment index)).prob false = 1 / 2 ∧
      (sharedCoin.map (fun assignment => assignment index)).prob true = 1 / 2 := by
  rw [infinite_shared_coin_marginal]
  norm_num [coin, FinDist.prob_mix, FinDist.prob_pure_eq_ite]

/-- The branch identified by an output need not itself be reached. -/
theorem unique_branch_may_be_unsupported :
    let law := FinDist.pure false
    let branch := fun value : Bool => FinDist.pure (if value then 1 else 0 : ℕ)
    true ∉ law.support ∧
      (law.bind branch).prob 1 = law.prob true * (branch true).prob 1 := by
  dsimp only
  constructor
  · simp
  · apply FinDist.prob_bind_of_unique_branch
    intro value _ hbranch
    cases value <;> simp at hbranch ⊢

/-- Event-weighting also covers a null event, without division by its mass. -/
theorem empty_event_weighting (law reference : FinDist ℕ) :
    law.probOf ∅ = reference.expect (fun _ => 0) := by
  apply FinDist.probOf_eq_expect_of_weighting
  intro outcome
  simp

end GameTheory.Tests.FinDistExtensions
