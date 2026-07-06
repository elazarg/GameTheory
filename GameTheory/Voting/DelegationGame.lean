/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Voting.LiquidDemocracy
import GameTheory.Concepts.Equilibrium.SolutionConcepts

/-!
# The delegation game

Fluid democracy induces a strategic game: every voter simultaneously submits a
delegative ballot — delegate to another voter or cast directly — and the
collective choice is the liquid extension of an anonymous voting rule applied
to the submitted profile. Formalizing this as a `KernelGame` puts delegation
strategizing in the library's common solution-concept vocabulary
(`IsNash`, `IsDominant`, `IsBestResponse`), rather than requiring bespoke
equilibrium definitions per voting model.

## Main definitions

* `Voting.delegationGame` — the one-shot delegative voting game for a rule `R`
  and outcome utilities `u`
* `Voting.directVotingGame` — the game where every voter must cast

## Main results

* `eu_delegationGame_update_cast` — copy lemma, payoff form: switching a
  delegative ballot to a direct cast of its resolved ballot changes no payoff
* `isBestResponse_cast_iff_of_resolves` — copy lemma, strategic form: a voter
  best-responds with a delegative ballot iff they best-respond by casting the
  ballot it resolves to
* `isBestResponse_cast_of_isNash` — in a Nash profile, every voter is also
  best-responding by casting their resolved ballot directly
* `isNash_directVotingGame_of_isNash_delegationGame` — an all-cast Nash profile
  of the delegation game restricts to a Nash profile of direct voting
-/

namespace GameTheory.Voting

open DelegationProfile

variable {ι β α : Type} [Fintype ι]

/-- The delegation game induced by an anonymous voting rule `R` and utilities
`u` over outcomes: each voter submits a delegative ballot and the collective
choice is the liquid extension of `R`. -/
noncomputable def delegationGame (R : Multiset β → α) (u : ι → α → ℝ) :
    KernelGame ι where
  Strategy := fun _ => ι ⊕ β
  Outcome := α
  utility := fun a i => u i a
  outcomeKernel := fun σ => PMF.pure (liquidExtension R σ)

@[simp] theorem eu_delegationGame (R : Multiset β → α) (u : ι → α → ℝ)
    (σ : DelegationProfile ι β) (i : ι) :
    (delegationGame R u).eu σ i = u i (liquidExtension R σ) := by
  simp [delegationGame, KernelGame.eu]

/-- Copy lemma, payoff form: a voter replacing their delegative ballot by a
direct cast of its resolved ballot leaves every player's payoff unchanged. -/
theorem eu_delegationGame_update_cast [DecidableEq ι] {R : Multiset β → α}
    {u : ι → α → ℝ} {σ : DelegationProfile ι β} {i : ι} {b : β}
    (hib : σ.Resolves i b) (k : ι) :
    (delegationGame R u).eu (Function.update σ i (Sum.inr b)) k
      = (delegationGame R u).eu σ k := by
  rw [eu_delegationGame, eu_delegationGame]
  exact congrArg (u k) (liquidExtension_update_cast R hib)

/-- Copy lemma, strategic form: a voter best-responds with their delegative
ballot iff they best-respond by directly casting the ballot it resolves to. -/
theorem isBestResponse_cast_iff_of_resolves [DecidableEq ι] {R : Multiset β → α}
    {u : ι → α → ℝ} {σ : DelegationProfile ι β} {i : ι} {b : β}
    (hib : σ.Resolves i b) :
    (delegationGame R u).IsBestResponse i σ (Sum.inr b)
      ↔ (delegationGame R u).IsBestResponse i σ (σ i) := by
  have hself : liquidExtension R (Function.update σ i (σ i)) = liquidExtension R σ := by
    rw [Function.update_eq_self]
  have hcast : liquidExtension R (Function.update σ i (Sum.inr b))
      = liquidExtension R σ :=
    liquidExtension_update_cast R hib
  constructor
  · intro h s'
    calc (delegationGame R u).eu (Function.update σ i (σ i)) i
        = u i (liquidExtension R σ) := by
          rw [eu_delegationGame]; exact congrArg (u i) hself
      _ = (delegationGame R u).eu (Function.update σ i (Sum.inr b)) i := by
          rw [eu_delegationGame]; exact (congrArg (u i) hcast).symm
      _ ≥ (delegationGame R u).eu (Function.update σ i s') i := h s'
  · intro h s'
    calc (delegationGame R u).eu (Function.update σ i (Sum.inr b)) i
        = u i (liquidExtension R σ) := by
          rw [eu_delegationGame]; exact congrArg (u i) hcast
      _ = (delegationGame R u).eu (Function.update σ i (σ i)) i := by
          rw [eu_delegationGame]; exact (congrArg (u i) hself).symm
      _ ≥ (delegationGame R u).eu (Function.update σ i s') i := h s'

/-- In a Nash profile of the delegation game, every voter is also
best-responding by directly casting their resolved ballot. -/
theorem isBestResponse_cast_of_isNash [DecidableEq ι]
    {R : Multiset β → α} {u : ι → α → ℝ} {σ : DelegationProfile ι β} {i : ι}
    {b : β} (hσ : (delegationGame R u).IsNash σ) (hib : σ.Resolves i b) :
    (delegationGame R u).IsBestResponse i σ (Sum.inr b) := by
  rw [isBestResponse_cast_iff_of_resolves hib]
  intro s'
  calc (delegationGame R u).eu (Function.update σ i (σ i)) i
      = (delegationGame R u).eu σ i :=
        congrArg (fun τ => (delegationGame R u).eu τ i) (Function.update_eq_self i σ)
    _ ≥ (delegationGame R u).eu (Function.update σ i s') i := hσ i s'

/-- The direct voting game: every voter must cast a ballot, and the outcome is
the rule applied to the cast ballots. -/
noncomputable def directVotingGame (R : Multiset β → α) (u : ι → α → ℝ) :
    KernelGame ι where
  Strategy := fun _ => β
  Outcome := α
  utility := fun a i => u i a
  outcomeKernel := fun p => PMF.pure (R (Finset.univ.val.map p))

@[simp] theorem eu_directVotingGame (R : Multiset β → α) (u : ι → α → ℝ)
    (p : ι → β) (i : ι) :
    (directVotingGame R u).eu p i = u i (R (Finset.univ.val.map p)) := by
  simp [directVotingGame, KernelGame.eu]

/-- Payoffs in the direct voting game coincide with payoffs in the delegation
game at the corresponding all-cast profile. -/
theorem eu_directVotingGame_eq_delegationGame (R : Multiset β → α)
    (u : ι → α → ℝ) (p : ι → β) (i : ι) :
    (directVotingGame R u).eu p i = (delegationGame R u).eu (directProfile p) i := by
  rw [eu_directVotingGame, eu_delegationGame, liquidExtension_directProfile]

/-- Restriction of equilibrium: if the all-cast profile is Nash in the
delegation game, the underlying ballot profile is Nash in the direct voting
game. -/
theorem isNash_directVotingGame_of_isNash_delegationGame [DecidableEq ι]
    {R : Multiset β → α} {u : ι → α → ℝ} {p : ι → β}
    (h : (delegationGame R u).IsNash (directProfile p)) :
    (directVotingGame R u).IsNash p := by
  intro who s'
  calc (directVotingGame R u).eu p who
      = (delegationGame R u).eu (directProfile p) who :=
        eu_directVotingGame_eq_delegationGame R u p who
    _ ≥ (delegationGame R u).eu
          (Function.update (directProfile p) who (Sum.inr s')) who :=
        h who (Sum.inr s')
    _ = (delegationGame R u).eu (directProfile (Function.update p who s')) who :=
        congrArg (fun τ => (delegationGame R u).eu τ who)
          (update_directProfile p who s')
    _ = (directVotingGame R u).eu (Function.update p who s') who :=
        (eu_directVotingGame_eq_delegationGame R u _ who).symm

end GameTheory.Voting
