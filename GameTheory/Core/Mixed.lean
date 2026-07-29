/-
# The mixed extension and its equilibria

Mixed Nash is not a new predicate: it is `IsNash` of the mixed extension, and the
whole point of `GameForm.mixed` is that no second solution concept is needed. The
facts below are what make that presentation usable.

The first is that pure equilibria survive the embedding, which is not automatic —
a pure equilibrium resists only pure deviations, and the mixed game offers a law
over them. What closes the gap is that the deviator's expected utility is the
*average* of the pure deviations' utilities, so nothing beats a bound that every
pure deviation already respects.

That step is stated for expected utility rather than for an arbitrary weak
preference, and deliberately: a preference that does not respect averaging has no
reason to survive the embedding, and nothing in a `WeakPreference` makes it do
so.
-/

import GameTheory.Core.Utility

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

variable {ι : Type uι} [Fintype ι] [DecidableEq ι] {F : GameForm ι}
variable {utility : F.sig.Outcome → ι → ℝ}

/-- Embedding a pure profile and then replacing one coordinate by a point mass is
the same as replacing that coordinate first. -/
theorem purify_update (F : GameForm ι) (σ : Profile F.sig) (who : ι)
    (replacement : F.sig.Strategy who) :
    Profile.update (F.purify σ) who (FinDist.pure replacement) =
      F.purify (Profile.update σ who replacement) := by
  funext other
  by_cases hwho : other = who
  · subst hwho
    rw [Profile.update_same]
    show FinDist.pure replacement = FinDist.pure (Profile.update σ other replacement other)
    rw [Profile.update_same]
  · rw [Profile.update_of_ne _ _ hwho]
    show F.purify σ other = FinDist.pure (Profile.update σ who replacement other)
    rw [Profile.update_of_ne _ _ hwho]
    rfl

/-- An expectation is no larger than a bound every point of the support
respects. -/
theorem expect_le_of_forall {α : Type*} (μ : FinDist α) (observable : α → ℝ) (bound : ℝ)
    (hbound : ∀ a ∈ μ.support, observable a ≤ bound) : μ.expect observable ≤ bound := by
  refine le_of_le_of_eq (FinDist.expect_mono hbound) ?_
  exact FinDist.expect_const μ bound

/-- **A pure equilibrium stays one in the mixed extension.** The deviator gains
nothing by randomizing, because randomizing averages deviations it already could
not gain from. -/
theorem IsNash.purify (hnash : IsNash F (euPreference utility) σ) :
    IsNash F.mixed (euPreference utility) (F.purify σ) := by
  rw [isNash_iff] at hnash ⊢
  intro who replacement
  show expectedUtility utility who (F.mixed.play (Profile.update (F.purify σ) who replacement)) ≤
    expectedUtility utility who (F.mixed.play (F.purify σ))
  rw [GameForm.mixed_play_purify, GameForm.mixed_play_update]
  show (replacement.bind fun s =>
      F.mixed.play (Profile.update (F.purify σ) who (FinDist.pure s))).expect _ ≤ _
  rw [FinDist.expect_bind]
  refine expect_le_of_forall _ _ _ fun s _ => ?_
  rw [purify_update, GameForm.mixed_play_purify]
  exact hnash who s

/-- And the embedding is faithful on outcomes, so the two equilibria describe the
same play. -/
theorem play_purify (σ : Profile F.sig) : F.mixed.play (F.purify σ) = F.play σ :=
  GameForm.mixed_play_purify F σ

end GameTheory
