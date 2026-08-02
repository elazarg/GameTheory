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
variable {utility : F.sig.Outcome → ι → ℝ} {mixedProfile : Profile F.sig.mixed}

/-- Bundle the existing mixed form with the original outcome utility. This is
only ergonomic packaging: it introduces neither a second mixed construction nor
a second evaluator. -/
@[reducible]
def UtilityGame.mixed (G : UtilityGame ι) : UtilityGame ι where
  form := G.form.mixed
  utility := G.utility

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

/-- **A mixed Nash profile induces a correlated equilibrium** on its
independent law of pure profiles. A recommendation-dependent response merely
maps the deviator's marginal, which is one admissible mixed replacement. The
argument preserves complete outcome laws, so no expected-utility assumption is
needed. -/
theorem IsNash.isCorrelatedEq_pi
    {preference : WeakPreference ι F.sig.Outcome}
    (hnash : IsNash F.mixed preference mixedProfile) :
    IsCorrelatedEq F preference (FinDist.pi mixedProfile) := by
  rw [isNash_iff] at hnash
  rw [isCorrelatedEq_iff]
  intro who respond
  have hdeviation := hnash who ((mixedProfile who).map respond)
  rw [GameForm.mixed_play, GameForm.mixed_play,
    ← GameForm.pi_map_recommendation F.sig mixedProfile who respond,
    FinDist.bind_map] at hdeviation
  exact hdeviation

/-- **A mixed Nash profile also induces a coarse correlated equilibrium.**
This is the recommendation-independent shadow of `IsNash.isCorrelatedEq_pi`;
it remains preference-parametric and needs no boundedness hypothesis. -/
theorem IsNash.isCoarseCorrelatedEq_pi
    {preference : WeakPreference ι F.sig.Outcome}
    (hnash : IsNash F.mixed preference mixedProfile) :
    IsCoarseCorrelatedEq F preference (FinDist.pi mixedProfile) :=
  hnash.isCorrelatedEq_pi.isCoarseCorrelatedEq

/-! ## What a mixed equilibrium randomizes over

A mixed equilibrium does not merely fail to gain by deviating; it is indifferent
across everything it actually plays. That is the fact every computation with
mixed equilibria uses, and it is a consequence rather than a definition. -/

/-- The expected utility of a mixed profile is the deviator's own average over
its own randomization. -/
theorem expectedUtility_mixed_eq_expect (F : GameForm ι) (utility : F.sig.Outcome → ι → ℝ)
    (mixedProfile : Profile F.sig.mixed) (who : ι) :
    expectedUtility utility who (F.mixed.play mixedProfile) =
      (mixedProfile who).expect fun s =>
        expectedUtility utility who
          (F.mixed.play (Profile.update mixedProfile who (FinDist.pure s))) := by
  conv_lhs => rw [show mixedProfile = Profile.update mixedProfile who (mixedProfile who) from
    (Profile.update_eq_self mixedProfile who).symm]
  rw [GameForm.mixed_play_update]
  exact FinDist.expect_bind ..

/-- **A mixed equilibrium is indifferent across its own support.** Every strategy
it gives positive weight is worth exactly what the mixture is worth — so none of
them is a strict loss, and none is a missed gain. -/
theorem IsNash.expectedUtility_eq_of_mem_support
    (hnash : IsNash F.mixed (euPreference utility) mixedProfile) (who : ι)
    {s : F.sig.Strategy who} (hs : s ∈ (mixedProfile who).support) :
    expectedUtility utility who
        (F.mixed.play (Profile.update mixedProfile who (FinDist.pure s))) =
      expectedUtility utility who (F.mixed.play mixedProfile) := by
  rw [isNash_iff] at hnash
  refine FinDist.eq_of_expect_eq_of_le (mixedProfile who) _ _ (fun t _ => hnash who _)
    ?_ hs
  exact (expectedUtility_mixed_eq_expect F utility mixedProfile who).symm

/-- And the embedding is faithful on outcomes, so the two equilibria describe the
same play. -/
theorem play_purify (σ : Profile F.sig) : F.mixed.play (F.purify σ) = F.play σ :=
  GameForm.mixed_play_purify F σ

end GameTheory
