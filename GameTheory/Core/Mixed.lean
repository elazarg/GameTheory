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

open GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι} [Fintype ι] [DecidableEq ι] {F : GameForm ι}
variable {utility : F.sig.Outcome → ι → ℝ} {mixedProfile : Profile F.sig.mixed}

/-- A pure-coordinate mixed outcome is a bind over the original product
belief, evaluated after replacing that coordinate. -/
theorem mixed_play_update_pure_eq_bind
    (beliefs : Profile F.sig.mixed) (who : ι)
    (strategy : F.sig.Strategy who) :
    F.mixed.play (Profile.update beliefs who (PMF.pure strategy)) =
      (independentProduct beliefs).bind fun profile =>
        F.play (Profile.update profile who strategy) := by
  rw [GameForm.mixed_play]
  rw [show PMF.pure strategy =
      (beliefs who).map (fun _ => strategy) by
        have hfunction : (fun _ : F.sig.Strategy who => strategy) =
            Function.const (F.sig.Strategy who) strategy := rfl
        rw [hfunction]
        exact (PMF.map_const (p := beliefs who) (b := strategy)).symm]
  rw [← GameForm.pi_map_recommendation, PMF.bind_map]
  rfl

/-- Bundle the existing mixed form with the original outcome utility. This is
only ergonomic packaging: it introduces neither a second mixed construction nor
a second evaluator. -/
@[reducible]
def UtilityGame.mixed (G : UtilityGame ι) : UtilityGame ι where
  form := G.form.mixed
  utility := G.utility

/-- The mixed play law is the player's own mixture of pure-action replacements. -/
theorem mixed_play_update_self (F : GameForm ι)
    (mixedProfile : Profile F.sig.mixed) (who : ι) :
    F.mixed.play mixedProfile =
      (mixedProfile who).bind (fun s =>
        F.mixed.play (Profile.update mixedProfile who (PMF.pure s))) := by
  calc
    F.mixed.play mixedProfile = F.mixed.play
        (Profile.update mixedProfile who (mixedProfile who)) := by
          rw [Profile.update_eq_self]
    _ = _ := GameForm.mixed_play_update F mixedProfile who (mixedProfile who)

omit [Fintype ι] in
/-- Embedding a pure profile and then replacing one coordinate by a point mass is
the same as replacing that coordinate first. -/
theorem purify_update (F : GameForm ι) (σ : Profile F.sig) (who : ι)
    (replacement : F.sig.Strategy who) :
    Profile.update (F.purify σ) who (PMF.pure replacement) =
      F.purify (Profile.update σ who replacement) := by
  funext other
  by_cases hwho : other = who
  · subst hwho
    rw [Profile.update_same]
    show PMF.pure replacement = PMF.pure (Profile.update σ other replacement other)
    rw [Profile.update_same]
  · rw [Profile.update_of_ne _ _ hwho]
    show F.purify σ other = PMF.pure (Profile.update σ who replacement other)
    rw [Profile.update_of_ne _ _ hwho]
    rfl

/-- **A pure equilibrium stays one in the mixed extension.** The deviator gains
nothing by randomizing, because randomizing averages deviations it already could
not gain from. Each randomized deviation must have an expected utility: mixing a
pure deviation worth `+∞` with one worth `−∞` leaves none. -/
theorem IsNash.purify {σ : Profile F.sig}
    (hnash : IsNash F (euPreference utility) σ)
    (hdeviation : ∀ who (replacement : PMF (F.sig.Strategy who)),
      UtilityHasExpectation utility who
        (F.mixed.play (Profile.update (F.purify σ) who replacement))) :
    IsNash F.mixed (euPreference utility) (F.purify σ) := by
  apply (isNash_mixed_iff (F := F) (utility := utility)
    (F.purify σ) hdeviation).2
  intro who s
  have hpure := (isNash_iff σ).1 hnash who s
  rw [GameForm.mixed_play_purify, purify_update, GameForm.mixed_play_purify]
  exact hpure

/-- With finite strategy carriers, integrable pure deviations make every
randomized deviation integrable. Outcome carriers may remain infinite. The
integrability is needed: a pure deviation worth `+∞` mixed with one worth `−∞`
has no expected utility. -/
theorem IsNash.purify_of_finite {σ : Profile F.sig}
    [∀ who, Finite (F.sig.Strategy who)]
    (hnash : IsNash F (euPreference utility) σ)
    (hdeviation : ∀ who replacement,
      UtilityIntegrable utility who (F.play (Profile.update σ who replacement))) :
    IsNash F.mixed (euPreference utility) (F.purify σ) := by
  refine hnash.purify fun who replacement => UtilityIntegrable.hasExpectation ?_
  rw [GameForm.mixed_play_update]
  apply payoffIntegrable_bind_of_finite (replacement)
    (fun s => F.mixed.play (Profile.update (F.purify σ) who (PMF.pure s)))
    (fun outcome => utility outcome who)
  intro s
  have heq : F.mixed.play (Profile.update (F.purify σ) who (PMF.pure s)) =
      F.play (Profile.update σ who s) := by
    rw [purify_update, GameForm.mixed_play_purify]
  simpa only [← heq] using hdeviation who s

/-- **A mixed Nash profile induces a correlated equilibrium** on its
independent law of pure profiles. A recommendation-dependent response merely
maps the deviator's marginal, which is one admissible mixed replacement. The
argument preserves complete outcome laws, so no expected-utility assumption is
needed. -/
theorem IsNash.isCorrelatedEq_pi
    {preference : WeakPreference ι F.sig.Outcome}
    (hnash : IsNash F.mixed preference mixedProfile) :
    IsCorrelatedEq F preference (independentProduct mixedProfile) := by
  rw [isNash_iff] at hnash
  rw [isCorrelatedEq_iff]
  intro who respond
  have hdeviation := hnash who ((mixedProfile who).map respond)
  rw [GameForm.mixed_play, GameForm.mixed_play,
    ← GameForm.pi_map_recommendation F.sig mixedProfile who respond,
    PMF.bind_map] at hdeviation
  exact hdeviation

/-- **A mixed Nash profile also induces a coarse correlated equilibrium.**
This is the recommendation-independent shadow of `IsNash.isCorrelatedEq_pi`;
it remains preference-parametric and needs no boundedness hypothesis. -/
theorem IsNash.isCoarseCorrelatedEq_pi
    {preference : WeakPreference ι F.sig.Outcome}
    (hnash : IsNash F.mixed preference mixedProfile) :
    IsCoarseCorrelatedEq F preference (independentProduct mixedProfile) :=
  hnash.isCorrelatedEq_pi.isCoarseCorrelatedEq

/-! ## What a mixed equilibrium randomizes over

A mixed equilibrium does not merely fail to gain by deviating; it is indifferent
across everything it actually plays. That is the fact every computation with
mixed equilibria uses, and it is a consequence rather than a definition. -/

/-- The expected utility of a mixed profile is the deviator's own average over
its own randomization. -/
theorem expectedUtility_mixed_eq_expect (F : GameForm ι) (utility : F.sig.Outcome → ι → ℝ)
    (mixedProfile : Profile F.sig.mixed) (who : ι)
    (hmixed : UtilityIntegrable utility who (F.mixed.play mixedProfile)) :
    expectedUtility utility who (F.mixed.play mixedProfile) =
      expect (mixedProfile who)
        (fun s => expectedUtility utility who
          (F.mixed.play (Profile.update mixedProfile who (PMF.pure s)))) := by
  let q := fun s => F.mixed.play (Profile.update mixedProfile who (PMF.pure s))
  have heq := mixed_play_update_self F mixedProfile who
  have hbind : UtilityIntegrable utility who ((mixedProfile who).bind q) := by
    rw [← heq]
    exact hmixed
  have htower := expectedUtility_bind utility who (mixedProfile who) q hbind
  calc
    expectedUtility utility who (F.mixed.play mixedProfile) =
        expectedUtility utility who ((mixedProfile who).bind q) :=
      expectedUtility_congr_law utility who heq
    _ = expect (mixedProfile who)
        (fun s => expectedUtility utility who (q s)) := htower

/-- **A mixed equilibrium is indifferent across its own support.** Every strategy
it gives positive weight is worth exactly what the mixture is worth — so none of
them is a strict loss, and none is a missed gain. -/
theorem IsNash.expectedUtility_eq_of_mem_support
    (hnash : IsNash F.mixed (euPreference utility) mixedProfile) (who : ι)
    (hbase : UtilityIntegrable utility who (F.mixed.play mixedProfile))
    {s : F.sig.Strategy who} (hs : s ∈ (mixedProfile who).support) :
    expectedUtility utility who
        (F.mixed.play (Profile.update mixedProfile who (PMF.pure s))) =
      expectedUtility utility who (F.mixed.play mixedProfile) := by
  let q := fun t => F.mixed.play (Profile.update mixedProfile who (PMF.pure t))
  have hbind : UtilityIntegrable utility who ((mixedProfile who).bind q) := by
    rw [← mixed_play_update_self F mixedProfile who]
    exact hbase
  have hpure : ∀ t ∈ (mixedProfile who).support, UtilityIntegrable utility who (q t) :=
    fun t ht => payoffIntegrable_bind_conditional_on_support _ q _ hbind t ht
  have houter := payoffIntegrable_bind_conditionalExpectation (mixedProfile who) q
    (fun outcome => utility outcome who) hbind
  rw [isNash_iff] at hnash
  let value := fun t => expectedUtility utility who (q t)
  let base := expectedUtility utility who (F.mixed.play mixedProfile)
  have hle : ∀ t ∈ (mixedProfile who).support, value t ≤ base := fun t ht =>
    (euPreference_iff utility who _ (q t) hbase (hpure t ht)).mp (hnash who (PMF.pure t))
  have havg : expect (mixedProfile who) value = base :=
    (expectedUtility_mixed_eq_expect F utility mixedProfile who hbase).symm
  exact expect_eq_const_of_le_on_support (mixedProfile who) value base houter hle havg s hs

omit [DecidableEq ι] in
/-- And the embedding is faithful on outcomes, so the two equilibria describe the
same play. -/
theorem play_purify (σ : Profile F.sig) : F.mixed.play (F.purify σ) = F.play σ :=
  GameForm.mixed_play_purify F σ

end GameTheory
