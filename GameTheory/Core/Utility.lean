/-
# Utility evaluation and expected-utility preference

Utility is separate data from the game form. `euPreference` is a *derived*
weak preference, so every equilibrium concept keeps exactly one logical
definition: `IsNash F (euPreference u) σ` is expected-utility Nash, and there is
no second predicate to rewrite between.

Expected utility stays specialized to `ℝ`. The executable frontend evaluates
rational payoffs and connects to this layer by a proved compilation, not by a
scalar parameter threaded through the core.
-/

import GameTheory.Core.Equilibrium
import GameTheory.Core.ExpectedUtility

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo uo'

variable {ι : Type uι} {sig : GameSignature ι} {Outcome : Type uo} {Outcome' : Type uo'}

/-- A real utility for each outcome and player. -/
abbrev Utility (sig : GameSignature ι) := sig.Outcome → ι → ℝ

/-- The dependent pair of a form and an evaluation. It repeats no strategy,
outcome, or play field; generic concepts still take the form and preference
explicitly, so bundling stays an ergonomic option rather than a second semantic
definition. -/
structure UtilityGame (ι : Type uι) where
  /-- The utility-free semantics. -/
  form : GameForm.{uι, us, uo} ι
  /-- How each player values an outcome. -/
  utility : Utility form.sig

-- The stored form retains independent strategy and outcome universes; the
-- linter sees those levels only through this dependent record.

/-- Every pure play has an integrable utility for each player. -/
def GameForm.HasIntegrableUtility {ι : Type uι} (F : GameForm ι)
    (utility : F.sig.Outcome → ι → ℝ) : Prop :=
  ∀ who profile, UtilityIntegrable utility who (F.play profile)

/-- A finite outcome carrier integrates every pure play law, without any
finiteness assumption on players or strategies. -/
theorem GameForm.hasIntegrableUtility_of_finiteOutcome {ι : Type uι}
    (F : GameForm ι) (utility : F.sig.Outcome → ι → ℝ)
    [Finite F.sig.Outcome] : F.HasIntegrableUtility utility := by
  intro who profile
  exact payoffIntegrable_of_finite (F.play profile) _

/-- Finite player and strategy carriers let pure-play integration pass through
independent mixed play, without restricting the outcome carrier. -/
theorem GameForm.HasIntegrableUtility.mixed_of_finite {ι : Type uι}
    [Fintype ι] {F : GameForm ι}
    {utility : F.sig.Outcome → ι → ℝ}
    (hintegrable : GameForm.HasIntegrableUtility F utility)
    [∀ i, Finite (F.sig.Strategy i)] :
    GameForm.HasIntegrableUtility F.mixed utility := by
  intro who mixedProfile
  have hbind := payoffIntegrable_bind_of_finite
    (independentProduct mixedProfile) F.play
    (fun outcome => utility outcome who)
    (fun profile => hintegrable who profile)
  simpa only [GameForm.mixed_play, UtilityIntegrable] using hbind

/-- Expected utility of a correlated profile law is the profile-law
expectation of the utility generated at each recommended profile. -/
theorem expectedUtility_outcomeLaw (F : GameForm ι)
    (utility : F.sig.Outcome → ι → ℝ) (agent : ι)
    (μ : PMF (Profile F.sig))
    (hbind : UtilityIntegrable utility agent (F.outcomeLaw μ)) :
    expectedUtility utility agent (F.outcomeLaw μ) =
      expect μ (fun profile => expectedUtility utility agent (F.play profile)) := by
  exact expectedUtility_bind utility agent μ F.play hbind

/-- Mapping every recommendation before play maps the integrand in the same
way. This covers both constant and recommendation-dependent deviations. -/
theorem expectedUtility_outcomeLaw_map (F : GameForm ι)
    (utility : F.sig.Outcome → ι → ℝ) (agent : ι)
    (μ : PMF (Profile F.sig)) (respond : Profile F.sig → Profile F.sig)
    (hbind : UtilityIntegrable utility agent
      (F.outcomeLaw (μ.map respond))) :
    expectedUtility utility agent (F.outcomeLaw (μ.map respond)) =
      expect μ (fun profile => expectedUtility utility agent
        (F.play (respond profile))) := by
  have hbind' : UtilityIntegrable utility agent
      (μ.bind fun profile => F.play (respond profile)) := by
    simpa only [GameForm.outcomeLaw, PMF.bind_map, Function.comp_def] using hbind
  simpa only [GameForm.outcomeLaw, PMF.bind_map, Function.comp_def] using
    expectedUtility_bind utility agent μ
      (fun profile => F.play (respond profile)) hbind'

/-! ## Integrable deviations

Expected-utility equilibria compare extended expected utilities, which may be
infinite. The predicates below say that every law an equilibrium concept
compares has an integrable payoff for the player who compares it, so all of
those comparisons are between real numbers. An equilibrium together with the
matching predicate is exactly an equilibrium of real-valued expected utility.
-/

section IntegrableDeviations

variable [DecidableEq ι]

/-- Every unilateral replacement at `profile`, staying included, has an
integrable payoff for the deviator. -/
def GameForm.HasIntegrableDeviations (F : GameForm ι)
    (utility : F.sig.Outcome → ι → ℝ) (profile : Profile F.sig) : Prop :=
  ∀ who replacement,
    UtilityIntegrable utility who (F.play (Profile.update profile who replacement))

/-- The recommended law and every constant unilateral replacement against it
have integrable payoffs for the deviator. -/
def GameForm.HasIntegrableCoarseDeviations (F : GameForm ι)
    (utility : F.sig.Outcome → ι → ℝ) (statusQuo : PMF (Profile F.sig)) : Prop :=
  (∀ who, UtilityIntegrable utility who (F.outcomeLaw statusQuo)) ∧
    ∀ who replacement, UtilityIntegrable utility who
      (statusQuo.bind fun profile => F.play (Profile.update profile who replacement))

/-- Every recommendation-dependent response to `statusQuo`, obedience included,
has an integrable payoff for the responder. -/
def GameForm.HasIntegrableResponses (F : GameForm ι)
    (utility : F.sig.Outcome → ι → ℝ) (statusQuo : PMF (Profile F.sig)) : Prop :=
  ∀ who (respond : F.sig.Strategy who → F.sig.Strategy who),
    UtilityIntegrable utility who
      (statusQuo.bind fun profile => F.play (Profile.update profile who (respond (profile who))))

variable {F : GameForm ι} {utility : F.sig.Outcome → ι → ℝ}

theorem GameForm.HasIntegrableDeviations.base {profile : Profile F.sig}
    (h : F.HasIntegrableDeviations utility profile) (who : ι) :
    UtilityIntegrable utility who (F.play profile) := by
  simpa only [Profile.update_eq_self] using h who (profile who)

theorem GameForm.HasIntegrableUtility.hasIntegrableDeviations
    (h : F.HasIntegrableUtility utility) (profile : Profile F.sig) :
    F.HasIntegrableDeviations utility profile :=
  fun who _ => h who _

theorem GameForm.HasIntegrableResponses.base {statusQuo : PMF (Profile F.sig)}
    (h : F.HasIntegrableResponses utility statusQuo) (who : ι) :
    UtilityIntegrable utility who (F.outcomeLaw statusQuo) := by
  simpa only [id, Profile.update_eq_self, GameForm.outcomeLaw] using h who id

theorem GameForm.HasIntegrableResponses.hasIntegrableCoarseDeviations
    {statusQuo : PMF (Profile F.sig)} (h : F.HasIntegrableResponses utility statusQuo) :
    F.HasIntegrableCoarseDeviations utility statusQuo :=
  ⟨h.base, fun who replacement => h who fun _ => replacement⟩

/-- A pure profile's point mass has integrable coarse deviations exactly when
the profile has integrable deviations. -/
theorem GameForm.hasIntegrableCoarseDeviations_pure_iff {profile : Profile F.sig} :
    F.HasIntegrableCoarseDeviations utility (PMF.pure profile) ↔
      F.HasIntegrableDeviations utility profile := by
  simp only [GameForm.HasIntegrableCoarseDeviations, GameForm.HasIntegrableDeviations,
    GameForm.outcomeLaw, PMF.pure_bind]
  exact ⟨fun h => h.2, fun h => ⟨fun who => by
    simpa only [Profile.update_eq_self] using h who (profile who), h⟩⟩

/-- With integrable deviations, expected-utility Nash is the real-valued
comparison of expected utilities. -/
theorem GameForm.HasIntegrableDeviations.isNash_iff {profile : Profile F.sig}
    (h : F.HasIntegrableDeviations utility profile) :
    IsNash F (euPreference utility) profile ↔
      ∀ who replacement,
        expectedUtility utility who (F.play (Profile.update profile who replacement)) ≤
          expectedUtility utility who (F.play profile) := by
  rw [GameTheory.isNash_iff]
  exact forall_congr' fun who => forall_congr' fun replacement =>
    euPreference_iff utility who _ _ (h.base who) (h who replacement)

/-- With integrable coarse deviations, expected-utility coarse correlated
equilibrium is the real-valued comparison of expected utilities. -/
theorem GameForm.HasIntegrableCoarseDeviations.isCoarseCorrelatedEq_iff
    {statusQuo : PMF (Profile F.sig)}
    (h : F.HasIntegrableCoarseDeviations utility statusQuo) :
    IsCoarseCorrelatedEq F (euPreference utility) statusQuo ↔
      ∀ who replacement,
        expectedUtility utility who
            (statusQuo.bind fun profile => F.play (Profile.update profile who replacement)) ≤
          expectedUtility utility who (F.outcomeLaw statusQuo) := by
  rw [GameTheory.isCoarseCorrelatedEq_iff]
  exact forall_congr' fun who => forall_congr' fun replacement =>
    euPreference_iff utility who _ _ (h.1 who) (h.2 who replacement)

/-- With integrable responses, expected-utility correlated equilibrium is the
real-valued comparison of expected utilities. -/
theorem GameForm.HasIntegrableResponses.isCorrelatedEq_iff
    {statusQuo : PMF (Profile F.sig)}
    (h : F.HasIntegrableResponses utility statusQuo) :
    IsCorrelatedEq F (euPreference utility) statusQuo ↔
      ∀ who (respond : F.sig.Strategy who → F.sig.Strategy who),
        expectedUtility utility who
            (statusQuo.bind fun profile =>
              F.play (Profile.update profile who (respond (profile who)))) ≤
          expectedUtility utility who (F.outcomeLaw statusQuo) := by
  rw [GameTheory.isCorrelatedEq_iff]
  exact forall_congr' fun who => forall_congr' fun respond =>
    euPreference_iff utility who _ _ (h.base who) (h who respond)

end IntegrableDeviations

/-- The preference package of a bundled utility game. -/
def UtilityGame.preference (G : UtilityGame ι) : WeakPreference ι G.form.sig.Outcome :=
  euPreference G.utility

/-! ## Expectation projections and team utilities -/

/-- At a Nash profile every player's incumbent payoff has an expectation. -/
theorem IsNash.utilityHasExpectation [DecidableEq ι] {F : GameForm ι}
    {utility : F.sig.Outcome → ι → ℝ} {profile : Profile F.sig}
    (hnash : IsNash F (euPreference utility) profile) (who : ι) :
    UtilityHasExpectation utility who (F.play profile) := by
  obtain ⟨hbase, -, -⟩ := (isNash_iff profile).1 hnash who (profile who)
  exact hbase

/-- At a coarse correlated equilibrium every player's payoff under the
recommended outcome law has an expectation. -/
theorem IsCoarseCorrelatedEq.utilityHasExpectation [DecidableEq ι] {F : GameForm ι}
    {utility : F.sig.Outcome → ι → ℝ} {law : PMF (Profile F.sig)}
    (hcce : IsCoarseCorrelatedEq F (euPreference utility) law) (who : ι) :
    UtilityHasExpectation utility who (F.outcomeLaw law) := by
  obtain ⟨hbase, -, -⟩ := (isCoarseCorrelatedEq_iff law).1 hcce who
    (law.support_nonempty.some who)
  exact hbase

/-- At a Nash profile every unilateral deviation's payoff has an expectation. -/
theorem IsNash.deviationHasExpectation [DecidableEq ι] {F : GameForm ι}
    {utility : F.sig.Outcome → ι → ℝ} {profile : Profile F.sig}
    (hnash : IsNash F (euPreference utility) profile) (who : ι)
    (replacement : F.sig.Strategy who) :
    UtilityHasExpectation utility who
      (F.play (Profile.update profile who replacement)) := by
  obtain ⟨-, hdeviation, -⟩ :=
    (isNash_iff profile).1 hnash who replacement
  exact hdeviation

/-- At a Nash profile of a team game, a unilateral deviation cannot improve
any player's expected utility, not only the deviator's. -/
theorem IsTeamGame.isNash_deviation_nonimproving [DecidableEq ι]
    {F : GameForm ι} {utility : F.sig.Outcome → ι → ℝ}
    (hteam : IsTeamGame utility) {profile : Profile F.sig}
    (hnash : IsNash F (euPreference utility) profile)
    (who : ι) (replacement : F.sig.Strategy who) (observer : ι) :
    extendedExpectedUtility utility observer
        (F.play (Profile.update profile who replacement)) ≤
      extendedExpectedUtility utility observer (F.play profile) := by
  obtain ⟨_, _, hle⟩ := (isNash_iff profile).mp hnash who replacement
  rw [hteam.extendedExpectedUtility_eq _ observer who,
    hteam.extendedExpectedUtility_eq _ observer who]
  exact hle

section Relabel

variable [DecidableEq ι]

/-- Relabeling outcomes and pulling the utility back along the relabeling leaves
Nash equilibrium unchanged. No cast appears in the statement because the
relabeled signature keeps the original strategy carriers. -/
theorem isNash_mapOutcome (F : GameForm ι) (relabel : F.sig.Outcome → Outcome')
    (utility : Outcome' → ι → ℝ) (profile : Profile F.sig) :
    IsNash (F.mapOutcome relabel) (euPreference utility) profile ↔
      IsNash F (euPreference fun outcome => utility (relabel outcome)) profile := by
  rw [isNash_iff, isNash_iff]
  refine forall_congr' fun who => forall_congr' fun replacement => ?_
  exact euPreference_map utility who relabel (F.play profile)
    (F.play (Profile.update profile who replacement))

end Relabel

/-! ## Expected-utility linearity in deviations

A randomized replacement is a convex combination of deterministic ones, so it
cannot beat all of them. This is why the standard equilibrium concepts may be
defined with deterministic deviations without weakening them. -/

section Linearity

variable [DecidableEq ι] {F : GameForm ι} {utility : Utility F.sig}

theorem isCoarseCorrelatedEq_randomized {statusQuo : PMF (Profile F.sig)}
    (h : IsCoarseCorrelatedEq F (euPreference utility) statusQuo)
    (hdev : ∀ who (replacement : PMF (F.sig.Strategy who)),
      UtilityHasExpectation utility who
        (F.outcomeLaw ((DeviationScheme.unilateralRandomized F.sig).apply
          statusQuo who replacement))) :
    IsEquilibrium F (euPreference utility) statusQuo
      (DeviationScheme.unilateralRandomized F.sig) := by
  intro who replacement
  let replacementPMF : PMF (F.sig.Strategy who) := replacement
  let q : F.sig.Strategy who → PMF F.sig.Outcome := fun s =>
    statusQuo.bind fun profile => F.play (Profile.update profile who s)
  have hlaw : F.outcomeLaw
      ((DeviationScheme.unilateralRandomized F.sig).apply statusQuo who replacementPMF) =
      replacementPMF.bind q := by
    rw [DeviationScheme.unilateralRandomized_apply]
    simp only [GameForm.outcomeLaw, PMF.bind_bind, PMF.bind_map]
    exact PMF.bind_comm statusQuo replacementPMF fun profile s =>
      F.play (Profile.update profile who s)
  have hpure := (isCoarseCorrelatedEq_iff statusQuo).mp h who
  have hbind : UtilityHasExpectation utility who (replacementPMF.bind q) := by
    simpa only [hlaw] using hdev who replacementPMF
  have hresult := euPreference_bind replacementPMF q (fun s _ => hpure s) hbind
  rwa [← hlaw] at hresult

/-- In the mixed extension a randomized deviation is a mixture of pure ones, so
mixed Nash is decided by pure deviations alone. This is what lets an executable
checker verify a supplied mixed profile against finitely many tests. -/
theorem isNash_mixed_iff [Fintype ι] (mixedProfile : Profile F.sig.mixed)
    (hdev : ∀ who (replacement : PMF (F.sig.Strategy who)),
      UtilityHasExpectation utility who
        (F.mixed.play (Profile.update mixedProfile who replacement))) :
    IsNash F.mixed (euPreference utility) mixedProfile ↔
      ∀ (who : ι) (s : F.sig.Strategy who),
        euPreference utility who (F.mixed.play mixedProfile)
          (F.mixed.play (Profile.update mixedProfile who (PMF.pure s))) := by
  rw [isNash_iff]
  refine ⟨fun h who s => h who (PMF.pure s), fun h who replacement => ?_⟩
  let replacementPMF : PMF (F.sig.Strategy who) := replacement
  let q : F.sig.Strategy who → PMF F.sig.Outcome := fun s =>
    F.mixed.play (Profile.update mixedProfile who (PMF.pure s))
  have heq := GameForm.mixed_play_update F mixedProfile who replacementPMF
  have hbind : UtilityHasExpectation utility who (replacementPMF.bind q) := by
    rw [← heq]
    exact hdev who replacementPMF
  have hresult := euPreference_bind replacementPMF q (fun s _ => h who s) hbind
  rwa [← heq] at hresult

end Linearity

end GameTheory
