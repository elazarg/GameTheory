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
    (hbind : UtilityIntegrable utility agent (F.outcomeLaw μ))
    (hcond : ∀ profile, UtilityIntegrable utility agent (F.play profile)) :
    expectedUtility utility agent (F.outcomeLaw μ) hbind =
      expect μ (fun profile => expectedUtility utility agent (F.play profile)
        (hcond profile))
        (payoffIntegrable_bind_conditionalExpectation μ F.play
          (fun outcome => utility outcome agent) hbind hcond) := by
  exact expectedUtility_bind utility agent μ F.play hbind hcond

/-- Mapping every recommendation before play maps the integrand in the same
way. This covers both constant and recommendation-dependent deviations. -/
theorem expectedUtility_outcomeLaw_map (F : GameForm ι)
    (utility : F.sig.Outcome → ι → ℝ) (agent : ι)
    (μ : PMF (Profile F.sig)) (respond : Profile F.sig → Profile F.sig)
    (hbind : UtilityIntegrable utility agent
      (F.outcomeLaw (μ.map respond)))
    (hcond : ∀ profile, UtilityIntegrable utility agent
      (F.play (respond profile))) :
    expectedUtility utility agent (F.outcomeLaw (μ.map respond)) hbind =
      expect μ (fun profile => expectedUtility utility agent
        (F.play (respond profile)) (hcond profile))
        (payoffIntegrable_bind_conditionalExpectation μ
          (fun profile => F.play (respond profile))
          (fun outcome => utility outcome agent)
          (show UtilityIntegrable utility agent
            (μ.bind fun profile => F.play (respond profile)) from by
              simpa only [GameForm.outcomeLaw, PMF.bind_map, Function.comp_def]
                using hbind) hcond) := by
  have hbind' : UtilityIntegrable utility agent
      (μ.bind fun profile => F.play (respond profile)) := by
    simpa only [GameForm.outcomeLaw, PMF.bind_map, Function.comp_def] using hbind
  simpa only [GameForm.outcomeLaw, PMF.bind_map, Function.comp_def] using
    expectedUtility_bind utility agent μ
      (fun profile => F.play (respond profile)) hbind' hcond

/-- The preference package of a bundled utility game. -/
def UtilityGame.preference (G : UtilityGame ι) : WeakPreference ι G.form.sig.Outcome :=
  euPreference G.utility

/-! ## Guard projections and team utilities -/

/-- A guarded Nash relation includes integrability of the incumbent payoff for
each player. -/
theorem IsNash.utilityIntegrable [DecidableEq ι] {F : GameForm ι}
    {utility : F.sig.Outcome → ι → ℝ} {profile : Profile F.sig}
    (hnash : IsNash F (euPreference utility) profile) (who : ι) :
    UtilityIntegrable utility who (F.play profile) := by
  obtain ⟨hbase, -, -⟩ := (isNash_iff profile).1 hnash who (profile who)
  exact hbase

/-- A guarded Nash relation includes integrability of every compared unilateral
outcome law. -/
theorem IsNash.deviationIntegrable [DecidableEq ι] {F : GameForm ι}
    {utility : F.sig.Outcome → ι → ℝ} {profile : Profile F.sig}
    (hnash : IsNash F (euPreference utility) profile) (who : ι)
    (replacement : F.sig.Strategy who) :
    UtilityIntegrable utility who
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
    (who : ι) (replacement : F.sig.Strategy who) (observer : ι)
    (hbase : UtilityIntegrable utility who (F.play profile))
    (hdev : UtilityIntegrable utility who
      (F.play (Profile.update profile who replacement))) :
    expectedUtility utility observer
        (F.play (Profile.update profile who replacement))
        (by
          exact payoffIntegrable_congr_on_support
            (fun outcome _ => hteam outcome who observer) hdev) ≤
      expectedUtility utility observer (F.play profile)
        (by
          exact payoffIntegrable_congr_on_support
            (fun outcome _ => hteam outcome who observer) hbase) := by
  have hrel := (isNash_iff profile).mp hnash who replacement
  rcases hrel with ⟨_, _, hle⟩
  have hbaseObserver : UtilityIntegrable utility observer (F.play profile) := by
    exact payoffIntegrable_congr_on_support
      (fun outcome _ => hteam outcome who observer) hbase
  have hdevObserver : UtilityIntegrable utility observer
      (F.play (Profile.update profile who replacement)) := by
    exact payoffIntegrable_congr_on_support
      (fun outcome _ => hteam outcome who observer) hdev
  calc
    expectedUtility utility observer
        (F.play (Profile.update profile who replacement)) hdevObserver =
      expectedUtility utility who
        (F.play (Profile.update profile who replacement)) hdev :=
      hteam.expectedUtility_eq _ observer who hdevObserver hdev
    _ ≤ expectedUtility utility who (F.play profile) hbase := hle
    _ = expectedUtility utility observer (F.play profile) hbaseObserver :=
      hteam.expectedUtility_eq _ who observer hbase hbaseObserver

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
      UtilityIntegrable utility who
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
  obtain ⟨s₀, hs₀⟩ := replacementPMF.support_nonempty
  obtain ⟨hbase, -, -⟩ := hpure s₀
  have hcond : ∀ s, UtilityIntegrable utility who (q s) := by
    intro s
    obtain ⟨-, hc, -⟩ := hpure s
    exact hc
  have hle : ∀ s, expectedUtility utility who (q s) (hcond s) ≤
      expectedUtility utility who (F.outcomeLaw statusQuo) hbase := by
    intro s
    exact (euPreference_iff utility who (F.outcomeLaw statusQuo) (q s)
      hbase (hcond s)).mp (hpure s)
  have hbind : UtilityIntegrable utility who (replacementPMF.bind q) := by
    simpa only [hlaw] using hdev who replacementPMF
  have htower := expectedUtility_bind utility who replacementPMF q hbind hcond
  have houter := payoffIntegrable_bind_conditionalExpectation replacementPMF q
    (fun outcome => utility outcome who) hbind hcond
  have hconstant := payoffIntegrable_of_bounded replacementPMF
    (fun _ => expectedUtility utility who (F.outcomeLaw statusQuo) hbase)
    (C := |expectedUtility utility who (F.outcomeLaw statusQuo) hbase|)
    (fun _ => le_rfl)
  have hmean := expect_mono (fun s _ => hle s) houter hconstant
  have hdev' : UtilityIntegrable utility who (replacementPMF.bind q) := by
    simpa only [hlaw] using hdev who replacementPMF
  have hvalue := calc
      expectedUtility utility who
          (F.outcomeLaw
            ((DeviationScheme.unilateralRandomized F.sig).apply statusQuo who replacementPMF))
          (hdev who replacementPMF) =
        expectedUtility utility who (replacementPMF.bind q) hbind := by
            simp only [expectedUtility, hlaw]
      _ = expect replacementPMF (fun s => expectedUtility utility who (q s) (hcond s))
          (payoffIntegrable_bind_conditionalExpectation replacementPMF q
            (fun outcome => utility outcome who) hbind hcond) := htower
  have hleFinal : expectedUtility utility who
      (F.outcomeLaw ((DeviationScheme.unilateralRandomized F.sig).apply
        statusQuo who replacementPMF)) (hdev who replacementPMF) ≤
      expectedUtility utility who (F.outcomeLaw statusQuo) hbase := by
    calc
      expectedUtility utility who
          (F.outcomeLaw
            ((DeviationScheme.unilateralRandomized F.sig).apply statusQuo who replacement))
          (hdev who replacement) =
        expect replacement (fun s => expectedUtility utility who (q s) (hcond s))
          (payoffIntegrable_bind_conditionalExpectation replacement q
            (fun outcome => utility outcome who) hbind hcond) := hvalue
      _ ≤ expectedUtility utility who (F.outcomeLaw statusQuo) hbase := by
        calc
          _ ≤ expect replacementPMF (fun _ =>
              expectedUtility utility who (F.outcomeLaw statusQuo) hbase) hconstant := hmean
          _ = expectedUtility utility who (F.outcomeLaw statusQuo) hbase :=
            expect_constant replacementPMF _ hconstant
  exact (euPreference_iff utility who (F.outcomeLaw statusQuo)
    (F.outcomeLaw ((DeviationScheme.unilateralRandomized F.sig).apply
      statusQuo who replacement)) hbase (hdev who replacement)).2 hleFinal

/-- In the mixed extension a randomized deviation is a mixture of pure ones, so
mixed Nash is decided by pure deviations alone. This is what lets an executable
checker verify a supplied mixed profile against finitely many tests. -/
theorem isNash_mixed_iff [Fintype ι] (mixedProfile : Profile F.sig.mixed)
    (hdev : ∀ who (replacement : PMF (F.sig.Strategy who)),
      UtilityIntegrable utility who
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
  have hpure := fun s => h who s
  obtain ⟨s₀, hs₀⟩ := (mixedProfile who).support_nonempty
  obtain ⟨hbase, -, -⟩ := hpure s₀
  have hcond : ∀ s, UtilityIntegrable utility who (q s) := by
    intro s
    obtain ⟨-, hc, -⟩ := hpure s
    exact hc
  have hle : ∀ s, expectedUtility utility who (q s) (hcond s) ≤
      expectedUtility utility who (F.mixed.play mixedProfile) hbase := by
    intro s
    exact (euPreference_iff utility who (F.mixed.play mixedProfile) (q s)
      hbase (hcond s)).mp (hpure s)
  have hbind : UtilityIntegrable utility who (replacementPMF.bind q) := by
    rw [← GameForm.mixed_play_update]
    exact hdev who replacementPMF
  have htower := expectedUtility_bind utility who replacementPMF q hbind hcond
  have houter := payoffIntegrable_bind_conditionalExpectation replacementPMF q
    (fun outcome => utility outcome who) hbind hcond
  have hconstant := payoffIntegrable_of_bounded replacementPMF
    (fun _ => expectedUtility utility who (F.mixed.play mixedProfile) hbase)
    (C := |expectedUtility utility who (F.mixed.play mixedProfile) hbase|)
    (fun _ => le_rfl)
  have hmean := expect_mono (fun s _ => hle s) houter hconstant
  have hleFinal : expectedUtility utility who (F.mixed.play mixedProfile) hbase ≥
      expectedUtility utility who (F.mixed.play (Profile.update mixedProfile who replacement))
        (hdev who replacement) := by
    calc
      expectedUtility utility who (F.mixed.play (Profile.update mixedProfile who replacementPMF))
          (hdev who replacementPMF) =
        expectedUtility utility who (replacementPMF.bind q) hbind := by
          have heq := GameForm.mixed_play_update F mixedProfile who replacementPMF
          exact expectedUtility_congr_law utility who heq
            (hdev who replacementPMF) hbind
      _ = expect replacementPMF (fun s => expectedUtility utility who (q s) (hcond s))
          (payoffIntegrable_bind_conditionalExpectation replacementPMF q
            (fun outcome => utility outcome who) hbind hcond) := htower
      _ ≤ expectedUtility utility who (F.mixed.play mixedProfile) hbase := by
        calc
          _ ≤ expect replacementPMF (fun _ =>
              expectedUtility utility who (F.mixed.play mixedProfile) hbase) hconstant := hmean
          _ = expectedUtility utility who (F.mixed.play mixedProfile) hbase :=
            expect_constant replacementPMF _ hconstant
  exact (euPreference_iff utility who (F.mixed.play mixedProfile)
    (F.mixed.play (Profile.update mixedProfile who replacement)) hbase
    (hdev who replacement)).2 hleFinal

end Linearity

end GameTheory
