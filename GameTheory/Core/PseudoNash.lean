/-
# Pseudo-Nash equilibrium

A pseudo-Nash equilibrium ranks a player's utility against each unilateral
deviation by computational mean dominance instead of by expectation. With any
polynomial number of plays of each profile, no deviation's empirical mean
comes out ahead with non-negligible advantage. Events of negligible
probability, such as guessing a key or opening a commitment to another value,
are invisible to this comparison however large their payoffs.

Games are parameterized by a size `κ`, such as a security parameter. The
strategy carriers are fixed, and play laws and utilities may depend on `κ`.
Pseudo-Nash is not a separate predicate: a profile determines the family of its
outcome laws across all sizes, so a parameterized game is a deterministic form
over those families, and pseudo-Nash is Nash of that form for the
mean-dominance preference. A random family is compared through its marginal at
each size. A fixed game is the constant family; its preference is the
mean-dominance preference read on constant families, which for bounded
utilities is expected-utility preference (`GameTheory.Analysis.PseudoNash`).

Replacing an ideal primitive by a secure implementation preserves pseudo-Nash.
A `SecureImplementation` compiles ideal strategies into real ones such that
compiled honest play, and every real deviation from it, is simulated by ideal
play whose utility ensembles a class of tests cannot tell apart from the real
ones. If that class can compare empirical means with the games' utility
ensembles, then each real deviation is covered by its simulation, and Nash
transfer along coverage turns an ideal pseudo-Nash equilibrium into a real
one. With every test seeing polynomially many draws, negligible statistical
distance of the utility ensembles suffices. With polynomial-time tests, it is the utility-level consequence of simulation-based
security plus efficient sampling of play; when both games compute utility from
a common view, indistinguishable views suffice.

Primary reference: A. Psomas, A. Terzoglou, Y. Wei, and V. Zikas,
“Pseudo-Equilibria, or: How to Stop Worrying About Crypto and Just Analyze the
Game,” arXiv:2506.22089 (2025).
-/
import GameTheory.Core.Equilibrium
import GameTheory.Math.Probability.Indistinguishability

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι}

/-- A game over a fixed strategy signature whose play law and utilities depend
on a size parameter `κ`. -/
structure ParameterizedGame (ι : Type uι) where
  /-- The strategy and outcome carriers, the same at every size. -/
  sig : GameSignature.{uι, us, uo} ι
  /-- The outcome law of each profile at each size. -/
  play : ℕ → Profile sig → PMF sig.Outcome
  /-- Each player's utility of an outcome at each size. -/
  utility : ℕ → sig.Outcome → ι → ℝ

-- Strategy and outcome universes stay independent, as in `GameSignature`.

namespace ParameterizedGame

/-- The game form at one size. -/
@[reducible]
def formAt (G : ParameterizedGame ι) (κ : ℕ) : GameForm ι where
  sig := G.sig
  play := G.play κ

/-- The form whose outcome is the family of outcome laws across all sizes. A
profile determines that family, so the form is deterministic; strategies are
those of the game. -/
@[reducible]
def ensembleForm (G : ParameterizedGame ι) : GameForm ι :=
  GameForm.deterministic (G.sig.mapOutcome (ℕ → PMF G.sig.Outcome))
    fun profile κ => G.play κ profile

/-- The ensemble of a player's realized utility at a profile. -/
def utilityLaw (G : ParameterizedGame ι) (who : ι) (profile : Profile G.sig) : ℕ → PMF ℝ :=
  fun κ => (G.play κ profile).map fun outcome => G.utility κ outcome who

/-- A fixed game as the constant family. -/
@[reducible]
def constant (F : GameForm ι) (utility : F.sig.Outcome → ι → ℝ) : ParameterizedGame ι where
  sig := F.sig
  play _ := F.play
  utility _ := utility

end ParameterizedGame

/-! ## Mean-dominance preferences -/

section Preferences

variable {Outcome : Type*}

/-- The law at size `κ` of a random family of outcome laws: draw the family,
then draw from its member at `κ`. -/
def ensembleMarginal (law : PMF (ℕ → PMF Outcome)) (κ : ℕ) : PMF Outcome :=
  law.bind fun family => family κ

@[simp]
theorem ensembleMarginal_pure (family : ℕ → PMF Outcome) (κ : ℕ) :
    ensembleMarginal (PMF.pure family) κ = family κ :=
  PMF.pure_bind _ _

/-- Relabeling each outcome as the constant family of its point mass marginalizes
back to the original law at every size. -/
theorem ensembleMarginal_map_const (law : PMF Outcome) (κ : ℕ) :
    ensembleMarginal (law.map fun outcome (_ : ℕ) => PMF.pure outcome) κ = law := by
  rw [ensembleMarginal, PMF.bind_map]
  exact PMF.bind_pure law

/-- A player prefers a random family of outcome laws when, size by size, the
ensemble of its utility computationally mean-dominates that of the
alternative. -/
def meanDominancePreference (utility : ℕ → Outcome → ι → ℝ) :
    WeakPreference ι (ℕ → PMF Outcome) :=
  fun who preferred alternative =>
    ComputationallyMeanDominates
      (fun κ => (ensembleMarginal preferred κ).map fun outcome => utility κ outcome who)
      (fun κ => (ensembleMarginal alternative κ).map fun outcome => utility κ outcome who)

theorem meanDominancePreference_pure (utility : ℕ → Outcome → ι → ℝ) (who : ι)
    (family family' : ℕ → PMF Outcome) :
    meanDominancePreference utility who (PMF.pure family) (PMF.pure family') ↔
      ComputationallyMeanDominates
        (fun κ => (family κ).map fun outcome => utility κ outcome who)
        (fun κ => (family' κ).map fun outcome => utility κ outcome who) := by
  simp only [meanDominancePreference, ensembleMarginal_pure]

/-- For a fixed utility, the mean-dominance preference on outcome laws: each law
is read as the constant family. -/
def empiricalMeanPreference (utility : Outcome → ι → ℝ) : WeakPreference ι Outcome :=
  Preference.comapOutcome (fun outcome (_ : ℕ) => PMF.pure outcome)
    (meanDominancePreference fun _ => utility)

theorem empiricalMeanPreference_apply (utility : Outcome → ι → ℝ) (who : ι)
    (preferred alternative : PMF Outcome) :
    empiricalMeanPreference utility who preferred alternative ↔
      ComputationallyMeanDominates (fun _ => preferred.map fun outcome => utility outcome who)
        (fun _ => alternative.map fun outcome => utility outcome who) := by
  simp only [empiricalMeanPreference, Preference.comapOutcome_apply, meanDominancePreference,
    ensembleMarginal_map_const]

end Preferences

/-! ## Pseudo-Nash equilibrium -/

/-- A pseudo-Nash equilibrium: Nash of the ensemble form for the mean-dominance
preference. -/
abbrev ParameterizedGame.IsPseudoNash [DecidableEq ι] (G : ParameterizedGame ι)
    (profile : Profile G.sig) : Prop :=
  IsNash G.ensembleForm (meanDominancePreference G.utility) profile

/-- Each player's utility ensemble computationally mean-dominates that of every
unilateral replacement. -/
theorem ParameterizedGame.isPseudoNash_iff [DecidableEq ι] (G : ParameterizedGame ι)
    (profile : Profile G.sig) :
    G.IsPseudoNash profile ↔
      ∀ who (replacement : G.sig.Strategy who),
        ComputationallyMeanDominates (G.utilityLaw who profile)
          (G.utilityLaw who (Profile.update profile who replacement)) := by
  rw [ParameterizedGame.IsPseudoNash, isNash_iff]
  exact forall_congr' fun who => forall_congr' fun replacement =>
    meanDominancePreference_pure _ _ _ _

/-- In a fixed game, pseudo-Nash is Nash for the empirical-mean preference. -/
theorem ParameterizedGame.isPseudoNash_constant_iff [DecidableEq ι] (F : GameForm ι)
    (utility : F.sig.Outcome → ι → ℝ) (profile : Profile F.sig) :
    (constant F utility).IsPseudoNash profile ↔
      IsNash F (empiricalMeanPreference utility) profile := by
  rw [isPseudoNash_iff, isNash_iff]
  exact forall_congr' fun who => forall_congr' fun replacement =>
    (empiricalMeanPreference_apply _ _ _ _).symm

/-! ## Views and utilities -/

section Views

universe us' uo'

/-- Indistinguishable views give indistinguishable utility ensembles when both
games compute the player's utility from the view by the same score and the view
tests contain the score's precompositions of the utility tests. -/
theorem ParameterizedGame.indistinguishableBy_utilityLaw_of_views {V : Type*}
    {viewTests : Set (SampleTest V)} {tests : Set (SampleTest ℝ)}
    {G : ParameterizedGame.{uι, us, uo} ι} {G' : ParameterizedGame.{uι, us', uo'} ι}
    (view : ℕ → G.sig.Outcome → V) (view' : ℕ → G'.sig.Outcome → V)
    (score : ℕ → V → ι → ℝ)
    (hscore : ∀ κ outcome who, G.utility κ outcome who = score κ (view κ outcome) who)
    (hscore' : ∀ κ outcome who, G'.utility κ outcome who = score κ (view' κ outcome) who)
    {who : ι} (hclosed : ClosedUnderComap viewTests (fun κ v => score κ v who) tests)
    {profile : Profile G.sig} {profile' : Profile G'.sig}
    (h : IndistinguishableBy viewTests (fun κ => (G.play κ profile).map (view κ))
      (fun κ => (G'.play κ profile').map (view' κ))) :
    IndistinguishableBy tests (G.utilityLaw who profile) (G'.utilityLaw who profile') := by
  have hG : G.utilityLaw who profile =
      fun κ => ((G.play κ profile).map (view κ)).map fun v => score κ v who := by
    funext κ
    rw [utilityLaw, PMF.map_comp]
    congr 1
    funext outcome
    exact hscore κ outcome who
  have hG' : G'.utilityLaw who profile' =
      fun κ => ((G'.play κ profile').map (view' κ)).map fun v => score κ v who := by
    funext κ
    rw [utilityLaw, PMF.map_comp]
    congr 1
    funext outcome
    exact hscore' κ outcome who
  rw [hG, hG']
  exact h.map hclosed

end Views

/-! ## Replacing ideal primitives by secure implementations -/

/-- A compilation of an ideal game's strategies into a real game's, simulated
at the level of utility ensembles: compiled honest play is indistinguishable
from ideal honest play, and every real unilateral deviation from compiled play
is indistinguishable from some ideal unilateral deviation. -/
structure SecureImplementation [DecidableEq ι] (tests : Set (SampleTest ℝ))
    (ideal real : ParameterizedGame.{uι, us, uo} ι) where
  /-- The real strategy running each ideal strategy on the implementation. -/
  compile : ∀ who, ideal.sig.Strategy who → real.sig.Strategy who
  honest : ∀ (profile : Profile ideal.sig) who,
    IndistinguishableBy tests (real.utilityLaw who (Profile.map compile profile))
      (ideal.utilityLaw who profile)
  simulate : ∀ (profile : Profile ideal.sig) who (deviation : real.sig.Strategy who),
    ∃ simulated : ideal.sig.Strategy who,
      IndistinguishableBy tests
        (real.utilityLaw who (Profile.update (Profile.map compile profile) who deviation))
        (ideal.utilityLaw who (Profile.update profile who simulated))

/-- **Ideal to real.** Compiling a pseudo-Nash equilibrium of the ideal game
yields a pseudo-Nash equilibrium of the real game, provided the tests can
compare empirical means with the utility ensembles of both games. Each real
deviation is covered by its simulation, so this is Nash transfer along
coverage. -/
theorem SecureImplementation.isPseudoNash [DecidableEq ι] {tests : Set (SampleTest ℝ)}
    {ideal real : ParameterizedGame.{uι, us, uo} ι} (impl : SecureImplementation tests ideal real)
    (hreal : ∀ who profile, ContainsMeanTests tests (real.utilityLaw who profile))
    (hideal : ∀ who profile, ContainsMeanTests tests (ideal.utilityLaw who profile))
    {profile : Profile ideal.sig} (h : ideal.IsPseudoNash profile) :
    real.IsPseudoNash (Profile.map impl.compile profile) := by
  refine IsNash.of_coverage (fun who deviation => ?_) h
  obtain ⟨simulated, hsimulated⟩ := impl.simulate profile who deviation
  refine ⟨simulated, fun hsource => ?_⟩
  have hdominates : ComputationallyMeanDominates (ideal.utilityLaw who profile)
      (ideal.utilityLaw who (Profile.update profile who simulated)) :=
    (meanDominancePreference_pure _ _ _ _).mp hsource
  have hhonest := (impl.honest profile who).meanTestIndistinguishable
    (hideal who (Profile.update profile who simulated))
  have hdeviation :=
    hsimulated.meanTestIndistinguishable (hreal who (Profile.map impl.compile profile))
  exact (meanDominancePreference_pure _ _ _ _).mpr
    ((ComputationallyMeanDominates.congr_right hdeviation).mpr
      ((ComputationallyMeanDominates.congr_left hhonest).mpr hdominates))

/-- Statistically simulated utilities need no efficiency assumption: the tests
seeing polynomially many draws contain every mean comparison. Negligible
statistical distance supplies such a certificate
(`indistinguishableBy_polySampleTests_of_statisticalDistance`). -/
theorem SecureImplementation.isPseudoNash_of_statistical [DecidableEq ι]
    {ideal real : ParameterizedGame.{uι, us, uo} ι}
    (impl : SecureImplementation (polySampleTests ℝ) ideal real)
    {profile : Profile ideal.sig} (h : ideal.IsPseudoNash profile) :
    real.IsPseudoNash (Profile.map impl.compile profile) :=
  impl.isPseudoNash (fun _ _ => containsMeanTests_polySampleTests _)
    (fun _ _ => containsMeanTests_polySampleTests _) h

end GameTheory
