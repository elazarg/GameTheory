/-
# Pseudo-Nash equilibrium

A pseudo-Nash equilibrium ranks a player's utility against each unilateral
deviation by computational mean dominance instead of by expectation. With any
polynomial number of plays of each profile, no deviation's empirical mean
comes out ahead with non-negligible advantage. Events of negligible
probability, such as guessing a key or opening a commitment to another value,
are invisible to this comparison however large their payoffs.

Games are parameterized by a size `κ`, such as a security parameter. The
strategy carriers are fixed, and play laws and utilities may depend on `κ`. A
fixed game is the constant family. There pseudo-Nash is Nash for
`empiricalMeanPreference`, which for bounded utilities is expected-utility
preference (`GameTheory.Analysis.PseudoNash`).

Replacing an ideal primitive by a secure implementation preserves pseudo-Nash.
A `SecureImplementation` compiles ideal strategies into real ones such that
compiled honest play, and every real deviation from it, is simulated by ideal
play whose utility ensembles a class of tests cannot tell apart from the real
ones. If that class can compare empirical means with the games' utility
ensembles, then compiling an ideal pseudo-Nash equilibrium gives a real
pseudo-Nash equilibrium. With all tests, the requirement is statistical
closeness. With polynomial-time tests, it is the utility-level consequence of
simulation-based security plus efficient sampling of play.

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

/-- The ensemble of a player's realized utility at a profile. -/
def utilityLaw (G : ParameterizedGame ι) (who : ι) (profile : Profile G.sig) : ℕ → PMF ℝ :=
  fun κ => (G.play κ profile).map fun outcome => G.utility κ outcome who

/-- A pseudo-Nash equilibrium: each player's utility ensemble computationally
mean-dominates that of every unilateral replacement. -/
def IsPseudoNash [DecidableEq ι] (G : ParameterizedGame ι) (profile : Profile G.sig) : Prop :=
  ∀ who (replacement : G.sig.Strategy who),
    ComputationallyMeanDominates (G.utilityLaw who profile)
      (G.utilityLaw who (Profile.update profile who replacement))

/-- A fixed game as the constant family. -/
@[reducible]
def constant (F : GameForm ι) (utility : F.sig.Outcome → ι → ℝ) : ParameterizedGame ι where
  sig := F.sig
  play _ := F.play
  utility _ := utility

end ParameterizedGame

/-- A player prefers an outcome law when the constant ensemble of its utility
computationally mean-dominates that of the alternative. -/
def empiricalMeanPreference {Outcome : Type*} (utility : Outcome → ι → ℝ) :
    WeakPreference ι Outcome :=
  fun who preferred alternative =>
    ComputationallyMeanDominates (fun _ => preferred.map fun outcome => utility outcome who)
      (fun _ => alternative.map fun outcome => utility outcome who)

/-- In a fixed game, pseudo-Nash is Nash for the empirical-mean preference. -/
theorem ParameterizedGame.isPseudoNash_constant_iff [DecidableEq ι] (F : GameForm ι)
    (utility : F.sig.Outcome → ι → ℝ) (profile : Profile F.sig) :
    (constant F utility).IsPseudoNash profile ↔
      IsNash F (empiricalMeanPreference utility) profile := by
  rw [isNash_iff]
  rfl

/-! ## Replacing ideal primitives by secure implementations -/

/-- A compilation of an ideal game's strategies into a real game's, simulated
at the level of utility ensembles: compiled honest play is indistinguishable
from ideal honest play, and every real unilateral deviation from compiled play
is indistinguishable from some ideal unilateral deviation. -/
structure SecureImplementation [DecidableEq ι] (tests : Set SampleTest)
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
compare empirical means with the utility ensembles of both games. -/
theorem SecureImplementation.isPseudoNash [DecidableEq ι] {tests : Set SampleTest}
    {ideal real : ParameterizedGame.{uι, us, uo} ι} (impl : SecureImplementation tests ideal real)
    (hreal : ∀ who profile, ContainsMeanTests tests (real.utilityLaw who profile))
    (hideal : ∀ who profile, ContainsMeanTests tests (ideal.utilityLaw who profile))
    {profile : Profile ideal.sig} (h : ideal.IsPseudoNash profile) :
    real.IsPseudoNash (Profile.map impl.compile profile) := by
  intro who deviation
  obtain ⟨simulated, hsimulated⟩ := impl.simulate profile who deviation
  have hhonest := (impl.honest profile who).meanTestIndistinguishable
    (hideal who (Profile.update profile who simulated))
  have hdeviation := hsimulated.meanTestIndistinguishable (hreal who (Profile.map impl.compile profile))
  exact (ComputationallyMeanDominates.congr_right hdeviation).mpr
    ((ComputationallyMeanDominates.congr_left hhonest).mpr (h who simulated))

/-- With statistically close utility ensembles no test needs to be efficient. -/
theorem SecureImplementation.isPseudoNash_of_statistical [DecidableEq ι]
    {ideal real : ParameterizedGame.{uι, us, uo} ι}
    (impl : SecureImplementation Set.univ ideal real)
    {profile : Profile ideal.sig} (h : ideal.IsPseudoNash profile) :
    real.IsPseudoNash (Profile.map impl.compile profile) :=
  impl.isPseudoNash (fun _ _ => containsMeanTests_univ _) (fun _ _ => containsMeanTests_univ _) h

end GameTheory
