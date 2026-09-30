/-
# Pseudo-correlated equilibrium

A correlation device for a parameterized game recommends a strategy profile at
each size. The device belongs inside the game, as an ideal functionality: the
mediated family draws the recommendation at size `κ` inside play at size `κ`,
and each player applies a response to its own recommendation. Obedience being
pseudo-Nash there is pseudo-correlated equilibrium.

Reading the device instead as one law over profiles of the ensemble form would
couple the sizes, and correlated equilibrium of the ensemble form depends on
that coupling: a recommendation at one size can reveal another player's
recommendation at another size. The mediated family never shows a
recommendation outside its own size, so no coupling has to be chosen.

In a fixed game with bounded utilities a constant device is a pseudo-correlated
equilibrium exactly when it is a correlated equilibrium, since obedience in a
mediated extension is correlated equilibrium for every preference. A secure
implementation of the mediated family, replacing the mediator by a protocol,
turns a pseudo-correlated equilibrium into a pseudo-Nash equilibrium of the
protocol game.
-/
import GameTheory.Analysis.CorrelationHierarchy
import GameTheory.Analysis.PseudoNash

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι} [DecidableEq ι]

/-- The mediated family: at each size the device draws a recommendation
profile inside play, and each player applies its response to its own
recommendation. A recommendation drawn at one size is never seen at another. -/
@[reducible]
def ParameterizedGame.mediated (G : ParameterizedGame.{uι, us, uo} ι)
    (device : ℕ → PMF (Profile G.sig)) : ParameterizedGame ι where
  sig := { Strategy := fun who => G.sig.Strategy who → G.sig.Strategy who
           Outcome := G.sig.Outcome }
  play κ responses := (device κ).bind fun recommended =>
    G.play κ fun who => responses who (recommended who)
  utility := G.utility

/-- Every player obeys its recommendation. -/
def ParameterizedGame.obedient (G : ParameterizedGame.{uι, us, uo} ι)
    (device : ℕ → PMF (Profile G.sig)) : Profile (G.mediated device).sig :=
  fun _ => id

/-- Pseudo-correlated equilibrium: obedience is pseudo-Nash in the mediated
family. -/
def ParameterizedGame.IsPseudoCorrelatedEq (G : ParameterizedGame.{uι, us, uo} ι)
    (device : ℕ → PMF (Profile G.sig)) : Prop :=
  (G.mediated device).IsPseudoNash (G.obedient device)

/-- **Pseudo-correlated equilibrium is correlated equilibrium** in a fixed game
with bounded utilities and a constant device. -/
theorem ParameterizedGame.isPseudoCorrelatedEq_constant_iff (F : GameForm.{uι, us, uo} ι)
    (utility : F.sig.Outcome → ι → ℝ)
    (hbounded : ∀ who, ∃ C, ∀ outcome, |utility outcome who| ≤ C)
    (device : PMF (Profile F.sig)) :
    (ParameterizedGame.constant F utility).IsPseudoCorrelatedEq (fun _ => device) ↔
      IsCorrelatedEq F (euPreference utility) device :=
  (ParameterizedGame.isPseudoNash_constant_iff_isNash (F.mediated device) utility hbounded
    (F.obedient device)).trans (F.isNash_mediated_obedient_iff (euPreference utility) device)

/-- **Replacing the mediator by a protocol.** A secure implementation of the
mediated family compiles a pseudo-correlated equilibrium into a pseudo-Nash
equilibrium of the protocol game, provided the tests can compare empirical
means with both games' utility ensembles. -/
theorem ParameterizedGame.IsPseudoCorrelatedEq.compile {tests : Set (SampleTest ℝ)}
    {G : ParameterizedGame.{uι, us, uo} ι} {device : ℕ → PMF (Profile G.sig)}
    {real : ParameterizedGame.{uι, us, uo} ι}
    (impl : SecureImplementation tests (G.mediated device) real)
    (hreal : ∀ who profile, ContainsMeanTests tests (real.utilityLaw who profile))
    (hideal : ∀ who profile, ContainsMeanTests tests ((G.mediated device).utilityLaw who profile))
    (h : G.IsPseudoCorrelatedEq device) :
    real.IsPseudoNash (Profile.map impl.compile (G.obedient device)) :=
  impl.isPseudoNash hreal hideal h

end GameTheory
