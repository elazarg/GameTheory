/-
# Uniform equilibrium in stochastic games

Uniformity quantifies one behavioral profile over all sufficiently long finite
horizons. It needs neither an infinite-path law nor a new equilibrium engine.
No general existence theorem is claimed here.
-/

import GameTheory.Stochastic.FiniteHorizon
import GameTheory.Core.Approximate

noncomputable section

namespace GameTheory.Stochastic

universe uι us ua

namespace Game

variable {ι : Type uι} (G : Game.{uι, us, ua} ι) [Fintype ι]

/-- Epsilon-Nash of a horizon is canonical approximate Nash on the compiled
behavioral form. -/
abbrev IsεHorizonNash [DecidableEq ι] (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (horizon : ℕ) (epsilon : ℝ)
    (profile : G.BehaviorProfile initial) : Prop :=
  IsεNash (G.horizonForm initial horizon) (G.horizonUtility initial horizon)
    epsilon profile

/-- The source-shaped deviation inequality is exactly canonical approximate
Nash on the Protocol horizon form. -/
theorem isεHorizonNash_iff [DecidableEq ι] (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (horizon : ℕ) (epsilon : ℝ)
    (profile : G.BehaviorProfile initial) :
    G.IsεHorizonNash initial horizon epsilon profile ↔
      ∀ who (deviation : (G.perfectMonitoring initial).BehavioralPolicy who),
        G.finiteAveragePayoff initial horizon
              (Profile.update profile who deviation) who ≤
          G.finiteAveragePayoff initial horizon profile who + epsilon := by
  exact isεNash_iff (F := G.horizonForm initial horizon)
    (utility := G.horizonUtility initial horizon)

/-- One profile is epsilon-Nash at every sufficiently long finite horizon. -/
def IsUniformεEquilibrium [DecidableEq ι] (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (epsilon : ℝ)
    (profile : G.BehaviorProfile initial) : Prop :=
  ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
    G.IsεHorizonNash initial horizon epsilon profile

/-- A uniform equilibrium payoff is approximated by one long-horizon
epsilon-equilibrium profile at each positive accuracy. -/
def IsUniformEquilibriumPayoff [DecidableEq ι] (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (value : ι → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ (profile : G.BehaviorProfile initial) (threshold : ℕ),
      ∀ horizon, threshold ≤ horizon →
        G.IsεHorizonNash initial horizon epsilon profile ∧
          ∀ who,
            |G.finiteAveragePayoff initial horizon profile who - value who| ≤ epsilon

theorem IsUniformεEquilibrium.mono [DecidableEq ι] {initial : G.State}
    [∀ i, Nonempty (G.Action i)] {epsilon epsilon' : ℝ}
    {profile : G.BehaviorProfile initial}
    (h : G.IsUniformεEquilibrium initial epsilon profile)
    (hepsilon : epsilon ≤ epsilon') :
    G.IsUniformεEquilibrium initial epsilon' profile := by
  obtain ⟨threshold, hthreshold⟩ := h
  exact ⟨threshold, fun horizon hhorizon =>
    IsεNash.mono (F := G.horizonForm initial horizon)
      (utility := G.horizonUtility initial horizon)
      (hthreshold horizon hhorizon) hepsilon⟩

end Game

end GameTheory.Stochastic
