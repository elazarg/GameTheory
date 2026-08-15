/-
# Uniform equilibrium in stochastic games

Uniformity quantifies one behavioral profile over all sufficiently long finite
horizons. It needs neither an infinite-path law nor a new equilibrium engine.
The payoff-level property may choose a new profile for each accuracy, unlike
`UtilityGame.IsUniformEquilibrium`, which is a property of one repeated
profile. No general existence theorem is claimed here.
-/

import GameTheory.Stochastic.FiniteHorizon
import GameTheory.Core.Approximate
import GameTheory.Math.Eventually

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

/-- Finite-horizon approximate Nash is monotone in its error allowance. -/
theorem IsεHorizonNash.mono [DecidableEq ι] {initial : G.State}
    [∀ i, Nonempty (G.Action i)] {horizon : ℕ} {epsilon epsilon' : ℝ}
    {profile : G.BehaviorProfile initial}
    (h : G.IsεHorizonNash initial horizon epsilon profile)
    (hepsilon : epsilon ≤ epsilon') :
    G.IsεHorizonNash initial horizon epsilon' profile := by
  exact IsεNash.mono (F := G.horizonForm initial horizon)
    (utility := G.horizonUtility initial horizon) h hepsilon

/-- One profile is epsilon-Nash at every sufficiently long finite horizon. -/
abbrev IsUniformεEquilibrium [DecidableEq ι] (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (epsilon : ℝ)
    (profile : G.BehaviorProfile initial) : Prop :=
  GameTheory.Math.EventuallyAtAll fun horizon =>
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
    G.IsUniformεEquilibrium initial epsilon' profile :=
  GameTheory.Math.EventuallyAtAll.mono h fun horizon hhorizon =>
    IsεNash.mono (F := G.horizonForm initial horizon)
      (utility := G.horizonUtility initial horizon)
      hhorizon hepsilon

/-- A proof-facing certificate for a uniform equilibrium payoff. At every
positive accuracy it supplies one profile whose on-path payoff is close to the
claimed value and whose unilateral deviations are capped by that value. -/
def HasUniformDeviationCapConstructor [DecidableEq ι] (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (value : ι → ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∃ (profile : G.BehaviorProfile initial) (threshold : ℕ),
      ∀ horizon, threshold ≤ horizon →
        (∀ who,
          |G.finiteAveragePayoff initial horizon profile who - value who| ≤ delta) ∧
        ∀ who (deviation : (G.perfectMonitoring initial).BehavioralPolicy who),
          G.finiteAveragePayoff initial horizon
              (Profile.update profile who deviation) who ≤ value who + delta

/-- A uniform deviation-cap constructor yields the semantic uniform-payoff
property. -/
theorem isUniformEquilibriumPayoff_of_deviation_caps [DecidableEq ι]
    (initial : G.State) [∀ i, Nonempty (G.Action i)] (value : ι → ℝ)
    (hcertificate : G.HasUniformDeviationCapConstructor initial value) :
    G.IsUniformEquilibriumPayoff initial value := by
  intro epsilon hepsilon
  have hdelta : 0 < epsilon / 2 := by linarith
  obtain ⟨profile, threshold, hprofile⟩ := hcertificate (epsilon / 2) hdelta
  refine ⟨profile, threshold, fun horizon hhorizon => ?_⟩
  obtain ⟨honPath, hdeviation⟩ := hprofile horizon hhorizon
  constructor
  · rw [G.isεHorizonNash_iff]
    intro who deviation
    have hlower := (abs_le.mp (honPath who)).1
    have hupper := hdeviation who deviation
    linarith
  · intro who
    exact (honPath who).trans (by linarith)

/-- The deviation-cap constructor is equivalent to the semantic uniform
equilibrium-payoff property. -/
theorem hasUniformDeviationCapConstructor_iff [DecidableEq ι]
    (initial : G.State) [∀ i, Nonempty (G.Action i)] (value : ι → ℝ) :
    G.HasUniformDeviationCapConstructor initial value ↔
      G.IsUniformEquilibriumPayoff initial value := by
  constructor
  · exact G.isUniformEquilibriumPayoff_of_deviation_caps initial value
  · intro hpayoff delta hdelta
    have hhalf : 0 < delta / 2 := by linarith
    obtain ⟨profile, threshold, hprofile⟩ := hpayoff (delta / 2) hhalf
    refine ⟨profile, threshold, fun horizon hhorizon => ?_⟩
    obtain ⟨hnash, honPath⟩ := hprofile horizon hhorizon
    constructor
    · intro who
      exact (honPath who).trans (by linarith)
    · intro who deviation
      have hdeviation := (G.isεHorizonNash_iff initial horizon (delta / 2) profile).mp
        hnash who deviation
      have honUpper := (abs_le.mp (honPath who)).2
      linarith

end Game

end GameTheory.Stochastic
