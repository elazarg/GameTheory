/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.MixtureSimulation
import GameTheory.Core.UtilitySimulation

/-! # From finite-mixture laws to unilateral utility coverage -/

noncomputable section

namespace GameTheory.GameForm

open GameTheory.Math.Probability

universe uPlayer uSource uTarget uSourceOutcome uTargetOutcome

variable {Player : Type uPlayer} [DecidableEq Player]

/-- Exact finite-mixture simulation supplies a one-player utility certificate
for every chosen utility on the common observation. A finite mixture has a
component whose utility is at least its mean, which is why the mixture
certificate is unilateral: a single component need not serve two members of a
coalition at once. -/
def MixtureSimulationOn.toUtilitySimulation
    {source : GameForm.{uPlayer, uSource, uSourceOutcome} Player}
    {target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player}
    {Observation : Type*} {sourceObserve : source.sig.Outcome → Observation}
    {targetObserve : target.sig.Outcome → Observation}
    {Considered : (who : Player) → target.sig.Strategy who → Prop}
    (simulation : MixtureSimulationOn source target sourceObserve targetObserve Considered)
    (utility : Observation → Player → ℝ) (hall : ∀ who strategy, Considered who strategy) :
    UtilitySimulation source target
      (fun outcome who => utility (sourceObserve outcome) who)
      (fun outcome who => utility (targetObserve outcome) who)
      (singletonGroups Player) :=
  UtilitySimulation.ofUnilateral simulation.compileStrategy
    (fun profile who => simulation.expect_compile profile (fun obs => utility obs who))
    (by
      intro profile who replacement
      obtain ⟨alternatives, hlaw⟩ :=
        simulation.deviation_mixture profile who replacement (hall who replacement)
      have hexpect := congrArg (fun law => law.expect (fun obs => utility obs who)) hlaw
      simp only [FinDist.expect_map, FinDist.expect_bind] at hexpect
      obtain ⟨alternative, _, hbound⟩ := FinDist.exists_expect_le_support alternatives
        (fun alternative => (source.play (Profile.update profile who alternative)).expect
          (fun outcome => utility (sourceObserve outcome) who))
      exact ⟨alternative, hexpect.le.trans hbound⟩)

end GameTheory.GameForm
