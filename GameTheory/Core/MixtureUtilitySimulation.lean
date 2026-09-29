/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.MixtureSimulation
import GameTheory.Core.UtilitySimulation

/-! # From PMF-mixture laws to unilateral utility coverage -/

noncomputable section

namespace GameTheory.GameForm

open GameTheory.Math.Probability

universe uPlayer uSource uTarget uSourceOutcome uTargetOutcome

variable {Player : Type uPlayer} [DecidableEq Player]

/-- An integrable PMF-mixture simulation supplies a one-player utility
certificate for any chosen utility on the common observation. One supported
source deviation has at least the mixture mean. -/
def MixtureSimulationOn.toUtilitySimulation
    {source : GameForm.{uPlayer, uSource, uSourceOutcome} Player}
    {target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player}
    {Observation : Type*} {sourceObserve : source.sig.Outcome → Observation}
    {targetObserve : target.sig.Outcome → Observation}
    {Considered : (who : Player) → target.sig.Strategy who → Prop}
    (simulation : MixtureSimulationOn source target sourceObserve targetObserve Considered)
    (utility : Observation → Player → ℝ)
    (hall : ∀ who strategy, Considered who strategy)
    (hdev : ∀ profile who replacement,
      UtilityIntegrable (fun outcome player => utility (targetObserve outcome) player)
        who (target.play (Profile.update
          (simulation.compileProfile profile) who replacement))) :
    UtilitySimulation source target
      (fun outcome who => utility (sourceObserve outcome) who)
      (fun outcome who => utility (targetObserve outcome) who)
      (singletonGroups Player) :=
  UtilitySimulation.ofUnilateral simulation.compileStrategy
    (fun profile who => simulation.integrable_compile_iff profile
      (fun observation => utility observation who))
    (fun profile who _ _ =>
      simulation.expect_compile profile (fun observation => utility observation who))
    (by
      intro profile who replacement
      let value : Observation → ℝ := fun observation => utility observation who
      let kernel : source.sig.Strategy who → PMF Observation := fun alternative =>
        (source.play (Profile.update profile who alternative)).map sourceObserve
      obtain ⟨alternatives, hlaw⟩ :=
        simulation.deviation_mixture profile who replacement (hall who replacement)
      let htarget := hdev profile who replacement
      have htobs : PayoffIntegrable
          ((target.play (Profile.update
            (simulation.compileProfile profile) who replacement)).map targetObserve)
          value := (payoffIntegrable_map_iff targetObserve _ value).mpr htarget
      have hbind : PayoffIntegrable (alternatives.bind kernel) value := by
        rw [← hlaw]
        exact htobs
      classical
      let g : source.sig.Strategy who → ℝ := fun a =>
        if ha : a ∈ alternatives.support then
          expect (kernel a) value
        else 0
      have hagree : ∀ a, ∀ ha : a ∈ alternatives.support,
          g a = expect (kernel a) value := by
        intro a ha
        have hne : alternatives a ≠ 0 := (alternatives.mem_support_iff a).mp ha
        simp [g, hne]
      let hg := payoffIntegrable_bind_conditionalValue_on_support
        alternatives kernel value hbind g hagree
      obtain ⟨alternative, ha, hmean⟩ :=
        exists_expect_le_support alternatives g hg
      refine ⟨alternative, ?_⟩
      intro hsource
      refine ⟨htarget, ?_⟩
      calc
        expectedUtility (fun outcome player => utility (targetObserve outcome) player) who
            (target.play (Profile.update
              (simulation.compileProfile profile) who replacement)) =
          expect (alternatives.bind kernel) value := by
            exact (expect_map targetObserve _ value).symm.trans
              (expect_congr_law hlaw value)
        _ = expect alternatives g :=
          expect_bind_tower_on_support alternatives kernel value hbind g hagree
        _ ≤ g alternative := hmean
        _ = expect (kernel alternative) value := hagree alternative ha
        _ = expectedUtility
            (fun outcome player => utility (sourceObserve outcome) player) who
            (source.play (Profile.update profile who alternative)) := by
              exact expect_map sourceObserve _ value)

end GameTheory.GameForm
