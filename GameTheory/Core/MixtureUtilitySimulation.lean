/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.MixtureSimulation
import GameTheory.Core.UtilitySimulation

/-! # From PMF-mixture laws to unilateral utility coverage -/

noncomputable section

namespace GameTheory.GameForm

open GameTheory.Math.Probability

universe uPlayer uSource uTarget uSourceOutcome uTargetOutcome

variable {Player : Type uPlayer} [DecidableEq Player]

namespace MixtureSimulationOn

variable {source : GameForm.{uPlayer, uSource, uSourceOutcome} Player}
  {target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player}
  {Observation : Type*} {sourceObserve : source.sig.Outcome → Observation}
  {targetObserve : target.sig.Outcome → Observation}
  {Considered : (who : Player) → target.sig.Strategy who → Prop}
  (simulation : MixtureSimulationOn source target sourceObserve targetObserve Considered)

/-- A considered target deviation with integrable utility is matched by one
supported source deviation with integrable utility and at least its expected
utility: some supported point of the mixture is at least its mean. -/
theorem exists_source_deviation_ge (utility : Observation → Player → ℝ)
    (profile : Profile source.sig) (who : Player) (replacement : target.sig.Strategy who)
    (considered : Considered who replacement)
    (integrable : UtilityIntegrable (fun outcome player => utility (targetObserve outcome) player)
      who (target.play (Profile.update (simulation.compileProfile profile) who replacement))) :
    ∃ alternative : source.sig.Strategy who,
      UtilityIntegrable (fun outcome player => utility (sourceObserve outcome) player) who
          (source.play (Profile.update profile who alternative)) ∧
        expectedUtility (fun outcome player => utility (targetObserve outcome) player) who
            (target.play (Profile.update (simulation.compileProfile profile) who replacement)) ≤
          expectedUtility (fun outcome player => utility (sourceObserve outcome) player) who
            (source.play (Profile.update profile who alternative)) := by
  classical
  let value : Observation → ℝ := fun observation => utility observation who
  let kernel : source.sig.Strategy who → PMF Observation := fun alternative =>
    (source.play (Profile.update profile who alternative)).map sourceObserve
  obtain ⟨alternatives, hlaw⟩ := simulation.deviation_mixture profile who replacement considered
  have hbind : PayoffIntegrable (alternatives.bind kernel) value := by
    rw [← hlaw]
    exact (payoffIntegrable_map_iff targetObserve _ value).mpr integrable
  let g : source.sig.Strategy who → ℝ := fun a =>
    if a ∈ alternatives.support then expect (kernel a) value else 0
  have hagree : ∀ a, ∀ _ : a ∈ alternatives.support, g a = expect (kernel a) value := by
    intro a ha
    simp only [g, ha, ↓reduceIte]
  have hg := payoffIntegrable_bind_conditionalValue_on_support alternatives kernel value hbind g
    hagree
  obtain ⟨alternative, ha, hmean⟩ := exists_expect_le_support alternatives g hg
  refine ⟨alternative, (payoffIntegrable_map_iff sourceObserve _ value).mp
    (payoffIntegrable_bind_conditional_on_support alternatives kernel value hbind
      alternative ha), ?_⟩
  calc
    expectedUtility (fun outcome player => utility (targetObserve outcome) player) who
        (target.play (Profile.update (simulation.compileProfile profile) who replacement)) =
      expect (alternatives.bind kernel) value :=
        (expect_map targetObserve _ value).symm.trans (expect_congr_law hlaw value)
    _ = expect alternatives g :=
      expect_bind_tower_on_support alternatives kernel value hbind g hagree
    _ ≤ g alternative := hmean
    _ = expect (kernel alternative) value := hagree alternative ha
    _ = expectedUtility (fun outcome player => utility (sourceObserve outcome) player) who
        (source.play (Profile.update profile who alternative)) :=
      expect_map sourceObserve _ value

/-- **Best responses compile against the considered class.** A source best
response of one player remains a best response of the compiled profile against
every considered target deviation with integrable utility. Only that player's
source incentives are used; the other players need not respond optimally. -/
theorem compileStrategy_ge_considered (utility : Observation → Player → ℝ)
    (profile : Profile source.sig) (who : Player)
    (best : IsBestResponse source
      (euPreference fun outcome player => utility (sourceObserve outcome) player) who profile
      (profile who))
    (replacement : target.sig.Strategy who) (considered : Considered who replacement)
    (integrable : UtilityIntegrable (fun outcome player => utility (targetObserve outcome) player)
      who (target.play (Profile.update (simulation.compileProfile profile) who replacement)))
    (baseline : UtilityIntegrable (fun outcome player => utility (sourceObserve outcome) player)
      who (source.play profile)) :
    euPreference (fun outcome player => utility (targetObserve outcome) player) who
      (target.play (simulation.compileProfile profile))
      (target.play (Profile.update (simulation.compileProfile profile) who replacement)) := by
  obtain ⟨alternative, halternative, bound⟩ :=
    simulation.exists_source_deviation_ge utility profile who replacement considered integrable
  have hbest := best alternative
  rw [Profile.update_eq_self] at hbest
  have hsource := (euPreference_iff _ _ _ _ baseline halternative).mp hbest
  refine (euPreference_iff _ _ _ _ ((simulation.integrable_compile_iff profile
    (fun observation => utility observation who)).mpr baseline) integrable).mpr ?_
  have honest := simulation.expect_compile profile (fun observation => utility observation who)
  exact bound.trans (hsource.trans_eq honest.symm)

end MixtureSimulationOn

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
    (fun profile who => hasExpectation_observed_law_iff _ _ targetObserve sourceObserve
      (fun observation => utility observation who) (simulation.honest_law profile))
    (fun profile who _ _ => extendedExpect_observed_law_eq _ _ targetObserve sourceObserve
      (fun observation => utility observation who) (simulation.honest_law profile))
    (by
      intro profile who replacement
      have htarget := hdev profile who replacement
      obtain ⟨alternative, hsource, hbound⟩ := simulation.exists_source_deviation_ge utility
        profile who replacement (hall who replacement) htarget
      exact ⟨alternative, fun _ => ⟨htarget.hasExpectation,
        (extendedExpectedUtility_eq htarget).le.trans ((EReal.coe_le_coe_iff.2 hbound).trans
          (extendedExpectedUtility_eq hsource).ge)⟩⟩)

end GameTheory.GameForm
