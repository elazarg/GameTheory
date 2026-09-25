/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.MixtureSimulation

/-! # Composition of PMF-mixture game-form simulations -/

noncomputable section

namespace GameTheory.GameForm.MixtureSimulationOn

open GameTheory.Math.Probability

universe uι us um ut uo umo uto uv

variable {Player : Type uι} [DecidableEq Player]
variable {source : GameForm.{uι, us, uo} Player}
variable {middle : GameForm.{uι, um, umo} Player}
variable {target : GameForm.{uι, ut, uto} Player}
variable {Observation : Type uv}
variable {sourceObserve : source.sig.Outcome → Observation}
variable {middleObserve : middle.sig.Outcome → Observation}
variable {targetObserve : target.sig.Outcome → Observation}
variable {LeftConsidered : (who : Player) → middle.sig.Strategy who → Prop}
variable {RightConsidered : (who : Player) → target.sig.Strategy who → Prop}

/-- Compose when the particular middle-deviation mixture used by the right
simulation is supported on deviations considered by the left simulation.
Compatibility is required only at profiles compiled from the source. -/
def transOn
    (left : MixtureSimulationOn source middle sourceObserve middleObserve LeftConsidered)
    (right : MixtureSimulationOn middle target middleObserve targetObserve RightConsidered)
    (compatible : ∀ (profile : Profile source.sig) who replacement,
      RightConsidered who replacement →
      ∃ alternatives : PMF (middle.sig.Strategy who),
        (target.play (Profile.update (right.compileProfile (left.compileProfile profile))
            who replacement)).map
            targetObserve =
          (alternatives.bind fun alternative =>
            (middle.play (Profile.update (left.compileProfile profile) who alternative)).map
              middleObserve) ∧
        ∀ alternative ∈ alternatives.support, LeftConsidered who alternative) :
    MixtureSimulationOn source target sourceObserve targetObserve RightConsidered where
  compileStrategy who strategy :=
    right.compileStrategy who (left.compileStrategy who strategy)
  honest_law profile := by
    exact (right.honest_law (left.compileProfile profile)).trans (left.honest_law profile)
  compiled_considered who strategy :=
    right.compiled_considered who (left.compileStrategy who strategy)
  deviation_mixture profile who replacement hreplacement := by
    classical
    obtain ⟨middleAlternatives, hright, hsupported⟩ :=
      compatible profile who replacement hreplacement
    let sourceAlternatives : middle.sig.Strategy who → PMF (source.sig.Strategy who) :=
      fun alternative =>
        if h : LeftConsidered who alternative then
          Classical.choose (left.deviation_mixture profile who alternative h)
        else PMF.pure (profile who)
    refine ⟨middleAlternatives.bind sourceAlternatives, ?_⟩
    have hcompose : Profile.map
        (fun who strategy => right.compileStrategy who (left.compileStrategy who strategy))
        profile = right.compileProfile (left.compileProfile profile) := by
      funext player
      rfl
    rw [hcompose, hright, PMF.bind_bind]
    apply bind_congr_on_support middleAlternatives
    intro alternative halternative
    have hconsidered := hsupported alternative halternative
    have hlaw := Classical.choose_spec
      (left.deviation_mixture profile who alternative hconsidered)
    simpa only [sourceAlternatives, dite_eq_left hconsidered,
      MixtureSimulationOn.compileProfile] using hlaw

/-- Composition when every middle strategy is considered by the left
simulation. Any deviation mixture supplied by the right simulation can then
be used directly. -/
def trans
    (left : MixtureSimulationOn source middle sourceObserve middleObserve LeftConsidered)
    (right : MixtureSimulationOn middle target middleObserve targetObserve RightConsidered)
    (leftTotal : ∀ who strategy, LeftConsidered who strategy) :
    MixtureSimulationOn source target sourceObserve targetObserve RightConsidered :=
  left.transOn right fun profile who replacement hreplacement => by
    obtain ⟨alternatives, hlaw⟩ :=
      right.deviation_mixture (left.compileProfile profile) who replacement hreplacement
    exact ⟨alternatives, hlaw, fun alternative _ => leftTotal who alternative⟩

end GameTheory.GameForm.MixtureSimulationOn
