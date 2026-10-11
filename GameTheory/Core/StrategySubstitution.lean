/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

import GameTheory.Core.Form

/-! # Independent stochastic strategy substitution

Each new strategy selects a law over the original strategies. Independent
sampling of these laws then uses the original game form's play law. Mixed
substitution flattens to independent mixtures of the strategy kernels, and
one-coordinate replacement commutes with this flattening. The construction
stores no utility, equilibrium predicate or translation certificate.
-/

noncomputable section
namespace GameTheory.GameForm
open GameTheory.Math.Probability
variable {ι : Type*} [Fintype ι] (F : GameForm ι) {Strategy : ι → Type*}

/-- Substitute a stochastic strategy kernel independently at each coordinate. -/
abbrev substituteStrategies (kernel : ∀ who, Strategy who → PMF (F.sig.Strategy who)) : GameForm ι
  where
  sig := { Strategy := Strategy, Outcome := F.sig.Outcome }
  play choice := F.mixed.play fun who => kernel who (choice who)

/-- Mixing substituted strategies flattens to mixing the original strategy laws. -/
theorem substituteStrategies_mixed_play
    (kernel : ∀ who, Strategy who → PMF (F.sig.Strategy who))
    (weights : ∀ who, PMF (Strategy who)) :
    (F.substituteStrategies kernel).mixed.play weights =
      F.mixed.play fun who => (weights who).bind (kernel who) := by
  change (independentProduct weights).bind
      (fun choice => (independentProduct fun who => kernel who (choice who)).bind F.play) =
    (independentProduct fun who => (weights who).bind (kernel who)).bind F.play
  rw [← PMF.bind_bind, independentProduct_bind]

/-- Flattening stochastic substitution respects the canonical coordinate update. -/
theorem substituteStrategies_update [DecidableEq ι]
    (kernel : ∀ who, Strategy who → PMF (F.sig.Strategy who))
    (weights : ∀ who, PMF (Strategy who)) (who : ι) (alternative : PMF (Strategy who)) :
    (fun player => (Profile.update (sig := (F.substituteStrategies kernel).sig.mixed)
      weights who alternative player).bind (kernel player)) =
      Profile.update (sig := F.sig.mixed) (fun player => (weights player).bind (kernel player))
        who (alternative.bind (kernel who)) := by
  funext player
  by_cases same : player = who
  · subst player
    simp only [Profile.update_same]
  · simp only [Profile.update_of_ne _ _ same]

end GameTheory.GameForm
