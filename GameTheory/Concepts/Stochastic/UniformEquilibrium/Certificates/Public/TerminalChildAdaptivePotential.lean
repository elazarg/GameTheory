/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Adaptive.PotentialSystem
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.TerminalChildLawTransfer

/-!
# Adaptive potential systems under terminal child dispatch

Expectation-level adaptive potential systems are insensitive to changes of a
behavior profile outside histories genuinely rooted at their entry state.
This file transports the named system along that agreement and specializes
the result to canonical terminal-child dispatch.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}

namespace AdaptivePotentialSystemAt

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]
  {left right : G.BehaviorProfile}
  {initial : G.State} {target : Payoff ι} {error : ℝ}

/-- Transport an adaptive potential system across behavior profiles that
agree on every history genuinely rooted at the entry state.

All potentials and scalar charge sequences are reused verbatim. -/
def transportOfProfilesAgreeOnStartsAt
    (system : G.AdaptivePotentialSystemAt left initial target error)
    (hagree : ProfilesAgreeOnStartsAt left right initial) :
    G.AdaptivePotentialSystemAt right initial target error where
  horizon := system.horizon
  lowerPotential := system.lowerPotential
  upperPotential := system.upperPotential
  deviationPotential := system.deviationPotential
  lowerCharge := system.lowerCharge
  upperCharge := system.upperCharge
  deviationCharge := system.deviationCharge
  horizon_ge_two := system.horizon_ge_two
  lower_initial := system.lower_initial
  upper_initial := system.upper_initial
  deviation_initial := system.deviation_initial
  lower_submartingale := by
    intro who time
    have current_eq :=
      G.expectedHistoryValue_eq_of_profilesAgreeOnStartsAt
        hagree (system.lowerPotential who) time
    have next_eq :=
      G.expectedHistoryValue_eq_of_profilesAgreeOnStartsAt
        hagree (system.lowerPotential who) (time + 1)
    rw [← current_eq, ← next_eq]
    exact system.lower_submartingale who time
  lower_stage := by
    intro who time
    have potential_eq :=
      G.expectedHistoryValue_eq_of_profilesAgreeOnStartsAt
        hagree (system.lowerPotential who) time
    have payoff_eq :=
      G.expectedStagePayoff_eq_of_profilesAgreeOnStartsAt
        hagree time who
    rw [← potential_eq, ← payoff_eq]
    exact system.lower_stage who time
  upper_supermartingale := by
    intro who time
    have current_eq :=
      G.expectedHistoryValue_eq_of_profilesAgreeOnStartsAt
        hagree (system.upperPotential who) time
    have next_eq :=
      G.expectedHistoryValue_eq_of_profilesAgreeOnStartsAt
        hagree (system.upperPotential who) (time + 1)
    rw [← current_eq, ← next_eq]
    exact system.upper_supermartingale who time
  upper_stage := by
    intro who time
    have potential_eq :=
      G.expectedHistoryValue_eq_of_profilesAgreeOnStartsAt
        hagree (system.upperPotential who) time
    have payoff_eq :=
      G.expectedStagePayoff_eq_of_profilesAgreeOnStartsAt
        hagree time who
    rw [← potential_eq, ← payoff_eq]
    exact system.upper_stage who time
  deviation_supermartingale := by
    intro who deviation time
    have updated_agreement := hagree.update who deviation
    have current_eq :=
      G.expectedHistoryValue_eq_of_profilesAgreeOnStartsAt
        updated_agreement (system.deviationPotential who) time
    have next_eq :=
      G.expectedHistoryValue_eq_of_profilesAgreeOnStartsAt
        updated_agreement (system.deviationPotential who) (time + 1)
    rw [← current_eq, ← next_eq]
    exact system.deviation_supermartingale who deviation time
  deviation_stage := by
    intro who deviation time
    have updated_agreement := hagree.update who deviation
    have potential_eq :=
      G.expectedHistoryValue_eq_of_profilesAgreeOnStartsAt
        updated_agreement (system.deviationPotential who) time
    have payoff_eq :=
      G.expectedStagePayoff_eq_of_profilesAgreeOnStartsAt
        updated_agreement time who
    rw [← potential_eq, ← payoff_eq]
    exact system.deviation_stage who deviation time
  lower_charge_cesaro := system.lower_charge_cesaro
  upper_charge_cesaro := system.upper_charge_cesaro
  deviation_charge_cesaro := system.deviation_charge_cesaro

/-- A raw child adaptive potential system becomes a system for its canonical
globally dispatched child profile. -/
def canonicalTerminalChildProfile
    (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel)
    (system :
      G.AdaptivePotentialSystemAt
        (child base) base.2 target error) :
    G.AdaptivePotentialSystemAt
      (G.canonicalTerminalChildProfile fuel selection child base)
      base.2 target error :=
  system.transportOfProfilesAgreeOnStartsAt
    (G.profilesAgreeOnStartsAt_canonicalTerminalChildProfile
      fuel selection child base).symm

end AdaptivePotentialSystemAt

end StochasticGame
end GameTheory
