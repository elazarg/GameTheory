/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Repeated.MonitoringInstances

/-!
# Tests for Repeated Games with Public Monitoring

Small checked examples exercise stochastic signal-history generation,
stationary payoffs, realized-action monitoring, and the general stationary-Nash
uniform-equilibrium theorem.
-/

noncomputable section

namespace GameTheory

namespace RepeatedMonitoringTests

open KernelGame

/-- A two-player coordination game whose outcome records the pure profile. -/
abbrev coordinationGame : KernelGame Bool :=
  { Strategy := fun _ => Bool
    Outcome := Bool → Bool
    utility := fun σ _ => if σ false = σ true then 1 else 0
    outcomeKernel := PMF.pure }

/-- The coordinated all-`true` action profile. -/
abbrev allTrueProfile : Profile coordinationGame :=
  fun _ => true

theorem allTrueProfile_isNash : coordinationGame.IsNash allTrueProfile := by
  intro who dev
  simp only [KernelGame.eu, Math.Probability.expect_pure]
  cases who <;> cases dev <;>
    norm_num [allTrueProfile, Function.update]

/-- Outcome monitoring of the deterministic coordination game generates the
expected one-period Dirac history. -/
example :
    coordinationGame.outcomeMonitoring.signalHistoryDist
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile allTrueProfile) 1 =
      PMF.pure (fun _ : Fin 1 => allTrueProfile) := by
  rw [PublicMonitoring.signalHistoryDist_succ,
    PublicMonitoring.signalHistoryDist_zero]
  simp only [PMF.pure_bind]
  change PMF.map
    (Fin.snoc (α := fun _ => Profile coordinationGame)
      (fun k : Fin 0 => k.elim0))
      (PMF.pure allTrueProfile) = _
  simp only [PMF.map]
  rw [PMF.pure_bind]
  apply congrArg PMF.pure
  funext k
  refine Fin.lastCases ?_ (fun j => Fin.elim0 j) k
  rw [Fin.snoc_last]

/-- Stationary monitored payoff evaluation is independent of the realized
signal history. -/
example (t : ℕ) :
    coordinationGame.outcomeMonitoring.stageEU
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile allTrueProfile)
        t false = 1 := by
  rw [PublicMonitoring.stageEU_stationaryMonitoredProfile]
  simp [KernelGame.eu, allTrueProfile]

/-- The checked stage Nash profile gives a monitored uniform equilibrium. -/
example :
    coordinationGame.outcomeMonitoring.IsUniformEquilibrium
      (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile allTrueProfile) :=
  by
    letI : Finite coordinationGame.Outcome := by
      change Finite (Bool → Bool)
      infer_instance
    exact PublicMonitoring.stationaryMonitoredProfile_isUniformEquilibrium_of_isNash
      (M := coordinationGame.outcomeMonitoring) allTrueProfile_isNash

/-- Dirac mixed actions expose the corresponding pure action profile under
realized-action monitoring. -/
example :
    coordinationGame.realizedActionMonitoring.signalKernel
        (fun i => (PMF.pure (allTrueProfile i) : PMF Bool)) =
      PMF.pure allTrueProfile := by
  exact coordinationGame.realizedActionMonitoring_signalKernel_pure allTrueProfile

/-- The general behavioral lift preserves the original signal law on Dirac
mixed actions. -/
example :
    coordinationGame.outcomeMonitoring.mixedExtension.signalKernel
        (coordinationGame.pureMixedProfile allTrueProfile) =
      coordinationGame.outcomeMonitoring.signalKernel allTrueProfile := by
  exact coordinationGame.outcomeMonitoring.mixedExtension_signalKernel_pure
    allTrueProfile

/-- Lifting observable pure profiles agrees with the dedicated
realized-action monitoring instance. -/
example (σ : Profile coordinationGame.mixedExtension) :
    coordinationGame.profileMonitoring.mixedExtension.signalKernel σ =
      coordinationGame.realizedActionMonitoring.signalKernel σ := by
  exact coordinationGame.profileMonitoring_mixedExtension_signalKernel σ

end RepeatedMonitoringTests

end GameTheory
