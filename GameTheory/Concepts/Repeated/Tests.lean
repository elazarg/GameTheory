/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Repeated.MonitoringPublicDraw

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
open KernelGame.PublicMonitoring
open KernelGame.PublicMonitoring.SelfGenerating

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

/-- Stationary monitored play remains stationary after every public history,
including histories that have zero probability. -/
example {t : ℕ}
    (h : coordinationGame.outcomeMonitoring.SignalHistory t) (n : ℕ) :
    coordinationGame.outcomeMonitoring.stageEU
        (coordinationGame.outcomeMonitoring.after
          (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
            allTrueProfile) h)
        n false = 1 := by
  rw [PublicMonitoring.after_stationaryMonitoredProfile,
    PublicMonitoring.stageEU_stationaryMonitoredProfile]
  simp [KernelGame.eu, allTrueProfile]

/-- One-signal and arbitrary-history continuation compose without dependent
index casts. -/
example (σ : coordinationGame.outcomeMonitoring.MonitoredProfile)
    {t : ℕ} (h : coordinationGame.outcomeMonitoring.SignalHistory t)
    (y : coordinationGame.outcomeMonitoring.Signal) :
    coordinationGame.outcomeMonitoring.afterSignal
        (coordinationGame.outcomeMonitoring.after σ h) y =
      coordinationGame.outcomeMonitoring.after σ (Fin.snoc h y) :=
  coordinationGame.outcomeMonitoring.afterSignal_after σ h y

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

/-- Stationary monitored play has its stage payoff under normalized
discounting. -/
example :
    coordinationGame.outcomeMonitoring.discountedAveragePayoff (1 / 2)
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
          allTrueProfile) false = 1 := by
  rw [coordinationGame.outcomeMonitoring.discountedAveragePayoff_stationaryMonitoredProfile
    (δ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)]
  simp [KernelGame.eu, allTrueProfile]

/-- The coordination equilibrium is sequentially rational after every public
history under discounted outcome monitoring. -/
example :
    coordinationGame.outcomeMonitoring.IsPerfectPublicEquilibrium (1 / 2)
      (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
        allTrueProfile) := by
  letI : Finite coordinationGame.Outcome := by
    change Finite (Bool → Bool)
    infer_instance
  exact PublicMonitoring.stationaryMonitoredProfile_isPerfectPublicEquilibrium_of_isNash
    coordinationGame.outcomeMonitoring (by norm_num) (by norm_num)
      allTrueProfile_isNash

/-- The one-shot-deviation test is equivalent to PPE in the finite-outcome
coordination example. -/
example :
    coordinationGame.outcomeMonitoring.IsPerfectPublicEquilibrium (1 / 2)
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
          allTrueProfile) ↔
      coordinationGame.outcomeMonitoring.HasNoProfitableOneShotDeviationAfterEveryHistory
        (1 / 2)
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
          allTrueProfile) := by
  letI : Finite coordinationGame.Outcome := by
    change Finite (Bool → Bool)
    infer_instance
  exact PublicMonitoring.isPerfectPublicEquilibrium_iff_noProfitableOneShotDeviation
    coordinationGame.outcomeMonitoring (by norm_num) (by norm_num) _

/-- Finiteness is not essential: the bounded-payoff statement exposes the
actual hypothesis used by the one-shot-deviation principle. -/
example :
    coordinationGame.outcomeMonitoring.IsPerfectPublicEquilibrium (1 / 2)
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
          allTrueProfile) ↔
      coordinationGame.outcomeMonitoring.HasNoProfitableOneShotDeviationAfterEveryHistory
        (1 / 2)
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
          allTrueProfile) := by
  apply PublicMonitoring.isPerfectPublicEquilibrium_iff_noProfitableOneShotDeviation_of_bounded
    coordinationGame.outcomeMonitoring (by norm_num) (by norm_num)
  intro who
  refine ⟨1, ?_⟩
  intro ρ
  simp only [coordinationGame, KernelGame.eu,
    Math.Probability.expect_pure]
  split <;> norm_num

/-- A suitably scaled local one-shot allowance gives the requested global PPE
allowance. -/
example {ε : ℝ} (hε : 0 ≤ ε)
    (h : PublicMonitoring.HasNoProfitableOneShotDeviationWithinAfterEveryHistory
      coordinationGame.outcomeMonitoring (1 / 2) ((1 - 1 / 2) * ε)
      (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
        allTrueProfile)) :
    coordinationGame.outcomeMonitoring.IsεPerfectPublicEquilibrium
      (1 / 2) ε
      (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
        allTrueProfile) := by
  letI : Finite coordinationGame.Outcome := by
    change Finite (Bool → Bool)
    infer_instance
  exact h.isεPPE_of_scaled (by norm_num) (by norm_num) hε

/-- Approximate PPE exposes the corresponding approximate one-shot checks. -/
example {ε : ℝ}
    (h : PublicMonitoring.IsεPerfectPublicEquilibrium
      coordinationGame.outcomeMonitoring (1 / 2) ε
      (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
        allTrueProfile)) :
    PublicMonitoring.HasNoProfitableOneShotDeviationWithinAfterEveryHistory
      coordinationGame.outcomeMonitoring (1 / 2) ε
      (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
        allTrueProfile) :=
  h.hasNoProfitableOneShotDeviationWithinAfterEveryHistory

/-- Constant continuation promises reduce APS enforceability to stage Nash. -/
example :
    coordinationGame.outcomeMonitoring.IsEnforceable (1 / 2)
      allTrueProfile
      (coordinationGame.outcomeMonitoring.constantContinuation
        (fun who => coordinationGame.eu allTrueProfile who)) := by
  exact (coordinationGame.outcomeMonitoring.isEnforceable_constant_iff_isNash
    (by norm_num) allTrueProfile _).2 allTrueProfile_isNash

/-- A stationary stage-Nash payoff is a self-generating singleton. -/
example :
    coordinationGame.outcomeMonitoring.SelfGenerating (1 / 2)
      ({fun who => coordinationGame.eu allTrueProfile who} :
        Set (Payoff Bool)) :=
  coordinationGame.outcomeMonitoring.selfGenerating_singleton_eu_of_isNash
    (by norm_num) allTrueProfile_isNash

/-- The APS self-generation theorem converts the stationary singleton into a
PPE payoff. -/
example :
    (fun who => coordinationGame.eu allTrueProfile who) ∈
      coordinationGame.outcomeMonitoring.perfectPublicEquilibriumPayoffs
        (1 / 2) := by
  letI : Finite coordinationGame.Outcome := by
    change Finite (Bool → Bool)
    infer_instance
  let W : Set (Payoff Bool) :=
    {fun who => coordinationGame.eu allTrueProfile who}
  have hW : PublicMonitoring.IsBoundedPayoffSet W := by
    intro who
    refine ⟨|coordinationGame.eu allTrueProfile who|, ?_⟩
    intro v hv
    rw [Set.mem_singleton_iff.mp hv]
  have hself : coordinationGame.outcomeMonitoring.SelfGenerating (1 / 2) W :=
    coordinationGame.outcomeMonitoring.selfGenerating_singleton_eu_of_isNash
      (by norm_num) allTrueProfile_isNash
  exact (selfGenerating_subset_perfectPublicEquilibriumPayoffs_of_finite_outcome
      coordinationGame.outcomeMonitoring (by norm_num) (by norm_num)
      hW hself) (Set.mem_singleton _)

/-- Conversely, the complete PPE payoff set decomposes relative to itself. -/
example :
    coordinationGame.outcomeMonitoring.SelfGenerating (1 / 2)
      (coordinationGame.outcomeMonitoring.perfectPublicEquilibriumPayoffs
        (1 / 2)) := by
  letI : Finite coordinationGame.Outcome := by
    change Finite (Bool → Bool)
    infer_instance
  exact PublicMonitoring.perfectPublicEquilibriumPayoffs_selfGenerating
    coordinationGame.outcomeMonitoring (by norm_num) (by norm_num)

/-- A finite public lottery has the expected convex-hull payoff. -/
example :
    (fun who => coordinationGame.eu allTrueProfile who) ∈
      PublicMonitoring.publicRandomizationHull
        ({fun who => coordinationGame.eu allTrueProfile who} :
          Set (Payoff Bool)) := by
  rw [PublicMonitoring.mem_publicRandomizationHull_iff]
  refine ⟨Unit, inferInstance, PMF.pure (),
    fun _ who => coordinationGame.eu allTrueProfile who, ?_, ?_⟩
  · simp
  · intro who
    simp

/-- Ordinary APS self-generation embeds into publicly randomized
self-generation through degenerate lotteries. -/
example :
    coordinationGame.outcomeMonitoring.PublicSelfGenerating (1 / 2)
      ({fun who => coordinationGame.eu allTrueProfile who} :
        Set (Payoff Bool)) := by
  have hself :
      coordinationGame.outcomeMonitoring.SelfGenerating (1 / 2)
        ({fun who => coordinationGame.eu allTrueProfile who} :
          Set (Payoff Bool)) :=
    coordinationGame.outcomeMonitoring.selfGenerating_singleton_eu_of_isNash
      (by norm_num) allTrueProfile_isNash
  exact hself.publicSelfGenerating

/-- Adding an independent public draw preserves the original monitoring
signal marginal. -/
example (a : Profile coordinationGame) :
    ((coordinationGame.outcomeMonitoring.withPublicDraw (PMF.pure true)).signalKernel
      a).map Prod.snd =
        coordinationGame.outcomeMonitoring.signalKernel a := by
  exact withPublicDraw_signalKernel_map_snd
    coordinationGame.outcomeMonitoring (PMF.pure true) a

/-- A stationary stage Nash equilibrium remains a seeded PPE when a public
draw is observed before play. -/
example :
    coordinationGame.outcomeMonitoring.IsSeededPerfectPublicEquilibrium
      (PMF.pure true) (1 / 2)
      (fun _ =>
        (coordinationGame.outcomeMonitoring.withPublicDraw
          (PMF.pure true)).stationaryMonitoredProfile allTrueProfile) := by
  letI : Finite coordinationGame.Outcome := by
    change Finite (Bool → Bool)
    infer_instance
  apply isSeededPerfectPublicEquilibrium_const
    coordinationGame.outcomeMonitoring (PMF.pure true)
  exact stationaryMonitoredProfile_isPerfectPublicEquilibrium_of_isNash
      (coordinationGame.outcomeMonitoring.withPublicDraw (PMF.pure true))
      (by norm_num) (by norm_num) allTrueProfile_isNash

end RepeatedMonitoringTests

end GameTheory
