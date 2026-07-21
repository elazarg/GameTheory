/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.Repeated.Monitoring
import GameTheory.Concepts.Repeated.Uniform

/-!
# Canonical Public-Monitoring Instances

This module provides monitoring structures for observable profiles, realized
stage outcomes, deterministic functions of outcomes, and realized pure actions
of a mixed extension.  It also proves that observable-profile monitoring
reduces exactly to the deterministic repeated-game API.

The reduction theorems are the compatibility boundary between the stochastic
monitoring layer and `GameTheory.Concepts.Repeated.Basic`: histories are Dirac,
stage and finite-average payoffs agree, and all uniform-equilibrium predicates
are equivalent.
-/

noncomputable section

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- Observable strategy profiles: the chosen profile is announced
deterministically after every period. -/
@[reducible] def profileMonitoring (G : KernelGame ι) : G.PublicMonitoring where
  Signal := Profile G
  signalKernel := PMF.pure

/-- Perfect outcome monitoring: the signal marginal is the stage outcome law.
For the additive expected-payoff semantics this represents announcing the
realized stage outcome. -/
def outcomeMonitoring (G : KernelGame ι) : G.PublicMonitoring where
  Signal := G.Outcome
  signalKernel := G.outcomeKernel

/-- Monitor a deterministic public function of the realized stage outcome. -/
def mapMonitoring (G : KernelGame ι) {S : Type} (f : G.Outcome → S) :
    G.PublicMonitoring where
  Signal := S
  signalKernel := fun σ => (G.outcomeKernel σ).map f

/-- Realized-action monitoring for the mixed extension.  Players choose mixed
stage strategies and the independently sampled pure strategy profile is the
public signal.  This re-exposes the intermediate product sample integrated out
by `G.mixedExtension.outcomeKernel`. -/
def realizedActionMonitoring (G : KernelGame ι) [Fintype ι] :
    G.mixedExtension.PublicMonitoring where
  Signal := Profile G
  signalKernel := Math.PMFProduct.pmfPi

@[simp] theorem profileMonitoring_signalKernel
    (G : KernelGame ι) (σ : Profile G) :
    G.profileMonitoring.signalKernel σ = PMF.pure σ :=
  rfl

@[simp] theorem outcomeMonitoring_signalKernel
    (G : KernelGame ι) (σ : Profile G) :
    G.outcomeMonitoring.signalKernel σ = G.outcomeKernel σ :=
  rfl

@[simp] theorem mapMonitoring_signalKernel
    (G : KernelGame ι) {S : Type} (f : G.Outcome → S) (σ : Profile G) :
    (G.mapMonitoring f).signalKernel σ = (G.outcomeKernel σ).map f :=
  rfl

@[simp] theorem realizedActionMonitoring_signalKernel
    (G : KernelGame ι) [Fintype ι] (σ : Profile G.mixedExtension) :
    G.realizedActionMonitoring.signalKernel σ = Math.PMFProduct.pmfPi σ :=
  rfl

/-- Pure mixed actions generate the corresponding pure public action profile
under realized-action monitoring. -/
@[simp] theorem realizedActionMonitoring_signalKernel_pure
    (G : KernelGame ι) [Fintype ι] (σ : Profile G) :
    G.realizedActionMonitoring.signalKernel
        (fun i => (PMF.pure (σ i) : PMF (G.Strategy i))) = PMF.pure σ := by
  exact Math.PMFProduct.pmfPi_pure σ

namespace PublicMonitoring

/-- Under observable-profile monitoring, the realized history distribution is
Dirac at the deterministic repeated-play prefix. -/
theorem signalHistoryDist_profileMonitoring
    (G : KernelGame ι) (σ : G.RepeatedProfile) : ∀ t : ℕ,
    G.profileMonitoring.signalHistoryDist σ t =
      PMF.pure (fun k : Fin t => G.repeatedPlay σ k)
  | 0 => by
      rw [signalHistoryDist_zero]
      apply congrArg PMF.pure
      funext k
      exact Fin.elim0 k
  | t + 1 => by
      rw [signalHistoryDist_succ, signalHistoryDist_profileMonitoring G σ t]
      simp only [PMF.pure_bind, PMF.map]
      change PMF.pure (Fin.snoc (fun k : Fin t => G.repeatedPlay σ k)
        (fun i => σ i t (fun k => G.repeatedPlay σ k))) =
          PMF.pure (fun k : Fin (t + 1) => G.repeatedPlay σ k)
      apply congrArg PMF.pure
      funext k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [Fin.snoc_last, KernelGame.repeatedPlay, Fin.val_last]
      · rw [Fin.snoc_castSucc, Fin.val_castSucc]

/-- Observable-profile monitoring has the same stage expected payoff as the
deterministic repeated-play path. -/
@[simp] theorem stageEU_profileMonitoring
    (G : KernelGame ι) (σ : G.RepeatedProfile) (t : ℕ) (who : ι) :
    G.profileMonitoring.stageEU σ t who = G.eu (G.repeatedPlay σ t) who := by
  rw [stageEU, signalHistoryDist_profileMonitoring, Math.Probability.expect_pure]
  apply congrArg (fun ρ => G.eu ρ who)
  funext i
  rw [KernelGame.repeatedPlay]

/-- Observable-profile monitoring has exactly the deterministic finite-average
payoff. -/
@[simp] theorem finiteAveragePayoff_profileMonitoring
    (G : KernelGame ι) (T : ℕ) (σ : G.RepeatedProfile) (who : ι) :
    G.profileMonitoring.finiteAveragePayoff T σ who =
      G.finiteAveragePayoff T σ who := by
  simp [PublicMonitoring.finiteAveragePayoff, KernelGame.finiteAveragePayoff]

/-- Long-run payoff convergence is preserved and reflected by the
observable-profile monitoring embedding. -/
theorem hasLongRunAveragePayoff_profileMonitoring
    (G : KernelGame ι) (σ : G.RepeatedProfile) (v : Payoff ι) :
    G.profileMonitoring.HasLongRunAveragePayoff σ v ↔
      G.HasLongRunAveragePayoff σ v := by
  simp only [PublicMonitoring.HasLongRunAveragePayoff,
    KernelGame.HasLongRunAveragePayoff, finiteAveragePayoff_profileMonitoring]

/-- Finite-horizon approximate Nash is preserved and reflected by
observable-profile monitoring. -/
theorem isεFiniteRepeatedNash_profileMonitoring
    (G : KernelGame ι) [DecidableEq ι]
    (T : ℕ) (ε : ℝ) (σ : G.RepeatedProfile) :
    G.profileMonitoring.IsεFiniteRepeatedNash T ε σ ↔
      G.IsεFiniteRepeatedNash T ε σ := by
  simp only [PublicMonitoring.IsεFiniteRepeatedNash,
    KernelGame.IsεFiniteRepeatedNash, finiteAveragePayoff_profileMonitoring]

/-- Uniform approximate equilibrium is preserved and reflected by
observable-profile monitoring. -/
theorem isUniformεEquilibrium_profileMonitoring
    (G : KernelGame ι) [DecidableEq ι]
    (ε : ℝ) (σ : G.RepeatedProfile) :
    G.profileMonitoring.IsUniformεEquilibrium ε σ ↔
      G.IsUniformεEquilibrium ε σ := by
  simp only [PublicMonitoring.IsUniformεEquilibrium,
    KernelGame.IsUniformεEquilibrium,
    isεFiniteRepeatedNash_profileMonitoring]

/-- The monitored and deterministic uniform-equilibrium concepts coincide
exactly under observable-profile monitoring. -/
theorem isUniformEquilibrium_profileMonitoring
    (G : KernelGame ι) [DecidableEq ι] (σ : G.RepeatedProfile) :
    G.profileMonitoring.IsUniformEquilibrium σ ↔ G.IsUniformEquilibrium σ := by
  simp only [PublicMonitoring.IsUniformEquilibrium,
    KernelGame.IsUniformEquilibrium, hasLongRunAveragePayoff_profileMonitoring,
    isUniformεEquilibrium_profileMonitoring]

/-- Stationary repetition of a stage-game Nash equilibrium is a uniform
equilibrium under every public monitoring structure.  The proof integrates the
stage Nash inequality over the deviator's random public-history distribution;
finite outcomes provide the boundedness needed for countable `expect`
monotonicity. -/
theorem stationaryMonitoredProfile_isUniformEquilibrium_of_isNash
    {G : KernelGame ι} (M : G.PublicMonitoring) [DecidableEq ι] [Finite G.Outcome]
    {σ : Profile G} (hN : G.IsNash σ) :
    M.IsUniformEquilibrium (M.stationaryMonitoredProfile σ) := by
  refine ⟨⟨G.eu σ, M.hasLongRunAveragePayoff_stationaryMonitoredProfile σ⟩,
    fun ε hε => ?_⟩
  refine ⟨1, fun T hT who dev => ?_⟩
  have hT0 : T ≠ 0 := by omega
  rw [M.finiteAveragePayoff_stationaryMonitoredProfile hT0]
  obtain ⟨C, hC⟩ := G.exists_eu_abs_bound_of_finite_outcome who
  have hstage : ∀ t,
      M.stageEU
        (Function.update (M.stationaryMonitoredProfile σ) who dev) t who ≤
          G.eu σ who := by
    intro t
    refine M.stageEU_le_const_of_forall
      (Function.update (M.stationaryMonitoredProfile σ) who dev) t who
      (B := G.eu σ who) (C := C) ?_ ?_ (hC σ)
    · intro hist
      have hprofile :
          (fun i => (Function.update (M.stationaryMonitoredProfile σ) who dev) i
            t hist) = Function.update σ who (dev t hist) := by
        funext i
        by_cases hi : i = who
        · subst hi
          simp
        · simp [Function.update, stationaryMonitoredProfile, hi]
      rw [hprofile]
      exact hN who _
    · intro hist
      exact hC _
  have havg :
      M.finiteAveragePayoff T
        (Function.update (M.stationaryMonitoredProfile σ) who dev) who ≤
          G.eu σ who :=
    M.finiteAveragePayoff_le_of_forall_stageEU_le hstage hT0
  linarith

end PublicMonitoring

end KernelGame

end GameTheory
