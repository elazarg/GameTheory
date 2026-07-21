/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Core.KernelGame
import Math.ProbabilityMassFunction

/-!
# Repeated Games with Realized Public Signals

A `PublicMonitoring` structure equips a `KernelGame` stage game with a public
signal kernel.  In every period, players choose a stage profile as a function
of the realized public-signal history, and the kernel samples the next signal.
The induced history is therefore a `PMF`, rather than the deterministic path of
`GameTheory.Concepts.Repeated.Basic`.

Only the signal marginal is represented.  Stage payoffs are additively
separable expected utilities, and strategies condition only on public signals,
so correlation between an unobserved stage outcome and the public signal does
not affect expected repeated-game payoffs.  This quotient is not suitable for
private monitoring, payoff-distribution questions, or nonseparable objectives;
those require a joint outcome-signal process.

## Main definitions

* `KernelGame.PublicMonitoring` — a public signal type and signal kernel
* `PublicMonitoring.MonitoredStrategy` / `MonitoredProfile` — public strategies
* `PublicMonitoring.garble` / `mapSignal` — transformations of public signals
* `PublicMonitoring.signalHistoryDist` — distribution of realized histories
* `PublicMonitoring.stageEU` / `finiteAveragePayoff` — expected repeated payoffs
* `PublicMonitoring.IsUniformEquilibrium` — uniform equilibrium with payoff
  convergence
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- Public monitoring for a stage game.  After a profile is chosen, every
player observes the same signal sampled from `signalKernel`. -/
structure PublicMonitoring (G : KernelGame ι) where
  /-- Type of publicly observed period signals. -/
  Signal : Type
  /-- Signal law conditional on the chosen stage profile. -/
  signalKernel : Math.Probability.Kernel (Profile G) Signal

namespace PublicMonitoring

variable {G : KernelGame ι}

/-- Public signal histories before period `t`. -/
abbrev SignalHistory (M : G.PublicMonitoring) (t : ℕ) : Type :=
  Fin t → M.Signal

/-- Concatenate a realized public prefix with a future public history. -/
def SignalHistory.append (M : G.PublicMonitoring) {t n : ℕ}
    (h : M.SignalHistory t) (k : M.SignalHistory n) :
    M.SignalHistory (t + n) :=
  Fin.append h k

/-- A public monitored strategy chooses a stage strategy after each realized
public-signal history. -/
abbrev MonitoredStrategy (M : G.PublicMonitoring) (i : ι) : Type :=
  (t : ℕ) → M.SignalHistory t → G.Strategy i

/-- A profile of public monitored strategies. -/
abbrev MonitoredProfile (M : G.PublicMonitoring) : Type :=
  ∀ i, M.MonitoredStrategy i

/-- History-independent monitored play of a fixed stage profile. -/
def stationaryMonitoredProfile (M : G.PublicMonitoring) (σ : Profile G) :
    M.MonitoredProfile :=
  fun i _ _ => σ i

/-- Continuation of a monitored profile after a specified public history.
The continuation is defined even after zero-probability histories, as required
for perfect-public equilibrium. -/
def after (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    {t : ℕ} (h : M.SignalHistory t) : M.MonitoredProfile :=
  fun i n k => σ i (t + n) (h.append M k)

@[simp] theorem after_apply
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    {t : ℕ} (h : M.SignalHistory t) (i : ι)
    (n : ℕ) (k : M.SignalHistory n) :
    M.after σ h i n k = σ i (t + n) (h.append M k) :=
  rfl

/-- Every continuation of stationary monitored play is the same stationary
profile. -/
@[simp] theorem after_stationaryMonitoredProfile
    (M : G.PublicMonitoring) (σ : Profile G)
    {t : ℕ} (h : M.SignalHistory t) :
    M.after (M.stationaryMonitoredProfile σ) h =
      M.stationaryMonitoredProfile σ := by
  rfl

/-- Post-process every public signal through a stochastic kernel.  This is the
standard garbling operation on a public monitoring structure. -/
def garble (M : G.PublicMonitoring) {S : Type}
    (K : Math.Probability.Kernel M.Signal S) : G.PublicMonitoring where
  Signal := S
  signalKernel := fun σ => (M.signalKernel σ).bind K

/-- Apply a deterministic relabeling or coarsening to every public signal. -/
def mapSignal (M : G.PublicMonitoring) {S : Type} (f : M.Signal → S) :
    G.PublicMonitoring :=
  M.garble (fun y => PMF.pure (f y))

@[simp] theorem garble_signalKernel
    (M : G.PublicMonitoring) {S : Type}
    (K : Math.Probability.Kernel M.Signal S) (σ : Profile G) :
    (M.garble K).signalKernel σ = (M.signalKernel σ).bind K :=
  rfl

@[simp] theorem mapSignal_signalKernel
    (M : G.PublicMonitoring) {S : Type} (f : M.Signal → S) (σ : Profile G) :
    (M.mapSignal f).signalKernel σ = (M.signalKernel σ).map f := by
  exact (PMF.bind_pure_comp f (M.signalKernel σ)).symm

/-- Garbling by the identity kernel leaves every conditional signal law
unchanged. -/
@[simp] theorem garble_pure_signalKernel
    (M : G.PublicMonitoring) (σ : Profile G) :
    (M.garble PMF.pure).signalKernel σ = M.signalKernel σ := by
  exact PMF.bind_pure _

/-- Successive garblings compose by Kleisli composition. -/
theorem garble_garble_signalKernel
    (M : G.PublicMonitoring) {S T : Type}
    (K : Math.Probability.Kernel M.Signal S)
    (L : Math.Probability.Kernel S T) (σ : Profile G) :
    ((M.garble K).garble L).signalKernel σ =
      (M.garble (fun y => (K y).bind L)).signalKernel σ := by
  change ((M.signalKernel σ).bind K).bind L =
    (M.signalKernel σ).bind fun y => (K y).bind L
  exact PMF.bind_bind _ _ _

/-- Distribution of public signal histories generated by a monitored profile.
The successor step appends the newly sampled signal to the realized prefix. -/
def signalHistoryDist (M : G.PublicMonitoring)
    (σ : M.MonitoredProfile) : (t : ℕ) → PMF (M.SignalHistory t)
  | 0 => PMF.pure (fun k => k.elim0)
  | t + 1 => (M.signalHistoryDist σ t).bind fun h =>
      (M.signalKernel (fun i => σ i t h)).map (Fin.snoc h)

@[simp] theorem signalHistoryDist_zero
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile) :
    M.signalHistoryDist σ 0 = PMF.pure (fun k => k.elim0) :=
  rfl

@[simp] theorem signalHistoryDist_succ
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile) (t : ℕ) :
    M.signalHistoryDist σ (t + 1) =
      (M.signalHistoryDist σ t).bind fun h =>
        (M.signalKernel (fun i => σ i t h)).map (Fin.snoc h) :=
  rfl

/-- The law of histories through time `t` depends only on actions prescribed
strictly before `t`. -/
theorem signalHistoryDist_congr_before
    (M : G.PublicMonitoring) (σ τ : M.MonitoredProfile) (t : ℕ)
    (h : ∀ s, s < t → ∀ hist i, σ i s hist = τ i s hist) :
    M.signalHistoryDist σ t = M.signalHistoryDist τ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [signalHistoryDist_succ, signalHistoryDist_succ]
      have hprefix : M.signalHistoryDist σ t = M.signalHistoryDist τ t :=
        ih (fun s hs => h s (by omega))
      rw [hprefix]
      congr 1
      funext hist
      have hprofile : (fun i => σ i t hist) = (fun i => τ i t hist) := by
        funext i
        exact h t (by omega) hist i
      rw [hprofile]

/-- Expected stage payoff in period `t`, integrating the stage expected utility
over the distribution of realized public histories. -/
def stageEU (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    (t : ℕ) (who : ι) : ℝ :=
  Math.Probability.expect (M.signalHistoryDist σ t)
    (fun h => G.eu (fun i => σ i t h) who)

/-- Expected utility at time `t` depends only on prescribed play through
time `t`. -/
theorem stageEU_congr_before_succ
    (M : G.PublicMonitoring) (σ τ : M.MonitoredProfile)
    (t : ℕ) (who : ι)
    (h : ∀ s, s < t + 1 → ∀ hist i, σ i s hist = τ i s hist) :
    M.stageEU σ t who = M.stageEU τ t who := by
  unfold stageEU
  rw [M.signalHistoryDist_congr_before σ τ t
    (fun s hs => h s (by omega))]
  congr 1
  funext hist
  have hprofile : (fun i => σ i t hist) = (fun i => τ i t hist) := by
    funext i
    exact h t (by omega) hist i
  rw [hprofile]

/-- The expected stage payoff of stationary monitored play is the stage-game
expected utility, independently of the monitoring structure. -/
@[simp] theorem stageEU_stationaryMonitoredProfile
    (M : G.PublicMonitoring) (σ : Profile G) (t : ℕ) (who : ι) :
    M.stageEU (M.stationaryMonitoredProfile σ) t who = G.eu σ who := by
  simp [stageEU, stationaryMonitoredProfile, Math.Probability.expect_const]

/-- Bound a monitored stage payoff by a constant using pointwise bounds at
every realized history.  The absolute bounds justify monotonicity of `expect`
even when the signal-history type is infinite. -/
theorem stageEU_le_const_of_forall
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile) (t : ℕ) (who : ι)
    {B C : ℝ}
    (hle : ∀ h, G.eu (fun i => σ i t h) who ≤ B)
    (habs : ∀ h, |G.eu (fun i => σ i t h) who| ≤ C)
    (hB : |B| ≤ C) :
    M.stageEU σ t who ≤ B := by
  rw [stageEU, ← Math.Probability.expect_const (M.signalHistoryDist σ t) B]
  exact Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
    (M.signalHistoryDist σ t)
    (fun h => G.eu (fun i => σ i t h) who) (fun _ => B) hle habs (fun _ => hB)

/-- Average expected payoff over the first `T` periods. -/
def finiteAveragePayoff (M : G.PublicMonitoring) (T : ℕ)
    (σ : M.MonitoredProfile) (who : ι) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, M.stageEU σ t who

/-- A finite-horizon payoff depends only on prescribed play before the
horizon. -/
theorem finiteAveragePayoff_congr_before
    (M : G.PublicMonitoring) (σ τ : M.MonitoredProfile)
    (T : ℕ) (who : ι)
    (h : ∀ t, t < T → ∀ hist i, σ i t hist = τ i t hist) :
    M.finiteAveragePayoff T σ who = M.finiteAveragePayoff T τ who := by
  unfold finiteAveragePayoff
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  exact M.stageEU_congr_before_succ σ τ t who
    (fun s hs => h s (by
      have htT : t < T := Finset.mem_range.mp ht
      omega))

@[simp] theorem finiteAveragePayoff_zero
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile) (who : ι) :
    M.finiteAveragePayoff 0 σ who = 0 := by
  simp [finiteAveragePayoff]

/-- The finite average of stationary monitored play is its stage payoff at
every nonempty horizon. -/
theorem finiteAveragePayoff_stationaryMonitoredProfile
    (M : G.PublicMonitoring) {T : ℕ} (hT : T ≠ 0)
    (σ : Profile G) (who : ι) :
    M.finiteAveragePayoff T (M.stationaryMonitoredProfile σ) who = G.eu σ who := by
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT
  simp [finiteAveragePayoff, Finset.sum_const, ← mul_assoc, inv_mul_cancel₀ hT']

/-- A periodwise upper bound bounds every nonempty finite average. -/
theorem finiteAveragePayoff_le_of_forall_stageEU_le
    (M : G.PublicMonitoring) {σ : M.MonitoredProfile} {B : ℝ} {who : ι}
    (h : ∀ t, M.stageEU σ t who ≤ B) {T : ℕ} (hT : T ≠ 0) :
    M.finiteAveragePayoff T σ who ≤ B := by
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT
  calc M.finiteAveragePayoff T σ who
      ≤ (T : ℝ)⁻¹ * ∑ _t ∈ Finset.range T, B := by
        unfold finiteAveragePayoff
        gcongr with t _
        exact h t
    _ = B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hT', one_mul]

/-- A monitored profile has long-run average payoff `v` when its finite
average expected payoffs converge coordinatewise to `v`. -/
def HasLongRunAveragePayoff (M : G.PublicMonitoring)
    (σ : M.MonitoredProfile) (v : Payoff ι) : Prop :=
  ∀ who, Filter.Tendsto (fun T => M.finiteAveragePayoff T σ who)
    Filter.atTop (nhds (v who))

/-- Stationary monitored play has its stage expected utility as its long-run
average payoff. -/
theorem hasLongRunAveragePayoff_stationaryMonitoredProfile
    (M : G.PublicMonitoring) (σ : Profile G) :
    M.HasLongRunAveragePayoff (M.stationaryMonitoredProfile σ) (G.eu σ) := by
  intro who
  have h : (fun _ : ℕ => G.eu σ who) =ᶠ[Filter.atTop]
      fun T => M.finiteAveragePayoff T (M.stationaryMonitoredProfile σ) who := by
    filter_upwards [Filter.eventually_ge_atTop 1] with T hT
    exact (M.finiteAveragePayoff_stationaryMonitoredProfile (by omega) σ who).symm
  exact Filter.Tendsto.congr' h tendsto_const_nhds

/-- `ε`-Nash equilibrium of the `T`-period monitored game under average
payoffs.  Deviations replace one player's whole public monitored strategy. -/
def IsεFiniteRepeatedNash (M : G.PublicMonitoring) [DecidableEq ι]
    (T : ℕ) (ε : ℝ) (σ : M.MonitoredProfile) : Prop :=
  ∀ who (dev : M.MonitoredStrategy who),
    M.finiteAveragePayoff T σ who + ε ≥
      M.finiteAveragePayoff T (Function.update σ who dev) who

/-- A uniform `ε`-equilibrium is an `ε`-Nash equilibrium at every sufficiently
long finite horizon, with one threshold for all players and deviations. -/
def IsUniformεEquilibrium (M : G.PublicMonitoring) [DecidableEq ι]
    (ε : ℝ) (σ : M.MonitoredProfile) : Prop :=
  ∃ T₀ : ℕ, ∀ T, T₀ ≤ T → M.IsεFiniteRepeatedNash T ε σ

/-- Uniform equilibrium under public monitoring: finite-average payoffs
converge, and the profile is a uniform `ε`-equilibrium for every `ε > 0`. -/
def IsUniformEquilibrium (M : G.PublicMonitoring) [DecidableEq ι]
    (σ : M.MonitoredProfile) : Prop :=
  (∃ v : Payoff ι, M.HasLongRunAveragePayoff σ v) ∧
    ∀ ε : ℝ, 0 < ε → M.IsUniformεEquilibrium ε σ

/-- Finite-horizon approximate Nash is monotone in the error allowance. -/
theorem IsεFiniteRepeatedNash.mono
    {M : G.PublicMonitoring} [DecidableEq ι]
    {T : ℕ} {ε ε' : ℝ} {σ : M.MonitoredProfile}
    (h : M.IsεFiniteRepeatedNash T ε σ) (hε : ε ≤ ε') :
    M.IsεFiniteRepeatedNash T ε' σ := by
  intro who dev
  have := h who dev
  linarith

/-- Uniform approximate equilibrium is monotone in the error allowance. -/
theorem IsUniformεEquilibrium.mono
    {M : G.PublicMonitoring} [DecidableEq ι]
    {ε ε' : ℝ} {σ : M.MonitoredProfile}
    (h : M.IsUniformεEquilibrium ε σ) (hε : ε ≤ ε') :
    M.IsUniformεEquilibrium ε' σ := by
  obtain ⟨T₀, hT₀⟩ := h
  exact ⟨T₀, fun T hT => (hT₀ T hT).mono hε⟩

end PublicMonitoring

end KernelGame

end GameTheory
