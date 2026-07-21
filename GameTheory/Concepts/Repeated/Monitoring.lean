/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Core.KernelGame
import Math.List
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

/-- Continuation after observing one next public signal.  Unlike general
prefix concatenation, this uses `Fin.cons` and therefore keeps the successor
time index definitionally aligned with `n + 1`. -/
def afterSignal (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    (y : M.Signal) : M.MonitoredProfile :=
  fun i n h => σ i (n + 1) (Fin.cons y h)

@[simp] theorem afterSignal_apply
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile) (y : M.Signal)
    (i : ι) (n : ℕ) (h : M.SignalHistory n) :
    M.afterSignal σ y i n h = σ i (n + 1) (Fin.cons y h) :=
  rfl

@[simp] theorem afterSignal_stationaryMonitoredProfile
    (M : G.PublicMonitoring) (σ : Profile G) (y : M.Signal) :
    M.afterSignal (M.stationaryMonitoredProfile σ) y =
      M.stationaryMonitoredProfile σ :=
  rfl

/-- Iterate one-signal continuation along a list of public signals. -/
def afterSignals (M : G.PublicMonitoring) (σ : M.MonitoredProfile) :
    List M.Signal → M.MonitoredProfile
  | [] => σ
  | y :: ys => M.afterSignals (M.afterSignal σ y) ys

/-- Continuation of a monitored profile after a specified public history.
The continuation is defined even after zero-probability histories, as required
for perfect-public equilibrium.  Iterating one-signal continuations makes the
sequential algebra definitionally well behaved, without casts between equal
`Fin` index types. -/
def after (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    {t : ℕ} (h : M.SignalHistory t) : M.MonitoredProfile :=
  M.afterSignals σ (List.ofFn h)

@[simp] theorem afterSignals_nil
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile) :
    M.afterSignals σ [] = σ :=
  rfl

@[simp] theorem afterSignals_cons
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    (y : M.Signal) (ys : List M.Signal) :
    M.afterSignals σ (y :: ys) =
      M.afterSignals (M.afterSignal σ y) ys :=
  rfl

/-- Sequential continuation respects concatenation of signal lists. -/
theorem afterSignals_append
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    (xs ys : List M.Signal) :
    M.afterSignals σ (xs ++ ys) =
      M.afterSignals (M.afterSignals σ xs) ys := by
  induction xs generalizing σ with
  | nil => rfl
  | cons x xs ih =>
      exact ih (M.afterSignal σ x)

/-- Taking a one-signal continuation after an existing prefix is the same as
continuing after the prefix with that signal appended. -/
theorem afterSignal_after
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    {t : ℕ} (h : M.SignalHistory t) (y : M.Signal) :
    M.afterSignal (M.after σ h) y = M.after σ (Fin.snoc h y) := by
  rw [after, after, Math.List.ofFn_snoc, M.afterSignals_append]
  rfl

/-- Continuing after two successive public histories is continuation after
their concatenation. -/
theorem after_after
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    {t n : ℕ} (h : M.SignalHistory t) (k : M.SignalHistory n) :
    M.after (M.after σ h) k = M.after σ (Fin.append h k) := by
  rw [after, after, after, List.ofFn_fin_append, M.afterSignals_append]

/-- A one-element history gives the corresponding one-signal continuation. -/
@[simp] theorem after_singleton
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile) (y : M.Signal) :
    M.after σ (Fin.cons y (fun k : Fin 0 => k.elim0)) =
      M.afterSignal σ y := by
  change M.afterSignals σ
      (List.ofFn (Fin.cons y (fun k : Fin 0 => k.elim0))) = _
  simp [List.ofFn_succ]

/-- A continuation after the first signal and a remaining history is the
continuation after the history obtained by adjoining that signal at the
front. -/
theorem after_afterSignal
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile) (y : M.Signal)
    {t : ℕ} (h : M.SignalHistory t) :
    M.after (M.afterSignal σ y) h = M.after σ (Fin.cons y h) := by
  change M.afterSignals (M.afterSignal σ y) (List.ofFn h) =
    M.afterSignals σ (List.ofFn (Fin.cons y h))
  simp [List.ofFn_succ]

/-- Pointwise characterization of continuation by prefix concatenation.  This
recovers the direct `Fin.append` view while `after` itself uses cast-free
one-signal iteration for compositional proofs. -/
@[simp] theorem after_apply
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    {t : ℕ} (h : M.SignalHistory t) (i : ι)
    (n : ℕ) (k : M.SignalHistory n) :
    M.after σ h i n k = σ i (t + n) (h.append M k) := by
  induction t generalizing σ n with
  | zero =>
      have hh : h = Fin.elim0 := Subsingleton.elim _ _
      subst h
      simp only [after, List.ofFn_zero, afterSignals_nil,
        SignalHistory.append, Fin.elim0_append]
      change (fun p : Σ m, M.SignalHistory m => σ i p.1 p.2) ⟨n, k⟩ =
        (fun p : Σ m, M.SignalHistory m => σ i p.1 p.2)
          ⟨0 + n, k ∘ Fin.cast (Nat.zero_add n)⟩
      apply congrArg (fun p : Σ m, M.SignalHistory m => σ i p.1 p.2)
      apply Sigma.ext (Nat.zero_add n).symm
      apply (Fin.heq_fun_iff (Nat.zero_add n).symm).2
      intro j
      rfl
  | succ t ih =>
      unfold after
      rw [List.ofFn_succ]
      simp only [afterSignals_cons]
      change M.after (M.afterSignal σ (h 0)) (Fin.tail h) i n k = _
      rw [ih]
      change σ i ((t + n) + 1)
          (Fin.cons (h 0) (Fin.append (Fin.tail h) k)) = _
      change (fun p : Σ m, M.SignalHistory m => σ i p.1 p.2)
          ⟨(t + n) + 1, Fin.cons (h 0) (Fin.append (Fin.tail h) k)⟩ =
        (fun p : Σ m, M.SignalHistory m => σ i p.1 p.2)
          ⟨(t + 1) + n, Fin.append h k⟩
      apply congrArg (fun p : Σ m, M.SignalHistory m => σ i p.1 p.2)
      apply Sigma.ext (Nat.add_right_comm t n 1)
      apply (Fin.heq_fun_iff (Nat.add_right_comm t n 1)).2
      intro j
      rw [← Fin.cons_self_tail h, Fin.append_cons]
      rfl

/-- Deviate only at the current period, then return to the prescribed public
strategy.  Applied to a continuation profile, this is the standard one-shot
deviation after the corresponding public history. -/
def oneShotDeviation (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    (who : ι) (a : G.Strategy who) : M.MonitoredStrategy who
  | 0, _ => a
  | n + 1, h => σ who (n + 1) h

/-- Continuation of one player's monitored strategy after a next public
signal. -/
def strategyAfterSignal (M : G.PublicMonitoring) {who : ι}
    (s : M.MonitoredStrategy who) (y : M.Signal) : M.MonitoredStrategy who :=
  fun n h => s (n + 1) (Fin.cons y h)

/-- Follow `dev` for the first `N` periods and return to `σ` thereafter. -/
def truncatedDeviation (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    (who : ι) (dev : M.MonitoredStrategy who) (N : ℕ) :
    M.MonitoredStrategy who :=
  fun n h => if n < N then dev n h else σ who n h

@[simp] theorem oneShotDeviation_zero
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    (who : ι) (a : G.Strategy who) (h : M.SignalHistory 0) :
    M.oneShotDeviation σ who a 0 h = a :=
  rfl

@[simp] theorem oneShotDeviation_succ
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    (who : ι) (a : G.Strategy who) (n : ℕ)
    (h : M.SignalHistory (n + 1)) :
    M.oneShotDeviation σ who a (n + 1) h = σ who (n + 1) h :=
  rfl

@[simp] theorem truncatedDeviation_zero
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    (who : ι) (dev : M.MonitoredStrategy who) :
    M.truncatedDeviation σ who dev 0 = σ who := by
  funext n h
  simp [truncatedDeviation]

@[simp] theorem truncatedDeviation_succ_zero
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    (who : ι) (dev : M.MonitoredStrategy who) (N : ℕ)
    (h : M.SignalHistory 0) :
    M.truncatedDeviation σ who dev (N + 1) 0 h = dev 0 h := by
  simp [truncatedDeviation]

/-- Continuing a truncated deviation removes its first deviation period. -/
theorem strategyAfterSignal_truncatedDeviation_succ
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    (who : ι) (dev : M.MonitoredStrategy who) (N : ℕ) (y : M.Signal) :
    M.strategyAfterSignal (M.truncatedDeviation σ who dev (N + 1)) y =
      M.truncatedDeviation (M.afterSignal σ y) who
        (M.strategyAfterSignal dev y) N := by
  funext n h
  simp [strategyAfterSignal, truncatedDeviation]

/-- Continuation commutes with a unilateral strategy update. -/
theorem afterSignal_update
    (M : G.PublicMonitoring) [DecidableEq ι]
    (σ : M.MonitoredProfile) (who : ι) (dev : M.MonitoredStrategy who)
    (y : M.Signal) :
    M.afterSignal (Function.update σ who dev) y =
      Function.update (M.afterSignal σ y) who
        (M.strategyAfterSignal dev y) := by
  funext i n h
  by_cases hi : i = who
  · subst hi
    simp [afterSignal, strategyAfterSignal]
  · simp [afterSignal, Function.update_of_ne hi]

/-- After the signal following a one-shot deviation, play returns to the
prescribed continuation profile. -/
@[simp] theorem afterSignal_update_oneShotDeviation
    (M : G.PublicMonitoring) [DecidableEq ι]
    (σ : M.MonitoredProfile) (who : ι) (a : G.Strategy who)
    (y : M.Signal) :
    M.afterSignal
        (Function.update σ who (M.oneShotDeviation σ who a)) y =
      M.afterSignal σ y := by
  rw [M.afterSignal_update σ who (M.oneShotDeviation σ who a) y]
  apply Function.update_eq_self

/-- Every continuation of stationary monitored play is the same stationary
profile. -/
@[simp] theorem after_stationaryMonitoredProfile
    (M : G.PublicMonitoring) (σ : Profile G)
    {t : ℕ} (h : M.SignalHistory t) :
    M.after (M.stationaryMonitoredProfile σ) h =
      M.stationaryMonitoredProfile σ := by
  unfold after
  induction List.ofFn h with
  | nil => rfl
  | cons y ys ih =>
      simpa only [afterSignals_cons,
        afterSignal_stationaryMonitoredProfile] using ih

/-- Post-process every public signal through a stochastic kernel.  This is the
standard garbling operation on a public monitoring structure. -/
@[reducible] def garble (M : G.PublicMonitoring) {S : Type}
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

/-- Decompose a public history by its first signal: sample the current signal,
then generate the remaining history from the corresponding continuation
profile. -/
theorem signalHistoryDist_succ_eq_bind_first
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile) : ∀ n : ℕ,
    M.signalHistoryDist σ (n + 1) =
      (M.signalKernel (fun i => σ i 0 (fun k => k.elim0))).bind fun y =>
        (M.signalHistoryDist (M.afterSignal σ y) n).map
          (Fin.cons (α := fun _ => M.Signal) y)
  | 0 => by
      rw [signalHistoryDist_succ, signalHistoryDist_zero]
      simp only [signalHistoryDist_zero, PMF.pure_bind, PMF.pure_map]
      have hf :
          Fin.snoc (α := fun _ => M.Signal) (fun k : Fin 0 => k.elim0) =
            (fun y : M.Signal =>
              Fin.cons (α := fun _ => M.Signal) y
                (fun k : Fin 0 => k.elim0)) := by
        funext y j
        exact Fin.eq_zero j ▸ rfl
      rw [hf]
      exact (PMF.bind_pure_comp _ _).symm
  | n + 1 => by
      rw [signalHistoryDist_succ, signalHistoryDist_succ_eq_bind_first M σ n]
      rw [PMF.bind_bind]
      congr 1
      funext y
      rw [PMF.bind_map]
      rw [signalHistoryDist_succ]
      rw [PMF.map_bind]
      congr 1
      funext h
      change (M.signalKernel (fun i => σ i (n + 1) (Fin.cons y h))).map
          (Fin.snoc (Fin.cons y h)) =
        ((M.signalKernel (fun i => σ i (n + 1) (Fin.cons y h))).map
          (Fin.snoc h)).map (Fin.cons (α := fun _ => M.Signal) y)
      rw [PMF.map_comp]
      congr 1
      funext z
      exact (Fin.cons_snoc_eq_snoc_cons y h z).symm

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

/-- At the initial stage there is a unique empty public history. -/
@[simp] theorem stageEU_zero
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile) (who : ι) :
    M.stageEU σ 0 who = G.eu (fun i => σ i 0 (fun k => k.elim0)) who := by
  simp [stageEU]

/-- Tower property for monitored stage payoff: condition first on the current
public signal, then evaluate the corresponding continuation profile. -/
theorem stageEU_succ_eq_expect_afterSignal
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile)
    (n : ℕ) (who : ι) {C : ℝ}
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C) :
    M.stageEU σ (n + 1) who =
      Math.Probability.expect
        (M.signalKernel (fun i => σ i 0 (fun k => k.elim0)))
        (fun y => M.stageEU (M.afterSignal σ y) n who) := by
  unfold stageEU
  rw [M.signalHistoryDist_succ_eq_bind_first σ n]
  rw [Math.Probability.expect_bind_of_bounded
    (hbd := fun h => hbd (fun i => σ i (n + 1) h))]
  apply congrArg
  funext y
  rw [show (M.signalHistoryDist (M.afterSignal σ y) n).map
      (Fin.cons (α := fun _ => M.Signal) y) =
      Math.ProbabilityMassFunction.pushforward
        (M.signalHistoryDist (M.afterSignal σ y) n)
        (Fin.cons (α := fun _ => M.Signal) y) by rfl]
  rw [Math.ProbabilityMassFunction.expect_pushforward_of_bounded
    (hbd := fun h => hbd (fun i => σ i (n + 1) h))]
  rfl

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

/-- Before its cutoff, a truncated unilateral deviation induces exactly the
same expected stage payoff as the full deviation. -/
theorem stageEU_update_truncatedDeviation_eq_of_lt
    (M : G.PublicMonitoring) [DecidableEq ι]
    (σ : M.MonitoredProfile) (who : ι)
    (dev : M.MonitoredStrategy who) {t N : ℕ} (htN : t < N) :
    M.stageEU
        (Function.update σ who (M.truncatedDeviation σ who dev N)) t who =
      M.stageEU (Function.update σ who dev) t who := by
  apply M.stageEU_congr_before_succ
  intro s hs hist i
  have hsN : s < N := by omega
  by_cases hi : i = who
  · subst hi
    simp [truncatedDeviation, hsN]
  · simp [hi]

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

/-- A uniform absolute bound on stage-game expected utility also bounds the
expected utility at every monitored stage. -/
theorem abs_stageEU_le_of_forall_eu_abs_le
    (M : G.PublicMonitoring) (σ : M.MonitoredProfile) (t : ℕ) (who : ι)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ρ : Profile G, |G.eu ρ who| ≤ C) :
    |M.stageEU σ t who| ≤ C := by
  apply abs_le.mpr
  constructor
  · rw [stageEU, ← Math.Probability.expect_const
      (M.signalHistoryDist σ t) (-C)]
    exact Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
      (M.signalHistoryDist σ t) (fun _ => -C)
      (fun h => G.eu (fun i => σ i t h) who)
      (fun h => (abs_le.mp (hC (fun i => σ i t h))).1)
      (fun _ => by rw [abs_neg, abs_of_nonneg hC0])
      (fun h => hC (fun i => σ i t h))
  · exact M.stageEU_le_const_of_forall σ t who
      (fun h => (abs_le.mp (hC (fun i => σ i t h))).2)
      (fun h => hC (fun i => σ i t h)) (by rw [abs_of_nonneg hC0])

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
