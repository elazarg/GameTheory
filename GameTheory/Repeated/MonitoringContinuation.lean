/-
# Continuations and finite deviations for public monitoring

This module contains the cast-free public-history algebra used by discounted
public-monitoring arguments.  It deliberately stops before defining payoffs or
equilibrium predicates.
-/

import GameTheory.Repeated.Monitoring

noncomputable section

namespace GameTheory

universe uι us uo uy

variable {ι : Type uι}

namespace UtilityGame

namespace PublicMonitoring

variable {G : UtilityGame.{uι, us, uo} ι}

/-- Concatenate a realized public prefix with a future public history. -/
def SignalHistory.append (M : G.PublicMonitoring) {t n : ℕ}
    (history : M.SignalHistory t) (future : M.SignalHistory n) :
    M.SignalHistory (t + n) :=
  Fin.append history future

/-- Strategic signature for public monitored strategies.  Its outcome is the
chosen monitored profile itself, so utilities may evaluate its generated
finite-history laws without adding a second equilibrium engine. -/
def monitoredSignature (M : G.PublicMonitoring) : GameSignature ι where
  Strategy := M.MonitoredStrategy
  Outcome := M.MonitoredProfile

/-- History-independent monitored play of a fixed stage profile. -/
def stationaryMonitoredProfile (M : G.PublicMonitoring)
    (profile : Profile G.form.sig) : M.MonitoredProfile :=
  fun i _ _ => profile i

/-- Iterate one-signal continuation along a list of public signals. -/
def afterSignals (M : G.PublicMonitoring) (profile : M.MonitoredProfile) :
    List M.Signal → M.MonitoredProfile
  | [] => profile
  | signal :: signals => M.afterSignals (M.afterSignal profile signal) signals

/-- Continuation after an arbitrary public history, including an off-path
history. -/
def after (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    {t : ℕ} (history : M.SignalHistory t) : M.MonitoredProfile :=
  M.afterSignals profile (List.ofFn history)

@[simp]
theorem afterSignals_nil (M : G.PublicMonitoring) (profile : M.MonitoredProfile) :
    M.afterSignals profile [] = profile :=
  rfl

@[simp]
theorem afterSignals_cons (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (signal : M.Signal) (signals : List M.Signal) :
    M.afterSignals profile (signal :: signals) =
      M.afterSignals (M.afterSignal profile signal) signals :=
  rfl

theorem afterSignals_append (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (first second : List M.Signal) :
    M.afterSignals profile (first ++ second) =
      M.afterSignals (M.afterSignals profile first) second := by
  induction first generalizing profile with
  | nil => rfl
  | cons signal first ih => exact ih (M.afterSignal profile signal)

theorem afterSignal_after (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    {t : ℕ} (history : M.SignalHistory t) (signal : M.Signal) :
    M.afterSignal (M.after profile history) signal =
      M.after profile (Fin.snoc history signal) := by
  have hlist : List.ofFn (Fin.snoc history signal) = List.ofFn history ++ [signal] := by
    simpa using (List.ofFn_succ' (Fin.snoc history signal))
  rw [after, after, hlist, M.afterSignals_append]
  rfl

theorem after_after (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    {t n : ℕ} (history : M.SignalHistory t) (future : M.SignalHistory n) :
    M.after (M.after profile history) future =
      M.after profile (Fin.append history future) := by
  rw [after, after, after, List.ofFn_fin_append, M.afterSignals_append]

@[simp]
theorem after_singleton (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (signal : M.Signal) :
    M.after profile (Fin.cons signal (fun k : Fin 0 => k.elim0)) =
      M.afterSignal profile signal := by
  unfold after
  simp [List.ofFn_succ]

theorem after_afterSignal (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (signal : M.Signal) {t : ℕ} (history : M.SignalHistory t) :
    M.after (M.afterSignal profile signal) history =
      M.after profile (Fin.cons signal history) := by
  unfold after
  simp [List.ofFn_succ]

@[simp]
theorem afterSignal_stationaryMonitoredProfile (M : G.PublicMonitoring)
    (profile : Profile G.form.sig) (signal : M.Signal) :
    M.afterSignal (M.stationaryMonitoredProfile profile) signal =
      M.stationaryMonitoredProfile profile :=
  rfl

@[simp]
theorem after_stationaryMonitoredProfile (M : G.PublicMonitoring)
    (profile : Profile G.form.sig) {t : ℕ} (history : M.SignalHistory t) :
    M.after (M.stationaryMonitoredProfile profile) history =
      M.stationaryMonitoredProfile profile := by
  unfold after
  induction List.ofFn history with
  | nil => rfl
  | cons signal signals ih =>
      simp only [afterSignals_cons, afterSignal_stationaryMonitoredProfile]
      exact ih

/-- Deviate only at the current period, then return to the prescribed public
strategy. -/
def oneShotDeviation (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (who : ι) (action : G.form.sig.Strategy who) : M.MonitoredStrategy who
  | 0, _ => action
  | n + 1, history => profile who (n + 1) history

/-- Continuation of one player's monitored strategy after one signal. -/
def strategyAfterSignal (M : G.PublicMonitoring) {who : ι}
    (strategy : M.MonitoredStrategy who) (signal : M.Signal) :
    M.MonitoredStrategy who :=
  fun n history => strategy (n + 1) (Fin.cons signal history)

/-- Follow `deviation` for the first `count` periods and return to `profile`.
-/
def truncatedDeviation (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (who : ι) (deviation : M.MonitoredStrategy who) (count : ℕ) :
    M.MonitoredStrategy who :=
  fun n history => if n < count then deviation n history else profile who n history

@[simp]
theorem oneShotDeviation_zero (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (who : ι) (action : G.form.sig.Strategy who) (history : M.SignalHistory 0) :
    M.oneShotDeviation profile who action 0 history = action :=
  rfl

@[simp]
theorem oneShotDeviation_succ (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (who : ι) (action : G.form.sig.Strategy who) (n : ℕ)
    (history : M.SignalHistory (n + 1)) :
    M.oneShotDeviation profile who action (n + 1) history = profile who (n + 1) history :=
  rfl

@[simp]
theorem truncatedDeviation_zero (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (who : ι) (deviation : M.MonitoredStrategy who) :
    M.truncatedDeviation profile who deviation 0 = profile who := by
  funext n history
  simp [truncatedDeviation]

@[simp]
theorem truncatedDeviation_succ_zero (M : G.PublicMonitoring)
    (profile : M.MonitoredProfile) (who : ι) (deviation : M.MonitoredStrategy who)
    (count : ℕ) (history : M.SignalHistory 0) :
    M.truncatedDeviation profile who deviation (count + 1) 0 history = deviation 0 history := by
  simp [truncatedDeviation]

theorem strategyAfterSignal_truncatedDeviation_succ (M : G.PublicMonitoring)
    (profile : M.MonitoredProfile) (who : ι) (deviation : M.MonitoredStrategy who)
    (count : ℕ) (signal : M.Signal) :
    M.strategyAfterSignal (M.truncatedDeviation profile who deviation (count + 1)) signal =
      M.truncatedDeviation (M.afterSignal profile signal) who
        (M.strategyAfterSignal deviation signal) count := by
  funext n history
  simp [strategyAfterSignal, truncatedDeviation]

/-- Continuation commutes with a unilateral monitored-strategy replacement. -/
theorem afterSignal_update (M : G.PublicMonitoring) [DecidableEq ι]
    (profile : M.MonitoredProfile) (who : ι) (deviation : M.MonitoredStrategy who)
    (signal : M.Signal) :
    M.afterSignal (Profile.update (sig := M.monitoredSignature) profile who deviation) signal =
      Profile.update (sig := M.monitoredSignature) (M.afterSignal profile signal) who
        (M.strategyAfterSignal deviation signal) := by
  funext i n history
  by_cases hi : i = who
  · subst hi
    simp [afterSignal, strategyAfterSignal]
  · simp [afterSignal, Profile.update_of_ne _ _ hi]

/-- After a one-shot deviation's signal, play returns to the prescribed
continuation profile. -/
@[simp]
theorem afterSignal_update_oneShotDeviation
    (M : G.PublicMonitoring) [DecidableEq ι]
    (profile : M.MonitoredProfile) (who : ι)
    (action : G.form.sig.Strategy who) (signal : M.Signal) :
    M.afterSignal
        (Profile.update (sig := M.monitoredSignature) profile who
          (M.oneShotDeviation profile who action)) signal =
      M.afterSignal profile signal := by
  rw [M.afterSignal_update profile who
    (M.oneShotDeviation profile who action) signal]
  apply Profile.update_eq_self

/-- The current stage of a unilateral one-shot deviation is the canonical
stage-profile update. -/
theorem currentProfile_update_oneShotDeviation
    (M : G.PublicMonitoring) [DecidableEq ι]
    (profile : M.MonitoredProfile) (who : ι)
    (action : G.form.sig.Strategy who) :
    (fun i =>
      (Profile.update (sig := M.monitoredSignature) profile who
        (M.oneShotDeviation profile who action)) i 0
          (fun k => k.elim0)) =
      Profile.update (fun i => profile i 0 (fun k => k.elim0)) who action := by
  funext i
  by_cases hi : i = who
  · subst hi
    simp
  · simp [Profile.update_of_ne _ _ hi]

end PublicMonitoring

end UtilityGame

end GameTheory
