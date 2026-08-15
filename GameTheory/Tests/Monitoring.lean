/-
Noisy finite public-monitoring probe.

The first public signal is a fair coin. The monitored strategy then repeats
that signal as its next action: after `false` the second signal is another fair
coin, while after `true` it is deterministically `true`. This distinguishes the
bind-first theorem from perfect public observation and from an independent
fixed signal process.
-/

import GameTheory.Repeated.Monitoring

noncomputable section

namespace GameTheory.Tests.Monitoring

open GameTheory.Math.Probability

@[reducible]
def signature : GameSignature Unit where
  Strategy _ := Bool
  Outcome := Unit

@[reducible]
def form : GameForm Unit where
  sig := signature
  play _ := FinDist.pure ()

@[reducible]
def game : UtilityGame Unit where
  form := form
  utility _ _ := 0

def fairCoin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

@[reducible]
def monitoring : game.PublicMonitoring where
  Signal := Bool
  signalLaw profile :=
    if profile () then FinDist.pure true else fairCoin

/-- Initially play `false`; thereafter play the first observed public signal. -/
def monitoredProfile : monitoring.MonitoredProfile
  | _, 0, _ => false
  | _, _ + 1, history => history 0

@[simp]
theorem fairCoin_prob_false : fairCoin.prob false = 1 / 2 := by
  rw [fairCoin, FinDist.prob_mix]
  norm_num [FinDist.prob_pure_eq_ite]

@[simp]
theorem fairCoin_prob_true : fairCoin.prob true = 1 / 2 := by
  rw [fairCoin, FinDist.prob_mix]
  norm_num [FinDist.prob_pure_eq_ite]

/-- The initial public signal is genuinely stochastic. -/
theorem initialSignal_not_deterministic :
    fairCoin ≠ FinDist.pure false ∧ fairCoin ≠ FinDist.pure true := by
  constructor
  · intro h
    have := congrArg (fun law : FinDist Bool => law.prob true) h
    norm_num [FinDist.prob_pure_eq_ite] at this
  · intro h
    have := congrArg (fun law : FinDist Bool => law.prob false) h
    norm_num [FinDist.prob_pure_eq_ite] at this

theorem initialSignalLaw :
    monitoring.signalLaw
        (fun i => monitoredProfile i 0 (fun k => k.elim0)) =
      fairCoin :=
  rfl

/-- A first `false` signal leads to another fair signal law. -/
theorem signalLaw_after_false :
    monitoring.signalLaw
        (fun i =>
          (monitoring.afterSignal monitoredProfile false) i 0
            (fun k => k.elim0)) =
      fairCoin :=
  rfl

/-- A first `true` signal changes the continuation signal law to a point mass.
Thus the second-period kernel genuinely depends on the observed prefix. -/
theorem signalLaw_after_true :
    monitoring.signalLaw
        (fun i =>
          (monitoring.afterSignal monitoredProfile true) i 0
            (fun k => k.elim0)) =
      FinDist.pure true :=
  rfl

/-- The generic bind-first law specializes to the noisy, history-dependent
two-period process: sample the fair first signal, then run its continuation. -/
theorem noisy_signalHistoryLaw_two :
    monitoring.signalHistoryLaw monitoredProfile 2 =
      fairCoin.bind fun signal =>
        (monitoring.signalHistoryLaw
            (monitoring.afterSignal monitoredProfile signal) 1).map
          (Fin.cons (α := fun _ => Bool) signal) := by
  simpa [monitoredProfile, monitoring] using
    monitoring.signalHistoryLaw_succ_eq_bind_first monitoredProfile 1

end GameTheory.Tests.Monitoring
