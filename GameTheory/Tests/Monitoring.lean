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
  play _ := PMF.pure ()

@[reducible]
def game : UtilityGame Unit where
  form := form
  utility _ _ := 0

def fairCoin : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure false) (PMF.pure true)

@[reducible]
def monitoring : game.PublicMonitoring where
  Signal := Bool
  signalLaw profile :=
    if profile () then PMF.pure true else fairCoin

/-- Initially play `false`; thereafter play the first observed public signal. -/
def monitoredProfile : monitoring.MonitoredProfile
  | _, 0, _ => false
  | _, _ + 1, history => history 0

@[simp]
theorem fairCoin_prob_false : fairCoin false = 1 / 2 := by
  norm_num [fairCoin, mix_apply]
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

@[simp]
theorem fairCoin_prob_true : fairCoin true = 1 / 2 := by
  norm_num [fairCoin, mix_apply]
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The initial public signal is genuinely stochastic. -/
theorem initialSignal_not_deterministic :
    fairCoin ≠ PMF.pure false ∧ fairCoin ≠ PMF.pure true := by
  constructor
  · intro h
    have := congrArg (fun law : PMF Bool => law true) h
    simp [fairCoin_prob_true] at this
  · intro h
    have := congrArg (fun law : PMF Bool => law false) h
    simp [fairCoin_prob_false] at this

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
      PMF.pure true :=
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
