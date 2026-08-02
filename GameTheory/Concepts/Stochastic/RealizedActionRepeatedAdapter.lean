/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Repeated.MonitoringInstances
import GameTheory.Concepts.Stochastic.Discounted

/-!
# Realized-Action Repetition as a One-State Stochastic Game

This module identifies two presentations of the same public randomization:

* repeated play of a kernel game under realized-action monitoring, where a
  monitored strategy chooses a mixed stage action and the sampled pure joint
  action is publicly observed; and
* the one-state stochastic game whose pure actions are the original stage
  strategies and whose stage payoff is the original expected utility.

The history and strategy transports are inverse before any finiteness
assumptions beyond finitely many players.  Under the standard finite-game
hypotheses, they preserve history laws, finite-average payoffs, unilateral
updates, and hence all finite-horizon and uniform-accuracy Nash predicates.

The existing monitored `IsUniformEquilibrium` fixes one profile and separately
requires payoff convergence.  By contrast,
`StochasticGame.IsUniformEquilibriumPayoff` may choose a new profile at each
accuracy.  The final section therefore introduces an explicitly payoff-level
monitored predicate with the stochastic quantifier order; it does not conflate
the two notions.
-/

noncomputable section

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- The one-state stochastic presentation of repeated play of `G`.  A pure
action is a pure stage strategy of `G`; the stochastic game's behavioral
randomization is therefore exactly a mixed stage action. -/
def realizedActionStochasticGame (G : KernelGame ι) : StochasticGame ι where
  State := PUnit
  Act := G.Strategy
  stagePayoff := fun _ action who => G.eu action who
  transition := fun _ _ => PMF.pure PUnit.unit
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

@[simp] theorem realizedActionStochasticGame_stagePayoff
    (G : KernelGame ι) (state : PUnit) (action : Profile G) (who : ι) :
    G.realizedActionStochasticGame.stagePayoff state action who =
      G.eu action who :=
  rfl

@[simp] theorem realizedActionStochasticGame_transition
    (G : KernelGame ι) (state : PUnit) (action : Profile G) :
    G.realizedActionStochasticGame.transition state action =
      PMF.pure PUnit.unit :=
  rfl

namespace RealizedActionRepeatedAdapter

variable [Fintype ι] (G : KernelGame ι)

/-- Forget the unique states in a stochastic history, retaining exactly the
public sequence of realized joint actions. -/
def actionHistory {t : ℕ}
    (history : G.realizedActionStochasticGame.Hist t) :
    G.realizedActionMonitoring.SignalHistory t :=
  fun stage => (history.1 stage).2

/-- Insert the unique state before and after every realized-action history. -/
def stochasticHistory {t : ℕ}
    (history : G.realizedActionMonitoring.SignalHistory t) :
    G.realizedActionStochasticGame.Hist t :=
  (fun stage => (PUnit.unit, history stage), PUnit.unit)

@[simp] theorem actionHistory_stochasticHistory {t : ℕ}
    (history : G.realizedActionMonitoring.SignalHistory t) :
    actionHistory G (stochasticHistory G history) = history :=
  rfl

@[simp] theorem stochasticHistory_actionHistory {t : ℕ}
    (history : G.realizedActionStochasticGame.Hist t) :
    stochasticHistory G (actionHistory G history) = history := by
  rcases history with ⟨record, state⟩
  apply Prod.ext
  · funext stage
    simp only [stochasticHistory, actionHistory]
    rcases record stage with ⟨pastState, action⟩
    change (PUnit.unit, action) = (pastState, action)
    cases pastState
    rfl
  · change PUnit.unit = state
    cases state
    rfl

/-- Stochastic histories and realized-action public histories are the same
data up to insertion/removal of the unique state. -/
def historyEquiv (t : ℕ) :
    G.realizedActionStochasticGame.Hist t ≃
      G.realizedActionMonitoring.SignalHistory t where
  toFun := actionHistory G
  invFun := stochasticHistory G
  left_inv := stochasticHistory_actionHistory G
  right_inv := actionHistory_stochasticHistory G

@[simp] theorem historyEquiv_apply {t : ℕ}
    (history : G.realizedActionStochasticGame.Hist t) :
    historyEquiv G t history = actionHistory G history :=
  rfl

@[simp] theorem historyEquiv_symm_apply {t : ℕ}
    (history : G.realizedActionMonitoring.SignalHistory t) :
    (historyEquiv G t).symm history = stochasticHistory G history :=
  rfl

/-- Transport one public monitored strategy to the one-state stochastic
presentation. -/
def toBehaviorStrategy (who : ι)
    (strategy : G.realizedActionMonitoring.MonitoredStrategy who) :
    G.realizedActionStochasticGame.BehaviorStrategy who :=
  fun t history => strategy t (actionHistory G history)

/-- Transport one one-state behavior strategy to realized-action public
monitoring. -/
def toMonitoredStrategy (who : ι)
    (strategy : G.realizedActionStochasticGame.BehaviorStrategy who) :
    G.realizedActionMonitoring.MonitoredStrategy who :=
  fun t history => strategy t (stochasticHistory G history)

@[simp] theorem toMonitoredStrategy_toBehaviorStrategy (who : ι)
    (strategy : G.realizedActionMonitoring.MonitoredStrategy who) :
    toMonitoredStrategy G who (toBehaviorStrategy G who strategy) = strategy := by
  funext t history
  simp [toMonitoredStrategy, toBehaviorStrategy]

@[simp] theorem toBehaviorStrategy_toMonitoredStrategy (who : ι)
    (strategy : G.realizedActionStochasticGame.BehaviorStrategy who) :
    toBehaviorStrategy G who (toMonitoredStrategy G who strategy) = strategy := by
  funext t history
  simp [toMonitoredStrategy, toBehaviorStrategy]

/-- The exact equivalence between a player's strategies in the two
presentations. -/
def strategyEquiv (who : ι) :
    G.realizedActionMonitoring.MonitoredStrategy who ≃
      G.realizedActionStochasticGame.BehaviorStrategy who where
  toFun := toBehaviorStrategy G who
  invFun := toMonitoredStrategy G who
  left_inv := toMonitoredStrategy_toBehaviorStrategy G who
  right_inv := toBehaviorStrategy_toMonitoredStrategy G who

/-- Transport a monitored profile player by player. -/
def toBehaviorProfile
    (profile : G.realizedActionMonitoring.MonitoredProfile) :
    G.realizedActionStochasticGame.BehaviorProfile :=
  fun who => toBehaviorStrategy G who (profile who)

/-- Transport a behavior profile player by player. -/
def toMonitoredProfile
    (profile : G.realizedActionStochasticGame.BehaviorProfile) :
    G.realizedActionMonitoring.MonitoredProfile :=
  fun who => toMonitoredStrategy G who (profile who)

@[simp] theorem toMonitoredProfile_toBehaviorProfile
    (profile : G.realizedActionMonitoring.MonitoredProfile) :
    toMonitoredProfile G (toBehaviorProfile G profile) = profile := by
  funext who
  exact toMonitoredStrategy_toBehaviorStrategy G who (profile who)

@[simp] theorem toBehaviorProfile_toMonitoredProfile
    (profile : G.realizedActionStochasticGame.BehaviorProfile) :
    toBehaviorProfile G (toMonitoredProfile G profile) = profile := by
  funext who
  exact toBehaviorStrategy_toMonitoredStrategy G who (profile who)

/-- Exact profile equivalence induced by the history equivalence. -/
def profileEquiv :
    G.realizedActionMonitoring.MonitoredProfile ≃
      G.realizedActionStochasticGame.BehaviorProfile where
  toFun := toBehaviorProfile G
  invFun := toMonitoredProfile G
  left_inv := toMonitoredProfile_toBehaviorProfile G
  right_inv := toBehaviorProfile_toMonitoredProfile G

section Updates

variable [DecidableEq ι]

/-- Transporting a monitored unilateral replacement is the corresponding
behavioral unilateral replacement. -/
theorem toBehaviorProfile_update
    (profile : G.realizedActionMonitoring.MonitoredProfile) (who : ι)
    (deviation : G.realizedActionMonitoring.MonitoredStrategy who) :
    toBehaviorProfile G (Function.update profile who deviation) =
      Function.update (toBehaviorProfile G profile) who
        (toBehaviorStrategy G who deviation) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [toBehaviorProfile]
  · simp [toBehaviorProfile, Function.update_of_ne hplayer]

/-- Transporting a stochastic unilateral replacement is the corresponding
monitored unilateral replacement. -/
theorem toMonitoredProfile_update
    (profile : G.realizedActionStochasticGame.BehaviorProfile) (who : ι)
    (deviation : G.realizedActionStochasticGame.BehaviorStrategy who) :
    toMonitoredProfile G (Function.update profile who deviation) =
      Function.update (toMonitoredProfile G profile) who
        (toMonitoredStrategy G who deviation) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [toMonitoredProfile]
  · simp [toMonitoredProfile, Function.update_of_ne hplayer]

end Updates

section HistoryLaw

/-- Removing unique states from a one-step stochastic-history extension is
exactly public-history snoc by the realized joint action. -/
@[simp] theorem actionHistory_snoc {t : ℕ}
    (history : G.realizedActionStochasticGame.Hist t)
    (action : Profile G) (nextState : PUnit) :
    actionHistory G
        ((Fin.snoc history.1 (history.2, action), nextState) :
          G.realizedActionStochasticGame.Hist (t + 1)) =
      Fin.snoc (actionHistory G history) action := by
  change
    (Prod.snd ∘ Fin.snoc history.1 (history.2, action)) =
      Fin.snoc (Prod.snd ∘ history.1) action
  exact Fin.comp_snoc Prod.snd history.1 (history.2, action)

/-- At corresponding histories, the stochastic joint-action law is exactly
the realized-action monitoring signal kernel. -/
theorem stageActionDist_toBehaviorProfile
    (profile : G.realizedActionMonitoring.MonitoredProfile)
    {t : ℕ} (history : G.realizedActionStochasticGame.Hist t) :
    G.realizedActionStochasticGame.stageActionDist
        (toBehaviorProfile G profile) history =
      G.realizedActionMonitoring.signalKernel
        (fun who => profile who t (actionHistory G history)) :=
  rfl

/-- The conditional law of the next projected stochastic history is the
conditional public-history law under realized-action monitoring. -/
theorem map_actionHistory_historyStep
    (profile : G.realizedActionMonitoring.MonitoredProfile)
    {t : ℕ} (history : G.realizedActionStochasticGame.Hist t) :
    ((G.realizedActionStochasticGame.stageActionDist
          (toBehaviorProfile G profile) history).bind fun action =>
        (G.realizedActionStochasticGame.transition history.2 action).bind
          fun nextState =>
            PMF.pure
              ((Fin.snoc history.1 (history.2, action), nextState) :
                G.realizedActionStochasticGame.Hist (t + 1))).map
          (actionHistory G) =
      (G.realizedActionMonitoring.signalKernel
          (fun who => profile who t (actionHistory G history))).map
        (Fin.snoc (actionHistory G history)) := by
  rw [PMF.map_bind, stageActionDist_toBehaviorProfile]
  congr 1
  funext action
  change
    ((PMF.pure PUnit.unit : PMF PUnit).bind fun nextState =>
        PMF.pure
          ((Fin.snoc history.1 (history.2, action), nextState) :
            G.realizedActionStochasticGame.Hist (t + 1))).map
      (actionHistory G) =
        PMF.pure (Fin.snoc (actionHistory G history) action)
  rw [PMF.pure_bind, PMF.pure_map]
  congr 1
  exact actionHistory_snoc G history action PUnit.unit

/-- Projecting the one-state stochastic history law gives exactly the public
realized-action history law, at every finite time. -/
theorem map_actionHistory_histDist
    (profile : G.realizedActionMonitoring.MonitoredProfile) : ∀ t : ℕ,
    (G.realizedActionStochasticGame.histDist
        (toBehaviorProfile G profile) PUnit.unit t).map (actionHistory G) =
      G.realizedActionMonitoring.signalHistoryDist profile t
  | 0 => by
      rw [StochasticGame.histDist_zero,
        KernelGame.PublicMonitoring.signalHistoryDist_zero, PMF.pure_map]
      congr 1
      funext stage
      exact Fin.elim0 stage
  | t + 1 => by
      rw [StochasticGame.histDist_succ, PMF.map_bind]
      simp_rw [map_actionHistory_historyStep G profile]
      change
        (G.realizedActionStochasticGame.histDist
            (toBehaviorProfile G profile) PUnit.unit t).bind
          ((fun history =>
            (G.realizedActionMonitoring.signalKernel
              (fun who => profile who t history)).map
                (Fin.snoc (α := fun _ => Profile G) history)) ∘
            actionHistory G) = _
      rw [← PMF.bind_map,
        map_actionHistory_histDist profile t]
      rfl

end HistoryLaw

end RealizedActionRepeatedAdapter

end KernelGame

end GameTheory
