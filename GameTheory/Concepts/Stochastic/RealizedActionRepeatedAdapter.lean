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

namespace PublicMonitoring

variable {G : KernelGame ι}

/-- A monitored payoff witness at one accuracy: one profile and one threshold
work simultaneously for approximate Nash and target delivery at every later
horizon.  This small wrapper makes the quantifier order explicit. -/
structure UniformPayoffWitnessAt (M : G.PublicMonitoring) [DecidableEq ι]
    (target : Payoff ι) (ε : ℝ) where
  profile : M.MonitoredProfile
  threshold : ℕ
  valid : ∀ T, threshold ≤ T →
    M.IsεFiniteRepeatedNash T ε profile ∧
      ∀ who, |M.finiteAveragePayoff T profile who - target who| ≤ ε

/-- Payoff-level uniform equilibrium under public monitoring, with exactly the
accuracy-indexed profile quantifiers used by
`StochasticGame.IsUniformEquilibriumPayoff`.

This is intentionally distinct from `IsUniformEquilibrium`, which fixes one
profile for every accuracy and asks separately for payoff convergence. -/
def IsUniformEquilibriumPayoff (M : G.PublicMonitoring) [DecidableEq ι]
    (target : Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → Nonempty (M.UniformPayoffWitnessAt target ε)

/-- A fixed monitored uniform equilibrium with specified long-run payoff is a
payoff-level uniform equilibrium.  The converse would require a coherent
selection/compactness theorem and is not asserted. -/
theorem IsUniformEquilibrium.isUniformEquilibriumPayoff_of_hasLongRunAveragePayoff
    {M : G.PublicMonitoring} [Fintype ι] [DecidableEq ι]
    {profile : M.MonitoredProfile} {target : Payoff ι}
    (hequilibrium : M.IsUniformEquilibrium profile)
    (hpayoff : M.HasLongRunAveragePayoff profile target) :
    M.IsUniformEquilibriumPayoff target := by
  intro ε hε
  obtain ⟨nashThreshold, hnash⟩ := hequilibrium.2 ε hε
  have hclose : ∀ᶠ T in Filter.atTop,
      ∀ who, |M.finiteAveragePayoff T profile who - target who| < ε := by
    apply Filter.eventually_all.mpr
    intro who
    have hball := (hpayoff who).eventually
      (Metric.ball_mem_nhds (target who) hε)
    filter_upwards [hball] with T hT
    simpa only [Metric.mem_ball, Real.dist_eq] using hT
  obtain ⟨payoffThreshold, hpayoffThreshold⟩ :=
    Filter.eventually_atTop.1 hclose
  refine ⟨{
    profile := profile
    threshold := max nashThreshold payoffThreshold
    valid := fun T hT => ?_ }⟩
  constructor
  · exact hnash T (le_trans (Nat.le_max_left _ _) hT)
  · intro who
    exact le_of_lt
      (hpayoffThreshold T (le_trans (Nat.le_max_right _ _) hT) who)

/-- Every fixed-profile monitored uniform equilibrium therefore supplies some
payoff-level uniform equilibrium payoff. -/
theorem IsUniformEquilibrium.exists_isUniformEquilibriumPayoff
    {M : G.PublicMonitoring} [Fintype ι] [DecidableEq ι]
    {profile : M.MonitoredProfile}
    (hequilibrium : M.IsUniformEquilibrium profile) :
    ∃ target : Payoff ι, M.IsUniformEquilibriumPayoff target := by
  obtain ⟨target, htarget⟩ := hequilibrium.1
  exact ⟨target,
    hequilibrium.isUniformEquilibriumPayoff_of_hasLongRunAveragePayoff htarget⟩

end PublicMonitoring

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

section Payoffs

variable [Finite G.Outcome]

/-- At corresponding histories, one-state stochastic expected stage payoff is
the mixed-extension expected utility used by the monitored presentation. -/
theorem stageEUAt_toBehaviorProfile
    (profile : G.realizedActionMonitoring.MonitoredProfile)
    {t : ℕ} (history : G.realizedActionStochasticGame.Hist t) (who : ι) :
    G.realizedActionStochasticGame.stageEUAt
        (toBehaviorProfile G profile) history who =
      G.mixedExtension.eu
        (fun player => profile player t (actionHistory G history)) who := by
  unfold StochasticGame.stageEUAt
  rw [stageActionDist_toBehaviorProfile]
  exact (G.mixedExtension_eu
    (fun player => profile player t (actionHistory G history)) who).symm

/-- Expected payoff in each period is preserved by profile transport. -/
theorem expectedStagePayoff_toBehaviorProfile
    (profile : G.realizedActionMonitoring.MonitoredProfile)
    (t : ℕ) (who : ι) :
    G.realizedActionStochasticGame.expectedStagePayoff
        (toBehaviorProfile G profile) PUnit.unit t who =
      G.realizedActionMonitoring.stageEU profile t who := by
  letI : Finite G.mixedExtension.Outcome := ‹Finite G.Outcome›
  obtain ⟨C, hC⟩ :=
    G.mixedExtension.exists_eu_abs_bound_of_finite_outcome who
  unfold StochasticGame.expectedStagePayoff
  simp_rw [stageEUAt_toBehaviorProfile G profile]
  rw [KernelGame.PublicMonitoring.stageEU,
    ← map_actionHistory_histDist G profile t]
  exact
    (Math.ProbabilityMassFunction.expect_pushforward_of_bounded
      (G.realizedActionStochasticGame.histDist
        (toBehaviorProfile G profile) PUnit.unit t)
      (actionHistory G)
      (fun history =>
        G.mixedExtension.eu (fun player => profile player t history) who)
      (fun history => hC (fun player => profile player t history))).symm

variable [∀ who, Finite (G.Strategy who)]

/-- Every finite-average payoff is preserved by the monitored-to-stochastic
profile transport. -/
theorem finiteAveragePayoff_toBehaviorProfile
    (profile : G.realizedActionMonitoring.MonitoredProfile)
    (T : ℕ) (who : ι) :
    G.realizedActionStochasticGame.finiteAveragePayoff PUnit.unit T
        (toBehaviorProfile G profile) who =
      G.realizedActionMonitoring.finiteAveragePayoff T profile who := by
  letI : Finite G.realizedActionStochasticGame.State :=
    inferInstanceAs (Finite PUnit)
  letI (player : ι) :
      Finite (G.realizedActionStochasticGame.Act player) :=
    ‹∀ who, Finite (G.Strategy who)› player
  rw [G.realizedActionStochasticGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  unfold KernelGame.PublicMonitoring.finiteAveragePayoff
  congr 1
  apply Finset.sum_congr rfl
  intro t _ht
  exact expectedStagePayoff_toBehaviorProfile G profile t who

/-- Every finite-average payoff is also preserved in the reverse direction. -/
theorem finiteAveragePayoff_toMonitoredProfile
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    (T : ℕ) (who : ι) :
    G.realizedActionMonitoring.finiteAveragePayoff T
        (toMonitoredProfile G profile) who =
      G.realizedActionStochasticGame.finiteAveragePayoff PUnit.unit T
        profile who := by
  have h := finiteAveragePayoff_toBehaviorProfile G
    (toMonitoredProfile G profile) T who
  simpa using h.symm

end Payoffs

section FiniteHorizonEquilibrium

variable [DecidableEq ι] [Finite G.Outcome]
  [∀ who, Finite (G.Strategy who)]

/-- Finite-horizon approximate Nash is exactly preserved and reflected by the
profile equivalence, including arbitrary whole-strategy unilateral
deviations. -/
theorem isεFiniteRepeatedNash_iff_isεHorizonNash
    (profile : G.realizedActionMonitoring.MonitoredProfile)
    (T : ℕ) (ε : ℝ) :
    G.realizedActionMonitoring.IsεFiniteRepeatedNash T ε profile ↔
      G.realizedActionStochasticGame.IsεHorizonNash PUnit.unit T ε
        (toBehaviorProfile G profile) := by
  constructor
  · intro hNash who deviation
    have h := hNash who (toMonitoredStrategy G who deviation)
    rw [← finiteAveragePayoff_toBehaviorProfile G profile T who,
      ← finiteAveragePayoff_toBehaviorProfile G
        (Function.update profile who
          (toMonitoredStrategy G who deviation)) T who,
      toBehaviorProfile_update,
      toBehaviorStrategy_toMonitoredStrategy] at h
    exact h
  · intro hNash who deviation
    have h := hNash who (toBehaviorStrategy G who deviation)
    rw [finiteAveragePayoff_toBehaviorProfile G profile T who,
      ← toBehaviorProfile_update,
      finiteAveragePayoff_toBehaviorProfile G
        (Function.update profile who deviation) T who] at h
    exact h

/-- Fixed-profile uniform `ε`-equilibrium is exactly preserved and reflected.
This statement has the same profile quantifier on both sides. -/
theorem isUniformεEquilibrium_iff
    (profile : G.realizedActionMonitoring.MonitoredProfile) (ε : ℝ) :
    G.realizedActionMonitoring.IsUniformεEquilibrium ε profile ↔
      G.realizedActionStochasticGame.IsUniformεEquilibrium PUnit.unit ε
        (toBehaviorProfile G profile) := by
  constructor
  · rintro ⟨threshold, hthreshold⟩
    exact ⟨threshold, fun T hT =>
      (isεFiniteRepeatedNash_iff_isεHorizonNash G profile T ε).mp
        (hthreshold T hT)⟩
  · rintro ⟨threshold, hthreshold⟩
    exact ⟨threshold, fun T hT =>
      (isεFiniteRepeatedNash_iff_isεHorizonNash G profile T ε).mpr
        (hthreshold T hT)⟩

omit [DecidableEq ι] in
/-- Coordinatewise long-run payoff convergence is preserved and reflected for
a fixed profile. -/
theorem hasLongRunAveragePayoff_iff
    (profile : G.realizedActionMonitoring.MonitoredProfile)
    (target : Payoff ι) :
    G.realizedActionMonitoring.HasLongRunAveragePayoff profile target ↔
      ∀ who, Filter.Tendsto
        (fun T =>
          G.realizedActionStochasticGame.finiteAveragePayoff PUnit.unit T
            (toBehaviorProfile G profile) who)
        Filter.atTop (nhds (target who)) := by
  constructor
  · intro hlimit who
    simpa only [finiteAveragePayoff_toBehaviorProfile G profile] using
      hlimit who
  · intro hlimit who
    simpa only [finiteAveragePayoff_toBehaviorProfile G profile] using
      hlimit who

end FiniteHorizonEquilibrium

section PayoffLevelEquilibrium

variable [DecidableEq ι] [Finite G.Outcome]
  [∀ who, Finite (G.Strategy who)]

/-- The payoff-level monitored predicate is exactly the stochastic uniform
equilibrium-payoff predicate for the one-state presentation.  Both sides may
choose an accuracy-dependent profile; no fixed-profile compactness is hidden
in this equivalence. -/
theorem isUniformEquilibriumPayoff_iff
    (target : Payoff ι) :
    G.realizedActionMonitoring.IsUniformEquilibriumPayoff target ↔
      G.realizedActionStochasticGame.IsUniformEquilibriumPayoff
        PUnit.unit target := by
  constructor
  · intro hmonitored ε hε
    obtain ⟨witness⟩ := hmonitored ε hε
    refine ⟨toBehaviorProfile G witness.profile, witness.threshold,
      fun T hT => ?_⟩
    obtain ⟨hnash, hpayoff⟩ := witness.valid T hT
    constructor
    · exact
        (isεFiniteRepeatedNash_iff_isεHorizonNash
          G witness.profile T ε).mp hnash
    · intro who
      rw [finiteAveragePayoff_toBehaviorProfile G witness.profile T who]
      exact hpayoff who
  · intro hstochastic ε hε
    obtain ⟨profile, threshold, hvalid⟩ := hstochastic ε hε
    refine ⟨{
      profile := toMonitoredProfile G profile
      threshold := threshold
      valid := fun T hT => ?_ }⟩
    obtain ⟨hnash, hpayoff⟩ := hvalid T hT
    constructor
    · apply
        (isεFiniteRepeatedNash_iff_isεHorizonNash G
          (toMonitoredProfile G profile) T ε).mpr
      simpa using hnash
    · intro who
      rw [finiteAveragePayoff_toMonitoredProfile G profile T who]
      exact hpayoff who

end PayoffLevelEquilibrium

end RealizedActionRepeatedAdapter

end KernelGame

end GameTheory
