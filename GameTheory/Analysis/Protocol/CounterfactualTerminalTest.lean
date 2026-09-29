/-
# Counterfactual regret on terminal play without a horizon

The countdown game has one Boolean decision at the root followed by a
geometric countdown, so no uniform horizon bounds play. Counterfactual regret
scored by terminal play still decomposes the root gain exactly: switching the
root choice from `false` to `true` gains one, and so does its counterfactual
regret at the root site.
-/

import GameTheory.Analysis.Protocol.CounterfactualDecomposition
import GameTheory.Analysis.Protocol.WellFoundedTerminalEquilibriumTest

noncomputable section

namespace GameTheory.Tests.CounterfactualTerminal

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.Tests.WellFoundedTerminalGate

/-- The root decision's history fiber is the initial history alone. -/
instance : Unique (information.InformationHistory () rootSite.1) where
  default := ⟨execution.initHistory, rfl⟩
  uniq history := Subtype.ext (informationHistory_eq_initHistory rootSite history)

/-- The history certificate of the countdown game. -/
abbrev certificate : execution.WellFoundedHistories := wellFounded.wellFoundedHistories

/-- Terminal play from the root. -/
def root (policies : (i : Unit) → information.BehavioralPolicy i) : PMF execution.History :=
  information.runBehavioralTerminalFrom certificate policies execution.initHistory

/-- The reference profile chooses `false` at the root. -/
def baseline (_who : Unit) : information.BehavioralPolicy () := fallbackPolicy

theorem update_baseline :
    Profile.update (sig := information.behavioralSignature) baseline () pureTruePolicy =
      fun _ => pureTruePolicy := by
  funext who
  cases who
  simp

/-- Terminal play under a whole policy is scored by its root choice alone. -/
theorem root_value (policy : information.BehavioralPolicy ()) :
    expect (root fun _ => policy) (terminalPayoff ()) =
      expect (policy 1) fun choice : information.Choice () 1 =>
        if choice.1 = some true then (1 : ℝ) else 0 := by
  rw [root, ← terminal_context_outcome_root (assessment 0) rootSite policy]
  exact terminal_context_value_eq_choice (assessment 0) rootSite policy

theorem root_integrable (policies : (i : Unit) → information.BehavioralPolicy i) :
    PayoffIntegrable (root policies) (terminalPayoff ()) :=
  information.payoffIntegrable_runBehavioralTerminalFrom_of_bounded_terminal certificate
    policies (terminalPayoff ()) 1 (terminalPayoff_bound ()) execution.initHistory

theorem rootSite_commonDepth : InformationSite.CommonDepth information rootSite 0 :=
  fun history => by rw [informationHistory_eq_initHistory rootSite history]; rfl

theorem pureTrue_agrees_off_root {info : ℝ} (hne : info ≠ rootSite.1) :
    pureTruePolicy info = baseline () info := by
  have hinfo : info ≠ 1 := hne
  simp [pureTruePolicy, baseline, fallbackPolicy, trueChoice, fallbackChoice, hinfo]

theorem ownReach_root (history : information.InformationHistory () rootSite.1) :
    information.playerReachProbability baseline () history.1.trace = 1 := by
  rw [Subsingleton.elim history default]
  exact information.playerReachProbability_start baseline ()

/-- **Root decomposition on terminal play.** The generic decomposition applies
with the terminal runner, which splits at every depth and reads only reachable
histories, although no horizon bounds play. -/
theorem rootGain_eq_counterfactualRegret :
    expect (root fun _ => pureTruePolicy) (terminalPayoff ()) -
        expect (root baseline) (terminalPayoff ()) =
      1 * information.counterfactualRegret baseline () rootSite (terminalPayoff ())
        (information.runBehavioralTerminalFrom certificate) pureTruePolicy := by
  rw [← update_baseline]
  exact information.rootGain_eq_ownReach_mul_counterfactualRegret baseline () rootSite
    pureTruePolicy 0 rootSite_commonDepth pureTrue_agrees_off_root 1 ownReach_root
    (terminalPayoff ()) root (information.runBehavioralTerminalFrom certificate)
    (information.runnerReadsReachable_terminal certificate)
    (fun policies => information.runBehavioralTerminalFrom_init_eq_bind certificate
      policies 0)
    (root_integrable _) (root_integrable _)

/-- Switching the root choice to `true` has counterfactual regret one on
terminal play. -/
theorem counterfactualRegret_eq_one :
    information.counterfactualRegret baseline () rootSite (terminalPayoff ())
      (information.runBehavioralTerminalFrom certificate) pureTruePolicy = 1 := by
  have hgain := rootGain_eq_counterfactualRegret
  rw [one_mul, root_value, show root baseline = root fun _ => fallbackPolicy from rfl,
    root_value] at hgain
  rw [← hgain]
  simp [pureTruePolicy, fallbackPolicy, trueChoice, fallbackChoice, expect_pure]

end GameTheory.Tests.CounterfactualTerminal
