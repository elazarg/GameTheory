/-
# Counterfactual regret on terminal play without a horizon

The countdown game has one Boolean decision at the root followed by a
geometric countdown, so no uniform horizon bounds play. Counterfactual regret
scored by terminal play still decomposes the root gain exactly: switching the
root choice from `false` to `true` gains one, and so does its counterfactual
regret at the root site.

No truncation of play recovers that regret. After any number of steps some
play chosen `true` is still counting down and has earned nothing, so every
truncated counterfactual regret falls strictly short of the terminal one.
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

/-! ## Every truncation underestimates the regret -/

/-- The profile that chooses `true` at the root. -/
def pureTrueProfile (_who : Unit) : information.BehavioralPolicy () := pureTruePolicy

theorem reward_nonneg (final : execution.History) : 0 ≤ terminalPayoff () final := by
  rcases final with ⟨state, trace⟩
  cases state with
  | root => simp [terminalPayoff, State.reward]
  | countdown chosen remaining => simp [terminalPayoff, State.reward]
  | done chosen => cases chosen <;> norm_num [terminalPayoff, State.reward]

theorem reward_abs_le_one (final : execution.History) : |terminalPayoff () final| ≤ 1 := by
  rw [abs_of_nonneg (reward_nonneg final)]
  exact terminalPayoff_le_one final

/-- One realized step whose action the pure `true` profile takes is in the
support of one step of play. -/
theorem extend_mem_support (history : execution.History)
    (joint : Unit → Option Bool) (isLegal : execution.Legal history.state joint)
    {reached : State} (realized : reached ∈ (execution.step history.state ⟨joint, isLegal⟩).support)
    (hchoice : ∀ i, (⟨joint i, (information.menu_adequate i history.trace (joint i)).mpr
        (execution.legalOption_of_legal isLegal i)⟩ :
        information.Choice i (information.infoOf i history.trace)) ∈
          (pureTrueProfile i (information.infoOf i history.trace)).support) :
    history.extend isLegal realized ∈
      (information.runBehavioralFrom pureTrueProfile 1 history).support := by
  have hterm : ¬ execution.terminal history.state := isLegal.1
  rw [information.runBehavioralFrom_succ_of_not_terminal pureTrueProfile 0 hterm,
    PMF.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨⟨joint, isLegal⟩,
    information.mem_support_behavioralJoint pureTrueProfile history.trace hterm joint
      isLegal hchoice, ?_⟩
  rw [PMF.support_bindOnSupport]
  refine Set.mem_iUnion₂.mpr ⟨reached, realized, ?_⟩
  simp [InformationModel.runBehavioralFrom]

/-- Once the root decision has passed, the information state is `0`. -/
theorem infoOf_countdownTrace (chosen : Bool) (elapsed remaining : ℕ) :
    signals.infoOf () (countdownTrace chosen elapsed remaining) = 0 := by
  cases elapsed <;> rfl

/-- After `elapsed + 1` steps, play that chose `true` and drew a long enough
countdown is still counting down. -/
theorem countdown_mem_support :
    ∀ (elapsed remaining : ℕ),
      (⟨.countdown true remaining, countdownTrace true elapsed remaining⟩ :
          execution.History) ∈
        (information.runBehavioralFrom pureTrueProfile (elapsed + 1)
          execution.initHistory).support
  | 0, remaining => by
      refine extend_mem_support execution.initHistory (rootJoint true)
        (rootJoint_legal true) (rootCountdown_realized true remaining) ?_
      intro i
      cases i
      simp [pureTrueProfile, pureTruePolicy, trueChoice, rootJoint,
        ExecutionProtocol.initHistory]
      exact Set.mem_singleton_iff.mpr rfl
  | elapsed + 1, remaining => by
      rw [information.runBehavioralFrom_add pureTrueProfile (elapsed + 1) 1, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨_, countdown_mem_support elapsed (remaining + 1), ?_⟩
      refine extend_mem_support _ execution.noop (countdownNoop_legal true (remaining + 1))
        (countdownNext_realized true remaining) ?_
      intro i
      cases i
      simp [pureTrueProfile, pureTruePolicy, trueChoice, ExecutionProtocol.noop,
        infoOf_countdownTrace]

/-- Choosing `true` earns strictly less than one when play is cut off after any
number of steps. -/
theorem truncated_value_lt_one (fuel : ℕ) :
    expect (information.runBehavioralFrom pureTrueProfile fuel execution.initHistory)
      (terminalPayoff ()) < 1 := by
  let law := information.runBehavioralFrom pureTrueProfile fuel execution.initHistory
  have hlt : ∀ atom ∈ law.support, terminalPayoff () atom = 0 →
      expect law (terminalPayoff ()) < 1 := by
    intro atom hatom hzero
    have h := expect_lt_of_mem_support (μ := law) (f := terminalPayoff ()) (g := fun _ => 1)
      (payoffIntegrable_of_bounded law _ reward_abs_le_one)
      (payoffIntegrable_constant law 1) (fun final _ => terminalPayoff_le_one final)
      atom hatom (by rw [hzero]; norm_num)
    rwa [expect_constant] at h
  cases fuel with
  | zero =>
      exact hlt execution.initHistory (by simp [law, InformationModel.runBehavioralFrom])
        (by simp [terminalPayoff, State.reward])
  | succ elapsed =>
      exact hlt _ (countdown_mem_support elapsed 0) (by simp [terminalPayoff, State.reward])

/-- **Truncation always underestimates.** For every number of steps, the
counterfactual regret of switching the root choice to `true`, scored by play cut
off after those steps, is strictly below its value on terminal play. -/
theorem truncated_counterfactualRegret_lt (fuel : ℕ) :
    information.counterfactualRegret baseline () rootSite (terminalPayoff ())
        (information.truncatedRunner fuel) pureTruePolicy <
      information.counterfactualRegret baseline () rootSite (terminalPayoff ())
        (information.runBehavioralTerminalFrom certificate) pureTruePolicy := by
  rw [counterfactualRegret_eq_one,
    information.counterfactualRegret_eq_sum_behavioralContinuationGain, Fintype.sum_unique]
  have hreach : information.counterfactualReachProbability baseline ()
      (default : information.InformationHistory () rootSite.1).1.trace = 1 :=
    information.counterfactualReachProbability_start baseline ()
  have htrue : Profile.update (sig := information.behavioralSignature) baseline ()
      pureTruePolicy = pureTrueProfile := update_baseline
  have hfalse : Profile.update (sig := information.behavioralSignature) baseline ()
      (baseline ()) = baseline := Profile.update_eq_self _ _
  rw [hreach, one_mul, htrue, hfalse]
  have hvalue := truncated_value_lt_one fuel
  have hnonneg : 0 ≤ expect (information.truncatedRunner fuel baseline
      (default : information.InformationHistory () rootSite.1).1) (terminalPayoff ()) :=
    expect_nonneg _ _ fun final _ => reward_nonneg final
  change expect (information.runBehavioralFrom pureTrueProfile fuel execution.initHistory)
      (terminalPayoff ()) - _ < 1
  linarith

end GameTheory.Tests.CounterfactualTerminal
