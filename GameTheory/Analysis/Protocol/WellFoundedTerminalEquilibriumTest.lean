/-
# Sequential equilibrium without a uniform horizon

The initial Boolean decision is followed by a random finite countdown. The
terminal reward retains that decision. A pure-true policy with a vanishing
false-action tremble has approximately optimal whole-policy continuations at
the sole decision site.
-/

import GameTheory.Analysis.Protocol.WellFoundedTerminalAssessmentTest
import GameTheory.Analysis.Protocol.SequentialLimits
import GameTheory.Math.Probability.ExpectationMixture

noncomputable section

namespace GameTheory.Tests.WellFoundedTerminalGate

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Filter

/-- The countdown cannot change the Boolean selected at the root. -/
theorem countdown_terminal_chosen (chooser : execution.RandomizedChooser)
    (chosen : Bool) :
    ∀ remaining (trace : Trace execution (.countdown chosen remaining))
      (final : execution.History),
      final ∈ (execution.randomizedBackwardLaw wellFounded.wellFoundedHistories chooser
        ⟨.countdown chosen remaining, trace⟩).support →
      final.state = .done chosen := by
  intro remaining
  induction remaining with
  | zero =>
      intro trace final hfinal
      have hnot : ¬ execution.terminal (.countdown chosen 0) := by
        simp
      rw [execution.randomizedBackwardLaw_of_not_terminal hnot,
        PMF.support_bind] at hfinal
      obtain ⟨draw, _, hstep⟩ := Set.mem_iUnion₂.mp hfinal
      rw [PMF.support_bindOnSupport] at hstep
      obtain ⟨target, realized, hchild⟩ := Set.mem_iUnion₂.mp hstep
      have htarget : target = .done chosen := by
        simpa [execution] using realized
      subst target
      rw [execution.randomizedBackwardLaw_of_terminal
        (by exact ⟨chosen, rfl⟩), PMF.mem_support_pure_iff] at hchild
      subst final
      rfl
  | succ remaining ih =>
      intro trace final hfinal
      have hnot : ¬ execution.terminal (.countdown chosen (remaining + 1)) := by
        simp
      rw [execution.randomizedBackwardLaw_of_not_terminal hnot,
        PMF.support_bind] at hfinal
      obtain ⟨draw, _, hstep⟩ := Set.mem_iUnion₂.mp hfinal
      rw [PMF.support_bindOnSupport] at hstep
      obtain ⟨target, realized, hchild⟩ := Set.mem_iUnion₂.mp hstep
      have htarget : target = .countdown chosen remaining := by
        simpa [execution] using realized
      subst target
      exact ih _ final hchild

/-- The random duration does not alter the terminal reward. -/
theorem countdown_reward_law (chooser : execution.RandomizedChooser)
    (chosen : Bool) (remaining : ℕ)
    (trace : Trace execution (.countdown chosen remaining)) :
    PMF.map (fun final : execution.History => final.state.reward)
      (execution.randomizedBackwardLaw wellFounded.wellFoundedHistories chooser
        ⟨.countdown chosen remaining, trace⟩) =
      PMF.pure (if chosen then (1 : ℝ) else 0) := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro value hvalue
  rw [PMF.mem_support_map_iff] at hvalue
  obtain ⟨final, hfinal, rfl⟩ := hvalue
  have hstate := countdown_terminal_chosen chooser chosen remaining trace final hfinal
  cases chosen <;> simp [State.reward, hstate]

/-- Each supported root draw starts a countdown carrying its chosen reward. -/
theorem root_step_reward_law (chooser : execution.RandomizedChooser)
    (draw : {joint : Unit → Option Bool // execution.Legal .root joint}) :
    PMF.map (fun final : execution.History => final.state.reward)
      ((execution.step .root draw).bindOnSupport fun _target realized =>
        execution.randomizedBackwardLaw wellFounded.wellFoundedHistories chooser
          (execution.initHistory.extend draw.2 realized)) =
      PMF.pure (if (draw.1 ()).getD false then (1 : ℝ) else 0) := by
  apply map_bindOnSupport_const
  intro target realized
  have htarget : ∃ remaining,
      target = .countdown ((draw.1 ()).getD false) remaining := by
    rw [PMF.mem_support_map_iff] at realized
    obtain ⟨remaining, _, hEq⟩ := realized
    exact ⟨remaining, hEq.symm⟩
  obtain ⟨remaining, rfl⟩ := htarget
  exact countdown_reward_law chooser ((draw.1 ()).getD false) remaining _

/-- The root reward law is the law of the root's Boolean action. -/
theorem root_reward_law (chooser : execution.RandomizedChooser) :
    PMF.map (fun final : execution.History => final.state.reward)
      (execution.randomizedBackwardLaw wellFounded.wellFoundedHistories chooser
        execution.initHistory) =
    PMF.map (fun draw => if (draw.1 ()).getD false then (1 : ℝ) else 0)
      (chooser execution.initHistory (by simp [execution])) := by
  rw [execution.randomizedBackwardLaw_of_not_terminal
    (by simp [execution]), PMF.map_bind]
  calc
    _ = (chooser execution.initHistory (by simp [execution])).bind
        (fun draw => PMF.pure
          (if (draw.1 ()).getD false then (1 : ℝ) else 0)) := by
      apply bind_congr_on_support
      intro draw _
      exact root_step_reward_law chooser draw
    _ = _ := (PMF.bind_pure_comp _ _).symm

/-- Every belief at a decision site is concentrated on the sole root history. -/
theorem belief_bind_root (assessment : information.BehavioralAssessment)
    (site : information.InformationSite ()) {α : Type*}
    (kernel : execution.History → PMF α) :
    ((assessment.belief () site).bind fun history => kernel history.1) =
      kernel execution.initHistory := by
  let rootHistory : information.InformationHistory () site.1 :=
    Classical.choose site.2
  have hsub : Subsingleton (information.InformationHistory () site.1) :=
    ⟨fun first second => Subtype.ext
      ((informationHistory_eq_initHistory site first).trans
        (informationHistory_eq_initHistory site second).symm)⟩
  rw [@eq_pure_of_subsingleton _ hsub (assessment.belief () site) rootHistory,
    PMF.pure_bind]
  exact congrArg kernel (informationHistory_eq_initHistory site rootHistory)

/-- In this one-player fixture, a whole-policy replacement is that policy. -/
theorem update_eq (assessment : information.BehavioralAssessment)
    (alternative : information.BehavioralPolicy ()) :
    Profile.update (sig := information.behavioralSignature)
      assessment.strategy () alternative = (fun _ => alternative) := by
  funext who
  cases who
  simp

def terminalPayoff (_ : Unit) (final : execution.History) : ℝ :=
  final.state.reward

set_option backward.isDefEq.respectTransparency false in
/-- A terminal continuation starts at the root under the replacement policy. -/
theorem terminal_context_outcome_root
    (assessment : information.BehavioralAssessment)
    (site : information.InformationSite ())
    (alternative : information.BehavioralPolicy ()) :
    (assessment.continuationContext wellFounded.wellFoundedHistories site
      (terminalPayoff ())).outcome alternative =
    information.runBehavioralTerminalFrom wellFounded.wellFoundedHistories
      (fun _ => alternative) execution.initHistory := by
  simpa only [InformationModel.BehavioralAssessment.continuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    Context.ofBelief, terminalPayoff, update_eq assessment alternative] using
    belief_bind_root assessment site
      (fun history => information.runBehavioralTerminalFrom wellFounded.wellFoundedHistories
        (fun _ => alternative) history)

/-- The terminal payoff is the selected Boolean reward. -/
theorem terminalPayoff_bound (_ : Unit) (final : execution.History)
    (_hterminal : execution.terminal final.state) :
    |terminalPayoff () final| ≤ 1 := by
  rcases final with ⟨state, trace⟩
  cases state with
  | root => simp [terminalPayoff, State.reward]
  | countdown chosen remaining => simp [terminalPayoff, State.reward]
  | done chosen => cases chosen <;> norm_num [terminalPayoff, State.reward]

theorem terminalPayoff_le_one (final : execution.History) :
    terminalPayoff () final ≤ 1 := by
  rcases final with ⟨state, trace⟩
  cases state with
  | root => simp [terminalPayoff, State.reward]
  | countdown chosen remaining => simp [terminalPayoff, State.reward]
  | done chosen => cases chosen <;> norm_num [terminalPayoff, State.reward]

/-- A whole-policy terminal continuation has the root choice's reward law. -/
theorem terminal_context_reward_law
    (assessment : information.BehavioralAssessment)
    (site : information.InformationSite ())
    (alternative : information.BehavioralPolicy ()) :
    PMF.map (terminalPayoff ())
      ((assessment.continuationContext wellFounded.wellFoundedHistories site
        (terminalPayoff ())).outcome alternative) =
    PMF.map (fun choice : information.Choice () 1 =>
      if choice.1 = some true then (1 : ℝ) else 0)
      (alternative 1) := by
  rw [terminal_context_outcome_root assessment site alternative]
  unfold InformationModel.runBehavioralTerminalFrom
  calc
    _ = PMF.map
          (fun draw => if (draw.1 ()).getD false then (1 : ℝ) else 0)
          (information.randomizedChooser (fun _ => alternative)
            execution.initHistory (by simp [execution])) := by
          have hreward : terminalPayoff () =
              (fun final : execution.History => final.state.reward) := rfl
          rw [hreward]
          exact root_reward_law
            (information.randomizedChooser (fun _ => alternative))
    _ = _ := root_behavioral_reward_law (fun _ => alternative)

/-- The terminal value equals the expected reward of the whole policy's
root choice; the unbounded random duration disappears from the value. -/
theorem terminal_context_value_eq_choice
    (assessment : information.BehavioralAssessment)
    (site : information.InformationSite ())
    (alternative : information.BehavioralPolicy ()) :
    (assessment.continuationContext wellFounded.wellFoundedHistories site
      (terminalPayoff ())).value alternative =
    expect (alternative 1)
      (fun choice : information.Choice () 1 =>
        if choice.1 = some true then (1 : ℝ) else 0) := by
  let rewardChoice : information.Choice () 1 → ℝ :=
    fun choice => if choice.1 = some true then 1 else 0
  have hvalue := expect_observed_law_eq
    ((assessment.continuationContext wellFounded.wellFoundedHistories site
      (terminalPayoff ())).outcome alternative)
    (alternative 1) (terminalPayoff ()) rewardChoice id
    (terminal_context_reward_law assessment site alternative)
  simpa [Context.value, Function.comp_def, rewardChoice,
    InformationModel.BehavioralAssessment.continuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    Context.ofBelief] using hvalue

/-- The incumbent's exact terminal value is one minus its false-action tremble. -/
theorem incumbent_terminal_value (n : ℕ)
    (site : information.InformationSite ()) :
    ((assessment n).continuationContext wellFounded.wellFoundedHistories site
      (terminalPayoff ())).value ((assessment n).strategy ()) =
      1 - trembleWeight n := by
  let rewardChoice : information.Choice () 1 → ℝ :=
    fun choice => if choice.1 = some true then 1 else 0
  have hmix := expect_mix (trembleWeight n) (trembleWeight_pos n).le
    (trembleWeight_le_one n) (fallbackPolicy 1) (pureTruePolicy 1)
    rewardChoice (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _)
  calc
    _ = expect (strategy n () 1) rewardChoice := by
          simpa only [assessment, InformationModel.bayesAssessment_strategy,
            rewardChoice] using
            terminal_context_value_eq_choice (assessment n) site
              ((assessment n).strategy ())
    _ = trembleWeight n * 0 + (1 - trembleWeight n) * 1 := by
          simpa [strategy, repair, fallbackPolicy, pureTruePolicy,
            fallbackChoice, trueChoice, rewardChoice, expect_pure] using hmix
    _ = 1 - trembleWeight n := by ring

/-- Every repaired whole-policy deviation gains at most the vanishing
tremble error over the incumbent. -/
theorem repaired_terminal_approximate_optimality
    (n : ℕ) (i : Unit) (site : information.InformationSite i)
    (alternative : information.BehavioralPolicy i) :
    ((assessment n).continuationContext wellFounded.wellFoundedHistories site
      (terminalPayoff i)).value (repair n i alternative) ≤
    ((assessment n).continuationContext wellFounded.wellFoundedHistories site
      (terminalPayoff i)).value ((assessment n).strategy i) +
      trembleWeight n := by
  cases i
  have hupper :
      ((assessment n).continuationContext wellFounded.wellFoundedHistories site
        (terminalPayoff ())).value (repair n () alternative) ≤ 1 := by
    apply expect_le_const _ _
      ((assessment n).continuationContext_integrable_of_bounded_terminal
        wellFounded.wellFoundedHistories site (terminalPayoff ()) 1 (terminalPayoff_bound ())
        (repair n () alternative))
    intro final _
    exact terminalPayoff_le_one final
  rw [incumbent_terminal_value n site]
  linarith

instance : ∀ i : Unit, Countable (information.InformationSite i) :=
  fun i => by cases i; infer_instance

/-- A well-founded stochastic protocol with unbounded finite play lengths has
a sequential equilibrium for its nonconstant Boolean reward. -/
theorem exists_sequential_equilibrium :
    ∃ target : information.BehavioralAssessment,
      target.IsSequentiallyRational wellFounded.wellFoundedHistories terminalPayoff ∧
        target.IsSequentiallyConsistent decisionInformationAntichain := by
  exact information.exists_sequentialEquilibrium_of_uniformlyTight
    wellFounded.wellFoundedHistories decisionInformationAntichain assessment
    assessment_strategy_uniformlyTight assessment_belief_uniformlyTight
    assessment_fullyMixed assessment_bayesConsistent repair
    repair_convergesPointwise_on_sites terminalPayoff (fun _ => 1)
    (by intro i; norm_num) terminalPayoff_bound trembleWeight
    trembleWeight_tendsto_zero repaired_terminal_approximate_optimality

theorem terminal_reward_nonconstant :
    State.reward (.done true) ≠ State.reward (.done false) := by
  norm_num [State.reward]

/-- The existence result holds although no uniform horizon bounds play. -/
theorem unbounded_sequential_equilibrium :
    (¬ ∃ horizon, execution.BoundedHorizon horizon) ∧
      ∃ target : information.BehavioralAssessment,
        target.IsSequentiallyRational wellFounded.wellFoundedHistories terminalPayoff ∧
          target.IsSequentiallyConsistent decisionInformationAntichain :=
  ⟨no_boundedHorizon, exists_sequential_equilibrium⟩

end GameTheory.Tests.WellFoundedTerminalGate
