import GameTheory.Analysis.Protocol.ComponentCompletion
import GameTheory.Analysis.Protocol.LocalDeviationBounds
import GameTheory.Analysis.Protocol.LocalSimulationLimit
import GameTheory.Analysis.Protocol.SequentialExistenceTest
noncomputable section
namespace GameTheory.Tests.ProtocolComponentCompletion
open GameTheory GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability Filter
open GameTheory.Tests.SequentialExistence

/-- Full-menu trembling components yield a sequential equilibrium from vanishing local gains. -/
theorem unequal_depth_equilibrium_from_components_of_terminal_range
    (terminalPayoff : Unit → execution.History → ℝ)
    (payoffRange : ∀ who final, execution.terminal final.state →
      0 ≤ terminalPayoff who final ∧ terminalPayoff who final ≤ 1) :
    (¬ ∃ depth, InformationSite.CommonDepth information actingSite depth) ∧
      ∃ limit : information.BehavioralAssessment,
        limit.IsSequentialEquilibrium antichain game.wellFoundedHistories terminalPayoff := by
  classical
  let _ : Fintype execution.History := execution.historyFintype treeShaped
  let F := information.agentForm fallback game.wellFoundedHistories
  let _ (agent : information.InformationAgent information.playedInformation) : Fintype
    (F.sig.Strategy agent) :=
    @Fintype.ofFinite _ (information.finite_choice_of_played agent.2.2)
  have inhabited (agent : information.InformationAgent information.playedInformation) : Nonempty
    (F.sig.Strategy agent) :=
    information.nonempty_choice_of_played agent.2.2
  let weight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have positive (n : ℕ) : 0 < weight n := by
    dsimp only [weight]
    positivity
  have small (n : ℕ) : weight n ≤ 1 := by
    dsimp only [weight]
    apply (div_le_one (by positivity : (0 : ℝ) < n + 2)).mpr
    have nonnegative : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have vanishes : Tendsto weight atTop (nhds 0) := by
    have bound := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    convert bound using 1
    funext n
    simp [weight, Nat.cast_add]
    ring
  let reference (agent : information.InformationAgent information.playedInformation) : PMF
    (F.sig.Strategy agent) :=
    PMF.uniformOfFintype _
  let component (n : ℕ) (agent : information.InformationAgent information.playedInformation)
      (part : F.sig.Strategy agent) := mix (weight n) (positive n).le (small n) (reference agent)
        (PMF.pure part)
  have full : ∀ n agent part, FullSupport (component n agent part) := by
    intro n agent part choice
    exact mem_support_mix_left _ _ _ (positive n)
      (PMF.mem_support_uniformOfFintype choice)
  let decisionRecallCertificate := information.decisionRecall_of_perfectRecall perfectRecall
  obtain ⟨weights, sequence, limit, index, played, mixed, bayes, increasing, converges,
      consistent, stepOptimal, limitFacts⟩ :=
    information.exists_consistent_component_completion decisionRecallCertificate fallback
      game.wellFoundedHistories terminalPayoff component full
  have gainBound n who (site : information.InformationSite who)
      (law : PMF (information.Choice who site.1)) :
      ((sequence n).continuationContext game.wellFoundedHistories site
          (terminalPayoff who)).value
          (((sequence n).strategy who).withLaw site.1 law) -
        ((sequence n).continuationContext game.wellFoundedHistories site
          (terminalPayoff who)).value
          ((sequence n).strategy who) ≤ weight n := by
    have bound := (sequence n).withLaw_gain_le_of_trembling_component_bound
      decisionRecallCertificate.actsOnceWhereItMatters game.wellFoundedHistories site
      (terminalPayoff who) 0 1
      (payoffRange who) (reference (information.agentAt site))
      (weight n) (positive n).le (small n) 0
      (fun alternative => sub_nonpos.mpr (stepOptimal n who site alternative)) law
    simpa only [sub_zero, mul_one, zero_add] using bound
  refine ⟨no_commonDepth, limit, ?_⟩
  exact converges.sequentialEquilibrium_of_copied_gain_bounds decisionRecallCertificate
    game.wellFoundedHistories terminalPayoff (fun _ _ => True)
    consistent (fun n _ _ _ => weight (index n))
    (fun _ _ _ _ => vanishes.comp increasing.tendsto_atTop)
    (fun n who site _ law => gainBound (index n) who site law)
    (fun _ _ impossible => False.elim (impossible trivial))

/-- The original hidden-bit payoff is nonconstant on terminal histories. -/
theorem unequal_depth_equilibrium_from_components :
    (¬ ∃ depth, InformationSite.CommonDepth information actingSite depth) ∧
      ∃ limit : information.BehavioralAssessment,
        limit.IsSequentialEquilibrium antichain game.wellFoundedHistories
          GameTheory.Tests.SequentialExistence.payoff := by
  apply unequal_depth_equilibrium_from_components_of_terminal_range
  intro who final _
  cases stateEq : final.state <;> simp [GameTheory.Tests.SequentialExistence.payoff, stateEq]
  all_goals split <;> norm_num

/-- Strictly reward the action `true`, independently of nature's hidden bit. -/
def actionPayoff (_ : Unit) (history : execution.History) : ℝ :=
  match history.state with
  | .terminal _ action => if action then 1 else 0
  | _ => 0

private def actionTerminal (action : Bool) : execution.History :=
  earlyHistory.extend (joint := fun _ => some action) (target := .terminal false action)
    (by
      change execution.Legal (.decision false) (fun _ => some action)
      simp [execution, ExecutionProtocol.Legal, IsLegalJoint,
        State.stopped, State.active])
    (by
      change State.terminal false action ∈ (PMF.pure (.terminal false action)).support
      simp)

/-- Quantitative component comparisons also apply when the two actions have
different terminal rewards, on the actual unequal-depth protocol. -/
theorem strict_action_equilibrium_from_components :
    actionPayoff () (actionTerminal true) = 1 ∧
      actionPayoff () (actionTerminal false) = 0 ∧
      ∃ limit : information.BehavioralAssessment,
        limit.IsSequentialEquilibrium antichain game.wellFoundedHistories actionPayoff := by
  have existsLimit := unequal_depth_equilibrium_from_components_of_terminal_range actionPayoff
    (fun who final _ => by
      cases stateEq : final.state <;> simp [actionPayoff, stateEq]
      all_goals split <;> norm_num)
  exact ⟨by simp [actionPayoff, actionTerminal], by simp [actionPayoff, actionTerminal],
    existsLimit.2⟩

end GameTheory.Tests.ProtocolComponentCompletion
