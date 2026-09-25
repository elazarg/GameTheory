/-
# Continuity of canonical behavioral play

Finite actions and states make bounded execution a finite composition of
continuous probability operations. All evaluations below use the existing
Protocol runner, including its absorbing terminal histories.
-/

import GameTheory.Analysis.Protocol.CounterfactualReach
import GameTheory.Analysis.Protocol.BehavioralBayes
import GameTheory.Math.Probability.Continuity

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} [Fintype ι]
    {E : ExecutionProtocol.{uι, us, ua} ι}
    (M : InformationModel.{uι, us, ua, up, uq, uk} E)
    {X : Type*} [TopologicalSpace X]

/-- Behavioral joint masses are finite products of local policy masses. -/
theorem continuous_behavioralJoint_prob
    (profile : X → (i : ι) → M.BehavioralPolicy i)
    (hprofile : ∀ i info choice,
      Continuous fun x => ((profile x i info choice).toReal))
    {state : E.State} (trace : E.Trace state) (hterm : ¬ E.terminal state)
    (joint : {joint : ∀ i, Option (E.Action i) // E.Legal state joint}) :
    Continuous fun x =>
      (M.behavioralJoint (profile x) trace hterm joint).toReal := by
  simp_rw [M.behavioralJoint_prob_eq_prod]
  exact continuous_finsetProd _ fun i _ => hprofile i _ _

/-- Bounded behavioral execution is continuous in all local action masses.
No recall or finiteness of the information-state carrier is needed. -/
theorem continuous_runBehavioralFrom_prob
    [Fintype E.State] [∀ i, Fintype (E.Action i)]
    (profile : X → (i : ι) → M.BehavioralPolicy i)
    (hprofile : ∀ i info choice,
      Continuous fun x => ((profile x i info choice).toReal))
    (fuel : ℕ) (history target : E.History) :
    Continuous fun x =>
      (M.runBehavioralFrom (profile x) fuel history target).toReal := by
  classical
  induction fuel generalizing history target with
  | zero =>
      simp only [runBehavioralFrom, ExecutionProtocol.runRandomizedFor_zero,
        PMF.pure_apply]
      split_ifs <;> exact continuous_const
  | succ fuel ih =>
      by_cases hterm : E.terminal history.state
      · simp_rw [M.runBehavioralFrom_of_terminal _ _ hterm]
        exact continuous_const
      · simp_rw [M.runBehavioralFrom_succ_of_not_terminal _ _ hterm]
        let branch (x : X) (draw :
            {action : ∀ i, Option (E.Action i) // E.Legal history.state action})
            (state : E.State) : PMF E.History :=
          if realized : state ∈ (E.step history.state draw).support then
            M.runBehavioralFrom (profile x) fuel
              (history.extend draw.2 realized)
          else PMF.pure history
        apply continuous_pmf_bind_mass
        · exact M.continuous_behavioralJoint_prob profile hprofile
            history.trace hterm
        · intro draw terminal
          have hstep (x : X) :
              (E.step history.state draw).bindOnSupport
                  (fun state realized => M.runBehavioralFrom (profile x) fuel
                    (history.extend draw.2 realized)) =
                (E.step history.state draw).bind (branch x draw) := by
            apply bindOnSupport_eq_bind_of_eq_on_support
            intro state realized
            simp only [branch, dite_eq_left realized]
          simp_rw [hstep]
          apply continuous_pmf_bind_mass
          · intro state
            exact continuous_const
          · intro state terminal
            by_cases realized : state ∈ (E.step history.state draw).support
            · simpa only [branch, dite_eq_left realized] using
                ih (history.extend draw.2 realized) terminal
            · simp only [branch, dite_eq_right realized]
              exact continuous_const

/-- Reach probabilities and information-event masses inherit runner continuity. -/
theorem continuous_historyReachProbability
    [Fintype E.State] [∀ i, Fintype (E.Action i)]
    (profile : X → (i : ι) → M.BehavioralPolicy i)
    (hprofile : ∀ i info choice,
      Continuous fun x => ((profile x i info choice).toReal))
    (history : E.History) :
    Continuous fun x => (M.historyReachWeight (profile x) history).toReal :=
  M.continuous_runBehavioralFrom_prob profile hprofile
    history.trace.length E.initHistory history

theorem continuous_informationMass
    [Fintype E.State] [∀ i, Fintype (E.Action i)]
    (profile : X → (i : ι) → M.BehavioralPolicy i)
    (hprofile : ∀ i info choice,
      Continuous fun x => ((profile x i info choice).toReal))
    (i : ι) (site : M.InformationSite i)
    [Fintype (M.InformationHistory i site.1)] :
    Continuous fun x => (M.informationMass (profile x) i site).toReal := by
  classical
  have hsum :
      (fun x => (M.informationMass (profile x) i site).toReal) =
        fun x => ∑ history : M.InformationHistory i site.1,
          (M.historyReachWeight (profile x) history.1).toReal := by
    funext x
    have hsum (x : X) :
      (M.informationMass (profile x) i site).toReal =
        ∑ history : M.InformationHistory i site.1,
          (M.historyReachWeight (profile x) history.1).toReal := by
      unfold informationMass
      rw [tsum_fintype, ENNReal.toReal_sum]
      intro history _
      exact (M.runBehavioral (profile x) history.1.trace.length).apply_ne_top
        history.1
    exact hsum x
  rw [hsum]
  exact continuous_finsetSum _ fun history _ =>
    M.continuous_historyReachProbability profile hprofile history.1

/-- Bayes normalization is continuous where the information event has positive mass. -/
theorem continuous_bayesBelief_prob
    [Fintype E.State] [∀ i, Fintype (E.Action i)]
    (profile : X → (i : ι) → M.BehavioralPolicy i)
    (hprofile : ∀ i info choice,
      Continuous fun x => ((profile x i info choice).toReal))
    (i : ι) (site : M.InformationSite i)
    [Fintype (M.InformationHistory i site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : ∀ x, 0 < M.informationMass (profile x) i site)
    (history : M.InformationHistory i site.1) :
    Continuous fun x =>
      (M.bayesBelief (profile x) i site hantichain (hmass x) history).toReal := by
  simp_rw [M.bayesBelief_apply, ENNReal.toReal_div]
  exact (M.continuous_historyReachProbability profile hprofile history.1).div
    (M.continuous_informationMass profile hprofile i site)
    (fun x => by
      apply ENNReal.toReal_ne_zero.mpr
      exact ⟨(hmass x).ne', (ne_of_lt
        (lt_of_le_of_lt (M.informationMass_le_one (profile x) i site hantichain)
          ENNReal.one_lt_top))⟩)

omit [Fintype ι] in
/-- Unilateral profile replacement preserves coordinate continuity. -/
theorem continuous_update_prob [DecidableEq ι]
    (profile : X → (i : ι) → M.BehavioralPolicy i)
    (hprofile : ∀ i info choice,
      Continuous fun x => ((profile x i info choice).toReal))
    (who : ι) (alternative : X → M.BehavioralPolicy who)
    (halternative : ∀ info choice,
      Continuous fun x => ((alternative x info choice).toReal))
    (i : ι) (info : M.InfoState i) (choice : M.Choice i info) :
    Continuous fun x =>
      ((Profile.update (sig := M.behavioralSignature) (profile x) who
        (alternative x)) i info choice).toReal := by
  by_cases hi : i = who
  · subst i
    simpa only [Profile.update_same] using halternative info choice
  · simpa only [Profile.update_of_ne _ _ hi] using hprofile i info choice

/-- Belief-averaged continuation values are jointly continuous in the
assessment and the deviating player's whole policy. -/
theorem continuous_continuationContext_value
    [DecidableEq ι] [Fintype E.State] [Fintype E.History]
    [∀ i, Fintype (E.Action i)]
    (assessment : X → M.BehavioralAssessment)
    (hstrategy : ∀ i info choice,
      Continuous fun x =>
        (((assessment x).strategy i info choice).toReal))
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hbelief : ∀ history,
      Continuous fun x => (((assessment x).belief who site history).toReal))
    (alternative : X → M.BehavioralPolicy who)
    (halternative : ∀ info choice,
      Continuous fun x => ((alternative x info choice).toReal))
    (payoff : E.History → ℝ) (fuel : ℕ) :
    Continuous fun x =>
      ((assessment x).continuationContext site payoff fuel).value (alternative x)
        (by
          simpa only [Context.IntegrableAt, Context.ofBelief,
            BehavioralAssessment.continuationContext] using
            (payoffIntegrable_of_finite
              (((assessment x).continuationContext site payoff fuel).outcome
                (alternative x)) payoff)) := by
  simp only [Context.value, BehavioralAssessment.continuationContext]
  apply continuous_pmf_expect
  · intro target
    apply continuous_pmf_bind_mass
    · exact hbelief
    · intro history target
      exact M.continuous_runBehavioralFrom_prob _
        (M.continuous_update_prob _ hstrategy who alternative halternative)
        fuel history.1 target
  · intro target
    exact continuous_const

end GameTheory.Protocol.InformationModel
