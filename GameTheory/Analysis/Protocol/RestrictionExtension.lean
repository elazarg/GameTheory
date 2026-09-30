/-
# Sequential equilibria extend across an action restriction

A sequential equilibrium of the smaller protocol extends to a sequential
equilibrium of the larger one when every new action at a retained site is
bounded by some whole continuation policy of the smaller protocol, under every
pair of extending profiles and every belief at the site. The extension keeps
behavior and beliefs at retained sites, completes new sites by a common
consistent construction, and has exactly the embedded terminal history and
payoff laws. Common decision depths are required at retained sites only.

The bound may be supplied by one comparator lottery per new action, and it
holds automatically for players who either keep all their choices or are
indifferent over all outcomes.
-/

import GameTheory.Analysis.Protocol.RestrictionCompletion
import GameTheory.Analysis.Protocol.RestrictionIncentives
import GameTheory.Analysis.Protocol.SequentialOneShot

noncomputable section

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability ExecutionProtocol

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E T : ExecutionProtocol ι} {M : InformationModel E} {N : InformationModel T}
  [Fintype T.History] [∀ i, DecidableEq (N.InfoState i)]
  (restriction : M.ActionRestriction N)

/-- **Extension from whole-policy bounds.** Every sequential equilibrium of the
smaller protocol extends when each new action at a retained site is bounded,
under every pair of extending profiles and every belief at the site, by the
value of some whole continuation policy of the smaller protocol. -/
theorem sequentialEquilibrium_extends_of_continuation
    (sourceAntichain : M.DecisionInformationAntichain)
    (sourceCertificate : E.WellFoundedHistories) (targetCertificate : T.WellFoundedHistories)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall)
    (depth : ∀ who, M.InformationSite who → ℕ)
    (clock : ∀ who site, InformationSite.CommonDepth N (restriction.site who site)
      (depth who site))
    (sourcePayoff : ι → E.History → ℝ) (targetPayoff : ι → T.History → ℝ)
    (matching : ∀ who history,
      targetPayoff who (restriction.history history) = sourcePayoff who history)
    (comparison : ∀ (sourceProfile : (i : ι) → M.BehavioralPolicy i)
      (targetProfile : (i : ι) → N.BehavioralPolicy i),
      restriction.ExtendsProfile sourceProfile targetProfile →
      ∀ who (site : M.InformationSite who)
        (action : N.Choice who (restriction.site who site).1),
        action ∉ Set.range (restriction.choice who site.1) →
        ∀ belief : PMF (M.InformationHistory who site.1),
          ∃ alternative : M.BehavioralPolicy who,
            expect belief (fun history => expect (N.runBehavioralTerminalFrom targetCertificate
              (Profile.update (sig := N.behavioralSignature) targetProfile who
                ((targetProfile who).commit (restriction.site who site).1 action))
              (restriction.history history.1)) (targetPayoff who)) ≤
            expect belief (fun history => expect (M.runBehavioralTerminalFrom sourceCertificate
              (Profile.update (sig := M.behavioralSignature) sourceProfile who alternative)
              history.1) (sourcePayoff who)))
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibrium sourceAntichain sourceCertificate
      sourcePayoff) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
        targetCertificate targetPayoff ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          restriction.history =
        N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          (fun history => (restriction.history history, fun who => sourcePayoff who history)) =
        (N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory).map
          (fun history => (history, fun who => targetPayoff who history)) := by
  classical
  have _ : Finite E.History := Finite.of_injective restriction.history restriction.history.injective
  obtain ⟨target, consistent, agrees, beliefs, newOptimal⟩ :=
    restriction.exists_consistent_extension source sourceAntichain sourceEquilibrium.2
      reference referenceMixed decisionRecall targetCertificate targetPayoff depth clock
  have localOptimal : ∀ who (site : N.InformationSite who) (law : PMF (N.Choice who site.1)),
      (target.continuationContext targetCertificate site (targetPayoff who)).value
          ((target.strategy who).withLaw site.1 law) ≤
        (target.continuationContext targetCertificate site (targetPayoff who)).value
          (target.strategy who) := by
    intro who site law
    by_cases retained : restriction.Retained who site.1
    · obtain ⟨original, observed⟩ := retained
      have same : restriction.site who original = site := Subtype.ext observed
      subst site
      apply restriction.retained_localOptimal_of_continuation sourceCertificate targetCertificate
        source target agrees decisionRecall.actsOnceWhereItMatters who original
        (beliefs who original) (sourcePayoff who) (targetPayoff who) (matching who)
        (sourceEquilibrium.1 who original) _ law
      intro action extra
      obtain ⟨alternative, bound⟩ := comparison source.strategy target.strategy agrees who original
        action extra (source.belief who original)
      refine ⟨alternative, ?_⟩
      unfold Context.value
      change expect ((target.belief who (restriction.site who original)).bind _) _ ≤
        expect ((source.belief who original).bind _) _
      rw [beliefs, PMF.bind_map, expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _),
        expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]
      exact bound
    · exact newOptimal who site retained law
  have historyLaw : (M.runBehavioralTerminalFrom sourceCertificate source.strategy
      E.initHistory).map restriction.history =
        N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory := by
    rw [← restriction.initial]
    exact restriction.terminal_law sourceCertificate targetCertificate _ _ agrees E.initHistory
  refine ⟨target, (BehavioralAssessment.isSequentialEquilibrium_iff_locallyOptimal N
    decisionRecall target targetCertificate targetPayoff).mpr ⟨consistent, localOptimal⟩, agrees,
    beliefs, historyLaw, ?_⟩
  calc
    _ = ((M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          restriction.history).map
        (fun history => (history, fun who => targetPayoff who history)) := by
      rw [PMF.map_comp]
      congr 1
      funext history
      exact congrArg (fun values => (restriction.history history, values))
        (funext fun who => (matching who history).symm)
    _ = _ := congrArg (PMF.map _) historyLaw

/-- **Extension from comparators.** It suffices that each new action at a
retained site is bounded by one legal local lottery of the smaller protocol,
under every pair of extending profiles and at every history of the site. -/
theorem sequentialEquilibrium_extends_of_comparator
    [∀ i, DecidableEq (M.InfoState i)]
    (sourceAntichain : M.DecisionInformationAntichain)
    (sourceCertificate : E.WellFoundedHistories) (targetCertificate : T.WellFoundedHistories)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall)
    (depth : ∀ who, M.InformationSite who → ℕ)
    (clock : ∀ who site, InformationSite.CommonDepth N (restriction.site who site)
      (depth who site))
    (sourcePayoff : ι → E.History → ℝ) (targetPayoff : ι → T.History → ℝ)
    (matching : ∀ who history,
      targetPayoff who (restriction.history history) = sourcePayoff who history)
    (comparator : ∀ who (site : M.InformationSite who),
      N.Choice who (restriction.site who site).1 → PMF (M.Choice who site.1))
    (comparison : ∀ (sourceProfile : (i : ι) → M.BehavioralPolicy i)
      (targetProfile : (i : ι) → N.BehavioralPolicy i),
      restriction.ExtendsProfile sourceProfile targetProfile →
      ∀ who (site : M.InformationSite who)
        (action : N.Choice who (restriction.site who site).1),
        action ∉ Set.range (restriction.choice who site.1) →
        ∀ history : M.InformationHistory who site.1,
          expect (N.runBehavioralTerminalFrom targetCertificate
            (Profile.update (sig := N.behavioralSignature) targetProfile who
              ((targetProfile who).commit (restriction.site who site).1 action))
            (restriction.history history.1)) (targetPayoff who) ≤
          expect (M.runBehavioralTerminalFrom sourceCertificate
            (Profile.update (sig := M.behavioralSignature) sourceProfile who
              ((sourceProfile who).withLaw site.1 (comparator who site action)))
            history.1) (sourcePayoff who))
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibrium sourceAntichain sourceCertificate
      sourcePayoff) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
        targetCertificate targetPayoff ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          restriction.history =
        N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          (fun history => (restriction.history history, fun who => sourcePayoff who history)) =
        (N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory).map
          (fun history => (history, fun who => targetPayoff who history)) := by
  have _ : Finite E.History := Finite.of_injective restriction.history restriction.history.injective
  apply restriction.sequentialEquilibrium_extends_of_continuation sourceAntichain
    sourceCertificate targetCertificate reference referenceMixed decisionRecall depth clock
    sourcePayoff targetPayoff matching _ source sourceEquilibrium
  intro sourceProfile targetProfile agrees who site action extra belief
  refine ⟨(sourceProfile who).withLaw site.1 (comparator who site action), ?_⟩
  exact expect_mono (fun history _ =>
    comparison sourceProfile targetProfile agrees who site action extra history)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)

/-- **Extension when new choices are harmless.** Every sequential equilibrium
extends when each player either keeps all its choices or is indifferent over
all outcomes of the larger protocol. Indifference must hold at every history,
not merely along equilibrium play. -/
theorem sequentialEquilibrium_extends_of_indifference
    [∀ i, DecidableEq (M.InfoState i)]
    (sourceAntichain : M.DecisionInformationAntichain)
    (sourceCertificate : E.WellFoundedHistories) (targetCertificate : T.WellFoundedHistories)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall)
    (depth : ∀ who, M.InformationSite who → ℕ)
    (clock : ∀ who site, InformationSite.CommonDepth N (restriction.site who site)
      (depth who site))
    (sourcePayoff : ι → E.History → ℝ) (targetPayoff : ι → T.History → ℝ)
    (matching : ∀ who history,
      targetPayoff who (restriction.history history) = sourcePayoff who history)
    (unchangedOrIndifferent : ∀ who,
      (∀ info, Function.Surjective (restriction.choice who info)) ∨
        ∃ constant, ∀ history, targetPayoff who history = constant)
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibrium sourceAntichain sourceCertificate
      sourcePayoff) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
        targetCertificate targetPayoff ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          restriction.history =
        N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          (fun history => (restriction.history history, fun who => sourcePayoff who history)) =
        (N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory).map
          (fun history => (history, fun who => targetPayoff who history)) := by
  classical
  let comparator (who : ι) (site : M.InformationSite who)
      (_ : N.Choice who (restriction.site who site).1) : PMF (M.Choice who site.1) :=
    PMF.pure ⟨some site.2.choose_spec.2.choose, site.2.choose_spec.2.choose_spec⟩
  apply restriction.sequentialEquilibrium_extends_of_comparator sourceAntichain
    sourceCertificate targetCertificate reference referenceMixed decisionRecall depth clock
    sourcePayoff targetPayoff matching comparator _ source sourceEquilibrium
  intro sourceProfile targetProfile _ who site action extra history
  rcases unchangedOrIndifferent who with unchanged | ⟨constant, indifferent⟩
  · exact (extra (unchanged site.1 action)).elim
  · have sourceConstant (final : E.History) : sourcePayoff who final = constant := by
      rw [← matching]
      exact indifferent _
    rw [show targetPayoff who = fun _ => constant from funext indifferent,
      show sourcePayoff who = fun _ => constant from funext sourceConstant, expect_constant,
      expect_constant]

end GameTheory.Protocol.InformationModel.ActionRestriction
