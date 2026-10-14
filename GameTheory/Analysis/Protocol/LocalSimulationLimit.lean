/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

import GameTheory.Analysis.Protocol.UniformPolicyLimit
import GameTheory.Analysis.Protocol.SequentialOneShot
import GameTheory.Math.Probability.StatisticalDistanceStability

/-! # Sequential equilibrium from approximate local comparisons

At copied sites, vanishing local gains pass to a consistent assessment limit.
Other sites may be certified directly at that limit, for example by component
completion. A source assessment supplies the bounds through mixtures of its
whole-policy gains. Source histories need not be finite and no common clock
or uniform source horizon is required.

Rationality and observed-law matching are separate conclusions. The latter
uses ordinary statistical distance and convergence of terminal play.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {Player : Type*} [DecidableEq Player]
  {T : ExecutionProtocol Player} {N : InformationModel T} [T.FiniteMovers]

/-- A consistent limit is a sequential equilibrium when copied-site gains
vanish and every other site is already locally optimal. Errors may depend on
the player, site and local law. The approximants need not be Bayesian or rational. -/
theorem BehavioralAssessmentConvergesPointwise.sequentialEquilibrium_of_copied_gain_bounds
    [Finite T.History] [∀ who, DecidableEq (N.InfoState who)]
    {sequence : ℕ → N.BehavioralAssessment} {target : N.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence target)
    (hrecall : N.DecisionRecall) (certificate : T.WellFoundedHistories)
    (payoff : Player → T.History → ℝ)
    (copied : ∀ who, N.InformationSite who → Prop)
    (consistent : target.IsSequentiallyConsistent hrecall.decisionInformationAntichain)
    (error : ℕ → ∀ who (site : N.InformationSite who), PMF (N.Choice who site.1) → ℝ)
    (vanishes : ∀ who (site : N.InformationSite who), copied who site →
      ∀ law, Tendsto (fun n => error n who site law) atTop (nhds 0))
    (gainBound : ∀ n who (site : N.InformationSite who), copied who site →
      ∀ law, ((sequence n).continuationContext certificate site (payoff who)).value
          (((sequence n).strategy who).withLaw site.1 law) -
        ((sequence n).continuationContext certificate site (payoff who)).value
          ((sequence n).strategy who) ≤ error n who site law)
    (freeOptimal : ∀ who (site : N.InformationSite who), ¬ copied who site →
      ∀ law, (target.continuationContext certificate site (payoff who)).value
          ((target.strategy who).withLaw site.1 law) ≤
        (target.continuationContext certificate site (payoff who)).value
          (target.strategy who)) :
    target.IsSequentialEquilibrium hrecall.decisionInformationAntichain certificate payoff := by
  classical
  let _ := Fintype.ofFinite T.History
  apply (target.isSequentialEquilibrium_iff_locallyOptimal N hrecall certificate payoff).mpr
  refine ⟨consistent, ?_⟩
  intro who site law
  by_cases kept : copied who site
  swap
  · exact freeOptimal who site kept law
  let C : ℝ := ∑ history : T.History, |payoff who history|
  have bounded (history : T.History) : |payoff who history| ≤ C :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff who other)) (Finset.mem_univ history)
  have nonnegative : 0 ≤ C := (abs_nonneg _).trans (bounded T.initHistory)
  have replacement (decision : N.InformationSite who) : PMFConvergesPointwise
      (fun n => ((sequence n).strategy who).withLaw site.1 law decision.1)
      ((target.strategy who).withLaw site.1 law decision.1) := by
    by_cases same : decision = site
    · subst decision
      simpa only [BehavioralPolicy.withLaw_self] using pmfConvergesPointwise_const law
    · have different : decision.1 ≠ site.1 := fun equal => same (Subtype.ext equal)
      simpa only [BehavioralPolicy.withLaw_of_ne _ _ _ different] using
        converges.strategy who decision
  have alternate := N.continuationContext_value_tendsto_of_bounded_terminal certificate
    converges.strategy who site (converges.belief who site) replacement (payoff who) C
    nonnegative (fun final _ => bounded final)
  have prescribed := N.continuationContext_value_tendsto_of_bounded_terminal certificate
    converges.strategy who site (converges.belief who site) (converges.strategy who)
    (payoff who) C nonnegative (fun final _ => bounded final)
  exact sub_nonpos.mp (le_of_tendsto_of_tendsto (alternate.sub prescribed)
    (vanishes who site kept law) (Eventually.of_forall fun n => gainBound n who site kept law))

variable {E : ExecutionProtocol Player} {M : InformationModel E} [E.FiniteMovers]

/-- Original-source whole-policy gain mixtures, or direct vanishing gain
bounds, certify copied sites of a consistent target limit. Mixtures may vary
with the perturbation, site and local law. The source only needs finite menus
at finitely many sites for each player, well-founded play and terminal-bounded
payoffs; it need not have finitely many histories or a uniform horizon. -/
theorem sequentialEquilibrium_of_copied_comparisons_limit
    [Finite T.History] [∀ who, DecidableEq (N.InfoState who)]
    [∀ who, Finite (M.InformationSite who)]
    [∀ who (site : M.InformationSite who), Finite (M.Choice who site.1)]
    (sourceCertificate : E.WellFoundedHistories) (targetCertificate : T.WellFoundedHistories)
    (hrecall : N.DecisionRecall)
    (sourcePayoff : Player → E.History → ℝ) (targetPayoff : Player → T.History → ℝ)
    (bound : Player → ℝ) (nonnegative : ∀ who, 0 ≤ bound who)
    (payoffBound : ∀ who final, E.terminal final.state → |sourcePayoff who final| ≤ bound who)
    {sourceSequence : ℕ → M.BehavioralAssessment} {source : M.BehavioralAssessment}
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRational sourceCertificate sourcePayoff)
    {targetSequence : ℕ → N.BehavioralAssessment} {target : N.BehavioralAssessment}
    (targetConverges : BehavioralAssessmentConvergesPointwise targetSequence target)
    (copied : ∀ who, N.InformationSite who → Prop)
    (consistent : target.IsSequentiallyConsistent hrecall.decisionInformationAntichain)
    (comparisonError : ℕ → ∀ who, N.InformationSite who → ℝ)
    (errorVanishes : ∀ who site, copied who site →
      Tendsto (fun n => comparisonError n who site) atTop (nhds 0))
    (comparisons : ∀ n who (site : N.InformationSite who), copied who site →
      ∀ law : PMF (N.Choice who site.1),
        let targetGain :=
          ((targetSequence n).continuationContext targetCertificate site (targetPayoff who)).value
              (((targetSequence n).strategy who).withLaw site.1 law) -
            ((targetSequence n).continuationContext targetCertificate site (targetPayoff who)).value
              ((targetSequence n).strategy who)
        targetGain ≤ comparisonError n who site ∨
          ∃ mixture : PMF (M.AssessmentDeviation who),
            targetGain ≤ expect mixture (fun deviation =>
              ((sourceSequence n).continuationContext sourceCertificate deviation.1
                  (sourcePayoff who)).value deviation.2 -
                ((sourceSequence n).continuationContext sourceCertificate deviation.1
                  (sourcePayoff who)).value ((sourceSequence n).strategy who)) +
              comparisonError n who site)
    (freeOptimal : ∀ who (site : N.InformationSite who), ¬ copied who site →
      ∀ law, (target.continuationContext targetCertificate site (targetPayoff who)).value
          ((target.strategy who).withLaw site.1 law) ≤
        (target.continuationContext targetCertificate site (targetPayoff who)).value
          (target.strategy who)) :
    target.IsSequentialEquilibrium hrecall.decisionInformationAntichain targetCertificate
      targetPayoff := by
  classical
  choose error errorNonnegative vanishes sourceBound using fun who =>
    sourceConverges.exists_uniform_terminal_policy_gain_bound who sourceCertificate
      (sourcePayoff who) (bound who) (nonnegative who) (payoffBound who) (sourceRational who)
  apply targetConverges.sequentialEquilibrium_of_copied_gain_bounds hrecall targetCertificate
    targetPayoff copied consistent (fun n who site _ => error who n + comparisonError n who site)
    (fun who site kept _ => by simpa using (vanishes who).add (errorVanishes who site kept))
    (fun n who site kept law => ?_) freeOptimal
  rcases comparisons n who site kept law with harmless | ⟨mixture, comparison⟩
  · exact harmless.trans (le_add_of_nonneg_left (errorNonnegative who n))
  · apply comparison.trans
    have values (site : M.InformationSite who) (alternative : M.BehavioralPolicy who) :
        |((sourceSequence n).continuationContext sourceCertificate site
            (sourcePayoff who)).value alternative| ≤ bound who := by
      apply expect_abs_le_of_bounded_on_support
      intro final supported
      exact payoffBound who final
        ((sourceSequence n).continuationContext_support_terminal sourceCertificate site
          (sourcePayoff who) alternative final supported)
    have gainBound (deviation : M.AssessmentDeviation who) :
        |((sourceSequence n).continuationContext sourceCertificate deviation.1
            (sourcePayoff who)).value deviation.2 -
          ((sourceSequence n).continuationContext sourceCertificate deviation.1
            (sourcePayoff who)).value ((sourceSequence n).strategy who)| ≤ 2 * bound who :=
      (abs_sub _ _).trans (by
        have first := values deviation.1 deviation.2
        have second := values deviation.1 ((sourceSequence n).strategy who)
        linarith)
    exact add_le_add (expect_le_const mixture _
      (payoffIntegrable_of_bounded mixture _ gainBound) (error who n)
      (fun deviation _ => sourceBound who n deviation.1 deviation.2)) le_rfl

/-- Fully mixed Bayes approximants with vanishing local gain bounds admit
one common subsequence whose limit is a sequential equilibrium. Unlike a
whole-policy approximate-optimality premise, only single-site deviations need
to be controlled. Errors may depend on the local law. -/
theorem exists_sequentialEquilibrium_limit_of_local_gain_bounds
    [Countable Player] [Finite T.History] [∀ who, DecidableEq (N.InfoState who)]
    (hrecall : N.DecisionRecall) (certificate : T.WellFoundedHistories)
    (payoff : Player → T.History → ℝ) (sequence : ℕ → N.BehavioralAssessment)
    (fullyMixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent N (sequence n)
      hrecall.decisionInformationAntichain)
    (error : ℕ → ∀ who (site : N.InformationSite who), PMF (N.Choice who site.1) → ℝ)
    (vanishes : ∀ who site law, Tendsto (fun n => error n who site law) atTop (nhds 0))
    (gainBound : ∀ n who (site : N.InformationSite who) law,
      ((sequence n).continuationContext certificate site (payoff who)).value
          (((sequence n).strategy who).withLaw site.1 law) -
        ((sequence n).continuationContext certificate site (payoff who)).value
          ((sequence n).strategy who) ≤ error n who site law) :
    ∃ (target : N.BehavioralAssessment) (index : ℕ → ℕ), StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) target ∧
      target.IsSequentialEquilibrium hrecall.decisionInformationAntichain certificate payoff := by
  obtain ⟨target, index, increasing, converges⟩ :=
    N.exists_subseq_behavioralAssessmentConvergesPointwise_atSites_of_uniformlyTight sequence
      (fun _ _ => uniformlyTight_of_finite _) (fun _ _ => uniformlyTight_of_finite _)
  refine ⟨target, index, increasing, converges, ?_⟩
  exact converges.sequentialEquilibrium_of_copied_gain_bounds hrecall certificate payoff
    (fun _ _ => True)
    (converges.isSequentiallyConsistent hrecall.decisionInformationAntichain
      (fun n => fullyMixed (index n)) (fun n => bayes (index n)))
    (fun n who site law => error (index n) who site law)
    (fun who site _ law => (vanishes who site law).comp increasing.tendsto_atTop)
    (fun n who site _ law => gainBound (index n) who site law)
    (fun _ _ impossible => False.elim (impossible trivial))

omit [DecidableEq Player] in
/-- Vanishing observed-law error preserves exact terminal laws at strategy
limits. Source and target players may differ. Belief convergence, rationality
and consistency are not needed. -/
theorem terminal_law_eq_of_vanishing_statisticalDistance
    {SourcePlayer : Type*} {SourceProtocol : ExecutionProtocol SourcePlayer}
    {SourceModel : InformationModel SourceProtocol} [SourceProtocol.FiniteMovers]
    {Outcome : Type*} (sourceObserve : SourceProtocol.History → Outcome)
    (targetObserve : T.History → Outcome)
    (sourceCertificate : SourceProtocol.WellFoundedHistories)
    (targetCertificate : T.WellFoundedHistories)
    {sourceSequence : ℕ → ∀ who, SourceModel.BehavioralPolicy who}
    {source : ∀ who, SourceModel.BehavioralPolicy who}
    (sourceConverges : ∀ who (site : SourceModel.InformationSite who),
      PMFConvergesPointwise (fun n => sourceSequence n who site.1) (source who site.1))
    {targetSequence : ℕ → ∀ who, N.BehavioralPolicy who}
    {target : ∀ who, N.BehavioralPolicy who}
    (targetConverges : ∀ who (site : N.InformationSite who),
      PMFConvergesPointwise (fun n => targetSequence n who site.1) (target who site.1))
    (error : ℕ → ℝ) (vanishes : Tendsto error atTop (nhds 0))
    (close : ∀ n, statisticalDistance
      ((N.runBehavioralTerminalFrom targetCertificate (targetSequence n) T.initHistory).map
        targetObserve)
      ((SourceModel.runBehavioralTerminalFrom sourceCertificate (sourceSequence n)
        SourceProtocol.initHistory).map sourceObserve) ≤ error n) :
    (N.runBehavioralTerminalFrom targetCertificate target T.initHistory).map targetObserve =
      (SourceModel.runBehavioralTerminalFrom sourceCertificate source
        SourceProtocol.initHistory).map sourceObserve := by
  exact ((N.runBehavioralTerminalFrom_convergesPointwise targetCertificate targetConverges
    T.initHistory).map targetObserve).eq_of_statisticalDistance_le
      ((SourceModel.runBehavioralTerminalFrom_convergesPointwise sourceCertificate sourceConverges
        SourceProtocol.initHistory).map sourceObserve) error vanishes close

end GameTheory.Protocol.InformationModel
