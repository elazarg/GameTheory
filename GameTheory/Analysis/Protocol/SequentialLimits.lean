/-
# Passing sequential rationality to assessment limits

Bounded terminal payoffs make whole-policy continuation values continuous in
behavioral laws and beliefs, on arbitrary history and action carriers. The
approximating deviations may obey restrictions that disappear in the limit and
keep their full policy type; this is the analytic step used to remove positive
trembles, and it does not assume that the limit assessment is rational.

On arbitrary carriers, uniform tightness supplies a common assessment
subsequence, so a tight sequence of fully mixed Bayes assessments with
vanishing optimality errors has a sequential-equilibrium limit. This needs
compactness but no fixed point.
-/

import GameTheory.Analysis.Protocol.AssessmentCompactness
import GameTheory.Analysis.Protocol.BehavioralTerminalConvergence

noncomputable section

namespace GameTheory.Protocol.InformationModel

open Filter GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {E : ExecutionProtocol.{uι, us, ua} ι}
    (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Bounded terminal payoffs have continuous terminal continuation values on
arbitrary history and action carriers. Nonterminal payoff values are irrelevant. -/
theorem continuationContext_value_tendsto_of_bounded_terminal
    (certificate : E.WellFoundedHistories)
    {sequence : ℕ → M.BehavioralAssessment}
    {target : M.BehavioralAssessment}
    (hstrategy : ∀ i (decision : M.InformationSite i), PMFConvergesPointwise
      (fun n => (sequence n).strategy i decision.1)
      (target.strategy i decision.1))
    (who : ι) (site : M.InformationSite who)
    (hbelief : PMFConvergesPointwise
      (fun n => (sequence n).belief who site) (target.belief who site))
    {alternative : ℕ → M.BehavioralPolicy who}
    {replacement : M.BehavioralPolicy who}
    (halternative : ∀ decision : M.InformationSite who, PMFConvergesPointwise
      (fun n => alternative n decision.1) (replacement decision.1))
    (payoff : E.History → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ final, E.terminal final.state → |payoff final| ≤ C) :
    Tendsto
      (fun n =>
        ((sequence n).continuationContext
          certificate site payoff).value (alternative n))
      atTop
      (nhds ((target.continuationContext
        certificate site payoff).value replacement)) := by
  classical
  let kernel (n : ℕ) (history : M.InformationHistory who site.1) : PMF E.History :=
    M.runBehavioralTerminalFrom certificate
      (Profile.update (sig := M.behavioralSignature)
        (sequence n).strategy who (alternative n)) history.1
  let kernelLimit (history : M.InformationHistory who site.1) : PMF E.History :=
    M.runBehavioralTerminalFrom certificate
      (Profile.update (sig := M.behavioralSignature)
        target.strategy who replacement) history.1
  have hkernel (history : M.InformationHistory who site.1) :
      PMFConvergesPointwise (fun n => kernel n history) (kernelLimit history) :=
    M.runBehavioralTerminalFrom_convergesPointwise certificate
      (M.update_convergesPointwise_on_sites hstrategy who halternative) history.1
  let law (n : ℕ) : PMF E.History :=
    ((sequence n).belief who site).bind (kernel n)
  let lawLimit : PMF E.History := (target.belief who site).bind kernelLimit
  have hlaw : PMFConvergesPointwise law lawLimit := hbelief.bind hkernel
  let clipped (final : E.History) : ℝ :=
    if E.terminal final.state then payoff final else 0
  have hclip : ∀ final, |clipped final| ≤ C := by
    intro final
    by_cases hterm : E.terminal final.state
    · simpa [clipped, hterm] using hbound final hterm
    · simpa [clipped, hterm] using hC
  have hseq (n : ℕ) :
      ((sequence n).continuationContext
        certificate site payoff).value (alternative n) =
      expect (law n) clipped := by
    apply expect_congr_on_support
    · intro final hfinal
      have hterm :=
        (sequence n).continuationContext_support_terminal certificate
          site payoff (alternative n) final hfinal
      show payoff final = clipped final
      simp [clipped, hterm]
  have htarget :
      (target.continuationContext certificate
        site payoff).value replacement =
      expect lawLimit clipped := by
    apply expect_congr_on_support
    · intro final hfinal
      have hterm :=
        target.continuationContext_support_terminal certificate site
          payoff replacement final hfinal
      show payoff final = clipped final
      simp [clipped, hterm]
  have hresult := hlaw.expect_of_bounded clipped hclip
  simpa only [hseq, htarget, law, lawLimit, kernel, kernelLimit] using hresult

/-- Whole-policy optimality passes to an assessment limit when the approximate
inequality has a vanishing error. Only terminal payoffs need a bound. -/
theorem BehavioralAssessment.isSequentiallyRational_of_converging_deviations_bounded
    (certificate : E.WellFoundedHistories)
    {sequence : ℕ → M.BehavioralAssessment}
    {target : M.BehavioralAssessment}
    (hstrategy : ∀ i (decision : M.InformationSite i), PMFConvergesPointwise
      (fun n => (sequence n).strategy i decision.1)
      (target.strategy i decision.1))
    (hbelief : ∀ i site, PMFConvergesPointwise
      (fun n => (sequence n).belief i site) (target.belief i site))
    (repair : ℕ → (i : ι) → M.BehavioralPolicy i → M.BehavioralPolicy i)
    (hrepair : ∀ i alternative (decision : M.InformationSite i),
      PMFConvergesPointwise
        (fun n => repair n i alternative decision.1)
        (alternative decision.1))
    (payoff : ι → E.History → ℝ)
    (bound : ι → ℝ) (hC : ∀ i, 0 ≤ bound i)
    (hbound : ∀ i final, E.terminal final.state →
      |payoff i final| ≤ bound i)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hoptimal : ∀ n i site alternative,
      ((sequence n).continuationContext
        certificate site (payoff i)).value (repair n i alternative) ≤
      ((sequence n).continuationContext
        certificate site (payoff i)).value ((sequence n).strategy i) + error n) :
    target.IsSequentiallyRational certificate payoff := by
  intro i site
  simp only [BehavioralAssessment.IsSequentiallyRationalAt]
  refine (Context.isLocallyOptimal_iff_of_integrable
    (target.continuationContext_integrable_of_bounded_terminal
      certificate site (payoff i) (bound i) (hbound i) (target.strategy i))
    fun alternative _ => target.continuationContext_integrable_of_bounded_terminal
      certificate site (payoff i) (bound i) (hbound i) alternative).2 fun alternative _ => ?_
  have hdeviation := M.continuationContext_value_tendsto_of_bounded_terminal
    certificate hstrategy i site (hbelief i site) (hrepair i alternative)
    (payoff i) (bound i) (hC i) (hbound i)
  have hbaseline := M.continuationContext_value_tendsto_of_bounded_terminal
    certificate hstrategy i site (hbelief i site) (hstrategy i)
    (payoff i) (bound i) (hC i) (hbound i)
  have hlimit := le_of_tendsto_of_tendsto hdeviation (hbaseline.add herror)
    (Eventually.of_forall fun n => hoptimal n i site alternative)
  simpa only [add_zero] using hlimit

/-- On finite history carriers every payoff is bounded, so exact whole-policy
optimality of approximating assessments against converging deviations passes
to the limit with no payoff hypothesis. -/
theorem BehavioralAssessment.isSequentiallyRational_of_converging_deviations
    [Finite E.History]
    (certificate : E.WellFoundedHistories)
    {sequence : ℕ → M.BehavioralAssessment}
    {target : M.BehavioralAssessment}
    (hstrategy : ∀ i (decision : M.InformationSite i), PMFConvergesPointwise
      (fun n => (sequence n).strategy i decision.1)
      (target.strategy i decision.1))
    (hbelief : ∀ i site, PMFConvergesPointwise
      (fun n => (sequence n).belief i site) (target.belief i site))
    (repair : ℕ → (i : ι) → M.BehavioralPolicy i → M.BehavioralPolicy i)
    (hrepair : ∀ i alternative (decision : M.InformationSite i),
      PMFConvergesPointwise
        (fun n => repair n i alternative decision.1)
        (alternative decision.1))
    (payoff : ι → E.History → ℝ)
    (hoptimal : ∀ n i site alternative,
      ((sequence n).continuationContext
        certificate site (payoff i)).value (repair n i alternative) ≤
      ((sequence n).continuationContext
        certificate site (payoff i)).value ((sequence n).strategy i)) :
    target.IsSequentiallyRational certificate payoff := by
  let _ := Fintype.ofFinite E.History
  let bound (i : ι) := ∑ history : E.History, |payoff i history|
  have hbound (i : ι) (history : E.History) : |payoff i history| ≤ bound i :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff i other))
      (Finset.mem_univ history)
  exact BehavioralAssessment.isSequentiallyRational_of_converging_deviations_bounded
    M certificate hstrategy hbelief repair hrepair payoff bound
    (fun i => (abs_nonneg _).trans (hbound i E.initHistory))
    (fun i final _ => hbound i final) (fun _ => 0) tendsto_const_nhds
    (fun n i site alternative => by simpa only [add_zero] using hoptimal n i site alternative)

/-- A tight sequence of fully mixed Bayes assessments whose incumbents are
approximately optimal against every repaired whole-policy deviation has a
sequential-equilibrium limit. The hypotheses explicitly supply the perturbed
assessments and their approximate optimality; this theorem extracts their
common limit and proves its two assessment properties. -/
theorem exists_sequentialEquilibrium_of_uniformlyTight
    [∀ i, Countable (M.InformationSite i)]
    (certificate : E.WellFoundedHistories)
    (hantichain : M.DecisionInformationAntichain)
    (sequence : ℕ → M.BehavioralAssessment)
    (hstrategyTight : ∀ i (site : M.InformationSite i),
      UniformlyTight (fun n => (sequence n).strategy i site.1))
    (hbeliefTight : ∀ i (site : M.InformationSite i),
      UniformlyTight (fun n => (sequence n).belief i site))
    (hfull : ∀ n, (sequence n).IsFullyMixed)
    (hbayes : ∀ n, BehavioralAssessment.IsBayesConsistent M
      (sequence n) hantichain)
    (repair : ℕ → (i : ι) → M.BehavioralPolicy i → M.BehavioralPolicy i)
    (hrepair : ∀ i alternative (site : M.InformationSite i),
      PMFConvergesPointwise
        (fun n => repair n i alternative site.1) (alternative site.1))
    (payoff : ι → E.History → ℝ)
    (bound : ι → ℝ) (hC : ∀ i, 0 ≤ bound i)
    (hbound : ∀ i final, E.terminal final.state → |payoff i final| ≤ bound i)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hoptimal : ∀ n i site alternative,
      ((sequence n).continuationContext
        certificate site (payoff i)).value (repair n i alternative) ≤
      ((sequence n).continuationContext
        certificate site (payoff i)).value ((sequence n).strategy i) + error n) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.IsSequentiallyRational certificate payoff ∧
        assessment.IsSequentiallyConsistent hantichain := by
  obtain ⟨assessment, subseq, hsubseq, hconvergence⟩ :=
    M.exists_subseq_behavioralAssessmentConvergesPointwise_atSites_of_uniformlyTight
      sequence hstrategyTight hbeliefTight
  refine ⟨assessment, ?_, ?_⟩
  · exact BehavioralAssessment.isSequentiallyRational_of_converging_deviations_bounded
      M
      certificate (fun i site => hconvergence.strategy i site)
      (fun i site => hconvergence.belief i site)
      (fun n i alternative => repair (subseq n) i alternative)
      (fun i alternative site => (hrepair i alternative site).subseq hsubseq)
      payoff bound hC hbound (fun n => error (subseq n))
      (herror.comp hsubseq.tendsto_atTop)
      (fun n i site alternative => hoptimal (subseq n) i site alternative)
  · exact hconvergence.isSequentiallyConsistent hantichain
      (fun n => hfull (subseq n)) (fun n => hbayes (subseq n))

end GameTheory.Protocol.InformationModel
