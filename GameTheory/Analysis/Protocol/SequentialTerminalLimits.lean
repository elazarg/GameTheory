/-
# Fuel-free limits of well-founded sequential rationality

Bounded terminal payoffs make whole-policy continuation values continuous in
behavioral laws and beliefs. Repaired deviations retain their full policy type.
-/

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
theorem terminalContinuationContext_value_tendsto_of_bounded_terminal
    (certificate : E.WellFoundedPlay)
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
        ((sequence n).terminalContinuationContext
          certificate site payoff).value (alternative n))
      atTop
      (nhds ((target.terminalContinuationContext
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
      ((sequence n).terminalContinuationContext
        certificate site payoff).value (alternative n) =
      expect (law n) clipped := by
    apply expect_congr_on_support
    · intro final hfinal
      have hterm :=
        (sequence n).terminalContinuationContext_support_terminal certificate
          site payoff (alternative n) final hfinal
      show payoff final = clipped final
      simp [clipped, hterm]
  have htarget :
      (target.terminalContinuationContext certificate
        site payoff).value replacement =
      expect lawLimit clipped := by
    apply expect_congr_on_support
    · intro final hfinal
      have hterm :=
        target.terminalContinuationContext_support_terminal certificate site
          payoff replacement final hfinal
      show payoff final = clipped final
      simp [clipped, hterm]
  have hresult := hlaw.expect_of_bounded clipped hclip
  simpa only [hseq, htarget, law, lawLimit, kernel, kernelLimit] using hresult

/-- Whole-policy optimality passes to a fuel-free terminal-law limit when the
approximate inequality has a vanishing error. -/
theorem BehavioralAssessment.isSequentiallyRationalTerminal_of_converging_deviations_bounded
    (certificate : E.WellFoundedPlay)
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
      ((sequence n).terminalContinuationContext
        certificate site (payoff i)).value (repair n i alternative) ≤
      ((sequence n).terminalContinuationContext
        certificate site (payoff i)).value ((sequence n).strategy i) + error n) :
    target.IsSequentiallyRationalTerminal certificate payoff := by
  intro i site
  simp only [BehavioralAssessment.IsSequentiallyRationalAt]
  refine (Context.isLocallyOptimal_iff_of_integrable
    (target.terminalContinuationContext_integrable_of_bounded_terminal
      certificate site (payoff i) (bound i) (hbound i) (target.strategy i))
    fun alternative _ => target.terminalContinuationContext_integrable_of_bounded_terminal
      certificate site (payoff i) (bound i) (hbound i) alternative).2 fun alternative _ => ?_
  have hdeviation := M.terminalContinuationContext_value_tendsto_of_bounded_terminal
    certificate hstrategy i site (hbelief i site) (hrepair i alternative)
    (payoff i) (bound i) (hC i) (hbound i)
  have hbaseline := M.terminalContinuationContext_value_tendsto_of_bounded_terminal
    certificate hstrategy i site (hbelief i site) (hstrategy i)
    (payoff i) (bound i) (hC i) (hbound i)
  have hlimit := le_of_tendsto_of_tendsto hdeviation (hbaseline.add herror)
    (Eventually.of_forall fun n => hoptimal n i site alternative)
  simpa only [add_zero] using hlimit

end GameTheory.Protocol.InformationModel
