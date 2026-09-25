/-
# Limits of behavioral continuation values

Coordinate convergence of behavioral policies passes through the canonical
bounded runner. Joint convergence of beliefs then passes through assessment
continuation values, including varying whole-policy deviations.
-/

import GameTheory.Math.Probability.Convergence
import GameTheory.Math.Probability.Support
import GameTheory.Analysis.Protocol.BehavioralBayes

noncomputable section

namespace GameTheory.Protocol.InformationModel

open Filter GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} [Fintype ι]
    {E : ExecutionProtocol.{uι, us, ua} ι}
    (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Local probability convergence passes through every bounded continuation.
The information carriers themselves need not be finite. -/
theorem runBehavioralFrom_convergesPointwise
    {sequence : ℕ → (i : ι) → M.BehavioralPolicy i}
    {target : (i : ι) → M.BehavioralPolicy i}
    (hlimit : ∀ i info, PMFConvergesPointwise (fun n => sequence n i info)
      (target i info)) (fuel : ℕ) (history : E.History) :
    PMFConvergesPointwise (fun n => M.runBehavioralFrom (sequence n) fuel history)
      (M.runBehavioralFrom target fuel history) := by
  classical
  induction fuel generalizing history with
  | zero =>
      simpa only [runBehavioralFrom, ExecutionProtocol.runRandomizedFor_zero]
        using pmfConvergesPointwise_const (PMF.pure history)
  | succ fuel ih =>
      by_cases hterm : E.terminal history.state
      · simpa only [M.runBehavioralFrom_of_terminal _ _ hterm] using
          pmfConvergesPointwise_const (PMF.pure history)
      · let jointLaw (n : ℕ) :=
          M.behavioralJoint (sequence n) history.trace hterm
        let jointTarget := M.behavioralJoint target history.trace hterm
        have hjoint : PMFConvergesPointwise jointLaw jointTarget := by
          unfold jointLaw jointTarget InformationModel.behavioralJoint
          exact (PMFConvergesPointwise.independentProduct fun i =>
            hlimit i (M.infoOf i history.trace)).map _
        let continuation (n : ℕ) (draw :
            {action : ∀ i, Option (E.Action i) // E.Legal history.state action}) :=
          (E.step history.state draw).bindOnSupport fun state realized =>
            M.runBehavioralFrom (sequence n) fuel
              (history.extend draw.2 realized)
        let targetContinuation (draw :
            {action : ∀ i, Option (E.Action i) // E.Legal history.state action}) :=
          (E.step history.state draw).bindOnSupport fun state realized =>
            M.runBehavioralFrom target fuel (history.extend draw.2 realized)
        have hcontinuation (draw :
            {action : ∀ i, Option (E.Action i) // E.Legal history.state action}) :
            PMFConvergesPointwise (fun n => continuation n draw)
              (targetContinuation draw) := by
          let kernel (n : ℕ) (state : E.State) : PMF E.History :=
            if realized : state ∈ (E.step history.state draw).support then
              M.runBehavioralFrom (sequence n) fuel
                (history.extend draw.2 realized)
            else PMF.pure history
          let targetKernel (state : E.State) : PMF E.History :=
            if realized : state ∈ (E.step history.state draw).support then
              M.runBehavioralFrom target fuel (history.extend draw.2 realized)
            else PMF.pure history
          have hkernel (state : E.State) :
              PMFConvergesPointwise (fun n => kernel n state)
                (targetKernel state) := by
            by_cases realized : state ∈ (E.step history.state draw).support
            · simpa only [kernel, targetKernel, dite_eq_left realized] using
                ih (history.extend draw.2 realized)
            · simpa only [kernel, targetKernel, dite_eq_right realized] using
                pmfConvergesPointwise_const (PMF.pure history)
          have hstep :=
            (pmfConvergesPointwise_const (E.step history.state draw)).bind
              (kernel := kernel) (targetKernel := targetKernel) hkernel
          have hbind (n : ℕ) :
              continuation n draw = (E.step history.state draw).bind (kernel n) := by
            unfold continuation kernel
            apply bindOnSupport_eq_bind_of_eq_on_support
            intro state realized
            simp only [dite_eq_left realized]
          have htarget :
              targetContinuation draw =
                (E.step history.state draw).bind targetKernel := by
            unfold targetContinuation targetKernel
            apply bindOnSupport_eq_bind_of_eq_on_support
            intro state realized
            simp only [dite_eq_left realized]
          simpa only [hbind, htarget] using hstep
        simpa only [M.runBehavioralFrom_succ_of_not_terminal _ fuel hterm,
          jointLaw, jointTarget, continuation, targetContinuation] using
          hjoint.bind hcontinuation

omit [Fintype ι] in
/-- Unilateral replacement preserves coordinate convergence. -/
theorem update_convergesPointwise [DecidableEq ι]
    {sequence : ℕ → (i : ι) → M.BehavioralPolicy i}
    {target : (i : ι) → M.BehavioralPolicy i}
    (hlimit : ∀ i info, PMFConvergesPointwise (fun n => sequence n i info)
      (target i info))
    (who : ι) {alternative : ℕ → M.BehavioralPolicy who}
    {replacement : M.BehavioralPolicy who}
    (halternative : ∀ info, PMFConvergesPointwise
      (fun n => alternative n info) (replacement info))
    (i : ι) (info : M.InfoState i) :
    PMFConvergesPointwise
      (fun n => (Profile.update (sig := M.behavioralSignature)
        (sequence n) who (alternative n)) i info)
      ((Profile.update (sig := M.behavioralSignature) target who replacement) i info) := by
  by_cases hi : i = who
  · subst i
    simpa only [Profile.update_same] using halternative info
  · simpa only [Profile.update_of_ne _ _ hi] using hlimit i info

/-- Continuation values converge on arbitrary carriers when the payoff has a
uniform absolute bound. The belief fiber, state space, and action spaces need
not be finite. -/
theorem continuationContext_value_tendsto_of_bounded
    [DecidableEq ι]
    {sequence : ℕ → M.BehavioralAssessment} {target : M.BehavioralAssessment}
    (hstrategy : ∀ i info, PMFConvergesPointwise
      (fun n => (sequence n).strategy i info) (target.strategy i info))
    (who : ι) (site : M.InformationSite who)
    (hbelief : PMFConvergesPointwise
      (fun n => (sequence n).belief who site) (target.belief who site))
    {alternative : ℕ → M.BehavioralPolicy who}
    {replacement : M.BehavioralPolicy who}
    (halternative : ∀ info, PMFConvergesPointwise
      (fun n => alternative n info) (replacement info))
    (payoff : E.History → ℝ) (fuel : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ history, |payoff history| ≤ C) :
    Tendsto
      (fun n => ((sequence n).continuationContext site payoff fuel).value
        (alternative n) (by
          exact payoffIntegrable_of_bounded _ payoff hbound)) atTop
      (nhds ((target.continuationContext site payoff fuel).value replacement
        (payoffIntegrable_of_bounded _ payoff hbound))) := by
  let kernel (n : ℕ) (history : M.InformationHistory who site.1) : PMF E.History :=
    M.runBehavioralFrom
      (Profile.update (sig := M.behavioralSignature)
        (sequence n).strategy who (alternative n)) fuel history.1
  let kernelLimit (history : M.InformationHistory who site.1) : PMF E.History :=
    M.runBehavioralFrom
      (Profile.update (sig := M.behavioralSignature)
        target.strategy who replacement) fuel history.1
  have hkernel (history : M.InformationHistory who site.1) :
      PMFConvergesPointwise (fun n => kernel n history) (kernelLimit history) :=
    M.runBehavioralFrom_convergesPointwise
      (M.update_convergesPointwise hstrategy who halternative) fuel history.1
  let conditionalValue (n : ℕ) (history : M.InformationHistory who site.1) : ℝ :=
    expect (kernel n history) payoff
      (payoffIntegrable_of_bounded (kernel n history) payoff hbound)
  let conditionalValueLimit (history : M.InformationHistory who site.1) : ℝ :=
    expect (kernelLimit history) payoff
      (payoffIntegrable_of_bounded (kernelLimit history) payoff hbound)
  have hconditional (history : M.InformationHistory who site.1) :
      Tendsto (fun n => conditionalValue n history) atTop
        (nhds (conditionalValueLimit history)) := by
    exact (hkernel history).expect_varying_of_bounded
      (observable := fun _ => payoff) (limit := payoff)
      (fun _ value => hbound value) (fun _ => tendsto_const_nhds)
  have hconditionalBound (n : ℕ) (history : M.InformationHistory who site.1) :
      |conditionalValue n history| ≤ C :=
    expect_abs_le_of_bounded hC hbound
      (payoffIntegrable_of_bounded (kernel n history) payoff hbound)
  have hconditionalLimitBound (history : M.InformationHistory who site.1) :
      |conditionalValueLimit history| ≤ C := by
    exact le_of_tendsto ((hconditional history).abs)
      (Eventually.of_forall fun n => hconditionalBound n history)
  have hresult := hbelief.expect_varying_of_bounded
    (observable := conditionalValue) (limit := conditionalValueLimit)
    (fun n history => hconditionalBound n history) hconditional
  have hseq (n : ℕ) :=
    (sequence n).continuationContext_value_tower site payoff fuel
      (alternative n)
      (payoffIntegrable_of_bounded _ payoff hbound)
      (fun history => payoffIntegrable_of_bounded
        (kernel n history) payoff hbound)
  have htarget := target.continuationContext_value_tower site payoff fuel
    replacement (payoffIntegrable_of_bounded _ payoff hbound)
    (fun history => payoffIntegrable_of_bounded
      (kernelLimit history) payoff hbound)
  simpa only [hseq, htarget, kernel, kernelLimit, conditionalValue,
    conditionalValueLimit] using hresult

/-- Finite terminal carriers bound every payoff, so the general bounded-payoff
continuity theorem specializes to arbitrary finite-history payoffs. -/
theorem continuationContext_value_tendsto
    [DecidableEq ι] [Fintype E.History]
    {sequence : ℕ → M.BehavioralAssessment} {target : M.BehavioralAssessment}
    (hstrategy : ∀ i info, PMFConvergesPointwise
      (fun n => (sequence n).strategy i info) (target.strategy i info))
    (who : ι) (site : M.InformationSite who)
    (hbelief : PMFConvergesPointwise
      (fun n => (sequence n).belief who site) (target.belief who site))
    {alternative : ℕ → M.BehavioralPolicy who}
    {replacement : M.BehavioralPolicy who}
    (halternative : ∀ info, PMFConvergesPointwise
      (fun n => alternative n info) (replacement info))
    (payoff : E.History → ℝ) (fuel : ℕ) :
    Tendsto (fun n => ((sequence n).continuationContext site payoff fuel).value
      (alternative n) (by exact payoffIntegrable_of_finite _ payoff)) atTop
      (nhds ((target.continuationContext site payoff fuel).value replacement
        (by exact payoffIntegrable_of_finite _ payoff))) := by
  let C := ∑ history : E.History, |payoff history|
  have hC : 0 ≤ C := by
    apply Finset.sum_nonneg
    intro history _
    exact abs_nonneg _
  have hbound (history : E.History) : |payoff history| ≤ C := by
    dsimp [C]
    exact Finset.single_le_sum (fun history _ => abs_nonneg (payoff history))
      (Finset.mem_univ history)
  have hresult := M.continuationContext_value_tendsto_of_bounded
    hstrategy who site hbelief halternative payoff fuel C hC hbound
  simpa only [Context.value, expect_proof_irrel] using hresult

end GameTheory.Protocol.InformationModel
