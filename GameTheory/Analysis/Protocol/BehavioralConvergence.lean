/-
# Limits of behavioral continuation values

Coordinate convergence of behavioral policies passes through the canonical
bounded runner. Joint convergence of beliefs then passes through assessment
continuation values, including varying whole-policy deviations.
-/

import GameTheory.Analysis.Protocol.BehavioralContinuity
import GameTheory.Math.Probability.Simplex

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
    [Fintype E.State] [∀ i, Fintype (E.Action i)]
    {sequence : ℕ → (i : ι) → M.BehavioralPolicy i}
    {target : (i : ι) → M.BehavioralPolicy i}
    (hlimit : ∀ i info, FinDistConvergesPointwise (fun n => sequence n i info)
      (target i info)) (fuel : ℕ) (history : E.History) :
    FinDistConvergesPointwise (fun n => M.runBehavioralFrom (sequence n) fuel history)
      (M.runBehavioralFrom target fuel history) := by
  classical
  let X := (i : ι) → (info : M.InfoState i) → simplexWeights (M.Choice i info)
  let profile (x : X) (i : ι) (info : M.InfoState i) : FinDist (M.Choice i info) :=
    FinDist.ofSimplex (x i info).2
  let weights (p : (i : ι) → M.BehavioralPolicy i) : X := fun i info =>
    ⟨(p i info).prob, (p i info).prob_mem_simplexWeights⟩
  have hprofile : ∀ i info choice,
      Continuous fun x : X => (profile x i info).prob choice := by
    intro i info choice
    simp only [profile, FinDist.prob_ofSimplex]
    exact (continuous_apply choice).comp (continuous_subtype_val.comp
      ((continuous_apply info).comp (continuous_apply i)))
  have hweights : Tendsto (fun n => weights (sequence n)) atTop (nhds (weights target)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro info
    apply tendsto_subtype_rng.mpr
    exact tendsto_pi_nhds.mpr (hlimit i info)
  intro terminal
  have h := ((M.continuous_runBehavioralFrom_prob profile hprofile fuel history terminal).tendsto
    (weights target)).comp hweights
  simpa only [Function.comp_def, profile, weights, FinDist.ofSimplex_prob] using h

omit [Fintype ι] in
/-- Unilateral replacement preserves coordinate convergence. -/
theorem update_convergesPointwise [DecidableEq ι]
    {sequence : ℕ → (i : ι) → M.BehavioralPolicy i}
    {target : (i : ι) → M.BehavioralPolicy i}
    (hlimit : ∀ i info, FinDistConvergesPointwise (fun n => sequence n i info)
      (target i info))
    (who : ι) {alternative : ℕ → M.BehavioralPolicy who}
    {replacement : M.BehavioralPolicy who}
    (halternative : ∀ info, FinDistConvergesPointwise
      (fun n => alternative n info) (replacement info))
    (i : ι) (info : M.InfoState i) :
    FinDistConvergesPointwise
      (fun n => (Profile.update (sig := M.behavioralSignature)
        (sequence n) who (alternative n)) i info)
      ((Profile.update (sig := M.behavioralSignature) target who replacement) i info) := by
  by_cases hi : i = who
  · subst i
    simpa only [Profile.update_same] using halternative info
  · simpa only [Profile.update_of_ne _ _ hi] using hlimit i info

/-- Converging assessments and deviations have converging continuation values. -/
theorem continuationContext_value_tendsto
    [DecidableEq ι] [Fintype E.State] [Fintype E.History]
    [∀ i, Fintype (E.Action i)]
    {sequence : ℕ → M.BehavioralAssessment} {target : M.BehavioralAssessment}
    (hstrategy : ∀ i info, FinDistConvergesPointwise
      (fun n => (sequence n).strategy i info) (target.strategy i info))
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hbelief : FinDistConvergesPointwise
      (fun n => (sequence n).belief who site) (target.belief who site))
    {alternative : ℕ → M.BehavioralPolicy who} {replacement : M.BehavioralPolicy who}
    (halternative : ∀ info, FinDistConvergesPointwise
      (fun n => alternative n info) (replacement info))
    (payoff : E.History → ℝ) (fuel : ℕ) :
    Tendsto (fun n => ((sequence n).continuationContext site payoff fuel).value
      (alternative n)) atTop
      (nhds ((target.continuationContext site payoff fuel).value replacement)) := by
  simp_rw [BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  exact hbelief.expect_varying fun history =>
    (M.runBehavioralFrom_convergesPointwise
      (M.update_convergesPointwise hstrategy who halternative) fuel history.1).expect payoff

end GameTheory.Protocol.InformationModel
