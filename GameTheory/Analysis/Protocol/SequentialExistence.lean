/-
# Existence of sequential equilibria

Positive uniform perturbations have locally optimal Bayes assessments.
Recall at decision information states upgrades those exact local inequalities
to whole-policy inequalities; observations made while a player cannot act may
forget its own play. Compactness supplies one joint strategy/belief limit, and
vanishingly perturbed deviations recover unrestricted sequential rationality.
-/

import GameTheory.Analysis.Protocol.AssessmentCompactness
import GameTheory.Analysis.Protocol.SequentialPerturbation
import GameTheory.Analysis.Protocol.SequentialOneShot
import GameTheory.Analysis.Protocol.SequentialLimits

noncomputable section

namespace GameTheory.Protocol.InformationModel

open Filter GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {E : ExecutionProtocol.{uι, us, ua} ι}
    (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Every decision-recall protocol with finitely many histories and inhabited
total policies has a consistent, sequentially rational assessment. Decision
sites and their menus are then finite, while the state, action, and
information-state carriers may be infinite; the fallback inhabits menus at
information values that no history reaches. No equilibrium or approximation
witness is assumed. -/
theorem exists_sequentialEquilibrium [Finite E.History]
    (hrecall : M.DecisionRecall) (fallback : (i : ι) → M.Policy i)
    (payoff : ι → E.History → ℝ) (certificate : E.WellFoundedHistories) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.IsSequentiallyRational certificate payoff ∧
        assessment.IsSequentiallyConsistent
          (hrecall.decisionInformationAntichain) := by
  classical
  let weight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have hpositive (n : ℕ) : 0 < weight n := by
    exact one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))
  have hone (n : ℕ) : weight n ≤ 1 := by
    apply (div_le_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))).mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hzero : Tendsto weight atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    convert h using 1
    funext n
    simp [weight, Nat.cast_add]
    ring
  choose sequence hfull hbayes hfeasible hlocal using fun n =>
    M.exists_uniformTremble_locallyOptimal_bayesAssessment fallback
      hrecall.actsOnceWhereItMatters
      (hrecall.decisionInformationAntichain)
      (weight n) (hpositive n) (hone n) payoff certificate
  obtain ⟨assessment, subseq, hsubseq, hconvergence⟩ :=
    M.exists_subseq_behavioralAssessmentConvergesPointwise_atSites_of_uniformlyTight sequence
      (fun _ _ => uniformlyTight_of_finite _) (fun _ _ => uniformlyTight_of_finite _)
  let tremble (n : ℕ) {i : ι} (site : M.InformationSite i) (law : PMF (M.Choice i site.1)) :
      PMF (M.Choice i site.1) :=
    mix (weight (subseq n)) (hpositive (subseq n)).le (hone (subseq n))
      (@PMF.uniformOfFintype _ (Fintype.ofFinite _) _) law
  let repair (n : ℕ) (i : ι) (alternative : M.BehavioralPolicy i) :
      M.BehavioralPolicy i := fun info =>
    if hsite : M.IsDecisionInfo i info then tremble n ⟨info, hsite⟩ (alternative info)
    else alternative info
  have hrepair_site (n : ℕ) (i : ι) (alternative : M.BehavioralPolicy i)
      (site : M.InformationSite i) :
      repair n i alternative site.1 = tremble n site (alternative site.1) :=
    dite_eq_left site.2
  have hrepair (i : ι) (alternative : M.BehavioralPolicy i) (site : M.InformationSite i) :
      PMFConvergesPointwise (fun n => repair n i alternative site.1) (alternative site.1) := by
    simp only [hrepair_site]
    exact pmfConvergesPointwise_mix_zero (fun n => weight (subseq n))
      (fun n => (hpositive (subseq n)).le) (fun n => hone (subseq n))
      (hzero.comp hsubseq.tendsto_atTop) _ _
  refine ⟨assessment, ?_, ?_⟩
  · apply BehavioralAssessment.isSequentiallyRational_of_converging_deviations M certificate
      (fun i site => hconvergence.strategy i site) (fun i site => hconvergence.belief i site)
      repair hrepair payoff
    intro n who site alternative
    apply BehavioralAssessment.continuation_value_le_of_locallyOptimal M hrecall
      (sequence (subseq n)) (hfull (subseq n)) (hbayes (subseq n))
      (fun i info law => ∀ [Finite (M.Choice i info)] [Nonempty (M.Choice i info)],
        law ∈ M.uniformTrembleLaws
          (weight (subseq n)) (hpositive (subseq n)).le (hone (subseq n)) i info)
      payoff certificate
      (fun i site law hlaw => (hlocal (subseq n) i site law hlaw).2.2) who site
    intro later _ _
    exact ⟨alternative later.1, hrepair_site n who alternative later⟩
  · exact hconvergence.isSequentiallyConsistent
      (hrecall.decisionInformationAntichain)
      (fun n => hfull (subseq n)) (fun n => hbayes (subseq n))

end GameTheory.Protocol.InformationModel
