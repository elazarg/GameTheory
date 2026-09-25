/-
# Existence of finite perfect-recall sequential equilibria

Positive uniform perturbations have locally optimal Bayes assessments.
Perfect recall upgrades those exact local inequalities to whole-policy
inequalities. Compactness supplies one joint strategy/belief limit, and
vanishingly perturbed deviations recover unrestricted sequential rationality.

The conclusion uses the existing assessment predicates and continuation
runner. The horizon is certified to reach termination, not a rolling deadline.
-/

import GameTheory.Analysis.Protocol.AssessmentCompactness
import GameTheory.Analysis.Protocol.SequentialPerturbation
import GameTheory.Analysis.Protocol.SequentialRationality
import GameTheory.Analysis.Protocol.SequentialLimits

noncomputable section

namespace GameTheory.Protocol.InformationModel

open Filter GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {E : ExecutionProtocol.{uι, us, ua} ι}
    (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Every finite perfect-recall protocol with inhabited total policies has a
consistent, sequentially rational assessment at any positive certified
terminal horizon. The fallback inhabits menus even at unused information
states; no equilibrium or approximation witness is assumed. -/
theorem exists_sequentialEquilibriumWithin
    [Fintype E.State] [Fintype E.History] [∀ i, Fintype (E.Action i)]
    [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)]
    (hrecall : M.PerfectRecall) (fallback : (i : ι) → M.Policy i)
    (payoff : ι → E.History → ℝ) (fuel : ℕ)
    (hbound : E.BoundedHorizon (fuel + 1)) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.IsSequentiallyRationalWithin payoff (fuel + 1) ∧
        assessment.IsSequentiallyConsistent
          (M.decisionInformationAntichain_of_perfectRecall hrecall) := by
  classical
  let (i : ι) (info : M.InfoState i) : Fintype (M.Choice i info) := inferInstance
  let (i : ι) (info : M.InfoState i) : Nonempty (M.Choice i info) := ⟨fallback i info⟩
  let (i : ι) (site : M.InformationSite i) :
      Fintype (M.InformationHistory i site.1) := inferInstance
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
    M.exists_uniformTremble_locallyOptimal_bayesAssessment
      (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
      (M.decisionInformationAntichain_of_perfectRecall hrecall)
      (weight n) (hpositive n) (hone n) payoff fuel
  obtain ⟨assessment, subseq, hsubseq, hstrategy, hconvergence⟩ :=
    M.exists_subseq_behavioralAssessmentConvergesPointwise sequence
  let repair (n : ℕ) (i : ι) (alternative : M.BehavioralPolicy i) :
    M.BehavioralPolicy i := fun info =>
    mix (weight (subseq n)) (hpositive (subseq n)).le (hone (subseq n))
      (PMF.uniformOfFintype _) (alternative info)
  have hrepair (i : ι) (alternative : M.BehavioralPolicy i) (info : M.InfoState i) :
      PMFConvergesPointwise (fun n => repair n i alternative info) (alternative info) :=
    pmfConvergesPointwise_mix_zero (fun n => weight (subseq n))
      (fun n => (hpositive (subseq n)).le) (fun n => hone (subseq n))
      (hzero.comp hsubseq.tendsto_atTop) _ _
  have hlocalFinite (n : ℕ) (i : ι) (site : M.InformationSite i)
      (law : PMF (M.Choice i site.1))
      (hlaw : law ∈ M.uniformTrembleLaws (weight n)
        (hpositive n).le (hone n) i site.1) :
      ((sequence n).continuationContext site (payoff i) (fuel + 1)).value
          (((sequence n).strategy i).withLaw site.1 law)
            (payoffIntegrable_of_finite _ _) ≤
        ((sequence n).continuationContext site (payoff i) (fuel + 1)).value
          ((sequence n).strategy i) (payoffIntegrable_of_finite _ _) := by
    obtain ⟨_halt, _hbase, hle⟩ := hlocal n i site law hlaw
    exact hle
  refine ⟨assessment, ?_, ?_⟩
  · apply BehavioralAssessment.isSequentiallyRationalWithin_of_converging_deviations
      hstrategy (fun i site => hconvergence.belief i site) repair hrepair payoff (fuel + 1)
    intro n who site alternative
    apply BehavioralAssessment.continuation_value_le_of_locallyOptimal M hrecall
      (sequence (subseq n)) (hfull (subseq n)) (hbayes (subseq n))
      (fun i info law => law ∈ M.uniformTrembleLaws
        (weight (subseq n)) (hpositive (subseq n)).le (hone (subseq n)) i info)
      (hfeasible (subseq n)) payoff hbound (hlocalFinite (subseq n)) who site
    intro info
    exact ⟨alternative info, rfl⟩
  · exact hconvergence.isSequentiallyConsistent
      (M.decisionInformationAntichain_of_perfectRecall hrecall)
      (fun n => hfull (subseq n)) (fun n => hbayes (subseq n))

end GameTheory.Protocol.InformationModel
