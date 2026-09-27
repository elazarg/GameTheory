/-
# Tight behavioral-assessment subsequences

Countably many uniformly tight strategy and belief coordinates admit one
common pointwise PMF subsequence. The strong theorem covers every raw
information state; the site-only theorem covers genuine decision sites and
leaves other raw strategy values at the first assessment. Finite carriers
imply tightness automatically.
-/

import GameTheory.Analysis.Protocol.Sequential
import GameTheory.Math.Probability.Compactness

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory GameTheory.Math.Probability

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι} {M : InformationModel E}

/-- Coordinatewise uniform tightness and countably many raw information
coordinates give one common strategy/belief subsequence. Choice and history
carriers may be arbitrary, including uncountable ambient types. -/
theorem exists_subseq_behavioralAssessmentConvergesPointwise_of_uniformlyTight
    [Countable ι] [∀ i, Countable (M.InfoState i)]
    (sequence : ℕ → M.BehavioralAssessment)
    (hstrategyTight : ∀ i info,
      UniformlyTight (fun n => (sequence n).strategy i info))
    (hbeliefTight : ∀ i site,
      UniformlyTight (fun n => (sequence n).belief i site)) :
    ∃ (target : M.BehavioralAssessment) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
        (∀ i info, PMFConvergesPointwise
          (fun n => (sequence (subseq n)).strategy i info) (target.strategy i info)) ∧
        BehavioralAssessmentConvergesPointwise (fun n => sequence (subseq n)) target := by
  classical
  obtain ⟨strategy, first, hfirst, hstrategy⟩ :=
    exists_subseq_pmfConvergesPointwise_pi_of_uniformlyTight
      (ι := (i : ι) × M.InfoState i)
      (A := fun coordinate => M.Choice coordinate.1 coordinate.2)
      (fun n coordinate => (sequence n).strategy coordinate.1 coordinate.2)
      (fun coordinate => hstrategyTight coordinate.1 coordinate.2)
  have (i : ι) : Countable (M.InformationSite i) := by
    unfold InformationSite
    infer_instance
  obtain ⟨belief, second, hsecond, hbelief⟩ :=
    exists_subseq_pmfConvergesPointwise_pi_of_uniformlyTight
      (ι := (i : ι) × M.InformationSite i)
      (A := fun coordinate => M.InformationHistory coordinate.1 coordinate.2.1)
      (fun n coordinate => (sequence (first n)).belief coordinate.1 coordinate.2)
      (fun coordinate => (hbeliefTight coordinate.1 coordinate.2).comp first)
  let target : M.BehavioralAssessment :=
    { strategy := fun i info => strategy ⟨i, info⟩
      belief := fun i site => belief ⟨i, site⟩ }
  have htotal : ∀ i info, PMFConvergesPointwise
      (fun n => (sequence (first (second n))).strategy i info) (target.strategy i info) :=
    fun i info => (hstrategy ⟨i, info⟩).subseq hsecond
  exact ⟨target, first ∘ second, hfirst.comp hsecond, htotal,
    ⟨fun i site => htotal i site.1, fun i site => hbelief ⟨i, site⟩⟩⟩

/-- Tightness only at genuine decision sites suffices to extract an
assessment limit at those sites. Values of the target strategy at other raw
information states come from the first approximation and carry no limit claim. -/
theorem exists_subseq_behavioralAssessmentConvergesPointwise_atSites_of_uniformlyTight
    [Countable ι] [∀ i, Countable (M.InformationSite i)]
    (sequence : ℕ → M.BehavioralAssessment)
    (hstrategyTight : ∀ i (site : M.InformationSite i),
      UniformlyTight (fun n => (sequence n).strategy i site.1))
    (hbeliefTight : ∀ i (site : M.InformationSite i),
      UniformlyTight (fun n => (sequence n).belief i site)) :
    ∃ (target : M.BehavioralAssessment) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
        BehavioralAssessmentConvergesPointwise (fun n => sequence (subseq n)) target := by
  classical
  obtain ⟨strategy, first, hfirst, hstrategy⟩ :=
    exists_subseq_pmfConvergesPointwise_pi_of_uniformlyTight
      (ι := (i : ι) × M.InformationSite i)
      (A := fun coordinate => M.Choice coordinate.1 coordinate.2.1)
      (fun n coordinate => (sequence n).strategy coordinate.1 coordinate.2.1)
      (fun coordinate => hstrategyTight coordinate.1 coordinate.2)
  obtain ⟨belief, second, hsecond, hbelief⟩ :=
    exists_subseq_pmfConvergesPointwise_pi_of_uniformlyTight
      (ι := (i : ι) × M.InformationSite i)
      (A := fun coordinate => M.InformationHistory coordinate.1 coordinate.2.1)
      (fun n coordinate => (sequence (first n)).belief coordinate.1 coordinate.2)
      (fun coordinate => (hbeliefTight coordinate.1 coordinate.2).comp first)
  let target : M.BehavioralAssessment :=
    { strategy := fun i info =>
        if h : M.IsDecisionInfo i info then strategy ⟨i, ⟨info, h⟩⟩
        else (sequence 0).strategy i info
      belief := fun i site => belief ⟨i, site⟩ }
  have hsite (i : ι) (site : M.InformationSite i) :
      PMFConvergesPointwise
        (fun n => (sequence (first (second n))).strategy i site.1)
        (target.strategy i site.1) := by
    rcases site with ⟨info, hinfo⟩
    have h := (hstrategy ⟨i, ⟨info, hinfo⟩⟩).subseq hsecond
    simpa only [target, dite_eq_left hinfo] using h
  exact ⟨target, first ∘ second, hfirst.comp hsecond,
    ⟨hsite, fun i site => hbelief ⟨i, site⟩⟩⟩

/-- Finite strategy and belief carriers satisfy the tightness hypotheses
automatically; the extraction includes every raw information coordinate. -/
theorem exists_subseq_behavioralAssessmentConvergesPointwise
    [Countable ι] [∀ i, Countable (M.InfoState i)]
    [∀ i info, Finite (M.Choice i info)]
    [∀ (i : ι) (site : M.InformationSite i),
      Finite (M.InformationHistory i site.1)]
    (sequence : ℕ → M.BehavioralAssessment) :
    ∃ (target : M.BehavioralAssessment) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
        (∀ i info, PMFConvergesPointwise
          (fun n => (sequence (subseq n)).strategy i info) (target.strategy i info)) ∧
        BehavioralAssessmentConvergesPointwise (fun n => sequence (subseq n)) target := by
  exact exists_subseq_behavioralAssessmentConvergesPointwise_of_uniformlyTight
    sequence
    (fun i info => uniformlyTight_of_finite (fun n => (sequence n).strategy i info))
    (fun i site => uniformlyTight_of_finite (fun n => (sequence n).belief i site))

/-- A convergent sequence of fully mixed Bayes-consistent assessments
witnesses sequential consistency of its limit. This applies in particular to
the common subsequence extracted by assessment compactness. -/
theorem BehavioralAssessmentConvergesPointwise.isSequentiallyConsistent
    [Fintype ι]
    {sequence : ℕ → M.BehavioralAssessment} {target : M.BehavioralAssessment}
    (hlimit : BehavioralAssessmentConvergesPointwise sequence target)
    (hantichain : M.DecisionInformationAntichain)
    (hfullyMixed : ∀ n, (sequence n).IsFullyMixed)
    (hbayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) hantichain) :
    target.IsSequentiallyConsistent hantichain :=
  ⟨sequence, fun n => ⟨hfullyMixed n, hbayes n⟩, hlimit⟩

end GameTheory.Protocol.InformationModel
