/-
# Sequential compactness of finite behavioral assessments

A finite family of finite strategy and belief simplices is sequentially
compact. Extraction retains convergence at every raw information state,
including those outside the reached decision sites used in the consistency
predicate. This stronger conclusion supports continuity of whole policies.
-/

import GameTheory.Analysis.Protocol.Sequential
import GameTheory.Math.Probability.Compactness

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory GameTheory.Math.Probability

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι} {M : InformationModel E}

/-- Every sequence of assessments with finitely many finite strategy and
belief coordinates has a common convergent subsequence. Strategy convergence
holds at every raw information state, and the resulting assessment convergence
also includes convergence of all information-site beliefs. The sequence itself
supplies the laws, so no additional nonemptiness assumptions are needed. -/
theorem exists_subseq_behavioralAssessmentConvergesPointwise
    [Fintype ι] [∀ i, Fintype (M.InfoState i)]
    [∀ i info, Fintype (M.Choice i info)]
    [∀ (i : ι) (site : M.InformationSite i),
      Fintype (M.InformationHistory i site.1)]
    (sequence : ℕ → M.BehavioralAssessment) :
    ∃ (target : M.BehavioralAssessment) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
        (∀ i info, PMFConvergesPointwise
          (fun n => (sequence (subseq n)).strategy i info) (target.strategy i info)) ∧
        BehavioralAssessmentConvergesPointwise (fun n => sequence (subseq n)) target := by
  classical
  obtain ⟨strategy, first, hfirst, hstrategy⟩ :=
    exists_subseq_pmfConvergesPointwise_pi
      (ι := (i : ι) × M.InfoState i)
      (A := fun coordinate => M.Choice coordinate.1 coordinate.2)
      (fun n coordinate => (sequence n).strategy coordinate.1 coordinate.2)
  let (i : ι) : Fintype (M.InformationSite i) := by
    unfold InformationSite
    infer_instance
  obtain ⟨belief, second, hsecond, hbelief⟩ :=
    exists_subseq_pmfConvergesPointwise_pi
      (ι := (i : ι) × M.InformationSite i)
      (A := fun coordinate => M.InformationHistory coordinate.1 coordinate.2.1)
      (fun n coordinate => (sequence (first n)).belief coordinate.1 coordinate.2)
  let target : M.BehavioralAssessment :=
    { strategy := fun i info => strategy ⟨i, info⟩
      belief := fun i site => belief ⟨i, site⟩ }
  have htotal : ∀ i info, PMFConvergesPointwise
      (fun n => (sequence (first (second n))).strategy i info) (target.strategy i info) :=
    fun i info => (hstrategy ⟨i, info⟩).subseq hsecond
  exact ⟨target, first ∘ second, hfirst.comp hsecond, htotal,
    ⟨fun i site => htotal i site.1, fun i site => hbelief ⟨i, site⟩⟩⟩

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
