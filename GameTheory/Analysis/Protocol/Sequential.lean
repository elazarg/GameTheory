/-
# Pointwise consistency and sequential equilibrium

Kreps-Wilson consistency is the analytic half of sequential equilibrium: a
target assessment is a pointwise limit of fully mixed assessments obeying
Bayes' rule. The assessment data, Bayes predicate, and sequential rationality
remain in stable Protocol; only convergence and the resulting specialization
live behind this one-way bridge.
-/

import GameTheory.Analysis.FiniteLaw
import GameTheory.Protocol.BehavioralAssessment

noncomputable section

namespace GameTheory.Protocol

open GameTheory GameTheory.Analysis Probability

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace InformationModel

variable {M : InformationModel E}

/-- Every local choice receives positive probability. -/
def BehavioralAssessment.IsFullyMixed
    (A : M.BehavioralAssessment) : Prop :=
  ∀ (i : ι) (site : M.InformationSite i),
    (A.strategy i site.1).FullSupport

/-- Pointwise convergence of behavioral strategies and history beliefs. -/
def BehavioralAssessmentConvergesPointwise
    (sequence : ℕ → M.BehavioralAssessment)
    (target : M.BehavioralAssessment) : Prop :=
  (∀ (i : ι) (site : M.InformationSite i),
      FinDistConvergesPointwise
        (fun n => (sequence n).strategy i site.1)
        (target.strategy i site.1)) ∧
    ∀ (i : ι) (site : M.InformationSite i),
      FinDistConvergesPointwise
        (fun n => (sequence n).belief i site)
        (target.belief i site)

/-- The strategy-coordinate consequence of pointwise assessment convergence. -/
theorem BehavioralAssessmentConvergesPointwise.strategy
    {sequence : ℕ → M.BehavioralAssessment}
    {target : M.BehavioralAssessment}
    (h : BehavioralAssessmentConvergesPointwise sequence target)
    (i : ι) (site : M.InformationSite i) :
    FinDistConvergesPointwise
      (fun n => (sequence n).strategy i site.1)
      (target.strategy i site.1) :=
  h.1 i site

/-- The belief-coordinate consequence of pointwise assessment convergence. -/
theorem BehavioralAssessmentConvergesPointwise.belief
    {sequence : ℕ → M.BehavioralAssessment}
    {target : M.BehavioralAssessment}
    (h : BehavioralAssessmentConvergesPointwise sequence target)
    (i : ι) (site : M.InformationSite i) :
    FinDistConvergesPointwise
      (fun n => (sequence n).belief i site)
      (target.belief i site) :=
  h.2 i site

/-- The constant assessment sequence converges in every strategy and belief
coordinate. -/
theorem behavioralAssessmentConvergesPointwise_const
    (A : M.BehavioralAssessment) :
    BehavioralAssessmentConvergesPointwise (fun _ => A) A :=
  ⟨fun _ _ => finDistConvergesPointwise_const _,
    fun _ _ => finDistConvergesPointwise_const _⟩

/-- Kreps-Wilson consistency for a finite protocol assessment: a pointwise
limit of fully mixed, Bayes-consistent behavioral assessments. -/
def BehavioralAssessment.IsSequentiallyConsistent
    [Fintype ι] (A : M.BehavioralAssessment)
    (hantichain : M.DecisionInformationAntichain)
    [∀ (i : ι) (site : M.InformationSite i),
      Fintype (M.InformationHistory i site.1)] : Prop :=
  A.IsLimitConsistent
    BehavioralAssessment.IsFullyMixed
    (fun assessment =>
      BehavioralAssessment.IsBayesConsistent M assessment hantichain)
    BehavioralAssessmentConvergesPointwise

/-- A fully mixed assessment that already obeys finite Bayes' rule is
sequentially consistent, witnessed by the constant approximating sequence. -/
theorem BehavioralAssessment.IsSequentiallyConsistent.of_fullyMixed_bayes
    [Fintype ι] {A : M.BehavioralAssessment}
    [∀ (i : ι) (site : M.InformationSite i),
      Fintype (M.InformationHistory i site.1)]
    (hantichain : M.DecisionInformationAntichain)
    (hfull : A.IsFullyMixed)
    (hbayes : BehavioralAssessment.IsBayesConsistent M A hantichain) :
    A.IsSequentiallyConsistent hantichain :=
  ⟨fun _ => A, fun _ => ⟨hfull, hbayes⟩,
    behavioralAssessmentConvergesPointwise_const A⟩

/-- Sequential equilibrium is the existing context-local rationality predicate
paired with Kreps-Wilson consistency. -/
def BehavioralAssessment.IsSequentialEquilibriumFor
    [Fintype ι] (A : M.BehavioralAssessment)
    [∀ (i : ι) (site : M.InformationSite i),
      Fintype (M.InformationHistory i site.1)]
    (hantichain : M.DecisionInformationAntichain)
    (context : (i : ι) → (site : M.InformationSite i) →
      GameTheory.Protocol.Context
        (M.BehavioralPolicy i) E.History) : Prop :=
  A.IsSequentiallyRational context ∧ A.IsSequentiallyConsistent hantichain

theorem BehavioralAssessment.isSequentialEquilibriumFor_iff
    [Fintype ι] (A : M.BehavioralAssessment)
    [∀ (i : ι) (site : M.InformationSite i),
      Fintype (M.InformationHistory i site.1)]
    (hantichain : M.DecisionInformationAntichain)
    (context : (i : ι) → (site : M.InformationSite i) →
      GameTheory.Protocol.Context
        (M.BehavioralPolicy i) E.History) :
    A.IsSequentialEquilibriumFor hantichain context ↔
      A.IsSequentiallyRational context ∧ A.IsSequentiallyConsistent hantichain :=
  Iff.rfl

end InformationModel

end GameTheory.Protocol
