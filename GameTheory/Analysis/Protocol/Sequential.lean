/-
# Pointwise consistency and sequential equilibrium

Kreps-Wilson consistency is the analytic half of sequential equilibrium: a
target assessment is a pointwise limit of fully mixed assessments obeying
Bayes' rule. The assessment data, Bayes predicate, and sequential rationality
remain in stable Protocol; only convergence and the resulting specialization
live behind this one-way bridge.
-/

import GameTheory.Math.Probability.Convergence
import GameTheory.Protocol.BehavioralBayes
import GameTheory.Protocol.BehavioralTerminal

noncomputable section

namespace GameTheory.Protocol

open GameTheory GameTheory.Math.Probability

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace InformationModel

variable {M : InformationModel E}

/-- Every local choice receives positive probability. -/
def BehavioralAssessment.IsFullyMixed
    (A : M.BehavioralAssessment) : Prop :=
  ∀ (i : ι) (site : M.InformationSite i),
    ∀ choice, choice ∈ (A.strategy i site.1).support

/-- Pointwise convergence of behavioral strategies and history beliefs. -/
def BehavioralAssessmentConvergesPointwise
    (sequence : ℕ → M.BehavioralAssessment)
    (target : M.BehavioralAssessment) : Prop :=
  (∀ (i : ι) (site : M.InformationSite i),
      PMFConvergesPointwise
        (fun n => (sequence n).strategy i site.1)
        (target.strategy i site.1)) ∧
    ∀ (i : ι) (site : M.InformationSite i),
      PMFConvergesPointwise
        (fun n => (sequence n).belief i site)
        (target.belief i site)

/-- The strategy-coordinate consequence of pointwise assessment convergence. -/
theorem BehavioralAssessmentConvergesPointwise.strategy
    {sequence : ℕ → M.BehavioralAssessment}
    {target : M.BehavioralAssessment}
    (h : BehavioralAssessmentConvergesPointwise sequence target)
    (i : ι) (site : M.InformationSite i) :
    PMFConvergesPointwise
      (fun n => (sequence n).strategy i site.1)
      (target.strategy i site.1) :=
  h.1 i site

/-- The belief-coordinate consequence of pointwise assessment convergence. -/
theorem BehavioralAssessmentConvergesPointwise.belief
    {sequence : ℕ → M.BehavioralAssessment}
    {target : M.BehavioralAssessment}
    (h : BehavioralAssessmentConvergesPointwise sequence target)
    (i : ι) (site : M.InformationSite i) :
    PMFConvergesPointwise
      (fun n => (sequence n).belief i site)
      (target.belief i site) :=
  h.2 i site

/-- The constant assessment sequence converges in every strategy and belief
coordinate. -/
theorem behavioralAssessmentConvergesPointwise_const
    (A : M.BehavioralAssessment) :
    BehavioralAssessmentConvergesPointwise (fun _ => A) A :=
  ⟨fun _ _ => pmfConvergesPointwise_const _,
    fun _ _ => pmfConvergesPointwise_const _⟩

/-- Kreps-Wilson consistency: a pointwise limit of fully mixed,
Bayes-consistent behavioral assessments. No finite action or history carrier
is required. The approximating laws themselves witness full support. -/
def BehavioralAssessment.IsSequentiallyConsistent
    [Fintype ι] (A : M.BehavioralAssessment)
    (hantichain : M.DecisionInformationAntichain) : Prop :=
  A.IsLimitConsistent
    BehavioralAssessment.IsFullyMixed
    (fun assessment =>
      BehavioralAssessment.IsBayesConsistent M assessment hantichain)
    BehavioralAssessmentConvergesPointwise

/-- A fully mixed assessment that already obeys Bayes' rule is
sequentially consistent, witnessed by the constant approximating sequence. -/
theorem BehavioralAssessment.IsSequentiallyConsistent.of_fullyMixed_bayes
    [Fintype ι] {A : M.BehavioralAssessment}
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
    (hantichain : M.DecisionInformationAntichain)
    (context : (i : ι) → (site : M.InformationSite i) →
      GameTheory.Protocol.Context
        (M.BehavioralPolicy i) E.History) : Prop :=
  A.IsSequentiallyRationalFor context ∧ A.IsSequentiallyConsistent hantichain

theorem BehavioralAssessment.isSequentialEquilibriumFor_iff
    [Fintype ι] (A : M.BehavioralAssessment)
    (hantichain : M.DecisionInformationAntichain)
    (context : (i : ι) → (site : M.InformationSite i) →
      GameTheory.Protocol.Context
        (M.BehavioralPolicy i) E.History) :
    A.IsSequentialEquilibriumFor hantichain context ↔
      A.IsSequentiallyRationalFor context ∧ A.IsSequentiallyConsistent hantichain :=
  Iff.rfl

/-- Sequential equilibrium: sequential rationality on terminal play together
with Kreps-Wilson consistency. -/
def BehavioralAssessment.IsSequentialEquilibrium
    [Fintype ι] [DecidableEq ι] (A : M.BehavioralAssessment)
    (hantichain : M.DecisionInformationAntichain)
    (certificate : E.WellFoundedHistories) (payoff : ι → E.History → ℝ) : Prop :=
  A.IsSequentialEquilibriumFor hantichain fun i site =>
    A.continuationContext certificate site (payoff i)

theorem BehavioralAssessment.isSequentialEquilibrium_iff
    [Fintype ι] [DecidableEq ι] (A : M.BehavioralAssessment)
    (hantichain : M.DecisionInformationAntichain)
    (certificate : E.WellFoundedHistories) (payoff : ι → E.History → ℝ) :
    A.IsSequentialEquilibrium hantichain certificate payoff ↔
      A.IsSequentiallyRational certificate payoff ∧ A.IsSequentiallyConsistent hantichain :=
  Iff.rfl

/-- Pointwise convergence sees only decision-site strategy coordinates and
history beliefs. Changing other strategy coordinates leaves convergence unchanged. -/
theorem behavioralAssessmentConvergesPointwise_iff_of_agreesAtDecisions
    (sequence : ℕ → M.BehavioralAssessment) {first second : M.BehavioralAssessment}
    (agree : ∀ who, (first.strategy who).AgreesAtDecisions (second.strategy who))
    (beliefs : ∀ who site, first.belief who site = second.belief who site) :
    BehavioralAssessmentConvergesPointwise sequence first ↔
      BehavioralAssessmentConvergesPointwise sequence second := by
  have strategies : ∀ who (site : M.InformationSite who),
      first.strategy who site.1 = second.strategy who site.1 :=
    fun who site => congrFun (agree who) site
  unfold BehavioralAssessmentConvergesPointwise
  simp_rw [strategies, beliefs]

/-- Consistency is unchanged by strategy coordinates outside decision sites
when the history beliefs remain the same; the same perturbation sequence witnesses it. -/
theorem BehavioralAssessment.isSequentiallyConsistent_iff_of_agreesAtDecisions
    [Fintype ι] {first second : M.BehavioralAssessment}
    (agree : ∀ who, (first.strategy who).AgreesAtDecisions (second.strategy who))
    (beliefs : ∀ who site, first.belief who site = second.belief who site)
    (antichain : M.DecisionInformationAntichain) :
    first.IsSequentiallyConsistent antichain ↔
      second.IsSequentiallyConsistent antichain := by
  constructor <;> rintro ⟨sequence, admissible, converges⟩
  · exact ⟨sequence, admissible,
      (behavioralAssessmentConvergesPointwise_iff_of_agreesAtDecisions
        sequence agree beliefs).mp converges⟩
  · exact ⟨sequence, admissible,
      (behavioralAssessmentConvergesPointwise_iff_of_agreesAtDecisions
        sequence agree beliefs).mpr converges⟩

/-- With common history beliefs, agreement at decisions preserves the entire
terminal continuation context, including every whole-policy deviation law. -/
theorem BehavioralAssessment.continuationContext_eq_of_agreesAtDecisions
    [Fintype ι] [DecidableEq ι] {first second : M.BehavioralAssessment}
    (agree : ∀ who, (first.strategy who).AgreesAtDecisions (second.strategy who))
    (beliefs : ∀ who site, first.belief who site = second.belief who site)
    (certificate : E.WellFoundedHistories) {who : ι}
    (site : M.InformationSite who) (payoff : E.History → ℝ) :
    first.continuationContext certificate site payoff =
      second.continuationContext certificate site payoff := by
  apply congrArg₂ (fun outcome continuation => Context.mk outcome continuation)
  · funext alternative
    change (first.belief who site).bind _ = (second.belief who site).bind _
    rw [beliefs who site]
    apply bind_congr_on_support
    intro history _
    apply M.runBehavioralTerminalFrom_eq_of_agreesAtDecisions
    intro player
    by_cases same : player = who
    · subst player
      simp [BehavioralPolicy.AgreesAtDecisions]
    · simpa only [Profile.update_of_ne _ _ same] using agree player
  · rfl

/-- Terminal sequential rationality depends only on decision-site strategy
laws and the common history beliefs. Expected-value guards are preserved by law equality. -/
theorem BehavioralAssessment.isSequentiallyRational_iff_of_agreesAtDecisions
    [Fintype ι] [DecidableEq ι] {first second : M.BehavioralAssessment}
    (agree : ∀ who, (first.strategy who).AgreesAtDecisions (second.strategy who))
    (beliefs : ∀ who site, first.belief who site = second.belief who site)
    (certificate : E.WellFoundedHistories) (payoff : ι → E.History → ℝ) :
    first.IsSequentiallyRational certificate payoff ↔
      second.IsSequentiallyRational certificate payoff := by
  have comparisons : ∀ who (site : M.InformationSite who),
      first.IsSequentiallyRationalAt site
          (first.continuationContext certificate site (payoff who)) ↔
        second.IsSequentiallyRationalAt site
          (second.continuationContext certificate site (payoff who)) := by
    intro who site
    have contexts := BehavioralAssessment.continuationContext_eq_of_agreesAtDecisions
      agree beliefs certificate site (payoff who)
    have incumbent :
        (first.continuationContext certificate site (payoff who)).outcome
            (first.strategy who) =
          (second.continuationContext certificate site (payoff who)).outcome
            (second.strategy who) := by
      change (first.belief who site).bind _ = (second.belief who site).bind _
      simp only [Profile.update_eq_self]
      rw [beliefs who site]
      apply bind_congr_on_support
      intro history _
      exact M.runBehavioralTerminalFrom_eq_of_agreesAtDecisions
        certificate agree history.1
    rw [contexts] at incumbent
    change Context.IsLocallyOptimal _ Set.univ _ ↔ Context.IsLocallyOptimal _ Set.univ _
    rw [contexts]
    unfold Context.IsLocallyOptimal Context.HasValueAt Context.extendedValue
    rw [incumbent]
  unfold BehavioralAssessment.IsSequentiallyRational
    BehavioralAssessment.IsSequentiallyRationalFor
  exact forall_congr' fun who => forall_congr' fun site => comparisons who site

/-- Common beliefs and agreement at decisions preserve terminal sequential equilibrium. -/
theorem BehavioralAssessment.isSequentialEquilibrium_iff_of_agreesAtDecisions
    [Fintype ι] [DecidableEq ι] {first second : M.BehavioralAssessment}
    (agree : ∀ who, (first.strategy who).AgreesAtDecisions (second.strategy who))
    (beliefs : ∀ who site, first.belief who site = second.belief who site)
    (antichain : M.DecisionInformationAntichain)
    (certificate : E.WellFoundedHistories) (payoff : ι → E.History → ℝ) :
    first.IsSequentialEquilibrium antichain certificate payoff ↔
      second.IsSequentialEquilibrium antichain certificate payoff := by
  rw [first.isSequentialEquilibrium_iff, second.isSequentialEquilibrium_iff]
  exact and_congr
    (BehavioralAssessment.isSequentiallyRational_iff_of_agreesAtDecisions
      agree beliefs certificate payoff)
    (BehavioralAssessment.isSequentiallyConsistent_iff_of_agreesAtDecisions
      agree beliefs antichain)

/-- Extending the same behavioral decision plans with different fallbacks
preserves sequential equilibrium when the history beliefs are retained. -/
theorem isSequentialEquilibrium_extend_iff [Fintype ι] [DecidableEq ι]
    (plans : (who : ι) → M.BehavioralDecisionPlan who)
    (belief : (who : ι) → (site : M.InformationSite who) →
      PMF (M.InformationHistory who site.1))
    (first second : (who : ι) → M.BehavioralPolicy who)
    (antichain : M.DecisionInformationAntichain)
    (certificate : E.WellFoundedHistories) (payoff : ι → E.History → ℝ) :
    ({ strategy := fun who => (plans who).extend (first who), belief := belief } :
        M.BehavioralAssessment).IsSequentialEquilibrium antichain certificate payoff ↔
      ({ strategy := fun who => (plans who).extend (second who), belief := belief } :
        M.BehavioralAssessment).IsSequentialEquilibrium antichain certificate payoff := by
  apply BehavioralAssessment.isSequentialEquilibrium_iff_of_agreesAtDecisions
  · intro who
    exact ((plans who).restrict_extend (first who)).trans
      ((plans who).restrict_extend (second who)).symm
  · intro who site
    rfl

end InformationModel

end GameTheory.Protocol
