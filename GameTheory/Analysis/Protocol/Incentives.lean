/-
# Incentive comparisons in sequential games

Each sequential solution concept is a family of incentive comparisons indexed
by a deviating player. Subgame perfection compares whole replacement
strategies at every proper subgame root. Sequential rationality compares whole
replacement policies at every information site, under the assessment's beliefs
and with all opponents fixed. No finiteness is needed for these identities.

On a finite observation carrier, preservation of either concept for every
observed utility is therefore exactly playerwise cone inclusion, and for a
linear class of joint utilities it is projected inclusion of the player-tagged
comparisons. Belief consistency is a separate obligation: preservation of
sequential equilibrium from a consistent source is exactly target consistency
together with the incentive criterion.
-/

import GameTheory.Analysis.IncentiveCone
import GameTheory.Analysis.IncentiveSimulation
import GameTheory.Analysis.Protocol.Sequential
import GameTheory.Protocol.Continuation

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

namespace Context

variable {Choice : Type*} {Outcome : Type*}

/-- Local optimality against every alternative is the family of comparisons of
the chosen continuation law with each alternative's law. -/
theorem isLocallyOptimal_univ_iff_holds (ctx : Context Choice Outcome) (choice : Choice) :
    ctx.IsLocallyOptimal Set.univ choice ↔
      ∀ alternative, (IncentiveComparison.mk (ctx.outcome choice)
        (ctx.outcome alternative)).Holds ctx.continuation := by
  constructor
  · rintro ⟨hchoice, halternatives, hoptimal⟩ alternative
    exact ⟨hchoice, halternatives alternative (Set.mem_univ _),
      hoptimal alternative (Set.mem_univ _)⟩
  · intro holds
    obtain ⟨hchoice, -, -⟩ := holds choice
    exact ⟨hchoice, fun alternative _ => (holds alternative).2.1,
      fun alternative _ => (holds alternative).2.2⟩

end Context

namespace InformationModel

universe uι us ua up uq uk uσ uω uo

variable {ι : Type uι}

/-! ## Subgame perfection -/

section Continuation

variable [DecidableEq ι] {E : ExecutionProtocol.{uι, us, ua} ι}
  (M : InformationModel.{uι, us, ua, up, uq, uk} E)
  {sig : GameSignature.{uι, uσ, uω} ι} {Observation : Type uo}

/-- A whole replacement strategy at a proper subgame root. -/
abbrev ContinuationDeviation (sig : GameSignature.{uι, uσ, uω} ι) (who : ι) :=
  {root : E.History // M.IsSubgameRoot root} × sig.Strategy who

/-- The comparison behind one continuation deviation, as seen through an
observation of outcomes. -/
def continuationComparison (play : E.History → Profile sig → PMF sig.Outcome)
    (observe : sig.Outcome → Observation) (profile : Profile sig) (who : ι)
    (deviation : M.ContinuationDeviation sig who) : IncentiveComparison Observation where
  prescribed := (play deviation.1.1 profile).map observe
  alternative := (play deviation.1.1 (Profile.update profile who deviation.2)).map observe

/-- Continuation Nash of observed payoffs is its comparison family. -/
theorem isContinuationNash_iff_holds (play : E.History → Profile sig → PMF sig.Outcome)
    (observe : sig.Outcome → Observation) (profile : Profile sig)
    (utility : Observation → ι → ℝ) :
    M.IsContinuationNash play profile (fun outcome who => utility (observe outcome) who) ↔
      ∀ who deviation,
        (M.continuationComparison play observe profile who deviation).Holds (utility · who) := by
  simp only [IsContinuationNash, isNash_iff, IncentiveComparison.euPreference_iff_holds,
    continuationComparison, IncentiveComparison.holds_map_iff]
  exact ⟨fun perfect who deviation => perfect deviation.1.1 deviation.1.2 who deviation.2,
    fun holds root proper who replacement => holds who (⟨root, proper⟩, replacement)⟩

variable {T : ExecutionProtocol.{uι, us, ua} ι} (N : InformationModel.{uι, us, ua, up, uq, uk} T)
  {sig' : GameSignature.{uι, uσ, uω} ι}

/-- **Exact subgame-perfection transfer for every utility.** Pure, behavioral,
and single-mover behavioral subgame perfection are all continuation Nash for a
supplied play law, so one criterion covers each of them and any mixture of
source and target semantics. -/
theorem isContinuationNash_preservation_iff_cone [Fintype Observation]
    (sourcePlay : E.History → Profile sig → PMF sig.Outcome)
    (targetPlay : T.History → Profile sig' → PMF sig'.Outcome)
    (sourceObserve : sig.Outcome → Observation) (targetObserve : sig'.Outcome → Observation)
    (source : Profile sig) (target : Profile sig') :
    (∀ utility : Observation → ι → ℝ,
      M.IsContinuationNash sourcePlay source
          (fun outcome who => utility (sourceObserve outcome) who) →
        N.IsContinuationNash targetPlay target
          (fun outcome who => utility (targetObserve outcome) who)) ↔
      ∀ who deviation,
        (N.continuationComparison targetPlay targetObserve target who deviation).difference ∈
          IncentiveComparison.cone
            (M.continuationComparison sourcePlay sourceObserve source who) := by
  simp only [isContinuationNash_iff_holds]
  exact IncentiveComparison.forall_holds_imp_iff_cone _ _

/-- **Subgame perfection from randomly matched roots.** Each target
continuation deviation is matched with a lottery over proper source roots and,
at every matched root, a lottery of source replacements: the target's honest
continuation law is the root lottery of source honest laws, and its deviating
law the same root lottery of mixed source deviations. Source subgame perfection
then transfers for every utility integrable against the continuation laws. The
matching may depend on the deviation, and the target profile need not be
compiled from the source one. -/
theorem isContinuationNash_of_root_mixture_laws
    (sourcePlay : E.History → Profile sig → PMF sig.Outcome)
    (targetPlay : T.History → Profile sig' → PMF sig'.Outcome)
    (sourceObserve : sig.Outcome → Observation) (targetObserve : sig'.Outcome → Observation)
    (source : Profile sig) (target : Profile sig')
    (coverage : ∀ who (deviation : N.ContinuationDeviation sig' who),
      ∃ (roots : PMF {root : E.History // M.IsSubgameRoot root})
        (replacements : {root : E.History // M.IsSubgameRoot root} → PMF (sig.Strategy who)),
        (targetPlay deviation.1.1 target).map targetObserve =
            roots.bind (fun root => (sourcePlay root.1 source).map sourceObserve) ∧
          (targetPlay deviation.1.1 (Profile.update target who deviation.2)).map
              targetObserve =
            roots.bind fun root => (replacements root).bind fun replacement =>
              (sourcePlay root.1 (Profile.update source who replacement)).map sourceObserve)
    (utility : Observation → ι → ℝ)
    (sourceIntegrable : ∀ who deviation,
      PayoffIntegrable (M.continuationComparison sourcePlay sourceObserve source who
          deviation).prescribed (utility · who) ∧
        PayoffIntegrable (M.continuationComparison sourcePlay sourceObserve source who
          deviation).alternative (utility · who))
    (targetIntegrable : ∀ who deviation,
      PayoffIntegrable (N.continuationComparison targetPlay targetObserve target who
          deviation).prescribed (utility · who) ∧
        PayoffIntegrable (N.continuationComparison targetPlay targetObserve target who
          deviation).alternative (utility · who))
    (perfect : M.IsContinuationNash sourcePlay source
      (fun outcome who => utility (sourceObserve outcome) who)) :
    N.IsContinuationNash targetPlay target
      (fun outcome who => utility (targetObserve outcome) who) := by
  rw [N.isContinuationNash_iff_holds targetPlay targetObserve target utility]
  rw [M.isContinuationNash_iff_holds sourcePlay sourceObserve source utility] at perfect
  choose roots replacements honest deviated using coverage
  let simulation : IncentiveSimulation (M.continuationComparison sourcePlay sourceObserve source)
      (N.continuationComparison targetPlay targetObserve target) :=
    { mixing := fun who deviation => (roots who deviation).bind fun root =>
        (replacements who deviation root).map fun replacement => (root, replacement)
      prescribed := fun who deviation => by
        change (targetPlay deviation.1.1 target).map targetObserve = _
        rw [honest who deviation, PMF.bind_bind]
        refine congrArg _ (funext fun root => ?_)
        rw [PMF.bind_map]
        exact (PMF.bind_const _ _).symm
      alternative := fun who deviation => by
        change (targetPlay deviation.1.1 (Profile.update target who deviation.2)).map
          targetObserve = _
        rw [deviated who deviation, PMF.bind_bind]
        refine congrArg _ (funext fun root => ?_)
        rw [PMF.bind_map]
        rfl }
  exact simulation.preserves utility perfect sourceIntegrable targetIntegrable

end Continuation

/-! ## Sequential rationality and equilibrium -/

section Assessment

variable [DecidableEq ι] {E : ExecutionProtocol ι} (M : InformationModel E)
  {Observation : Type uo}

/-- A whole replacement policy at an information site. -/
abbrev AssessmentDeviation (who : ι) := M.InformationSite who × M.BehavioralPolicy who

/-- The continuation law of a policy at an information site under the
assessment's belief, with all opponents fixed and continued play computed by
`run`. -/
def assessmentLawWith (run : M.ContinuationRunner)
    (assessment : M.BehavioralAssessment) {who : ι}
    (site : M.InformationSite who) (policy : M.BehavioralPolicy who) : PMF E.History :=
  (assessment.belief who site).bind fun history =>
    run (Profile.update (sig := M.behavioralSignature) assessment.strategy who policy) history.1

/-- The comparison behind one whole-policy deviation at an information site. -/
def assessmentComparisonWith (run : M.ContinuationRunner)
    (observe : E.History → Observation) (assessment : M.BehavioralAssessment) (who : ι)
    (deviation : M.AssessmentDeviation who) : IncentiveComparison Observation where
  prescribed := (M.assessmentLawWith run assessment deviation.1 (assessment.strategy who)).map
    observe
  alternative := (M.assessmentLawWith run assessment deviation.1 deviation.2).map observe

/-- Rationality against a continuation runner, for observed payoffs, is its
comparison family. -/
theorem isSequentiallyRationalWith_iff_holds (run : M.ContinuationRunner)
    (observe : E.History → Observation) (assessment : M.BehavioralAssessment)
    (utility : Observation → ι → ℝ) :
    assessment.IsSequentiallyRationalWith run (fun who history => utility (observe history) who) ↔
      ∀ who deviation,
        (M.assessmentComparisonWith run observe assessment who deviation).Holds
          (utility · who) := by
  simp only [BehavioralAssessment.IsSequentiallyRationalWith,
    BehavioralAssessment.IsSequentiallyRationalFor, BehavioralAssessment.IsSequentiallyRationalAt,
    Context.isLocallyOptimal_univ_iff_holds, assessmentComparisonWith,
    IncentiveComparison.holds_map_iff]
  exact ⟨fun rational who deviation => rational who deviation.1 deviation.2,
    fun holds who site alternative => holds who (site, alternative)⟩

/-- The terminal continuation law of a whole-policy deviation at a site, under
the assessment's belief. -/
def assessmentLaw [Fintype ι]
    (certificate : E.WellFoundedHistories) (assessment : M.BehavioralAssessment)
    {who : ι} (site : M.InformationSite who) (policy : M.BehavioralPolicy who) :
    PMF E.History :=
  M.assessmentLawWith (M.runBehavioralTerminalFrom certificate) assessment site policy

/-- The sequential-rationality comparison of one whole-policy deviation at a
site, evaluated on terminal play. -/
def assessmentComparison [Fintype ι]
    (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation) (assessment : M.BehavioralAssessment) (who : ι)
    (deviation : M.AssessmentDeviation who) : IncentiveComparison Observation :=
  M.assessmentComparisonWith (M.runBehavioralTerminalFrom certificate) observe assessment who
    deviation

@[simp]
theorem assessmentComparison_prescribed [Fintype ι]
    (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation) (assessment : M.BehavioralAssessment) (who : ι)
    (deviation : M.AssessmentDeviation who) :
    (M.assessmentComparison certificate observe assessment who deviation).prescribed =
      (M.assessmentLaw certificate assessment deviation.1 (assessment.strategy who)).map
        observe :=
  rfl

@[simp]
theorem assessmentComparison_alternative [Fintype ι]
    (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation) (assessment : M.BehavioralAssessment) (who : ι)
    (deviation : M.AssessmentDeviation who) :
    (M.assessmentComparison certificate observe assessment who deviation).alternative =
      (M.assessmentLaw certificate assessment deviation.1 deviation.2).map observe :=
  rfl

/-- Sequential rationality of observed payoffs is its comparison family. -/
theorem isSequentiallyRational_iff_holds [Fintype ι]
    (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation) (assessment : M.BehavioralAssessment)
    (utility : Observation → ι → ℝ) :
    assessment.IsSequentiallyRational certificate
        (fun who history => utility (observe history) who) ↔
      ∀ who deviation,
        (M.assessmentComparison certificate observe assessment who deviation).Holds
          (utility · who) :=
  M.isSequentiallyRationalWith_iff_holds (M.runBehavioralTerminalFrom certificate) observe
    assessment utility

variable {T : ExecutionProtocol ι} (N : InformationModel T)

/-- **Exact transport of sequential rationality** for fixed assessments and
every observed utility. Neither belief system need be consistent, and the
criterion does not depend on how continued play is computed: sequential
rationality is the instance `M.runBehavioralTerminalFrom certificate`, and play
cut off after a fixed number of steps is another. -/
theorem sequentialRationality_preservation_iff_cone [Fintype Observation]
    (sourceRun : M.ContinuationRunner) (targetRun : N.ContinuationRunner)
    (sourceObserve : E.History → Observation) (targetObserve : T.History → Observation)
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment) :
    (∀ utility : Observation → ι → ℝ,
      source.IsSequentiallyRationalWith sourceRun
          (fun who history => utility (sourceObserve history) who) →
        target.IsSequentiallyRationalWith targetRun
          (fun who history => utility (targetObserve history) who)) ↔
      ∀ who deviation,
        (N.assessmentComparisonWith targetRun targetObserve target who deviation).difference ∈
          IncentiveComparison.cone
            (M.assessmentComparisonWith sourceRun sourceObserve source who) := by
  simp only [isSequentiallyRationalWith_iff_holds]
  exact IncentiveComparison.forall_holds_imp_iff_cone _ _

/-- Exact transport of sequential rationality over a linear class of joint
utilities, including classes coupling different players' payoffs. -/
theorem sequentialRationality_preservation_iff_coneWithin [Fintype ι] [Fintype Observation]
    (utilities : Submodule ℝ (EuclideanSpace ℝ (ι × Observation)))
    (sourceRun : M.ContinuationRunner) (targetRun : N.ContinuationRunner)
    (sourceObserve : E.History → Observation) (targetObserve : T.History → Observation)
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment) :
    (∀ utility : utilities,
      source.IsSequentiallyRationalWith sourceRun
          (fun who history => WithLp.ofLp utility.val (who, sourceObserve history)) →
        target.IsSequentiallyRationalWith targetRun
          (fun who history => WithLp.ofLp utility.val (who, targetObserve history))) ↔
      ∀ deviation : Σ who, N.AssessmentDeviation who,
        utilities.orthogonalProjectionOnto
            ((N.assessmentComparisonWith targetRun targetObserve target deviation.1
              deviation.2).tag deviation.1).difference ∈
          IncentiveComparison.coneWithin utilities
            fun deviation : Σ who, M.AssessmentDeviation who =>
              (M.assessmentComparisonWith sourceRun sourceObserve source deviation.1
                deviation.2).tag deviation.1 := by
  have hsource (utility : utilities) := M.isSequentiallyRationalWith_iff_holds sourceRun
    sourceObserve source fun observation who => WithLp.ofLp utility.val (who, observation)
  have htarget (utility : utilities) := N.isSequentiallyRationalWith_iff_holds targetRun
    targetObserve target fun observation who => WithLp.ofLp utility.val (who, observation)
  simp only [hsource, htarget]
  exact IncentiveComparison.forall_holds_imp_iff_coneWithin utilities _ _

/-- **Exact transport of sequential equilibrium.** From a consistent source
assessment, every observed-utility sequential equilibrium maps to one of the
target exactly when the target is consistent and its incentive differences lie
in the source cones. The zero utility separates the two obligations. As for
sequential rationality, the runners are arbitrary. -/
theorem sequentialEquilibrium_preservation_iff [Fintype ι] [Fintype Observation]
    (sourceAntichain : M.DecisionInformationAntichain)
    (targetAntichain : N.DecisionInformationAntichain)
    (sourceRun : M.ContinuationRunner) (targetRun : N.ContinuationRunner)
    (sourceObserve : E.History → Observation) (targetObserve : T.History → Observation)
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (sourceConsistent : source.IsSequentiallyConsistent sourceAntichain) :
    (∀ utility : Observation → ι → ℝ,
      source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
          source.continuationContextWith sourceRun site
            (fun history => utility (sourceObserve history) who)) →
        target.IsSequentialEquilibriumFor targetAntichain (fun who site =>
          target.continuationContextWith targetRun site
            (fun history => utility (targetObserve history) who))) ↔
      target.IsSequentiallyConsistent targetAntichain ∧
        ∀ who deviation,
          (N.assessmentComparisonWith targetRun targetObserve target who deviation).difference ∈
            IncentiveComparison.cone
              (M.assessmentComparisonWith sourceRun sourceObserve source who) := by
  constructor
  · intro preserves
    have hconsistent := (preserves (fun _ _ => 0)
      ⟨source.isSequentiallyRationalWith_zero sourceRun, sourceConsistent⟩).2
    refine ⟨hconsistent, ?_⟩
    apply (M.sequentialRationality_preservation_iff_cone N sourceRun targetRun sourceObserve
      targetObserve source target).1
    intro utility rational
    exact (preserves utility ⟨rational, sourceConsistent⟩).1
  · rintro ⟨hconsistent, included⟩ utility ⟨rational, _⟩
    exact ⟨(M.sequentialRationality_preservation_iff_cone N sourceRun targetRun sourceObserve
      targetObserve source target).2 included utility rational, hconsistent⟩

/-- Sequential-equilibrium transport over a linear class of joint utilities.
The zero utility lies in every class, so consistency is again forced. -/
theorem sequentialEquilibrium_preservation_iff_coneWithin [Fintype ι] [Fintype Observation]
    (utilities : Submodule ℝ (EuclideanSpace ℝ (ι × Observation)))
    (sourceAntichain : M.DecisionInformationAntichain)
    (targetAntichain : N.DecisionInformationAntichain)
    (sourceRun : M.ContinuationRunner) (targetRun : N.ContinuationRunner)
    (sourceObserve : E.History → Observation) (targetObserve : T.History → Observation)
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (sourceConsistent : source.IsSequentiallyConsistent sourceAntichain) :
    (∀ utility : utilities,
      source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
          source.continuationContextWith sourceRun site
            (fun history => WithLp.ofLp utility.val (who, sourceObserve history))) →
        target.IsSequentialEquilibriumFor targetAntichain (fun who site =>
          target.continuationContextWith targetRun site
            (fun history => WithLp.ofLp utility.val (who, targetObserve history)))) ↔
      target.IsSequentiallyConsistent targetAntichain ∧
        ∀ deviation : Σ who, N.AssessmentDeviation who,
          utilities.orthogonalProjectionOnto
              ((N.assessmentComparisonWith targetRun targetObserve target deviation.1
                deviation.2).tag deviation.1).difference ∈
            IncentiveComparison.coneWithin utilities
              fun deviation : Σ who, M.AssessmentDeviation who =>
                (M.assessmentComparisonWith sourceRun sourceObserve source deviation.1
                  deviation.2).tag deviation.1 := by
  have hzero : source.IsSequentiallyRationalWith sourceRun
      (fun who history => WithLp.ofLp (0 : utilities).val (who, sourceObserve history)) := by
    simpa using source.isSequentiallyRationalWith_zero sourceRun
  constructor
  · intro preserves
    have hconsistent := (preserves 0 ⟨hzero, sourceConsistent⟩).2
    refine ⟨hconsistent, ?_⟩
    apply (M.sequentialRationality_preservation_iff_coneWithin N utilities sourceRun targetRun
      sourceObserve targetObserve source target).1
    intro utility rational
    exact (preserves utility ⟨rational, sourceConsistent⟩).1
  · rintro ⟨hconsistent, included⟩ utility ⟨rational, _⟩
    exact ⟨(M.sequentialRationality_preservation_iff_coneWithin N utilities sourceRun
      targetRun sourceObserve targetObserve source target).2 included utility rational,
      hconsistent⟩

/-- A law-pair simulation between the continuation comparisons of two
assessments transfers sequential rationality for every utility integrable
against the source and target continuation laws, whatever the runners and the
outcome carrier. It constructs neither the assessments nor their consistency. -/
theorem sequentialRationality_of_simulation
    (sourceRun : M.ContinuationRunner) (targetRun : N.ContinuationRunner)
    (sourceObserve : E.History → Observation) (targetObserve : T.History → Observation)
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (simulation : IncentiveSimulation (M.assessmentComparisonWith sourceRun sourceObserve source)
      (N.assessmentComparisonWith targetRun targetObserve target))
    (utility : Observation → ι → ℝ)
    (rational : source.IsSequentiallyRationalWith sourceRun
      (fun who history => utility (sourceObserve history) who))
    (integrable : ∀ who deviation,
      PayoffIntegrable (M.assessmentComparisonWith sourceRun sourceObserve source who
          deviation).prescribed (utility · who) ∧
        PayoffIntegrable (M.assessmentComparisonWith sourceRun sourceObserve source who
          deviation).alternative (utility · who))
    (targetIntegrable : ∀ who deviation,
      PayoffIntegrable (N.assessmentComparisonWith targetRun targetObserve target who
          deviation).prescribed (utility · who) ∧
        PayoffIntegrable (N.assessmentComparisonWith targetRun targetObserve target who
          deviation).alternative (utility · who)) :
    target.IsSequentiallyRationalWith targetRun
      (fun who history => utility (targetObserve history) who) := by
  rw [N.isSequentiallyRationalWith_iff_holds targetRun targetObserve target utility]
  exact simulation.preserves utility
    ((M.isSequentiallyRationalWith_iff_holds sourceRun sourceObserve source utility).mp rational)
    integrable targetIntegrable

/-- Once target consistency is established, a simulation transfers sequential
equilibrium for every utility integrable against the continuation laws. -/
theorem sequentialEquilibrium_of_simulation [Fintype ι]
    (sourceAntichain : M.DecisionInformationAntichain)
    (targetAntichain : N.DecisionInformationAntichain)
    (sourceRun : M.ContinuationRunner) (targetRun : N.ContinuationRunner)
    (sourceObserve : E.History → Observation) (targetObserve : T.History → Observation)
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (simulation : IncentiveSimulation (M.assessmentComparisonWith sourceRun sourceObserve source)
      (N.assessmentComparisonWith targetRun targetObserve target))
    (targetConsistent : target.IsSequentiallyConsistent targetAntichain)
    (utility : Observation → ι → ℝ)
    (equilibrium : source.IsSequentialEquilibriumFor sourceAntichain fun who site =>
      source.continuationContextWith sourceRun site
        (fun history => utility (sourceObserve history) who))
    (integrable : ∀ who deviation,
      PayoffIntegrable (M.assessmentComparisonWith sourceRun sourceObserve source who
          deviation).prescribed (utility · who) ∧
        PayoffIntegrable (M.assessmentComparisonWith sourceRun sourceObserve source who
          deviation).alternative (utility · who))
    (targetIntegrable : ∀ who deviation,
      PayoffIntegrable (N.assessmentComparisonWith targetRun targetObserve target who
          deviation).prescribed (utility · who) ∧
        PayoffIntegrable (N.assessmentComparisonWith targetRun targetObserve target who
          deviation).alternative (utility · who)) :
    target.IsSequentialEquilibriumFor targetAntichain fun who site =>
      target.continuationContextWith targetRun site
        (fun history => utility (targetObserve history) who) :=
  ⟨M.sequentialRationality_of_simulation N sourceRun targetRun sourceObserve targetObserve
    source target simulation utility equilibrium.1 integrable targetIntegrable,
    targetConsistent⟩

end Assessment

end InformationModel

end GameTheory.Protocol
