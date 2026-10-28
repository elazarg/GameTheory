module

/-
# Sequential equilibrium and conditional-probability consistency

Fully mixed Bayesian assessments induce fully supported terminal laws.
Taking one common subsequence of all their conditional laws supplies a
conditional probability system, including at events of vanishing reach.
-/

public import GameTheory.Analysis.Protocol.BeliefTransport
public import GameTheory.Analysis.Protocol.BehavioralTerminalConvergence
public import GameTheory.Protocol.ConditionalPBE
public import GameTheory.Math.Probability.ConditionalSystemCompactness

@[expose] public section

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability
open Filter
open scoped ENNReal

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι} (M : InformationModel E)
    [E.FiniteMovers]

private theorem terminal_event_factor (certificate : E.WellFoundedHistories)
    (strategy : (i : ι) → M.BehavioralPolicy i) (root : E.History)
    (event : Set E.History) (below : event ⊆ historyCone root) :
    (M.runBehavioralTerminalFrom certificate strategy E.initHistory).toOuterMeasure event =
      M.historyReachWeight strategy root *
        (M.runBehavioralTerminalFrom certificate strategy root).toOuterMeasure event := by
  classical
  change (E.randomizedBackwardLaw certificate (M.randomizedChooser strategy)
    E.initHistory).toOuterMeasure event = _
  rw [E.randomizedBackwardLaw_eq_bind_runRandomizedFor certificate _ root.trace.length,
    PMF.toOuterMeasure_bind_apply]
  have outside (prior : E.History)
      (supported : prior ∈ (M.runBehavioral strategy root.trace.length).support)
      (different : prior ≠ root) :
      (E.randomizedBackwardLaw certificate (M.randomizedChooser strategy) prior).toOuterMeasure
        event = 0 := by
    rw [PMF.toOuterMeasure_apply_eq_zero_iff]
    refine Set.disjoint_left.mpr fun final finalSupported inEvent => different ?_
    obtain ⟨fuel, priorReaches⟩ := E.randomizedBackwardLaw_support_reaches prior final
      finalSupported
    obtain ⟨rootFuel, rootReaches⟩ := below inEvent
    have depth := M.runBehavioralFrom_reachesWithin strategy root.trace.length E.initHistory
      prior supported
    have upper : prior.trace.length ≤ root.trace.length := by
      simpa [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length]
        using depth.trace_length_le_add
    have lower : root.trace.length ≤ prior.trace.length := by
      rcases E.runRandomizedFor_terminal_or_length (M.randomizedChooser strategy)
          root.trace.length E.initHistory prior supported with terminal | length
      · have finalEqual : final = prior := priorReaches.eq_of_terminal terminal
        subst final
        exact rootReaches.trace_length_le
      · simpa [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length] using length
    exact ExecutionProtocol.ReachesWithin.eq_start_of_same_length priorReaches rootReaches
      (Nat.le_antisymm upper lower)
  have term (prior : E.History) :
      M.runBehavioral strategy root.trace.length prior *
          (E.randomizedBackwardLaw certificate (M.randomizedChooser strategy) prior).toOuterMeasure
            event =
        if prior = root then
          M.runBehavioral strategy root.trace.length root *
            (M.runBehavioralTerminalFrom certificate strategy root).toOuterMeasure event
        else 0 := by
    by_cases equal : prior = root
    · subst prior
      simp only [ite_true]
      rfl
    · rw [ite_eq_right equal]
      by_cases supported : prior ∈ (M.runBehavioral strategy root.trace.length).support
      · rw [outside prior supported equal, mul_zero]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr supported, zero_mul]
  change ∑' prior, M.runBehavioral strategy root.trace.length prior * _ = _
  rw [tsum_congr term, tsum_ite_eq]
  rfl

private theorem terminal_atom_pos_of_fullSupport (certificate : E.WellFoundedHistories)
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (full : ∀ i (site : M.InformationSite i) choice, choice ∈ (strategy i site.1).support)
    (history : E.History) (terminal : E.terminal history.state) :
    0 < M.runBehavioralTerminalFrom certificate strategy E.initHistory history := by
  have singleton : historyCone history = {history} := by
    ext final
    constructor
    · rintro ⟨fuel, reaches⟩
      exact Set.mem_singleton_iff.mpr (reaches.eq_of_terminal terminal)
    · intro equal
      subst final
      exact ExecutionProtocol.HistoryReaches.refl E history
  have positive := M.historyReachWeight_pos_of_fullSupport strategy full history
  rw [← M.coneMass_eq_historyReachWeight certificate strategy history] at positive
  change 0 < (M.runBehavioralTerminalFrom certificate strategy E.initHistory).toOuterMeasure
    (historyCone history) at positive
  rwa [singleton, PMF.toOuterMeasure_apply_singleton] at positive

private theorem conditional_terminal_continuation (certificate : E.WellFoundedHistories)
    (strategy : (i : ι) → M.BehavioralPolicy i) (root later : E.History)
    (reaches : E.HistoryReaches root later) (positive : 0 < M.historyReachWeight strategy root) :
    (M.runBehavioralTerminalFrom certificate strategy E.initHistory).toOuterMeasure
        (historyCone later) /
      (M.runBehavioralTerminalFrom certificate strategy E.initHistory).toOuterMeasure
        (historyCone root) =
      (M.runBehavioralTerminalFrom certificate strategy root).toOuterMeasure
        (historyCone later) := by
  have below : historyCone later ⊆ historyCone root := by
    rintro final ⟨fuel, laterReaches⟩
    obtain ⟨depth, rootReaches⟩ := reaches
    exact ⟨depth + fuel, rootReaches.trans laterReaches⟩
  rw [M.terminal_event_factor certificate strategy root _ below]
  have rootMass :
      (M.runBehavioralTerminalFrom certificate strategy E.initHistory).toOuterMeasure
        (historyCone root) = M.historyReachWeight strategy root :=
    M.coneMass_eq_historyReachWeight certificate strategy root
  rw [rootMass, mul_comm, mul_div_assoc,
    ENNReal.div_self positive.ne' (PMF.apply_ne_top _ _), mul_one]

private theorem terminalLaw_event (certificate : E.WellFoundedHistories)
    (strategy : (i : ι) → M.BehavioralPolicy i) (start : E.History) (event : Set E.History) :
    (M.terminalLaw certificate strategy start).toOuterMeasure (Subtype.val ⁻¹' event) =
      (M.runBehavioralTerminalFrom certificate strategy start).toOuterMeasure event := by
  rw [← PMF.toOuterMeasure_map_apply, M.terminalLaw_map_val]

private theorem terminalLaw_cone (certificate : E.WellFoundedHistories)
    (strategy : (i : ι) → M.BehavioralPolicy i) (start root : E.History) :
    (M.terminalLaw certificate strategy start).toOuterMeasure (E.terminalCone root) =
      (M.runBehavioralTerminalFrom certificate strategy start).toOuterMeasure (historyCone root) :=
  M.terminalLaw_event certificate strategy start (historyCone root)

private theorem terminalLaw_passage (certificate : E.WellFoundedHistories)
    (strategy : (i : ι) → M.BehavioralPolicy i) (who : ι) (site : M.InformationSite who) :
    (M.terminalLaw certificate strategy E.initHistory).toOuterMeasure (M.terminalPassage who site) =
      (M.runBehavioralTerminalFrom certificate strategy E.initHistory).toOuterMeasure
        {final | ∃ history, M.infoOf who history.trace = site.1 ∧
          E.HistoryReaches history final} := by
  have events : M.terminalPassage who site = Subtype.val ⁻¹'
      {final : E.History | ∃ history, M.infoOf who history.trace = site.1 ∧
        E.HistoryReaches history final} := by
    ext final
    simp [terminalPassage]
  rw [events, M.terminalLaw_event]

private theorem terminalLaw_fullSupport (certificate : E.WellFoundedHistories)
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (full : ∀ i (site : M.InformationSite i) choice, choice ∈ (strategy i site.1).support) :
    FullSupport (M.terminalLaw certificate strategy E.initHistory) := by
  intro final
  apply (PMF.mem_support_iff _ _).mpr
  rw [M.terminalLaw_apply]
  exact (M.terminal_atom_pos_of_fullSupport certificate strategy full final.1 final.2).ne'

private theorem fullSupport_represents (certificate : E.WellFoundedHistories)
    (antichain : M.DecisionInformationAntichain) (A : M.BehavioralAssessment)
    (full : A.IsFullyMixed)
    (bayes : BehavioralAssessment.IsBayesConsistent M A antichain)
    (who : ι) (site : M.InformationSite who) (history : M.InformationHistory who site.1)
    (nonempty : (M.terminalPassage who site).Nonempty) :
    A.belief who site history =
      (ConditionalProbabilitySystem.ofFullSupport
        (M.terminalLaw certificate A.strategy E.initHistory)
        (M.terminalLaw_fullSupport certificate A.strategy full)).prob
          (E.terminalCone history.1) (M.terminalPassage who site) nonempty := by
  have subset : E.terminalCone history.1 ⊆ M.terminalPassage who site :=
    fun final reaches => ⟨history, reaches⟩
  rw [ConditionalProbabilitySystem.ofFullSupport_prob, Set.inter_eq_left.mpr subset,
    M.terminalLaw_cone, M.terminalLaw_passage]
  have positive := M.informationMass_pos_of_fullSupport A.strategy full who site
  have belief := bayes who site positive history
  rw [← M.coneMass_eq_historyReachWeight certificate A.strategy history.1,
    M.informationMass_eq_passage certificate A.strategy who site (antichain who site)] at belief
  exact belief

private theorem fullSupport_continuation (certificate : E.WellFoundedHistories)
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (full : ∀ i (site : M.InformationSite i) choice, choice ∈ (strategy i site.1).support)
    (root later : E.History) (reaches : E.HistoryReaches root later)
    (nonempty : (E.terminalCone root).Nonempty) :
    (ConditionalProbabilitySystem.ofFullSupport
      (M.terminalLaw certificate strategy E.initHistory)
      (M.terminalLaw_fullSupport certificate strategy full)).prob
        (E.terminalCone later) (E.terminalCone root) nonempty =
      (M.runBehavioralTerminalFrom certificate strategy root).toOuterMeasure
        (historyCone later) := by
  have subset : E.terminalCone later ⊆ E.terminalCone root := by
    rintro final ⟨fuel, laterReaches⟩
    obtain ⟨depth, rootReaches⟩ := reaches
    exact ⟨depth + fuel, rootReaches.trans laterReaches⟩
  rw [ConditionalProbabilitySystem.ofFullSupport_prob, Set.inter_eq_left.mpr subset,
    M.terminalLaw_cone, M.terminalLaw_cone]
  exact M.conditional_terminal_continuation certificate strategy root later reaches
    (M.historyReachWeight_pos_of_fullSupport strategy full root)

/-- A sequentially consistent assessment admits one common conditional system
on terminal histories. Finite histories give compactness of all conditional
laws simultaneously, including the laws conditional on unreached events. -/
theorem BehavioralAssessment.IsSequentiallyConsistent.isConditionalProbabilityConsistent
    [Finite E.History] {A : M.BehavioralAssessment}
    (antichain : M.DecisionInformationAntichain) (certificate : E.WellFoundedHistories)
    (consistent : A.IsSequentiallyConsistent antichain) :
    A.IsConditionalProbabilityConsistent M certificate := by
  obtain ⟨sequence, approximates, converges⟩ := consistent
  let systems (n : ℕ) : ConditionalProbabilitySystem E.TerminalHistory :=
    ConditionalProbabilitySystem.ofFullSupport
      (M.terminalLaw certificate (sequence n).strategy E.initHistory)
      (M.terminalLaw_fullSupport certificate (sequence n).strategy (approximates n).1)
  obtain ⟨system, subsequence, increasing, systemsConverge⟩ :=
    exists_subseq_conditionalSystemConverges systems
  have policyConverges : ∀ i (site : M.InformationSite i),
      PMFConvergesPointwise (fun n => (sequence (subsequence n)).strategy i site.1)
        (A.strategy i site.1) := by
    intro i site action
    exact (converges.strategy i site action).comp increasing.tendsto_atTop
  have continuation (root later : E.History) (reaches : E.HistoryReaches root later) :
      system.prob (E.terminalCone later) (E.terminalCone root)
          (M.terminalCone_nonempty certificate A.strategy root) =
        (M.terminalLaw certificate A.strategy root).toOuterMeasure (E.terminalCone later) := by
    let nonempty := M.terminalCone_nonempty certificate A.strategy root
    have conditionalLimit : Tendsto
        (fun n => (systems (subsequence n)).prob (E.terminalCone later) (E.terminalCone root)
          nonempty) atTop (nhds (system.prob (E.terminalCone later) (E.terminalCone root)
          nonempty)) :=
      (systemsConverge (E.terminalCone root) nonempty).toOuterMeasure_finite _
    have actualLimit := (M.runBehavioralTerminalFrom_convergesPointwise certificate
      policyConverges root).toOuterMeasure_finite (historyCone later)
    have equality (n : ℕ) :
        (M.runBehavioralTerminalFrom certificate
          (sequence (subsequence n)).strategy root).toOuterMeasure (historyCone later) =
          (systems (subsequence n)).prob (E.terminalCone later) (E.terminalCone root)
            nonempty :=
      (M.fullSupport_continuation certificate (sequence (subsequence n)).strategy
        (approximates (subsequence n)).1 root later reaches nonempty).symm
    have sameLimit := actualLimit.congr' (Eventually.of_forall equality)
    exact (tendsto_nhds_unique conditionalLimit sameLimit).trans
      (M.terminalLaw_cone certificate A.strategy root later).symm
  refine ⟨system, ?_⟩
  constructor
  · intro who site history
    let nonempty := M.terminalPassage_nonempty certificate A.strategy who site
    have conditionalLimit : Tendsto
        (fun n => (systems (subsequence n)).prob (E.terminalCone history.1)
          (M.terminalPassage who site) nonempty) atTop
        (nhds (system.prob (E.terminalCone history.1) (M.terminalPassage who site) nonempty)) :=
      (systemsConverge (M.terminalPassage who site) nonempty).toOuterMeasure_finite _
    have beliefLimit := (converges.belief who site history).comp increasing.tendsto_atTop
    have equality (n : ℕ) :
        (systems (subsequence n)).prob (E.terminalCone history.1)
            (M.terminalPassage who site) nonempty =
          (sequence (subsequence n)).belief who site history :=
      (M.fullSupport_represents certificate antichain (sequence (subsequence n))
        (approximates (subsequence n)).1 (approximates (subsequence n)).2 who site history
        nonempty).symm
    exact tendsto_nhds_unique beliefLimit
      (conditionalLimit.congr' (Eventually.of_forall equality))
  · intro who site history _ later reaches
    exact continuation history.1 later reaches
  · intro history _ _ later reaches
    exact continuation history later reaches

/-- Finite-history sequential equilibrium with explicit chance refines
conditional-probability PBE, with the same assessment and terminal payoffs. -/
theorem BehavioralAssessment.IsSequentialEquilibrium.isConditionalPBE
    [DecidableEq ι] [Finite E.History] {A : M.BehavioralAssessment}
    (antichain : M.DecisionInformationAntichain) (certificate : E.WellFoundedHistories)
    (explicitChance : E.HasExplicitChance)
    (payoff : ι → E.History → ℝ)
    (equilibrium : A.IsSequentialEquilibrium antichain certificate payoff) :
    A.IsConditionalPBE M certificate payoff :=
  ⟨equilibrium.1,
    equilibrium.2.isConditionalProbabilityConsistent M antichain certificate, explicitChance⟩

end GameTheory.Protocol.InformationModel
