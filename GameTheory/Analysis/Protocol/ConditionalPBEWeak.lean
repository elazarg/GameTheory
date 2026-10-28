module

/-
# Conditional-probability equilibrium implies weak Bayesian equilibrium

The common terminal conditional system has the actual unconditional play law:
at the initial history either a player acts with belief one or Nature's
compatibility condition applies. Its chain rule therefore yields ordinary
Bayes beliefs at every information site reached with positive probability.
-/

public import GameTheory.Protocol.ConditionalPBE
public import GameTheory.Protocol.WeakPBE
public import GameTheory.Analysis.Protocol.BeliefTransport

@[expose] public section

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability
open scoped ENNReal

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace InformationModel

variable (M : InformationModel E) [E.FiniteMovers]

/-- Compatibility fixes the unconditional common-system law to actual terminal
behavioral play. No on-path Bayes condition is assumed. -/
theorem BehavioralAssessment.ConditionalProbabilityCompatible.law_univ
    {A : M.BehavioralAssessment} {certificate : E.WellFoundedHistories}
    {C : ConditionalProbabilitySystem E.TerminalHistory}
    (compatible : A.ConditionalProbabilityCompatible M certificate C)
    (nonempty : (Set.univ : Set E.TerminalHistory).Nonempty) :
    C.law Set.univ nonempty = M.terminalLaw certificate A.strategy E.initHistory := by
  classical
  by_cases terminal : E.terminal E.initHistory.state
  · have equal (final : E.TerminalHistory) : final.1 = E.initHistory :=
      (E.reachesWithin_from_init final.1).eq_of_terminal terminal
    have singleton : Subsingleton E.TerminalHistory :=
      ⟨fun first second => Subtype.ext ((equal first).trans (equal second).symm)⟩
    let : Subsingleton E.TerminalHistory := singleton
    apply PMF.ext
    intro final
    have mass (law : PMF E.TerminalHistory) : law final = 1 := by
      rw [← law.tsum_coe, tsum_eq_single final]
      intro other different
      exact False.elim (different (Subsingleton.elim _ _))
    rw [mass, mass]
  have continuation : ∀ later : E.History, E.HistoryReaches E.initHistory later →
      C.prob (E.terminalCone later) (E.terminalCone E.initHistory)
          (M.terminalCone_nonempty certificate A.strategy E.initHistory) =
        (M.terminalLaw certificate A.strategy E.initHistory).toOuterMeasure
          (E.terminalCone later) := by
    by_cases active : ∃ who, E.active E.initHistory.state who
    · obtain ⟨who, active⟩ := active
      obtain ⟨site, observed⟩ := M.exists_informationSite_of_active who E.initHistory
        terminal active
      let root : M.InformationHistory who site.1 := ⟨E.initHistory, observed.symm⟩
      have belief : A.belief who site root = 1 := by
        rw [compatible.represents who site root]
        simp only [root, ExecutionProtocol.terminalCone_init,
          ConditionalProbabilitySystem.prob_univ]
      exact compatible.continuation who site root (by rw [belief]; exact zero_lt_one)
    · exact compatible.nature E.initHistory terminal (not_exists.mp active)
  apply PMF.ext
  intro final
  have equality := continuation final.1 ⟨_, E.reachesWithin_from_init final.1⟩
  simpa only [ConditionalProbabilitySystem.prob, ExecutionProtocol.terminalCone_init,
    ExecutionProtocol.terminalCone_terminal, PMF.toOuterMeasure_apply_singleton] using equality

/-- Common-system consistency implies actual Bayes consistency at every
positive-mass information site. -/
theorem BehavioralAssessment.IsConditionalProbabilityConsistent.isBayesConsistent
    {A : M.BehavioralAssessment} {certificate : E.WellFoundedHistories}
    (consistent : A.IsConditionalProbabilityConsistent M certificate)
    (antichain : M.DecisionInformationAntichain) :
    BehavioralAssessment.IsBayesConsistent M A antichain := by
  classical
  obtain ⟨C, compatible⟩ := consistent
  have nonempty : (Set.univ : Set E.TerminalHistory).Nonempty :=
    (M.terminalCone_nonempty certificate A.strategy E.initHistory).mono (Set.subset_univ _)
  have rootLaw := compatible.law_univ M nonempty
  intro who site positive history
  have passageMass :
      (M.terminalLaw certificate A.strategy E.initHistory).toOuterMeasure
        (M.terminalPassage who site) = M.informationMass A.strategy who site := by
    rw [M.informationMass_eq_passage certificate A.strategy who site (antichain who site),
      ← M.terminalLaw_map_val certificate A.strategy E.initHistory,
      PMF.toOuterMeasure_map_apply]
    congr 1
    ext final
    simp only [terminalPassage, Set.mem_ofPred_eq, Set.mem_preimage, Subtype.exists, exists_prop]
  have coneMass :
      (M.terminalLaw certificate A.strategy E.initHistory).toOuterMeasure
        (E.terminalCone history.1) = M.historyReachWeight A.strategy history.1 := by
    rw [← M.coneMass_eq_historyReachWeight certificate A.strategy history.1]
    change _ = (M.runBehavioralTerminalFrom certificate A.strategy E.initHistory).toOuterMeasure
      (historyCone history.1)
    rw [← M.terminalLaw_map_val certificate A.strategy E.initHistory,
      PMF.toOuterMeasure_map_apply]
    rfl
  have subset : E.terminalCone history.1 ⊆ M.terminalPassage who site :=
    fun _ reached => ⟨history, reached⟩
  have chain := C.prob_chain (E.terminalCone history.1) (M.terminalPassage who site)
    Set.univ (M.terminalPassage_nonempty certificate A.strategy who site) nonempty
    (Set.subset_univ _)
  rw [← compatible.represents who site history] at chain
  change A.belief who site history * (C.law Set.univ nonempty).toOuterMeasure
      (M.terminalPassage who site) =
    (C.law Set.univ nonempty).toOuterMeasure
      (E.terminalCone history.1 ∩ M.terminalPassage who site) at chain
  rw [rootLaw, Set.inter_eq_left.mpr subset, passageMass, coneMass] at chain
  rw [← chain, ENNReal.mul_div_cancel_right positive.ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top
      (M.informationMass_le_one A.strategy who site (antichain who site)))]

/-- Conditional-probability perfect Bayesian equilibrium refines weak perfect
Bayesian equilibrium; its on-path Bayes property is derived from the common
conditional system. -/
theorem BehavioralAssessment.IsConditionalPBE.isWeakPBE [DecidableEq ι]
    {A : M.BehavioralAssessment} {certificate : E.WellFoundedHistories}
    {payoff : ι → E.History → ℝ}
    (equilibrium : A.IsConditionalPBE M certificate payoff)
    (antichain : M.DecisionInformationAntichain) :
    A.IsWeakPBE antichain certificate payoff :=
  ⟨equilibrium.1, equilibrium.2.1.isBayesConsistent M antichain⟩

end InformationModel
end GameTheory.Protocol
