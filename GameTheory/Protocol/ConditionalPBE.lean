module

/-
# Conditional-probability perfect Bayesian equilibrium

One conditional probability system on terminal histories represents all
information-set beliefs, including off-path beliefs. At a node assigned
positive belief, its conditional continuation agrees with behavioral play.
Nature's continuation law is respected at every chance node, even off path.
Together with whole-policy sequential rationality these conditions define
conditional-probability perfect Bayesian equilibrium for protocols that expose
Nature as separate chance nodes. A named certificate enforces that boundary.
-/

public import GameTheory.Protocol.BehavioralTerminal
public import GameTheory.Protocol.ExplicitChance
public import GameTheory.Math.Probability.ConditionalSystem

@[expose] public section

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace InformationModel

variable (M : InformationModel E) [E.FiniteMovers]

/-- Terminal histories whose paths pass through a decision information site. -/
def terminalPassage (who : ι) (site : M.InformationSite who) : Set E.TerminalHistory :=
  {final | ∃ history : M.InformationHistory who site.1, E.HistoryReaches history.1 final.1}

theorem terminalPassage_nonempty (certificate : E.WellFoundedHistories)
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who) :
    (M.terminalPassage who site).Nonempty := by
  obtain ⟨history, _⟩ := site.2
  obtain ⟨final, reached⟩ := M.terminalCone_nonempty certificate strategy history.1
  exact ⟨final, history, reached⟩

/-- A common conditional system represents beliefs and behavioral continuations.
The positive-belief guard allows arbitrary continuation beliefs at nodes ruled
out by the assessment; chance nodes remain constrained independently of reach. -/
structure BehavioralAssessment.ConditionalProbabilityCompatible
    (A : M.BehavioralAssessment) (certificate : E.WellFoundedHistories)
    (C : ConditionalProbabilitySystem E.TerminalHistory) : Prop where
  represents : ∀ (who : ι) (site : M.InformationSite who)
    (history : M.InformationHistory who site.1),
    A.belief who site history = C.prob (E.terminalCone history.1)
      (M.terminalPassage who site) (M.terminalPassage_nonempty certificate A.strategy who site)
  continuation : ∀ (who : ι) (site : M.InformationSite who)
    (history : M.InformationHistory who site.1), 0 < A.belief who site history →
    ∀ later : E.History, E.HistoryReaches history.1 later →
      C.prob (E.terminalCone later) (E.terminalCone history.1)
        (M.terminalCone_nonempty certificate A.strategy history.1) =
      (M.terminalLaw certificate A.strategy history.1).toOuterMeasure (E.terminalCone later)
  nature : ∀ history : E.History, ¬ E.terminal history.state →
    (∀ who, ¬ E.active history.state who) →
    ∀ later : E.History, E.HistoryReaches history later →
      C.prob (E.terminalCone later) (E.terminalCone history)
        (M.terminalCone_nonempty certificate A.strategy history) =
      (M.terminalLaw certificate A.strategy history).toOuterMeasure (E.terminalCone later)

/-- All on-path and off-path beliefs come from one common conditional system. -/
def BehavioralAssessment.IsConditionalProbabilityConsistent
    (A : M.BehavioralAssessment) (certificate : E.WellFoundedHistories) : Prop :=
  ∃ C : ConditionalProbabilitySystem E.TerminalHistory,
    A.ConditionalProbabilityCompatible M certificate C

/-- Conditional-probability perfect Bayesian equilibrium with explicitly represented
chance, whole-policy rationality and a common conditional system respecting play. -/
def BehavioralAssessment.IsConditionalPBE
    [DecidableEq ι] (A : M.BehavioralAssessment) (certificate : E.WellFoundedHistories)
    (payoff : ι → E.History → ℝ) : Prop :=
  A.IsSequentiallyRational certificate payoff ∧
    A.IsConditionalProbabilityConsistent M certificate ∧ E.HasExplicitChance

end InformationModel
end GameTheory.Protocol
