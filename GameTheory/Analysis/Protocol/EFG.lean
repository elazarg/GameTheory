/-
# Sequential equilibrium for EFG presentations

Stable `Languages.EFG` syntax imports no solution concepts. This analysis
adapter transparently specializes Protocol predicates to EFG continuations,
without finiteness assumptions on states, information states, or history fibers.
-/

import GameTheory.Analysis.Protocol.Sequential
import GameTheory.Languages.EFG

noncomputable section

namespace GameTheory.Languages.EFG

open GameTheory.Protocol

universe uι

variable {ι : Type uι}

namespace Game

/-- Generic Kreps-Wilson consistency for an EFG assessment. -/
def IsSequentiallyConsistent
    (G : Game ι)
    (hantichain : G.information.DecisionInformationAntichain)
    (assessment : G.information.BehavioralAssessment) : Prop :=
  assessment.IsSequentiallyConsistent hantichain

/-- Sequential equilibrium of an EFG assessment: the Protocol predicate on
terminal play, specialized to the game's information model. -/
def IsSequentialEquilibrium
    (G : Game ι)
    [DecidableEq ι]
    (hantichain : G.information.DecisionInformationAntichain)
    (assessment : G.information.BehavioralAssessment)
    (certificate : G.execution.WellFoundedHistories)
    (payoff : ι → G.History → ℝ) : Prop :=
  assessment.IsSequentialEquilibrium hantichain certificate payoff

/-- The adapter unfolds to whole-policy sequential rationality on terminal play
and generic Kreps-Wilson consistency. -/
theorem isSequentialEquilibrium_iff
    (G : Game ι)
    [DecidableEq ι]
    (hantichain : G.information.DecisionInformationAntichain)
    (assessment : G.information.BehavioralAssessment)
    (certificate : G.execution.WellFoundedHistories)
    (payoff : ι → G.History → ℝ) :
    G.IsSequentialEquilibrium hantichain assessment certificate payoff ↔
      assessment.IsSequentiallyRational certificate payoff ∧
        G.IsSequentiallyConsistent hantichain assessment :=
  Iff.rfl

end Game

end GameTheory.Languages.EFG
