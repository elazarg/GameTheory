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
    [Fintype ι]
    (hantichain : G.information.DecisionInformationAntichain)
    (assessment : G.information.BehavioralAssessment) : Prop :=
  assessment.IsSequentiallyConsistent hantichain

/-- Sequential equilibrium of an EFG assessment over a supplied finite-horizon
payoff. The predicate is the generic Protocol predicate specialized to the
assessment's canonical continuation contexts. -/
def IsSequentialEquilibriumWithin
    (G : Game ι)
    [Fintype ι] [DecidableEq ι]
    (hantichain : G.information.DecisionInformationAntichain)
    (assessment : G.information.BehavioralAssessment)
    (payoff : ι → G.History → ℝ) (fuel : ℕ) : Prop :=
  assessment.IsSequentialEquilibriumFor hantichain fun i site =>
    assessment.continuationContext site (payoff i) fuel

/-- The adapter unfolds to full-policy rationality in the assessment's
continuation contexts and generic Kreps-Wilson consistency. -/
theorem isSequentialEquilibriumWithin_iff
    (G : Game ι)
    [Fintype ι] [DecidableEq ι]
    (hantichain : G.information.DecisionInformationAntichain)
    (assessment : G.information.BehavioralAssessment)
    (payoff : ι → G.History → ℝ) (fuel : ℕ) :
    G.IsSequentialEquilibriumWithin hantichain assessment payoff fuel ↔
      assessment.IsSequentiallyRationalWithin payoff fuel ∧
        G.IsSequentiallyConsistent hantichain assessment :=
  Iff.rfl

end Game

end GameTheory.Languages.EFG
