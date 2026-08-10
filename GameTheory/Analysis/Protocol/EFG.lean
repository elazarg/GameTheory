/-
# Sequential equilibrium for finite EFG presentations

This language adapter keeps stable EFG syntax
is a transparent specialization of Protocol and imports no solution concept.
Here, above the analytic boundary, finite tree-shaped histories provide the
instances required by pointwise Bayes consistency, and the assessment's own
continuation contexts supply full-policy sequential rationality.
-/

import GameTheory.Analysis.Protocol.Sequential
import GameTheory.Languages.EFG

noncomputable section

namespace GameTheory.Languages.EFG

open GameTheory.Protocol

universe uι

variable {ι : Type uι}

namespace Game

/-- Generic Kreps-Wilson consistency with the finite history-fiber instances
supplied by the EFG's finite state carrier and tree-shapedness law. -/
def IsSequentiallyConsistent
    (G : Game ι)
    [Fintype ι]
    [Fintype G.execution.State]
    [∀ i, DecidableEq (G.information.InfoState i)]
    (assessment : G.information.BehavioralAssessment) : Prop := by
  letI : Fintype G.History := G.historyFintype
  letI (i : ι) (site : G.information.InformationSite i) :
      Fintype (G.information.InformationHistory i site.1) := by
    classical
    infer_instance
  exact assessment.IsSequentiallyConsistent

/-- Sequential equilibrium of a finite EFG assessment over a supplied
finite-horizon payoff. The logical predicate is the generic Protocol predicate;
this adapter only supplies finite history fibers and canonical continuation
contexts. -/
def IsSequentialEquilibriumWithin
    (G : Game ι)
    [Fintype ι] [DecidableEq ι]
    [Fintype G.execution.State]
    [∀ i, DecidableEq (G.information.InfoState i)]
    (assessment : G.information.BehavioralAssessment)
    (payoff : ι → G.History → ℝ) (fuel : ℕ) : Prop := by
  letI : Fintype G.History := G.historyFintype
  letI (i : ι) (site : G.information.InformationSite i) :
      Fintype (G.information.InformationHistory i site.1) := by
    classical
    infer_instance
  exact assessment.IsSequentialEquilibriumFor fun i site =>
    assessment.continuationContext site (payoff i) fuel

/-- The adapter unfolds to full-policy rationality in the assessment's
continuation contexts and generic Kreps-Wilson consistency. -/
theorem isSequentialEquilibriumWithin_iff
    (G : Game ι)
    [Fintype ι] [DecidableEq ι]
    [Fintype G.execution.State]
    [∀ i, DecidableEq (G.information.InfoState i)]
    (assessment : G.information.BehavioralAssessment)
    (payoff : ι → G.History → ℝ) (fuel : ℕ) :
    G.IsSequentialEquilibriumWithin assessment payoff fuel ↔
      assessment.IsSequentiallyRationalWithin payoff fuel ∧
        G.IsSequentiallyConsistent assessment :=
  Iff.rfl

end Game

end GameTheory.Languages.EFG
