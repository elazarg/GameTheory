/-
# Sequential-equilibrium existence for finite extensive games

This explicit analytic import adds existence to the lightweight EFG
assessment interface. Finite tree-shaped execution supplies finite histories;
perfect recall and inhabited total policies supply the strategic hypotheses.
-/

import GameTheory.Analysis.Protocol.EFG
import GameTheory.Analysis.Protocol.SequentialExistence
import GameTheory.Protocol.FiniteHorizon

noncomputable section

namespace GameTheory.Languages.EFG.Game

open GameTheory.Protocol

universe uι us ua up uq uk

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (G : Game.{uι, us, ua, up, uq, uk} ι)
    [Fintype G.execution.State] [∀ i, Fintype (G.execution.Action i)]
    [∀ i, Fintype (G.information.InfoState i)]
    [∀ i, DecidableEq (G.information.InfoState i)]

/-- Finite perfect-recall EFGs have a sequential equilibrium at every positive
certified terminal horizon. The conclusion is the existing EFG predicate. -/
theorem exists_isSequentialEquilibriumWithin
    (hrecall : G.information.PerfectRecall)
    (fallback : (i : ι) → G.information.Policy i)
    (payoff : ι → G.History → ℝ) (bound : ℕ) (hpositive : 0 < bound)
    (hbound : G.execution.BoundedHorizon bound) :
    ∃ assessment : G.information.BehavioralAssessment,
      G.IsSequentialEquilibriumWithin
        (G.information.decisionInformationAntichain_of_perfectRecall hrecall)
        assessment payoff bound := by
  let : Fintype G.History := G.historyFintype
  obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
  exact G.information.exists_sequentialEquilibriumWithin hrecall fallback payoff fuel hbound

/-- The finite tree supplies a sufficient horizon automatically. -/
theorem exists_isSequentialEquilibrium
    (hrecall : G.information.PerfectRecall)
    (fallback : (i : ι) → G.information.Policy i)
    (payoff : ι → G.History → ℝ) :
    ∃ (bound : ℕ) (assessment : G.information.BehavioralAssessment),
      0 < bound ∧ G.execution.BoundedHorizon bound ∧
        G.IsSequentialEquilibriumWithin
          (G.information.decisionInformationAntichain_of_perfectRecall hrecall)
          assessment payoff bound := by
  let : Fintype G.History := G.historyFintype
  obtain ⟨bound, hpositive, hbound⟩ := G.execution.exists_pos_boundedHorizon
  obtain ⟨assessment, hequilibrium⟩ :=
    G.exists_isSequentialEquilibriumWithin hrecall fallback payoff bound hpositive hbound
  exact ⟨bound, assessment, hpositive, hbound, hequilibrium⟩

end GameTheory.Languages.EFG.Game
