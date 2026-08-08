/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.DebtAugmentedEdge
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Compact occupation laws of debt-augmented quitting edges

This file packages the exact finite algebra needed before any Palm argument.
The bounded debt-augmented edge relation is compact.  Consequently every
sequence of empirical laws of exact finite debt chains has a weakly
convergent subsequence.  The finite source/target discrepancy is an endpoint
term, so every such weak limit is invariant.

No claim is made here that an invariant zero-density law retains marked
bursts, or that such bursts can be converted into a uniform strategy.  That
is the separate Palm/rare-event boundary.
-/

noncomputable section

namespace GameTheory

open Filter MeasureTheory Math.Probability Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Closed and compact augmented edge space -/

/-- Bounded exact debt-edge graph. -/
def quittingDebtEdgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingDebtPoint ι × QuittingDebtPoint ι) :=
  {edge | edge.1 ∈ quittingDebtBox reward ∧
    edge.2 ∈ quittingDebtBox reward ∧
    IsQuittingDebtEdge reward edge.1 edge.2}

/-- Membership in the bounded debt-edge graph contains an exact debt edge. -/
theorem isQuittingDebtEdge_of_mem_edgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {edge : QuittingDebtPoint ι × QuittingDebtPoint ι}
    (hedge : edge ∈ quittingDebtEdgeGraph reward) :
    IsQuittingDebtEdge reward edge.1 edge.2 :=
  hedge.2.2

/-- Opponent Continue mass is continuous in the augmented state. -/
theorem continuous_quittingDebtOpponentContinueMass (owner : ι) :
    Continuous (fun state : QuittingDebtPoint ι ↦
      quittingDebtOpponentContinueMass state owner) := by
  unfold quittingDebtOpponentContinueMass
  apply continuous_finsetProd
  intro other _
  exact (continuous_apply false).comp
    (continuous_subtype_val.comp
      ((continuous_apply other).comp (continuous_snd.comp continuous_fst)))

/-- The bounded exact augmented edge graph is closed. -/
theorem isClosed_quittingDebtEdgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsClosed (quittingDebtEdgeGraph reward) := by
  let nashProjection :
      (QuittingDebtPoint ι × QuittingDebtPoint ι) →
        (QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι) :=
    fun edge ↦ (edge.1.1, edge.2.1)
  let debtCurrent :
      (QuittingDebtPoint ι × QuittingDebtPoint ι) → Payoff ι :=
    fun edge ↦ edge.1.2
  let debtSuccessor :
      (QuittingDebtPoint ι × QuittingDebtPoint ι) → Payoff ι :=
    fun edge ↦ edge.2.2
  let recurrence : ι →
      (QuittingDebtPoint ι × QuittingDebtPoint ι) → ℝ :=
    fun who edge ↦ edge.1.2 who -
      quittingDebtOpponentContinueMass edge.1 who * edge.2.2 who
  have hnash : IsClosed
      (nashProjection ⁻¹'
        {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
          edge.1 ∈ quittingNashBellmanBox (quittingRewardBound reward) ∧
          edge.2 ∈ quittingNashBellmanBox (quittingRewardBound reward) ∧
          IsQuittingNashBellmanEdge reward edge.1 edge.2}) :=
    (isClosed_quittingNashBellmanEdgeGraph reward
      (quittingRewardBound reward)).preimage (by
        dsimp only [nashProjection]
        fun_prop)
  have hcurrentDebt : IsClosed
      (debtCurrent ⁻¹' Set.Icc (0 : Payoff ι)
        (quittingPositiveSingletonDebtCap reward)) :=
    isClosed_Icc.preimage (by
      dsimp only [debtCurrent]
      fun_prop)
  have hsuccessorDebt : IsClosed
      (debtSuccessor ⁻¹' Set.Icc (0 : Payoff ι)
        (quittingPositiveSingletonDebtCap reward)) :=
    isClosed_Icc.preimage (by
      dsimp only [debtSuccessor]
      fun_prop)
  have hrecurrence : IsClosed
      {edge : QuittingDebtPoint ι × QuittingDebtPoint ι |
        ∀ who, recurrence who edge = 0} := by
    have heq : {edge : QuittingDebtPoint ι × QuittingDebtPoint ι |
          ∀ who, recurrence who edge = 0} =
        ⋂ who, {edge | recurrence who edge = 0} := by
      ext edge
      simp
    rw [heq]
    apply isClosed_iInter
    intro who
    exact isClosed_eq (by
      dsimp only [recurrence]
      exact ((continuous_apply who).comp
          (continuous_snd.comp continuous_fst)).sub
        ((continuous_quittingDebtOpponentContinueMass who).comp
            continuous_fst |>.mul
          ((continuous_apply who).comp
            (continuous_snd.comp continuous_snd)))) continuous_const
  have heq : quittingDebtEdgeGraph reward =
      nashProjection ⁻¹'
          {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
            edge.1 ∈ quittingNashBellmanBox (quittingRewardBound reward) ∧
            edge.2 ∈ quittingNashBellmanBox (quittingRewardBound reward) ∧
            IsQuittingNashBellmanEdge reward edge.1 edge.2} ∩
        debtCurrent ⁻¹' Set.Icc (0 : Payoff ι)
          (quittingPositiveSingletonDebtCap reward) ∩
        debtSuccessor ⁻¹' Set.Icc (0 : Payoff ι)
          (quittingPositiveSingletonDebtCap reward) ∩
        {edge | ∀ who, recurrence who edge = 0} := by
    ext edge
    simp only [quittingDebtEdgeGraph, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_preimage, nashProjection, debtCurrent, debtSuccessor,
      recurrence, quittingDebtBox, IsQuittingDebtEdge, sub_eq_zero]
    aesop
  rw [heq]
  exact ((hnash.inter hcurrentDebt).inter hsuccessorDebt).inter hrecurrence

/-- A limit of eventually exact bounded debt edges is an exact debt edge. -/
theorem isQuittingDebtEdge_of_tendsto_edgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {edge : QuittingDebtPoint ι × QuittingDebtPoint ι}
    {candidate : ℕ → QuittingDebtPoint ι × QuittingDebtPoint ι}
    (hcandidate : Tendsto candidate atTop (nhds edge))
    (heventually : ∀ᶠ index in atTop,
      candidate index ∈ quittingDebtEdgeGraph reward) :
    IsQuittingDebtEdge reward edge.1 edge.2 :=
  isQuittingDebtEdge_of_mem_edgeGraph reward
    ((isClosed_quittingDebtEdgeGraph reward).mem_of_tendsto
      hcandidate heventually)

/-- The bounded exact augmented edge graph is compact. -/
theorem quittingDebtEdgeGraph_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (quittingDebtEdgeGraph reward) := by
  apply (quittingDebtBox_isCompact reward).prod
      (quittingDebtBox_isCompact reward) |>.of_isClosed_subset
    (isClosed_quittingDebtEdgeGraph reward)
  intro edge hedge
  exact ⟨hedge.1, hedge.2.1⟩

/-- A point in the compact exact augmented edge graph. -/
abbrev QuittingDebtEdgePoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  {edge : QuittingDebtPoint ι × QuittingDebtPoint ι //
    edge ∈ quittingDebtEdgeGraph reward}

instance quittingDebtEdgePointCompactSpace
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    CompactSpace (QuittingDebtEdgePoint reward) :=
  isCompact_iff_compactSpace.mp (quittingDebtEdgeGraph_isCompact reward)

end GameTheory
