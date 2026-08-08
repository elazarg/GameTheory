/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Public.FullHorizonPublicHistoryEnvelope

/-!
# Realizing full-horizon public-history envelope witnesses

The abstract finite stopping envelope returns nodes in the augmented
public-history tree.  This file records the concrete facts needed by the
prefix compiler:

* prescribed reachability from the empty-history root implies positive
  support under the ordinary public-history law;
* one explicit finite constant bounds both prescribed and worst-unilateral
  history potentials at every time up to the horizon;
* a positive abstract Bellman gap is a strict controlled-versus-prescribed
  continuation inequality at an actually supported public history.

No stopping rule, child selector, or punishment certificate is constructed
here.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.PMFProduct Math.Probability
open Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

namespace FiniteFullHistoryControlledStoppingModel

variable
    [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)]
    {fuel : ℕ}
    (profile : G.BehaviorProfile)
    (obstacle : G.Hist fuel → ι → ℝ)

omit [Finite G.State] [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] in
private theorem prescribedReachable_support_aux
    (initial : G.State)
    {node : G.BoundedStoppedHistory fuel}
    (reachable :
      (G.finiteFullHistoryControlledStoppingModel profile obstacle)
        |>.PrescribedReachable
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) initial)
          node) :
    node.2 ∈ (G.histDist profile initial node.1.val).support := by
  induction reachable with
  | root =>
      change
        G.emptyHist initial ∈
          (PMF.pure (G.emptyHist initial)).support
      exact PMF.mem_support_pure_iff _ _ |>.mpr rfl
  | @step node next reachable nonterminal nonzero ih =>
      have strict : node.1.val < fuel := by
        change ¬G.IsFullHorizonNode node at nonterminal
        unfold IsFullHorizonNode at nonterminal
        have length_le : node.1.val ≤ fuel :=
          Nat.lt_succ_iff.mp node.1.isLt
        omega
      have member :
          next ∈
            (G.boundedPublicHistoryPrescribedKernel
              profile node).support := by
        change
          G.boundedPublicHistoryPrescribedKernel profile node next ≠ 0
          at nonzero
        simpa only [PMF.mem_support_iff] using nonzero
      rw [boundedPublicHistoryPrescribedKernel, dif_pos strict] at member
      simp only [PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
        at member
      obtain ⟨action, action_mem, successor, successor_mem, rfl⟩ := member
      change
        ((Fin.snoc node.2.1 (node.2.2, action), successor) :
            G.Hist (node.1.val + 1)) ∈
          (G.histDist profile initial (node.1.val + 1)).support
      rw [G.mem_support_histDist_succ]
      exact
        ⟨node.2, ih, action, action_mem, successor, successor_mem, rfl⟩

omit [Finite G.State] [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] in
/-- Every node reached by positive-mass prescribed transitions from the
concrete root is its own ordinary public history with positive prescribed
probability at the encoded time. -/
theorem mem_support_histDist_of_prescribedReachable
    (initial : G.State)
    {node : G.BoundedStoppedHistory fuel}
    (reachable :
      (G.finiteFullHistoryControlledStoppingModel profile obstacle)
        |>.PrescribedReachable
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) initial)
          node) :
    node.2 ∈ (G.histDist profile initial node.1.val).support :=
  prescribedReachable_support_aux profile obstacle initial reachable

/-- The tagged finite family containing both node potentials. -/
private def taggedEnvelopePotential :
    (ι × G.BoundedStoppedHistory fuel) × Bool → ℝ
  | ((who, node), true) =>
      prescribedNodePotential profile obstacle who node
  | ((who, node), false) =>
      worstUnilateralNodePotential profile obstacle who node

/-- One explicit common bound for the two node potentials.  The outer
maximum makes nonnegativity independent of whether the player type is
inhabited. -/
def fullHorizonEnvelopePotentialBound : ℝ :=
  max 0 <|
    Classical.choose <|
      Math.Probability.exists_abs_bound_of_finite
        (taggedEnvelopePotential profile obstacle)

/-- The explicit common potential bound is nonnegative. -/
theorem fullHorizonEnvelopePotentialBound_nonneg :
    0 ≤ fullHorizonEnvelopePotentialBound profile obstacle := by
  exact le_max_left _ _

/-- The prescribed node potential is bounded by the common finite
constant. -/
theorem abs_prescribedNodePotential_le_fullHorizonEnvelopePotentialBound
    (who : ι) (node : G.BoundedStoppedHistory fuel) :
    |prescribedNodePotential profile obstacle who node| ≤
      fullHorizonEnvelopePotentialBound profile obstacle := by
  apply le_max_of_le_right
  have bound :=
    Classical.choose_spec <|
      Math.Probability.exists_abs_bound_of_finite
        (taggedEnvelopePotential profile obstacle)
  simpa [taggedEnvelopePotential] using bound ((who, node), true)

/-- The worst-unilateral node potential is bounded by the same common
finite constant. -/
theorem abs_worstUnilateralNodePotential_le_fullHorizonEnvelopePotentialBound
    (who : ι) (node : G.BoundedStoppedHistory fuel) :
    |worstUnilateralNodePotential profile obstacle who node| ≤
      fullHorizonEnvelopePotentialBound profile obstacle := by
  apply le_max_of_le_right
  have bound :=
    Classical.choose_spec <|
      Math.Probability.exists_abs_bound_of_finite
        (taggedEnvelopePotential profile obstacle)
  simpa [taggedEnvelopePotential] using bound ((who, node), false)

/-- The prescribed ordinary-history potential is uniformly bounded at
every time carrying finite-horizon semantics. -/
theorem abs_prescribedHistoryPotential_le_fullHorizonEnvelopePotentialBound
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_le : time ≤ fuel) :
    |prescribedHistoryPotential profile obstacle who time history| ≤
      fullHorizonEnvelopePotentialBound profile obstacle := by
  rw [prescribedHistoryPotential_of_le
    profile obstacle who history time_le]
  exact
    abs_prescribedNodePotential_le_fullHorizonEnvelopePotentialBound
      profile obstacle who
      (G.boundedPublicHistoryNode history time_le)

/-- The worst-unilateral ordinary-history potential is uniformly bounded
at every time carrying finite-horizon semantics.  The bound is independent
of the deviation law whose supported histories are later supplied to the
prefix compiler. -/
theorem
    abs_worstUnilateralHistoryPotential_le_fullHorizonEnvelopePotentialBound
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_le : time ≤ fuel) :
    |worstUnilateralHistoryPotential profile obstacle who time history| ≤
      fullHorizonEnvelopePotentialBound profile obstacle := by
  rw [worstUnilateralHistoryPotential_of_le
    profile obstacle who history time_le]
  exact
    abs_worstUnilateralNodePotential_le_fullHorizonEnvelopePotentialBound
      profile obstacle who
      (G.boundedPublicHistoryNode history time_le)

omit [Finite G.State] in
private theorem deviationEnvelope_successor_eq_historyPotential
    (who : ι) (node : G.BoundedStoppedHistory fuel)
    (strict : node.1.val < fuel) (depth : ℕ)
    (rank_eq :
      G.boundedPublicHistoryRank node = depth + 1)
    (action : G.JointAct) (next : G.State) :
    (G.finiteFullHistoryControlledStoppingModel
        profile obstacle).deviationEnvelope depth who
        (G.boundedPublicHistorySuccessor node strict action next) =
      worstUnilateralHistoryPotential profile obstacle who
        (node.1.val + 1)
        (Fin.snoc node.2.1 (node.2.2, action), next) := by
  have time_le : node.1.val + 1 ≤ fuel :=
    Nat.succ_le_of_lt strict
  rw [worstUnilateralHistoryPotential_of_le
    profile obstacle who
    ((Fin.snoc node.2.1 (node.2.2, action), next) :
      G.Hist (node.1.val + 1))
    time_le]
  have node_eq :
      G.boundedPublicHistoryNode
          ((Fin.snoc node.2.1 (node.2.2, action), next) :
            G.Hist (node.1.val + 1))
          time_le =
        G.boundedPublicHistorySuccessor node strict action next := by
    cases node
    rfl
  rw [node_eq]
  unfold worstUnilateralNodePotential
  unfold Math.Probability.FiniteControlledStoppingModel.worstCasePotential
  congr 1
  change
    depth =
      G.boundedPublicHistoryRank
        (G.boundedPublicHistorySuccessor node strict action next)
  unfold boundedPublicHistoryRank at rank_eq ⊢
  simp only [boundedPublicHistorySuccessor_length]
  omega

/-- Concrete history-level data carried by an abstract positive Bellman
gap. -/
structure SupportedHistoryPositiveBellmanGap
    (initial : G.State) (who : ι) where
  time : ℕ
  time_lt : time < fuel
  history : G.Hist time
  history_mem : history ∈ (G.histDist profile initial time).support
  action : G.Act who
  positive :
    G.historyContinuationEU profile
        (worstUnilateralHistoryPotential profile obstacle who) history <
      expect
        (pmfPi
          (Function.update
            (fun player => profile player time history)
            who (PMF.pure action))) fun jointAction =>
        expect (G.transition history.2 jointAction) fun next =>
          worstUnilateralHistoryPotential profile obstacle who
            (time + 1)
            (Fin.snoc history.1 (history.2, jointAction), next)

/-- Translate an abstract reachable Bellman-gap witness into a strict
one-step continuation inequality at an ordinary prescribed-supported
public history. -/
def supportedHistoryPositiveBellmanGapOfPositiveBellmanGap
    (initial : G.State) (who : ι)
    (gap :
      (G.finiteFullHistoryControlledStoppingModel
        profile obstacle).PositiveBellmanGap
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) initial)
      who) :
    SupportedHistoryPositiveBellmanGap
      profile obstacle initial who where
  time := gap.node.1.val
  time_lt := by
    have nonterminal := gap.nonterminal
    change ¬G.IsFullHorizonNode gap.node at nonterminal
    unfold IsFullHorizonNode at nonterminal
    have length_le : gap.node.1.val ≤ fuel :=
      Nat.lt_succ_iff.mp gap.node.1.isLt
    omega
  history := gap.node.2
  history_mem :=
    mem_support_histDist_of_prescribedReachable
      profile obstacle initial gap.reachable
  action := gap.action
  positive := by
    let model :=
      G.finiteFullHistoryControlledStoppingModel profile obstacle
    have strict : gap.node.1.val < fuel := by
      have nonterminal := gap.nonterminal
      change ¬G.IsFullHorizonNode gap.node at nonterminal
      unfold IsFullHorizonNode at nonterminal
      have length_le : gap.node.1.val ≤ fuel :=
        Nat.lt_succ_iff.mp gap.node.1.isLt
      omega
    have prescribed_eq :
        expect (model.prescribedKernel gap.node)
            (model.deviationEnvelope gap.depth who) =
          G.historyContinuationEU profile
            (worstUnilateralHistoryPotential profile obstacle who)
            gap.node.2 := by
      change
        expect
            (G.boundedPublicHistoryPrescribedKernel profile gap.node)
            (model.deviationEnvelope gap.depth who) =
          _
      rw [boundedPublicHistoryPrescribedKernel, dif_pos strict,
        expect_bind]
      unfold historyContinuationEU
      apply congrArg (expect (G.stageActionDist profile gap.node.2))
      funext action
      rw [expect_bind]
      apply congrArg (expect (G.transition gap.node.2.2 action))
      funext next
      rw [expect_pure]
      exact
        deviationEnvelope_successor_eq_historyPotential
          profile obstacle who gap.node strict gap.depth
          (by
            have rank_eq := gap.rank_eq
            change G.boundedPublicHistoryRank gap.node =
              gap.depth + 1 at rank_eq
            exact rank_eq)
          action next
    have controlled_eq :
        expect (model.controlledKernel gap.node who gap.action)
            (model.deviationEnvelope gap.depth who) =
          expect
            (pmfPi
              (Function.update
                (fun player =>
                  profile player gap.node.1.val gap.node.2)
                who (PMF.pure gap.action))) fun jointAction =>
            expect (G.transition gap.node.2.2 jointAction) fun next =>
              worstUnilateralHistoryPotential profile obstacle who
                (gap.node.1.val + 1)
                (Fin.snoc gap.node.2.1
                  (gap.node.2.2, jointAction), next) := by
      change
        expect
            (G.boundedPublicHistoryControlledKernel
              profile gap.node who gap.action)
            (model.deviationEnvelope gap.depth who) =
          _
      rw [boundedPublicHistoryControlledKernel, dif_pos strict,
        expect_bind]
      apply congrArg
      funext jointAction
      rw [expect_bind]
      apply congrArg (expect (G.transition gap.node.2.2 jointAction))
      funext next
      rw [expect_pure]
      exact
        deviationEnvelope_successor_eq_historyPotential
          profile obstacle who gap.node strict gap.depth
          (by
            have rank_eq := gap.rank_eq
            change G.boundedPublicHistoryRank gap.node =
              gap.depth + 1 at rank_eq
            exact rank_eq)
          jointAction next
    rw [← prescribed_eq, ← controlled_eq]
    exact gap.positive

/-- Root obstacle safety or an ordinary prescribed-supported public history
with a strict player-owned one-step continuation gap. -/
theorem rootGap_le_or_supportedHistoryPositiveBellmanGap
    (initial : G.State) (who : ι)
    (error : ℝ) (error_nonneg : 0 ≤ error) :
    let model :=
      G.finiteFullHistoryControlledStoppingModel profile obstacle
    model.worstCasePotential who
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) initial) ≤
        model.prescribedPotential who
            (FinitePublicHistoryControlledStoppingModel.root
              (fuel := fuel) initial) +
          error ∨
      Nonempty
        (SupportedHistoryPositiveBellmanGap
          profile obstacle initial who) := by
  have split :=
    rootGap_le_or_reachablePositiveBellmanGap
      profile obstacle initial who error error_nonneg
  cases split with
  | inl safe =>
      exact Or.inl safe
  | inr gap =>
      exact Or.inr <|
        gap.map <|
          supportedHistoryPositiveBellmanGapOfPositiveBellmanGap
            profile obstacle initial who

end FiniteFullHistoryControlledStoppingModel

end StochasticGame
end GameTheory
