/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicStoppedHistoryAccounting
import Math.PMFProduct.Update
import Math.Probability.FiniteControlledStoppingEnvelope

/-!
# Bellman envelopes on a finite public-history tree

This file supplies the concrete time-augmented history tree used by the
finite controlled stopping-envelope theorem.  A node is a public history
whose length is at most a fixed fuel.  Its rank is the remaining time.
Prescribed transitions follow a supplied behavior profile; a controlled
transition replaces one player's current mixed action by one pure action.

At full horizon the obstacle is read from the stopped public-history
selected by a deterministic bounded selector.  It can therefore be the
selected child's initial target or deviation potential and may depend on the
complete terminal public history.

The construction is intentionally a finite-horizon obstacle theorem.  It
does not itself identify the obstacle with a child certificate, prove the
selector causal, or assemble the post-stopping dispatcher.  Those are the
separate strategic interfaces in the variable-stopping compiler.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.PMFProduct Math.Probability
open Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

/-- Extend a bounded public-history node by one action and successor state. -/
def boundedPublicHistorySuccessor {fuel : ℕ}
    (node : G.BoundedStoppedHistory fuel)
    (strict : node.1.val < fuel)
    (action : G.JointAct) (next : G.State) :
    G.BoundedStoppedHistory fuel :=
  ⟨⟨node.1.val + 1, Nat.succ_lt_succ strict⟩,
    (Fin.snoc node.2.1 (node.2.2, action), next)⟩

@[simp] theorem boundedPublicHistorySuccessor_length {fuel : ℕ}
    (node : G.BoundedStoppedHistory fuel)
    (strict : node.1.val < fuel)
    (action : G.JointAct) (next : G.State) :
    (G.boundedPublicHistorySuccessor node strict action next).1.val =
      node.1.val + 1 :=
  rfl

/-- Remaining time on the bounded public-history tree. -/
def boundedPublicHistoryRank {fuel : ℕ}
    (node : G.BoundedStoppedHistory fuel) : ℕ :=
  fuel - node.1.val

/-- Full-horizon nodes are exactly the terminal nodes of the augmented
history tree. -/
def IsFullHorizonNode {fuel : ℕ}
    (node : G.BoundedStoppedHistory fuel) : Prop :=
  node.1.val = fuel

/-- Regard a full-horizon bounded node as an ordinary history of length
`fuel`. -/
def fullHistoryOfBoundedNode {fuel : ℕ}
    (node : G.BoundedStoppedHistory fuel)
    (full : G.IsFullHorizonNode node) : G.Hist fuel :=
  cast (congrArg G.Hist full) node.2

/-- Terminal obstacle obtained by applying a bounded stopping selector to a
full public history.  Values away from full horizon are irrelevant because
backward induction reads the obstacle only at terminal nodes. -/
def selectedStoppedHistoryObstacle
    {Player : Type} {fuel : ℕ}
    (selector : G.BoundedPublicStopSelector fuel)
    (boundary : G.BoundedStoppedHistory fuel → Player → ℝ)
    (node : G.BoundedStoppedHistory fuel) (who : Player) : ℝ := by
  classical
  exact
    if full : G.IsFullHorizonNode node then
      boundary
        (G.selectedStoppedHistory selector
          (G.fullHistoryOfBoundedNode node full))
        who
    else
      0

/-- One prescribed step on the time-augmented public-history tree.  A
full-horizon node is held fixed only to make this a total kernel; the
controlled stopping model never takes another step there. -/
def boundedPublicHistoryPrescribedKernel
    [Fintype ι] {fuel : ℕ}
    (profile : G.BehaviorProfile)
    (node : G.BoundedStoppedHistory fuel) :
    PMF (G.BoundedStoppedHistory fuel) :=
  if strict : node.1.val < fuel then
    (G.stageActionDist profile node.2).bind fun action =>
      (G.transition node.2.2 action).bind fun next =>
        PMF.pure
          (G.boundedPublicHistorySuccessor node strict action next)
  else
    PMF.pure node

/-- One pure unilateral replacement on the same finite history tree. -/
def boundedPublicHistoryControlledKernel
    [Fintype ι] [DecidableEq ι] {fuel : ℕ}
    (profile : G.BehaviorProfile)
    (node : G.BoundedStoppedHistory fuel)
    (who : ι) (deviation : G.Act who) :
    PMF (G.BoundedStoppedHistory fuel) :=
  if strict : node.1.val < fuel then
    (pmfPi
      (Function.update
        (fun player => profile player node.1.val node.2)
        who (PMF.pure deviation))).bind fun action =>
      (G.transition node.2.2 action).bind fun next =>
        PMF.pure
          (G.boundedPublicHistorySuccessor node strict action next)
  else
    PMF.pure node

private theorem boundedPublicHistorySuccessor_rank
    {fuel : ℕ} (node : G.BoundedStoppedHistory fuel)
    (strict : node.1.val < fuel)
    (action : G.JointAct) (next : G.State) :
    G.boundedPublicHistoryRank
          (G.boundedPublicHistorySuccessor node strict action next) +
        1 =
      G.boundedPublicHistoryRank node := by
  unfold boundedPublicHistoryRank
  simp only [boundedPublicHistorySuccessor_length]
  omega

/-- Concrete finite controlled stopping model on the public-history tree. -/
def finitePublicHistoryControlledStoppingModel
    [Fintype ι] [DecidableEq ι] {fuel : ℕ}
    (profile : G.BehaviorProfile)
    (selector : G.BoundedPublicStopSelector fuel)
    (boundary : G.BoundedStoppedHistory fuel → ι → ℝ) :
    FiniteControlledStoppingModel
      ι (G.BoundedStoppedHistory fuel) G.Act where
  terminal := G.IsFullHorizonNode
  rank := G.boundedPublicHistoryRank
  obstacle := G.selectedStoppedHistoryObstacle selector boundary
  prescribedKernel := G.boundedPublicHistoryPrescribedKernel profile
  controlledKernel :=
    G.boundedPublicHistoryControlledKernel profile
  prescribedAction :=
    fun node who => profile who node.1.val node.2
  terminal_of_rank_zero := by
    intro node rank_zero
    unfold boundedPublicHistoryRank at rank_zero
    unfold IsFullHorizonNode
    have length_le : node.1.val ≤ fuel :=
      Nat.lt_succ_iff.mp node.1.isLt
    omega
  prescribed_step_rank := by
    intro node next nonterminal nonzero
    have strict : node.1.val < fuel := by
      unfold IsFullHorizonNode at nonterminal
      have length_le : node.1.val ≤ fuel :=
        Nat.lt_succ_iff.mp node.1.isLt
      omega
    have member :
        next ∈
          (G.boundedPublicHistoryPrescribedKernel
            profile node).support := by
      simpa [PMF.mem_support_iff] using nonzero
    rw [boundedPublicHistoryPrescribedKernel, dif_pos strict] at member
    simp only [PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
      at member
    obtain ⟨action, _, successor, _, rfl⟩ := member
    exact G.boundedPublicHistorySuccessor_rank
      node strict action successor
  controlled_step_rank := by
    intro node who deviation next nonterminal nonzero
    have strict : node.1.val < fuel := by
      unfold IsFullHorizonNode at nonterminal
      have length_le : node.1.val ≤ fuel :=
        Nat.lt_succ_iff.mp node.1.isLt
      omega
    have member :
        next ∈
          (G.boundedPublicHistoryControlledKernel
            profile node who deviation).support := by
      simpa [PMF.mem_support_iff] using nonzero
    rw [boundedPublicHistoryControlledKernel, dif_pos strict] at member
    simp only [PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
      at member
    obtain ⟨action, _, successor, _, rfl⟩ := member
    exact G.boundedPublicHistorySuccessor_rank
      node strict action successor
  prescribed_eq_mix := by
    intro node who
    by_cases strict : node.1.val < fuel
    · rw [boundedPublicHistoryPrescribedKernel, dif_pos strict]
      unfold stageActionDist
      let actions : ∀ player, PMF (G.Act player) :=
        fun player => profile player node.1.val node.2
      have product_decomposition :
          pmfPi actions =
            (actions who).bind fun deviation =>
              pmfPi
                (Function.update actions who (PMF.pure deviation)) := by
        calc
          pmfPi actions =
              pmfPi
                (Function.update actions who (actions who)) := by
            congr 1
            funext player
            simp
          _ =
              (actions who).bind fun deviation =>
                pmfPi
                  (Function.update actions who
                    (PMF.pure deviation)) :=
            pmfPi_update_bind actions who (actions who)
      rw [product_decomposition, PMF.bind_bind]
      apply congrArg
      funext deviation
      rw [boundedPublicHistoryControlledKernel, dif_pos strict]
    · rw [
        boundedPublicHistoryPrescribedKernel,
        dif_neg strict
      ]
      calc
        PMF.pure node =
            (profile who node.1.val node.2).bind
              (fun _ => PMF.pure node) :=
          (PMF.bind_const _ _).symm
        _ =
            (profile who node.1.val node.2).bind
              (G.boundedPublicHistoryControlledKernel
                profile node who) := by
          apply congrArg
          funext deviation
          rw [boundedPublicHistoryControlledKernel, dif_neg strict]

namespace FinitePublicHistoryControlledStoppingModel

variable
    [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)]
    {fuel : ℕ}
    (profile : G.BehaviorProfile)
    (selector : G.BoundedPublicStopSelector fuel)
    (boundary : G.BoundedStoppedHistory fuel → ι → ℝ)

/-- The initial empty-history node of the augmented tree. -/
def root (initial : G.State) : G.BoundedStoppedHistory fuel :=
  ⟨⟨0, Nat.zero_lt_succ fuel⟩, G.emptyHist initial⟩

omit [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] in
@[simp] theorem root_rank (initial : G.State) :
    G.boundedPublicHistoryRank
        (root (fuel := fuel) initial) = fuel := by
  simp [root, boundedPublicHistoryRank]

/-- Concrete root-level obstacle/envelope alternative for one player.

The positive branch contains a node reachable by positive-mass prescribed
history steps, not an arbitrary off-tree history. -/
theorem rootGap_le_or_reachablePositiveBellmanGap
    (initial : G.State) (who : ι)
    (error : ℝ) (error_nonneg : 0 ≤ error) :
    let model :=
      G.finitePublicHistoryControlledStoppingModel
        profile selector boundary
    model.worstCasePotential who
          (root (fuel := fuel) initial) ≤
        model.prescribedPotential who
            (root (fuel := fuel) initial) +
          error ∨
      Nonempty
        (model.PositiveBellmanGap
          (root (fuel := fuel) initial) who) := by
  let model :=
    G.finitePublicHistoryControlledStoppingModel
      profile selector boundary
  exact model.rootGap_le_or_positiveBellmanGap
    (root (fuel := fuel) initial)
    who error error_nonneg

end FinitePublicHistoryControlledStoppingModel

end StochasticGame
end GameTheory
