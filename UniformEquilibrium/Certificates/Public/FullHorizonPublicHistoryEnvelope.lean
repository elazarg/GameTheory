/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.Strategy.Potential.Adaptive
import UniformEquilibrium.Certificates.Public.FinitePublicHistoryStoppingEnvelope

/-!
# Full-horizon Bellman envelopes on public histories

This file specializes the finite public-history stopping model to an
obstacle that sees the complete public history at the fixed horizon.  The
obstacle may therefore depend jointly on a selected prefix and everything
that happens after that prefix; no premature projection to the selected
prefix occurs in the Bellman recursion.

The resulting rank-indexed potentials are first defined on bounded
public-history nodes.  They are then exposed as ordinary history potentials
up to the fixed horizon.  Before the horizon:

* the prescribed potential is exactly harmonic under the actual prescribed
  behavior profile;
* the worst-unilateral potential is superharmonic under every mixed
  unilateral replacement, including every history-dependent behavior
  deviation.

At the horizon both potentials equal the supplied full-history obstacle.
The root alternative from the abstract finite controlled stopping model is
retained: either the worst unilateral obstacle is close to the prescribed
one, or a prescribed-reachable public history contains a player-owned
positive Bellman gap.

This is a finite-prefix construction.  It does not select a child, identify
the obstacle with a child certificate, or splice the child after the
horizon.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.PMFProduct Math.Probability
open Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

/-- Regard an ordinary public history of length at most `fuel` as a node of
the bounded public-history tree. -/
def boundedPublicHistoryNode {fuel time : ℕ}
    (history : G.Hist time) (time_le : time ≤ fuel) :
    G.BoundedStoppedHistory fuel :=
  ⟨⟨time, Nat.lt_succ_of_le time_le⟩, history⟩

@[simp] theorem boundedPublicHistoryNode_length {fuel time : ℕ}
    (history : G.Hist time) (time_le : time ≤ fuel) :
    (G.boundedPublicHistoryNode history time_le).1.val = time :=
  rfl

@[simp] theorem boundedPublicHistoryNode_rank {fuel time : ℕ}
    (history : G.Hist time) (time_le : time ≤ fuel) :
    G.boundedPublicHistoryRank
        (G.boundedPublicHistoryNode history time_le) =
      fuel - time :=
  rfl

/-- The complete public history encoded by a full-horizon node. -/
theorem fullHistoryOfBoundedNode_boundedPublicHistoryNode
    {fuel : ℕ} (history : G.Hist fuel) :
    G.fullHistoryOfBoundedNode
        (G.boundedPublicHistoryNode history (le_refl fuel))
        rfl =
      history := by
  rfl

/-- A terminal obstacle that reads the complete fixed-horizon public
history.  Its value away from full-horizon nodes is irrelevant. -/
def fullPublicHistoryObstacle
    {Player : Type} {fuel : ℕ}
    (obstacle : G.Hist fuel → Player → ℝ)
    (node : G.BoundedStoppedHistory fuel) (who : Player) : ℝ := by
  classical
  exact
    if full : G.IsFullHorizonNode node then
      obstacle (G.fullHistoryOfBoundedNode node full) who
    else
      0

private def horizonSelector {fuel : ℕ} :
    G.BoundedPublicStopSelector fuel :=
  fun _ => ⟨fuel, Nat.lt_succ_self fuel⟩

/-- The finite controlled stopping model whose terminal datum sees the
complete history of length `fuel`.

Only the obstacle differs from
`finitePublicHistoryControlledStoppingModel`; the transition and rank
proofs are reused verbatim. -/
def finiteFullHistoryControlledStoppingModel
    [Fintype ι] [DecidableEq ι] {fuel : ℕ}
    (profile : G.BehaviorProfile)
    (obstacle : G.Hist fuel → ι → ℝ) :
    FiniteControlledStoppingModel
      ι (G.BoundedStoppedHistory fuel) G.Act :=
  { G.finitePublicHistoryControlledStoppingModel
      profile (horizonSelector (G := G))
      (fun _ _ => 0) with
    obstacle := G.fullPublicHistoryObstacle obstacle }

namespace FiniteFullHistoryControlledStoppingModel

variable
    [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)]
    {fuel : ℕ}
    (profile : G.BehaviorProfile)
    (obstacle : G.Hist fuel → ι → ℝ)

/-- Rank-indexed prescribed value on bounded public-history nodes. -/
def prescribedNodePotential (who : ι) :
    G.BoundedStoppedHistory fuel → ℝ :=
  (G.finiteFullHistoryControlledStoppingModel
    profile obstacle).prescribedPotential who

/-- Rank-indexed worst-unilateral value on bounded public-history nodes. -/
def worstUnilateralNodePotential (who : ι) :
    G.BoundedStoppedHistory fuel → ℝ :=
  (G.finiteFullHistoryControlledStoppingModel
    profile obstacle).worstCasePotential who

/-- The prescribed finite-prefix value as an ordinary history potential.
Only values at times at most `fuel` carry semantic content. -/
def prescribedHistoryPotential (who : ι) : G.HistoryPotential :=
  fun time history =>
    if time_le : time ≤ fuel then
      prescribedNodePotential profile obstacle who
        (G.boundedPublicHistoryNode history time_le)
    else
      0

/-- The worst-unilateral finite-prefix envelope as an ordinary history
potential.  Only values at times at most `fuel` carry semantic content. -/
def worstUnilateralHistoryPotential (who : ι) :
    G.HistoryPotential :=
  fun time history =>
    if time_le : time ≤ fuel then
      worstUnilateralNodePotential profile obstacle who
        (G.boundedPublicHistoryNode history time_le)
    else
      0

omit [Finite G.State] [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] in
@[simp] theorem prescribedHistoryPotential_of_le
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_le : time ≤ fuel) :
    prescribedHistoryPotential profile obstacle who time history =
      prescribedNodePotential profile obstacle who
        (G.boundedPublicHistoryNode history time_le) := by
  simp [prescribedHistoryPotential, time_le]

omit [Finite G.State] in
@[simp] theorem worstUnilateralHistoryPotential_of_le
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_le : time ≤ fuel) :
    worstUnilateralHistoryPotential profile obstacle who time history =
      worstUnilateralNodePotential profile obstacle who
        (G.boundedPublicHistoryNode history time_le) := by
  simp [worstUnilateralHistoryPotential, time_le]

omit [Finite G.State] [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] in
@[simp] theorem prescribedHistoryPotential_at_horizon
    (who : ι) (history : G.Hist fuel) :
    prescribedHistoryPotential profile obstacle who fuel history =
      obstacle history who := by
  rw [prescribedHistoryPotential_of_le
    profile obstacle who history (le_refl fuel)]
  unfold prescribedNodePotential
  calc
    (G.finiteFullHistoryControlledStoppingModel profile obstacle).prescribedPotential who
          (G.boundedPublicHistoryNode history (le_refl fuel)) =
        (G.finiteFullHistoryControlledStoppingModel profile obstacle).obstacle
          (G.boundedPublicHistoryNode history (le_refl fuel)) who :=
      Math.Probability.FiniteControlledStoppingModel.prescribedPotential_eq_obstacle_of_terminal
          (model :=
            G.finiteFullHistoryControlledStoppingModel profile obstacle)
          who _ rfl
    _ = obstacle history who := by
      change
        G.fullPublicHistoryObstacle obstacle
            (G.boundedPublicHistoryNode history (le_refl fuel)) who =
          obstacle history who
      unfold fullPublicHistoryObstacle
      have full :
          G.IsFullHorizonNode
            (G.boundedPublicHistoryNode history (le_refl fuel)) :=
        rfl
      rw [dif_pos full]
      have proof_eq : full = rfl := Subsingleton.elim _ _
      rw [proof_eq]
      rfl

omit [Finite G.State] in
@[simp] theorem worstUnilateralHistoryPotential_at_horizon
    (who : ι) (history : G.Hist fuel) :
    worstUnilateralHistoryPotential profile obstacle who fuel history =
      obstacle history who := by
  rw [worstUnilateralHistoryPotential_of_le
    profile obstacle who history (le_refl fuel)]
  unfold worstUnilateralNodePotential
  calc
    (G.finiteFullHistoryControlledStoppingModel profile obstacle).worstCasePotential who
          (G.boundedPublicHistoryNode history (le_refl fuel)) =
        (G.finiteFullHistoryControlledStoppingModel profile obstacle).obstacle
          (G.boundedPublicHistoryNode history (le_refl fuel)) who :=
      Math.Probability.FiniteControlledStoppingModel.worstCasePotential_eq_obstacle_of_terminal
          (model :=
            G.finiteFullHistoryControlledStoppingModel profile obstacle)
          who _ rfl
    _ = obstacle history who := by
      change
        G.fullPublicHistoryObstacle obstacle
            (G.boundedPublicHistoryNode history (le_refl fuel)) who =
          obstacle history who
      unfold fullPublicHistoryObstacle
      have full :
          G.IsFullHorizonNode
            (G.boundedPublicHistoryNode history (le_refl fuel)) :=
        rfl
      rw [dif_pos full]
      have proof_eq : full = rfl := Subsingleton.elim _ _
      rw [proof_eq]
      rfl

omit [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] in
private theorem boundedPublicHistorySuccessor_node
    {time : ℕ} (history : G.Hist time) (time_lt : time < fuel)
    (action : G.JointAct) (next : G.State) :
    G.boundedPublicHistorySuccessor
        (G.boundedPublicHistoryNode history (Nat.le_of_lt time_lt))
        time_lt action next =
      G.boundedPublicHistoryNode
        ((Fin.snoc history.1 (history.2, action), next) :
          G.Hist (time + 1))
        (Nat.succ_le_of_lt time_lt) := by
  rfl

omit [Finite G.State] [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] in
/-- Before the horizon, the node potential is exactly harmonic under the
prescribed one-step public-history kernel. -/
theorem prescribedNodePotential_harmonic
    (who : ι) (node : G.BoundedStoppedHistory fuel)
    (nonterminal : ¬G.IsFullHorizonNode node) :
    expect (G.boundedPublicHistoryPrescribedKernel profile node)
        (prescribedNodePotential profile obstacle who) =
      prescribedNodePotential profile obstacle who node := by
  exact
    Math.Probability.FiniteControlledStoppingModel.prescribedPotential_harmonic
        (model :=
          G.finiteFullHistoryControlledStoppingModel profile obstacle)
        who node nonterminal

/-- Before the horizon, the node envelope is superharmonic under every
mixed unilateral action. -/
theorem worstUnilateralNodePotential_mixed_superharmonic
    (who : ι) (node : G.BoundedStoppedHistory fuel)
    (nonterminal : ¬G.IsFullHorizonNode node)
    (mixed : PMF (G.Act who)) :
    expect
        (mixed.bind
          (G.boundedPublicHistoryControlledKernel profile node who))
        (worstUnilateralNodePotential profile obstacle who) ≤
      worstUnilateralNodePotential profile obstacle who node := by
  exact
    Math.Probability.FiniteControlledStoppingModel.worstCasePotential_mixed_superharmonic
        (model :=
          G.finiteFullHistoryControlledStoppingModel profile obstacle)
        who node nonterminal mixed

omit [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] in
/-- The prescribed history potential is exactly harmonic under the actual
behavior profile at every public history strictly before `fuel`. -/
theorem prescribedHistoryPotential_harmonic
    [∀ who, Finite (G.Act who)]
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    G.historyContinuationEU profile
        (prescribedHistoryPotential profile obstacle who) history =
      prescribedHistoryPotential profile obstacle who time history := by
  letI : ∀ who, Fintype (G.Act who) :=
    fun _ => Fintype.ofFinite _
  let node :=
    G.boundedPublicHistoryNode history (Nat.le_of_lt time_lt)
  have nonterminal : ¬G.IsFullHorizonNode node := by
    simpa [node, IsFullHorizonNode] using ne_of_lt time_lt
  have harmonic :=
    prescribedNodePotential_harmonic
      profile obstacle who node nonterminal
  dsimp [node] at harmonic
  rw [
    boundedPublicHistoryPrescribedKernel,
    dif_pos (by simpa using time_lt),
    expect_bind
  ] at harmonic
  unfold historyContinuationEU
  rw [prescribedHistoryPotential_of_le
    profile obstacle who history (Nat.le_of_lt time_lt)]
  apply Eq.trans _ harmonic
  apply congrArg (expect (G.stageActionDist profile history))
  funext action
  rw [expect_bind]
  apply congrArg (expect (G.transition history.2 action))
  funext next
  rw [expect_pure]
  rw [prescribedHistoryPotential_of_le
    profile obstacle who
    ((Fin.snoc history.1 (history.2, action), next) :
      G.Hist (time + 1))
    (Nat.succ_le_of_lt time_lt)]
  exact congrArg
    (prescribedNodePotential profile obstacle who)
    (boundedPublicHistorySuccessor_node
      history time_lt action next).symm

/-- The worst-unilateral history potential is superharmonic after an
arbitrary mixed replacement of player `who`'s current action. -/
theorem worstUnilateralHistoryPotential_mixed_superharmonic
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) (mixed : PMF (G.Act who)) :
    (expect
        (pmfPi
          (Function.update
            (fun player => profile player time history)
            who mixed)) fun action =>
      expect (G.transition history.2 action) fun next =>
        worstUnilateralHistoryPotential profile obstacle who
          (time + 1)
          (Fin.snoc history.1 (history.2, action), next)) ≤
      worstUnilateralHistoryPotential profile obstacle who time history := by
  let node :=
    G.boundedPublicHistoryNode history (Nat.le_of_lt time_lt)
  have nonterminal : ¬G.IsFullHorizonNode node := by
    simpa [node, IsFullHorizonNode] using ne_of_lt time_lt
  have superharmonic :=
    worstUnilateralNodePotential_mixed_superharmonic
      profile obstacle who node nonterminal mixed
  dsimp [node] at superharmonic
  rw [expect_bind] at superharmonic
  let actions : ∀ player, PMF (G.Act player) :=
    fun player => profile player time history
  have product_decomposition :
      pmfPi (Function.update actions who mixed) =
        mixed.bind fun action =>
          pmfPi
            (Function.update actions who (PMF.pure action)) := by
    rw [← pmfPi_update_bind actions who mixed]
  rw [product_decomposition, expect_bind]
  rw [worstUnilateralHistoryPotential_of_le
    profile obstacle who history (Nat.le_of_lt time_lt)]
  apply le_trans _ superharmonic
  apply le_of_eq
  apply congrArg (expect mixed)
  funext deviation
  rw [
    boundedPublicHistoryControlledKernel,
    dif_pos (by simpa using time_lt),
    expect_bind
  ]
  apply congrArg
  funext action
  rw [expect_bind]
  apply congrArg (expect (G.transition history.2 action))
  funext next
  rw [expect_pure]
  rw [worstUnilateralHistoryPotential_of_le
    profile obstacle who
    ((Fin.snoc history.1 (history.2, action), next) :
      G.Hist (time + 1))
    (Nat.succ_le_of_lt time_lt)]
  exact congrArg
    (worstUnilateralNodePotential profile obstacle who)
    (boundedPublicHistorySuccessor_node
      history time_lt action next).symm

/-- In particular, the worst-unilateral history potential is
superharmonic under every history-dependent unilateral behavior
deviation. -/
theorem worstUnilateralHistoryPotential_deviation_superharmonic
    (who : ι) (deviation : G.BehaviorStrategy who)
    {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    G.historyContinuationEU
        (Function.update profile who deviation)
        (worstUnilateralHistoryPotential profile obstacle who)
        history ≤
      worstUnilateralHistoryPotential profile obstacle who time history := by
  have action_dist :
      G.stageActionDist (Function.update profile who deviation) history =
        pmfPi
          (Function.update
            (fun player => profile player time history)
            who (deviation time history)) := by
    unfold stageActionDist
    congr 1
    funext player
    by_cases same : player = who
    · subst same
      simp
    · simp [Function.update_of_ne same]
  unfold historyContinuationEU
  rw [action_dist]
  exact
    worstUnilateralHistoryPotential_mixed_superharmonic
      profile obstacle who history time_lt (deviation time history)

/-- Root-level deviation-safe obstacle alternative with a
prescribed-reachable positive Bellman gap in the second branch. -/
theorem rootGap_le_or_reachablePositiveBellmanGap
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
        (model.PositiveBellmanGap
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) initial) who) := by
  let model :=
    G.finiteFullHistoryControlledStoppingModel profile obstacle
  exact model.rootGap_le_or_positiveBellmanGap
    (FinitePublicHistoryControlledStoppingModel.root
      (fuel := fuel) initial)
    who error error_nonneg

end FiniteFullHistoryControlledStoppingModel

end StochasticGame
end GameTheory
