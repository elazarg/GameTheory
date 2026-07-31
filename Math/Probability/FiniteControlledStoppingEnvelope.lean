/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ProbabilityMassFunction
import Math.PMFIter

/-!
# Finite controlled stopping envelopes

This file isolates the finite Bellman construction needed when a public
selection phase is not action-independent.  A finite ranked transition
system has one prescribed kernel and, for each player and pure action, one
unilateral controlled kernel.  The prescribed kernel is the mixture of the
controlled kernels under the prescribed mixed action.

For a terminal obstacle, backward induction constructs two values:

* the prescribed stopping value;
* the worst unilateral stopping envelope.

The envelope is superharmonic for every pure action and hence for every
mixed unilateral action.  It dominates the prescribed value.  If the
domination is strict at a root, a descent through the prescribed support
finds a prescribed-reachable node and a player-owned action with a strictly
positive Bellman gap.  Thus a large root gap cannot be caused only by an
unreachable branch of the finite tree.

The obstacle may depend on the complete finite public history encoded by
`Node`.  In a stopped-child application it should be the selected child's
initial target or deviation potential at that terminal history.  No
globally absorbing implementation is assumed here.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Math.ProbabilityMassFunction

variable {Player Node : Type} {Action : Player → Type}

/-- Finite ranked stopping data for one prescribed process and every pure
unilateral one-step replacement.

The rank condition is imposed on both the prescribed kernel and every
controlled kernel.  It is the finite-tree condition that makes backward
induction exact.  `prescribed_eq_mix` records the ordinary behavioral fact
that prescribed play is the mixture of its pure unilateral replacements. -/
structure FiniteControlledStoppingModel
    (Player Node : Type) (Action : Player → Type) where
  terminal : Node → Prop
  rank : Node → ℕ
  obstacle : Node → Player → ℝ
  prescribedKernel : Node → PMF Node
  controlledKernel : Node → (who : Player) → Action who → PMF Node
  prescribedAction : Node → (who : Player) → PMF (Action who)
  terminal_of_rank_zero :
    ∀ node, rank node = 0 → terminal node
  prescribed_step_rank :
    ∀ node next,
      ¬ terminal node →
        prescribedKernel node next ≠ 0 →
          rank next + 1 = rank node
  controlled_step_rank :
    ∀ node who action next,
      ¬ terminal node →
        controlledKernel node who action next ≠ 0 →
          rank next + 1 = rank node
  prescribed_eq_mix :
    ∀ node who,
      prescribedKernel node =
        (prescribedAction node who).bind
          (controlledKernel node who)

namespace FiniteControlledStoppingModel

variable
    [Finite Node]
    [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)]
    (model : FiniteControlledStoppingModel Player Node Action)

/-- Values of all pure controlled actions against a continuation value. -/
def controlledActionValues
    (who : Player) (node : Node) (continuation : Node → ℝ) :
    Finset ℝ := by
  classical
  exact Finset.univ.image fun action =>
    expect (model.controlledKernel node who action) continuation

omit [Finite Node] in
theorem controlledActionValues_nonempty
    (who : Player) (node : Node) (continuation : Node → ℝ) :
    (model.controlledActionValues who node continuation).Nonempty := by
  classical
  exact Finset.univ_nonempty.image _

/-- Maximum one-step value available to a unilateral pure action. -/
def maxControlledValue
    (who : Player) (node : Node) (continuation : Node → ℝ) : ℝ := by
  classical
  exact
    (model.controlledActionValues who node continuation).max'
      (model.controlledActionValues_nonempty who node continuation)

omit [Finite Node] in
theorem controlled_expect_le_maxControlledValue
    (who : Player) (node : Node) (continuation : Node → ℝ)
    (action : Action who) :
    expect (model.controlledKernel node who action) continuation ≤
      model.maxControlledValue who node continuation := by
  classical
  apply Finset.le_max'
  exact Finset.mem_image.mpr
    ⟨action, Finset.mem_univ action, rfl⟩

omit [Finite Node] in
theorem exists_controlled_expect_eq_maxControlledValue
    (who : Player) (node : Node) (continuation : Node → ℝ) :
    ∃ action : Action who,
      expect (model.controlledKernel node who action) continuation =
        model.maxControlledValue who node continuation := by
  classical
  have member :
      model.maxControlledValue who node continuation ∈
        model.controlledActionValues who node continuation :=
    Finset.max'_mem _ _
  exact Finset.mem_image.mp member |>.imp fun _ witness => witness.2

open Classical in
/-- Backward value of the prescribed stopping process. -/
def prescribedValue : ℕ → Player → Node → ℝ
  | 0, who, node => model.obstacle node who
  | depth + 1, who, node =>
      if model.terminal node then
        model.obstacle node who
      else
        expect (model.prescribedKernel node)
          (prescribedValue depth who)

open Classical in
/-- Backward worst-case envelope over unilateral pure controls. -/
def deviationEnvelope : ℕ → Player → Node → ℝ
  | 0, who, node => model.obstacle node who
  | depth + 1, who, node =>
      if model.terminal node then
        model.obstacle node who
      else
        model.maxControlledValue who node
          (deviationEnvelope depth who)

omit [Finite Node] [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)] in
@[simp] theorem prescribedValue_zero
    (who : Player) (node : Node) :
    model.prescribedValue 0 who node = model.obstacle node who :=
  rfl

omit [Finite Node] in
@[simp] theorem deviationEnvelope_zero
    (who : Player) (node : Node) :
    model.deviationEnvelope 0 who node = model.obstacle node who :=
  rfl

omit [Finite Node] [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)] in
@[simp] theorem prescribedValue_of_terminal
    (depth : ℕ) (who : Player) (node : Node)
    (terminal : model.terminal node) :
    model.prescribedValue depth who node = model.obstacle node who := by
  cases depth with
  | zero => rfl
  | succ depth =>
      simp [prescribedValue, terminal]

omit [Finite Node] in
@[simp] theorem deviationEnvelope_of_terminal
    (depth : ℕ) (who : Player) (node : Node)
    (terminal : model.terminal node) :
    model.deviationEnvelope depth who node =
      model.obstacle node who := by
  cases depth with
  | zero => rfl
  | succ depth =>
      simp [deviationEnvelope, terminal]

omit [Finite Node] [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)] in
theorem prescribedValue_succ_of_nonterminal
    (depth : ℕ) (who : Player) (node : Node)
    (nonterminal : ¬ model.terminal node) :
    model.prescribedValue (depth + 1) who node =
      expect (model.prescribedKernel node)
        (model.prescribedValue depth who) := by
  simp [prescribedValue, nonterminal]

omit [Finite Node] in
theorem deviationEnvelope_succ_of_nonterminal
    (depth : ℕ) (who : Player) (node : Node)
    (nonterminal : ¬ model.terminal node) :
    model.deviationEnvelope (depth + 1) who node =
      model.maxControlledValue who node
        (model.deviationEnvelope depth who) := by
  simp [deviationEnvelope, nonterminal]

private theorem expect_le_of_le_on_support
    (law : PMF Node) (f g : Node → ℝ)
    (hfg : ∀ node, law node ≠ 0 → f node ≤ g node) :
    expect law f ≤ expect law g := by
  classical
  let patched : Node → ℝ :=
    fun node => if law node = 0 then g node else f node
  calc
    expect law f = expect law patched := by
      apply expect_congr_on_support
      intro node member
      have nonzero : law node ≠ 0 := by
        simpa [PMF.mem_support_iff] using member
      simp [patched, nonzero]
    _ ≤ expect law g := by
      apply expect_mono
      intro node
      by_cases zero : law node = 0
      · simp [patched, zero]
      · simpa [patched, zero] using hfg node zero

private theorem exists_lt_on_support_of_expect_lt
    (law : PMF Node) (f g : Node → ℝ)
    (strict : expect law f < expect law g) :
    ∃ node, law node ≠ 0 ∧ f node < g node := by
  classical
  by_contra absent
  push Not at absent
  have reverse :
      expect law g ≤ expect law f := by
    apply expect_le_of_le_on_support
    intro node nonzero
    exact absent node nonzero
  exact (not_le_of_gt strict) reverse

theorem prescribed_expect_le_maxControlledValue
    (who : Player) (node : Node) (continuation : Node → ℝ) :
    expect (model.prescribedKernel node) continuation ≤
      model.maxControlledValue who node continuation := by
  rw [model.prescribed_eq_mix node who, expect_bind]
  calc
    expect (model.prescribedAction node who)
        (fun action =>
          expect (model.controlledKernel node who action)
            continuation) ≤
      expect (model.prescribedAction node who)
        (fun _ => model.maxControlledValue who node continuation) := by
          apply expect_mono
          intro action
          exact model.controlled_expect_le_maxControlledValue
            who node continuation action
    _ = model.maxControlledValue who node continuation := by
      rw [expect_const]

/-- Backward induction: the unilateral envelope dominates the prescribed
stopping value at every node whose rank fits in the remaining depth. -/
theorem prescribedValue_le_deviationEnvelope_of_rank_le :
    ∀ depth who node,
      model.rank node ≤ depth →
        model.prescribedValue depth who node ≤
          model.deviationEnvelope depth who node := by
  intro depth
  induction depth with
  | zero =>
      intro who node rank_le
      have rank_zero : model.rank node = 0 :=
        Nat.eq_zero_of_le_zero rank_le
      have terminal := model.terminal_of_rank_zero node rank_zero
      simp [terminal]
  | succ depth ih =>
      intro who node rank_le
      by_cases terminal : model.terminal node
      · simp [terminal]
      · rw [
          model.prescribedValue_succ_of_nonterminal
            depth who node terminal,
          model.deviationEnvelope_succ_of_nonterminal
            depth who node terminal
        ]
        calc
          expect (model.prescribedKernel node)
              (model.prescribedValue depth who) ≤
            expect (model.prescribedKernel node)
              (model.deviationEnvelope depth who) := by
                apply expect_le_of_le_on_support
                intro next nonzero
                apply ih
                have step :=
                  model.prescribed_step_rank node next terminal nonzero
                omega
          _ ≤ model.maxControlledValue who node
                (model.deviationEnvelope depth who) :=
            model.prescribed_expect_le_maxControlledValue
              who node (model.deviationEnvelope depth who)

/-- Rank-indexed prescribed stopping potential. -/
def prescribedPotential (who : Player) (node : Node) : ℝ :=
  model.prescribedValue (model.rank node) who node

open Classical in
/-- Prescribed kernel stopped at terminal nodes. -/
def stoppedPrescribedKernel (node : Node) : PMF Node :=
  if model.terminal node then PMF.pure node
  else model.prescribedKernel node

omit [Finite Node] [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)] in
theorem iter_stoppedPrescribedKernel_of_terminal
    (node : Node) (terminal : model.terminal node) :
    ∀ depth,
      Math.PMFIter.iter model.stoppedPrescribedKernel depth node =
        PMF.pure node := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [Math.PMFIter.iter_succ]
      unfold stoppedPrescribedKernel
      rw [if_pos terminal, PMF.pure_bind]
      exact ih

omit [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)] in
/-- The recursive prescribed value is exactly the expected terminal obstacle
under the stopped prescribed kernel. -/
theorem prescribedValue_eq_expect_iter
    (depth : ℕ) (who : Player) (node : Node) :
    model.prescribedValue depth who node =
      expect
        (Math.PMFIter.iter
          model.stoppedPrescribedKernel depth node)
        (fun terminal => model.obstacle terminal who) := by
  induction depth generalizing node with
  | zero =>
      rw [Math.PMFIter.iter_zero, expect_pure]
      rfl
  | succ depth ih =>
      by_cases terminal : model.terminal node
      · rw [
          model.prescribedValue_of_terminal
            (depth + 1) who node terminal,
          model.iter_stoppedPrescribedKernel_of_terminal
            node terminal (depth + 1),
          expect_pure
        ]
      · rw [
          model.prescribedValue_succ_of_nonterminal
            depth who node terminal,
          Math.PMFIter.iter_succ,
          stoppedPrescribedKernel,
          if_neg terminal,
          expect_bind
        ]
        apply congrArg (expect (model.prescribedKernel node))
        funext next
        exact ih next

/-- Rank-indexed worst unilateral stopping envelope. -/
def worstCasePotential (who : Player) (node : Node) : ℝ :=
  model.deviationEnvelope (model.rank node) who node

theorem prescribedPotential_le_worstCasePotential
    (who : Player) (node : Node) :
    model.prescribedPotential who node ≤
      model.worstCasePotential who node :=
  model.prescribedValue_le_deviationEnvelope_of_rank_le
    (model.rank node) who node (le_refl _)

omit [Finite Node] [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)] in
theorem prescribedPotential_eq_obstacle_of_terminal
    (who : Player) (node : Node) (terminal : model.terminal node) :
    model.prescribedPotential who node = model.obstacle node who :=
  model.prescribedValue_of_terminal _ who node terminal

omit [Finite Node] in
theorem worstCasePotential_eq_obstacle_of_terminal
    (who : Player) (node : Node) (terminal : model.terminal node) :
    model.worstCasePotential who node = model.obstacle node who :=
  model.deviationEnvelope_of_terminal _ who node terminal

omit [Finite Node] [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)] in
theorem rank_eq_succ_of_nonterminal
    (node : Node) (nonterminal : ¬ model.terminal node) :
    ∃ depth, model.rank node = depth + 1 := by
  cases rank_eq : model.rank node with
  | zero =>
      exact False.elim
        (nonterminal (model.terminal_of_rank_zero node rank_eq))
  | succ depth =>
      exact ⟨depth, rfl⟩

omit [Finite Node] [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)] in
/-- The prescribed rank-indexed potential is harmonic before stopping. -/
theorem prescribedPotential_harmonic
    (who : Player) (node : Node)
    (nonterminal : ¬ model.terminal node) :
    expect (model.prescribedKernel node)
        (model.prescribedPotential who) =
      model.prescribedPotential who node := by
  obtain ⟨depth, rank_eq⟩ :=
    model.rank_eq_succ_of_nonterminal node nonterminal
  rw [prescribedPotential, rank_eq,
    model.prescribedValue_succ_of_nonterminal
      depth who node nonterminal]
  apply expect_congr_on_support
  intro next member
  have nonzero : model.prescribedKernel node next ≠ 0 := by
    simpa [PMF.mem_support_iff] using member
  have next_rank :=
    model.prescribed_step_rank node next nonterminal nonzero
  change
    model.prescribedValue (model.rank next) who next =
      model.prescribedValue depth who next
  have next_rank_eq : model.rank next = depth := by
    omega
  rw [next_rank_eq]

omit [Finite Node] in
/-- The rank-indexed worst-case envelope is superharmonic for every pure
unilateral action before stopping. -/
theorem worstCasePotential_superharmonic
    (who : Player) (node : Node)
    (nonterminal : ¬ model.terminal node)
    (action : Action who) :
    expect (model.controlledKernel node who action)
        (model.worstCasePotential who) ≤
      model.worstCasePotential who node := by
  obtain ⟨depth, rank_eq⟩ :=
    model.rank_eq_succ_of_nonterminal node nonterminal
  rw [worstCasePotential, rank_eq,
    model.deviationEnvelope_succ_of_nonterminal
      depth who node nonterminal]
  calc
    expect (model.controlledKernel node who action)
        (model.worstCasePotential who) =
      expect (model.controlledKernel node who action)
        (model.deviationEnvelope depth who) := by
          apply expect_congr_on_support
          intro next member
          have nonzero :
              model.controlledKernel node who action next ≠ 0 := by
            simpa [PMF.mem_support_iff] using member
          have next_rank :=
            model.controlled_step_rank node who action next
              nonterminal nonzero
          change
            model.deviationEnvelope (model.rank next) who next =
              model.deviationEnvelope depth who next
          have next_rank_eq : model.rank next = depth := by
            omega
          rw [next_rank_eq]
    _ ≤ model.maxControlledValue who node
          (model.deviationEnvelope depth who) :=
      model.controlled_expect_le_maxControlledValue
        who node (model.deviationEnvelope depth who) action

/-- The same envelope inequality holds for every mixed unilateral action. -/
theorem worstCasePotential_mixed_superharmonic
    (who : Player) (node : Node)
    (nonterminal : ¬ model.terminal node)
    (mixed : PMF (Action who)) :
    expect
        (mixed.bind (model.controlledKernel node who))
        (model.worstCasePotential who) ≤
      model.worstCasePotential who node := by
  rw [expect_bind]
  calc
    expect mixed
        (fun action =>
          expect (model.controlledKernel node who action)
            (model.worstCasePotential who)) ≤
      expect mixed
        (fun _ => model.worstCasePotential who node) := by
          apply expect_mono
          intro action
          exact model.worstCasePotential_superharmonic
            who node nonterminal action
    _ = model.worstCasePotential who node := by
      rw [expect_const]

open Classical in
/-- Backward stopping value of an arbitrary history-dependent unilateral
mixed control.  The control is read at the current node, so `Node` may encode
the complete public history. -/
def controlledPolicyValue
    (who : Player) (policy : Node → PMF (Action who)) :
    ℕ → Node → ℝ
  | 0, node => model.obstacle node who
  | depth + 1, node =>
      if model.terminal node then
        model.obstacle node who
      else
        expect (policy node) fun action =>
          expect (model.controlledKernel node who action)
            (controlledPolicyValue who policy depth)

omit [Finite Node] [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)] in
@[simp] theorem controlledPolicyValue_of_terminal
    (who : Player) (policy : Node → PMF (Action who))
    (depth : ℕ) (node : Node) (terminal : model.terminal node) :
    model.controlledPolicyValue who policy depth node =
      model.obstacle node who := by
  cases depth with
  | zero => rfl
  | succ depth =>
      simp [controlledPolicyValue, terminal]

omit [Finite Node] [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)] in
theorem controlledPolicyValue_succ_of_nonterminal
    (who : Player) (policy : Node → PMF (Action who))
    (depth : ℕ) (node : Node)
    (nonterminal : ¬ model.terminal node) :
    model.controlledPolicyValue who policy (depth + 1) node =
      expect (policy node) fun action =>
        expect (model.controlledKernel node who action)
          (model.controlledPolicyValue who policy depth) := by
  simp [controlledPolicyValue, nonterminal]

/-- The constructed envelope dominates every adaptive unilateral policy on
the finite ranked stopping tree. -/
theorem controlledPolicyValue_le_deviationEnvelope_of_rank_le
    (who : Player) (policy : Node → PMF (Action who)) :
    ∀ depth node,
      model.rank node ≤ depth →
        model.controlledPolicyValue who policy depth node ≤
          model.deviationEnvelope depth who node := by
  intro depth
  induction depth with
  | zero =>
      intro node rank_le
      have rank_zero : model.rank node = 0 :=
        Nat.eq_zero_of_le_zero rank_le
      have terminal := model.terminal_of_rank_zero node rank_zero
      simp [terminal]
  | succ depth ih =>
      intro node rank_le
      by_cases terminal : model.terminal node
      · simp [terminal]
      · rw [
          model.controlledPolicyValue_succ_of_nonterminal
            who policy depth node terminal,
          model.deviationEnvelope_succ_of_nonterminal
            depth who node terminal
        ]
        calc
          expect (policy node)
              (fun action =>
                expect (model.controlledKernel node who action)
                  (model.controlledPolicyValue who policy depth)) ≤
            expect (policy node)
              (fun action =>
                expect (model.controlledKernel node who action)
                  (model.deviationEnvelope depth who)) := by
                    apply expect_mono
                    intro action
                    apply expect_le_of_le_on_support
                    intro next nonzero
                    apply ih
                    have step :=
                      model.controlled_step_rank node who action next
                        terminal nonzero
                    omega
          _ ≤
            expect (policy node)
              (fun _ =>
                model.maxControlledValue who node
                  (model.deviationEnvelope depth who)) := by
                    apply expect_mono
                    intro action
                    exact
                      model.controlled_expect_le_maxControlledValue
                        who node
                        (model.deviationEnvelope depth who) action
          _ =
            model.maxControlledValue who node
              (model.deviationEnvelope depth who) := by
                rw [expect_const]

/-- Semantic finite-tree ceiling for an arbitrary adaptive unilateral
policy, indexed by the root rank. -/
theorem controlledPolicyStoppingValue_le_worstCasePotential
    (who : Player) (policy : Node → PMF (Action who)) (root : Node) :
    model.controlledPolicyValue who policy (model.rank root) root ≤
      model.worstCasePotential who root :=
  model.controlledPolicyValue_le_deviationEnvelope_of_rank_le
    who policy (model.rank root) root (le_refl _)

/-- Reachability using only positive-mass prescribed transitions. -/
inductive PrescribedReachable (root : Node) : Node → Prop
  | root : PrescribedReachable root root
  | step {node next : Node} :
      PrescribedReachable root node →
      ¬ model.terminal node →
      model.prescribedKernel node next ≠ 0 →
      PrescribedReachable root next

/-- A reachable player-owned pure action with strict Bellman advantage over
the prescribed continuation of the worst-case envelope. -/
structure PositiveBellmanGap (root : Node) (who : Player) where
  node : Node
  depth : ℕ
  reachable : model.PrescribedReachable root node
  nonterminal : ¬ model.terminal node
  rank_eq : model.rank node = depth + 1
  action : Action who
  positive :
    expect (model.prescribedKernel node)
        (model.deviationEnvelope depth who) <
      expect (model.controlledKernel node who action)
        (model.deviationEnvelope depth who)

/-- Strict root domination descends through positive-mass prescribed edges
until it encounters a reachable player-owned action with positive Bellman
gap. -/
theorem exists_positiveBellmanGap_of_prescribedValue_lt :
    ∀ {root node : Node} (who : Player),
      model.PrescribedReachable root node →
      model.prescribedPotential who node <
        model.worstCasePotential who node →
      Nonempty (model.PositiveBellmanGap root who) := by
  intro root node who reachable strict
  generalize rank_eq_depth : model.rank node = depth
  induction depth using Nat.strong_induction_on
      generalizing node reachable strict with
  | h depth ih =>
      by_cases terminal : model.terminal node
      · rw [
          model.prescribedPotential_eq_obstacle_of_terminal
            who node terminal,
          model.worstCasePotential_eq_obstacle_of_terminal
            who node terminal
        ] at strict
        exact False.elim (lt_irrefl _ strict)
      · obtain ⟨previous, rank_eq_previous⟩ :=
          model.rank_eq_succ_of_nonterminal node terminal
        have prescribed_unfold :
            model.prescribedPotential who node =
              expect (model.prescribedKernel node)
                (model.prescribedValue previous who) := by
          rw [prescribedPotential, rank_eq_previous,
            model.prescribedValue_succ_of_nonterminal
              previous who node terminal]
        have envelope_unfold :
            model.worstCasePotential who node =
              model.maxControlledValue who node
                (model.deviationEnvelope previous who) := by
          rw [worstCasePotential, rank_eq_previous,
            model.deviationEnvelope_succ_of_nonterminal
              previous who node terminal]
        let prescribedEnvelope :=
          expect (model.prescribedKernel node)
            (model.deviationEnvelope previous who)
        have prescribed_le_envelope :
            expect (model.prescribedKernel node)
                (model.prescribedValue previous who) ≤
              prescribedEnvelope := by
          apply expect_le_of_le_on_support
          intro next nonzero
          apply model.prescribedValue_le_deviationEnvelope_of_rank_le
          have step :=
            model.prescribed_step_rank node next terminal nonzero
          omega
        have envelope_le_max :
            prescribedEnvelope ≤
              model.maxControlledValue who node
                (model.deviationEnvelope previous who) :=
          model.prescribed_expect_le_maxControlledValue
            who node (model.deviationEnvelope previous who)
        by_cases localGap :
            prescribedEnvelope <
              model.maxControlledValue who node
                (model.deviationEnvelope previous who)
        · obtain ⟨action, action_eq⟩ :=
            model.exists_controlled_expect_eq_maxControlledValue
              who node (model.deviationEnvelope previous who)
          exact ⟨{
            node := node
            depth := previous
            reachable := reachable
            nonterminal := terminal
            rank_eq := rank_eq_previous
            action := action
            positive := by simpa [prescribedEnvelope, action_eq]
          }⟩
        · have max_eq : prescribedEnvelope =
              model.maxControlledValue who node
                (model.deviationEnvelope previous who) :=
            le_antisymm envelope_le_max (le_of_not_gt localGap)
          have expectation_strict :
              expect (model.prescribedKernel node)
                  (model.prescribedValue previous who) <
                expect (model.prescribedKernel node)
                  (model.deviationEnvelope previous who) := by
            dsimp [prescribedEnvelope] at max_eq ⊢
            rw [max_eq,
              ← envelope_unfold, ← prescribed_unfold]
            exact strict
          obtain ⟨next, nonzero, next_strict⟩ :=
            exists_lt_on_support_of_expect_lt
              (model.prescribedKernel node)
              (model.prescribedValue previous who)
              (model.deviationEnvelope previous who)
              expectation_strict
          have next_rank :
              model.rank next = previous := by
            have step :=
              model.prescribed_step_rank node next terminal nonzero
            omega
          exact
            ih previous (by omega)
              (PrescribedReachable.step (model := model)
                reachable terminal nonzero)
              (by
                simpa [prescribedPotential, worstCasePotential, next_rank]
                  using next_strict)
              next_rank

/-- The finite obstacle/envelope split at a root.

If the worst unilateral terminal envelope is within `error` of the
prescribed stopping value, the first branch records that quantitative
deviation-safe ceiling.  Otherwise, nonnegative `error` implies strict root
domination, and the second branch returns a prescribed-reachable owned
action with positive Bellman gap. -/
theorem rootGap_le_or_positiveBellmanGap
    (root : Node) (who : Player) (error : ℝ) (error_nonneg : 0 ≤ error) :
    model.worstCasePotential who root ≤
        model.prescribedPotential who root + error ∨
      Nonempty (model.PositiveBellmanGap root who) := by
  by_cases safe :
      model.worstCasePotential who root ≤
        model.prescribedPotential who root + error
  · exact Or.inl safe
  · apply Or.inr
    apply model.exists_positiveBellmanGap_of_prescribedValue_lt
      who (PrescribedReachable.root (model := model))
    have dominates :=
      model.prescribedPotential_le_worstCasePotential who root
    linarith

end FiniteControlledStoppingModel
end Probability
end Math
