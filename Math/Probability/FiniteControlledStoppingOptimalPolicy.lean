/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import Math.Probability.FiniteControlledStoppingEnvelope

/-!
# Optimal pure policies for finite controlled stopping models

The finite controlled stopping envelope is attained, not merely an upper
bound.  Choosing at every nonterminal node a pure action maximizing the
continuation envelope gives a node-dependent pure policy whose controlled
stopping value equals the worst-case potential, by backward induction.
-/

noncomputable section

namespace Math
namespace Probability

open Math.ProbabilityMassFunction

variable {Player Node : Type} {Action : Player → Type}

namespace FiniteControlledStoppingModel

variable
    [Finite Node]
    [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)]
    (model : FiniteControlledStoppingModel Player Node Action)

/-- Continuation used to select a maximizing pure action at a node.

At a nonterminal node of rank `depth + 1`, this is exactly the depth-indexed
deviation envelope read by the Bellman recursion. -/
def optimalContinuation (who : Player) (node : Node) : Node → ℝ :=
  model.deviationEnvelope (model.rank node - 1) who

/-- A node-dependent pure action attaining the maximum in the Bellman
envelope. -/
def optimalPureAction (who : Player) (node : Node) : Action who :=
  Classical.choose
    (model.exists_controlled_expect_eq_maxControlledValue
      who node (model.optimalContinuation who node))

omit [Finite Node] in
theorem optimalPureAction_spec
    (who : Player) (node : Node) :
    expect
        (model.controlledKernel node who
          (model.optimalPureAction who node))
        (model.optimalContinuation who node) =
      model.maxControlledValue who node
        (model.optimalContinuation who node) :=
  Classical.choose_spec
    (model.exists_controlled_expect_eq_maxControlledValue
      who node (model.optimalContinuation who node))

omit [Finite Node] in
/-- The pure maximizing action realizes the rank-indexed envelope's
one-step Bellman equality. -/
theorem optimalPureAction_expect_eq_worstCasePotential
    (who : Player) (node : Node)
    (nonterminal : ¬ model.terminal node) :
    expect
        (model.controlledKernel node who
          (model.optimalPureAction who node))
        (model.worstCasePotential who) =
      model.worstCasePotential who node := by
  obtain ⟨depth, rank_eq⟩ :=
    model.rank_eq_succ_of_nonterminal node nonterminal
  calc
    expect
        (model.controlledKernel node who
          (model.optimalPureAction who node))
        (model.worstCasePotential who) =
      expect
        (model.controlledKernel node who
          (model.optimalPureAction who node))
        (model.deviationEnvelope depth who) := by
          apply expect_congr_on_support
          intro next member
          have nonzero :
              model.controlledKernel node who
                  (model.optimalPureAction who node) next ≠ 0 := by
            simpa [PMF.mem_support_iff] using member
          have next_rank :=
            model.controlled_step_rank node who
              (model.optimalPureAction who node) next
              nonterminal nonzero
          have next_rank_eq : model.rank next = depth := by
            omega
          simp only [worstCasePotential, next_rank_eq]
    _ =
      model.maxControlledValue who node
        (model.deviationEnvelope depth who) := by
          simpa [optimalContinuation, rank_eq] using
            model.optimalPureAction_spec who node
    _ = model.worstCasePotential who node := by
      rw [worstCasePotential, rank_eq,
        model.deviationEnvelope_succ_of_nonterminal
          depth who node nonterminal]

/-- The maximizing pure action as a degenerate mixed node policy. -/
def optimalPurePolicy
    (who : Player) (node : Node) : PMF (Action who) :=
  PMF.pure (model.optimalPureAction who node)

omit [Finite Node] in
/-- The canonical node-dependent pure policy attains the worst-case
stopping envelope at every root. -/
theorem optimalPurePolicyValue_eq_worstCasePotential
    (who : Player) :
    ∀ node,
      model.controlledPolicyValue who
          (model.optimalPurePolicy who) (model.rank node) node =
        model.worstCasePotential who node := by
  intro node
  generalize rank_eq : model.rank node = depth
  induction depth using Nat.strong_induction_on generalizing node with
  | h depth ih =>
      by_cases terminal : model.terminal node
      · rw [
          model.controlledPolicyValue_of_terminal
            who (model.optimalPurePolicy who) depth node terminal,
          model.worstCasePotential_eq_obstacle_of_terminal
            who node terminal
        ]
      · obtain ⟨previous, node_rank⟩ :=
          model.rank_eq_succ_of_nonterminal node terminal
        have depth_eq : depth = previous + 1 := by
          omega
        subst depth
        rw [node_rank]
        rw [
          model.controlledPolicyValue_succ_of_nonterminal
            who (model.optimalPurePolicy who) previous node terminal,
          optimalPurePolicy,
          expect_pure
        ]
        calc
          expect
              (model.controlledKernel node who
                (model.optimalPureAction who node))
              (model.controlledPolicyValue who
                (model.optimalPurePolicy who) previous) =
            expect
              (model.controlledKernel node who
                (model.optimalPureAction who node))
              (model.worstCasePotential who) := by
                apply expect_congr_on_support
                intro next member
                have nonzero :
                    model.controlledKernel node who
                        (model.optimalPureAction who node) next ≠ 0 := by
                  simpa [PMF.mem_support_iff] using member
                have next_rank :=
                  model.controlled_step_rank node who
                    (model.optimalPureAction who node) next
                    terminal nonzero
                have next_rank_eq : model.rank next = previous := by
                  omega
                exact
                  ih previous (by omega) next next_rank_eq
          _ = model.worstCasePotential who node :=
            model.optimalPureAction_expect_eq_worstCasePotential
              who node terminal

omit [Finite Node] in
/-- Existence form of exact envelope attainment by a pure node policy. -/
theorem exists_purePolicyValue_eq_worstCasePotential
    (who : Player) (root : Node) :
    ∃ pure : Node → Action who,
      model.controlledPolicyValue who
          (fun node => PMF.pure (pure node))
          (model.rank root) root =
        model.worstCasePotential who root :=
  ⟨model.optimalPureAction who,
    model.optimalPurePolicyValue_eq_worstCasePotential who root⟩

end FiniteControlledStoppingModel
end Probability
end Math
