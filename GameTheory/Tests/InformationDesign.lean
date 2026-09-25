/-
Hostile finite-persuasion regression.

The false state emits a fair random signal while the true state emits `true`.
The receiver strictly follows either message.  A sender who always prefers the
true action therefore obtains `3/4`, strictly above the `1/2` delivered by full
information.  The witness exercises a non-point-mass kernel rather than merely
renaming deterministic states.
-/

import GameTheory.Mechanism.InformationDesign
import GameTheory.Math.Probability.Uniform

noncomputable section

namespace GameTheory.Tests.InformationDesign

open GameTheory.Math.Probability

def fairBool : PMF Bool := PMF.uniformOfFintype Bool

def partialSignal : SignalStructure Bool Bool where
  kernel state := if state then PMF.pure true else fairBool

def partialProblem : PersuasionProblem Bool Bool Bool where
  prior := fairBool
  signal := partialSignal
  senderUtility _ action := if action then 1 else 0
  receiverUtility state action := if action = state then 1 else 0

def fullProblem : PersuasionProblem Bool Bool Bool where
  prior := fairBool
  signal := SignalStructure.fullInformation Bool
  senderUtility _ action := if action then 1 else 0
  receiverUtility state action := if action = state then 1 else 0

def followMessage : partialProblem.DecisionRule := id

/-- Finite prior support integrates every receiver-weighted fixture payoff. -/
theorem receiverGuard (message action : Bool) :
    PayoffIntegrable partialProblem.prior
      (partialProblem.receiverWeighted message action) :=
  payoffIntegrable_of_finite _ _

/-- Finite joint support integrates every sender payoff for a decision rule. -/
theorem senderGuard (P : PersuasionProblem Bool Bool Bool)
    (rule : P.DecisionRule) :
    PayoffIntegrable (P.signal.joint P.prior)
      (fun outcome => P.senderUtility outcome.1 (rule outcome.2)) :=
  payoffIntegrable_of_finite _ _

theorem partialSignal_is_stochastic :
    (partialSignal.kernel false) false = 1 / 2 ∧
      (partialSignal.kernel false) true = 1 / 2 := by
  norm_num [partialSignal, fairBool, PMF.uniformOfFintype_apply]

theorem partialJoint_has_prior_marginal :
    (partialSignal.joint fairBool).map Prod.fst = fairBool :=
  partialSignal.map_fst_joint fairBool

theorem partialJoint_false_messages_are_nontrivial :
    (partialSignal.joint fairBool) (false, false) = 1 / 4 ∧
      (partialSignal.joint fairBool) (false, true) = 1 / 4 := by
  constructor <;>
    rw [SignalStructure.joint_apply] <;>
    norm_num [partialSignal, fairBool, PMF.uniformOfFintype_apply,
      ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)] <;>
    rw [← ENNReal.mul_inv (a := 2) (b := 2)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))] <;> norm_num

theorem receiver_scores_are_strict :
    partialProblem.receiverScore false false (receiverGuard false false) = 1 / 4 ∧
      partialProblem.receiverScore false true (receiverGuard false true) = 0 ∧
      partialProblem.receiverScore true false (receiverGuard true false) = 1 / 4 ∧
      partialProblem.receiverScore true true (receiverGuard true true) = 1 / 2 := by
  norm_num [PersuasionProblem.receiverScore, expect_eq_sum,
    PersuasionProblem.receiverWeighted, partialProblem, partialSignal,
    fairBool, Fintype.sum_bool, PMF.uniformOfFintype_apply,
    PMF.pure_apply]

theorem followMessage_isPersuasive :
    partialProblem.IsPersuasive followMessage := by
  intro message
  refine ⟨receiverGuard message, ?_⟩
  intro alternative
  rcases receiver_scores_are_strict with ⟨hff, hft, htf, htt⟩
  cases message <;> cases alternative <;>
    norm_num [followMessage, hff, hft, htf, htt]

theorem partial_senderEU :
    partialProblem.senderEU followMessage
      (senderGuard partialProblem followMessage) = 3 / 4 := by
  rw [PersuasionProblem.senderEU_eq_sum]
  norm_num [followMessage, partialProblem, partialSignal, fairBool,
    Fintype.sum_bool, PMF.uniformOfFintype_apply, PMF.pure_apply]

theorem fullInformation_senderEU :
    fullProblem.senderEU id (senderGuard fullProblem id) = 1 / 2 := by
  rw [PersuasionProblem.senderEU_eq_sum]
  norm_num [fullProblem, fairBool, Fintype.sum_bool,
    PMF.uniformOfFintype_apply, PMF.pure_apply]

theorem partial_revelation_strictly_improves_sender_value :
    fullProblem.senderEU id (senderGuard fullProblem id) <
      partialProblem.senderEU followMessage
        (senderGuard partialProblem followMessage) := by
  rw [fullInformation_senderEU, partial_senderEU]
  norm_num

/-- The generic finite optimizer theorem applies to the nontrivial persuasive
rule, without exporting a classical selector as executable code. -/
theorem optimal_persuasive_rule_exists :
    ∃ rule : partialProblem.DecisionRule,
      partialProblem.IsOptimalPersuasive rule :=
  PersuasionProblem.exists_optimalPersuasive partialProblem
    ⟨followMessage, followMessage_isPersuasive⟩
    (fun rule _ => senderGuard partialProblem rule)

end GameTheory.Tests.InformationDesign
