/-
Hostile finite-persuasion regression.

The false state emits a fair random signal while the true state emits `true`.
The receiver strictly follows either message.  A sender who always prefers the
true action therefore obtains `3/4`, strictly above the `1/2` delivered by full
information.  The witness exercises a non-point-mass kernel rather than merely
renaming deterministic states.
-/

import GameTheory.Mechanism.InformationDesign

noncomputable section

namespace GameTheory.Tests.InformationDesign

open Probability

def fairBool : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

def partialSignal : SignalStructure Bool Bool where
  kernel state := if state then FinDist.pure true else fairBool

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

theorem partialSignal_is_stochastic :
    (partialSignal.kernel false).prob false = 1 / 2 ∧
      (partialSignal.kernel false).prob true = 1 / 2 := by
  norm_num [partialSignal, fairBool, FinDist.prob_mix,
    FinDist.prob_pure_eq_ite]

theorem partialJoint_has_prior_marginal :
    (partialSignal.joint fairBool).map Prod.fst = fairBool :=
  partialSignal.map_fst_joint fairBool

theorem partialJoint_false_messages_are_nontrivial :
    (partialSignal.joint fairBool).prob (false, false) = 1 / 4 ∧
      (partialSignal.joint fairBool).prob (false, true) = 1 / 4 := by
  constructor <;>
    rw [SignalStructure.prob_joint] <;>
    norm_num [partialSignal, fairBool, FinDist.prob_mix,
      FinDist.prob_pure_eq_ite]

theorem receiver_scores_are_strict :
    partialProblem.receiverScore false false = 1 / 4 ∧
      partialProblem.receiverScore false true = 0 ∧
      partialProblem.receiverScore true false = 1 / 4 ∧
      partialProblem.receiverScore true true = 1 / 2 := by
  norm_num [PersuasionProblem.receiverScore, partialProblem, partialSignal,
    fairBool, FinDist.expect_mix, FinDist.prob_mix,
    FinDist.prob_pure_eq_ite]

theorem followMessage_isPersuasive :
    partialProblem.IsPersuasive followMessage := by
  intro message alternative
  cases message <;> cases alternative <;>
    norm_num [PersuasionProblem.IsReceiverOptimal,
      PersuasionProblem.receiverScore, followMessage, partialProblem,
      partialSignal, fairBool, FinDist.expect_mix, FinDist.prob_mix,
      FinDist.prob_pure_eq_ite]

theorem partial_senderEU :
    partialProblem.senderEU followMessage = 3 / 4 := by
  rw [PersuasionProblem.senderEU_eq_expect]
  norm_num [followMessage, partialProblem, partialSignal, fairBool,
    FinDist.expect_mix]

theorem fullInformation_senderEU :
    fullProblem.senderEU id = 1 / 2 := by
  rw [PersuasionProblem.senderEU_eq_expect]
  norm_num [fullProblem, fairBool, FinDist.expect_mix]

theorem partial_revelation_strictly_improves_sender_value :
    fullProblem.senderEU id < partialProblem.senderEU followMessage := by
  rw [fullInformation_senderEU, partial_senderEU]
  norm_num

/-- The generic finite optimizer theorem applies to the nontrivial persuasive
rule, without exporting a classical selector as executable code. -/
theorem optimal_persuasive_rule_exists :
    ∃ rule : partialProblem.DecisionRule,
      partialProblem.IsOptimalPersuasive rule :=
  PersuasionProblem.exists_optimalPersuasive partialProblem
    ⟨followMessage, followMessage_isPersuasive⟩

end GameTheory.Tests.InformationDesign
