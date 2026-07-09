/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.Bayesian.BayesianGame
import Math.Probability

/-!
# Finite Information Design

Finite signal structures and persuasion-style design predicates.  The file is
deliberately finite and PMF-based: it gives a reusable substrate for Bayesian
persuasion and finite-grid information-design examples without invoking
measure-theoretic type spaces.

## Main definitions

* `SignalStructure` — a Markov kernel from states to public messages
* `SignalStructure.joint` — the induced joint law over states and messages
* `HasPriorMarginal` — a joint state-message law whose state marginal is the prior
  (the information-design form of Bayes plausibility)
* `PersuasionProblem` — finite sender/receiver persuasion primitives
* `PersuasionProblem.IsPersuasive` — message-contingent receiver optimality

## Main results

* `joint_hasPriorMarginal` — every signal structure's joint law has the prior as state marginal
* `SignalStructure.messageMarginal_apply` — finite-sum form of message marginals
* `PersuasionProblem.senderEU_eq_sum` — finite-sum form of sender value
* `PersuasionProblem.senderEU_eq_sum_senderScore` — sender value as a sum of scores
-/

namespace GameTheory

open Math.Probability

/-- A signal structure: after state `ω` is drawn, a public message is
sampled from `kernel ω`. -/
structure SignalStructure (Ω Msg : Type) where
  kernel : Ω → PMF Msg

namespace SignalStructure

variable {Ω Msg : Type}

/-- The joint distribution over states and messages induced by a prior and a
signal structure. -/
noncomputable def joint (S : SignalStructure Ω Msg) (prior : PMF Ω) : PMF (Ω × Msg) :=
  prior.bind fun ω => (S.kernel ω).map fun m => (ω, m)

/-- The induced marginal distribution of public messages. -/
noncomputable def messageMarginal (S : SignalStructure Ω Msg) (prior : PMF Ω) : PMF Msg :=
  (S.joint prior).map Prod.snd

/-- A joint state-message law **has the prior as its state marginal**: the
information-design form of Bayes plausibility (cf. `FeasiblePosteriors.IsBayesPlausible`,
the posterior-law/mean form, and `BayesCorrelatedEq.BayesPlausible`, the
recommendation-law form). -/
def HasPriorMarginal (prior : PMF Ω) (ν : PMF (Ω × Msg)) : Prop :=
  ν.map Prod.fst = prior

/-- Every signal structure induces a joint law with the prior as its state marginal. -/
theorem joint_hasPriorMarginal (S : SignalStructure Ω Msg) (prior : PMF Ω) :
    HasPriorMarginal prior (S.joint prior) := by
  unfold HasPriorMarginal joint
  rw [PMF.map_bind]
  conv_lhs =>
    enter [2, ω]
    rw [PMF.map_comp]
    change (S.kernel ω).map (Function.const Msg ω)
    rw [PMF.map_const]
  rw [PMF.bind_pure]

/-- The uninformative signal structure with a single public message. -/
noncomputable def uninformative (Ω : Type) : SignalStructure Ω Unit where
  kernel := fun _ => PMF.pure ()

/-- The full-information signal structure that reports the realized state. -/
noncomputable def fullInformation (Ω : Type) : SignalStructure Ω Ω where
  kernel := fun ω => PMF.pure ω

@[simp] theorem uninformative_kernel (ω : Ω) :
    (uninformative Ω).kernel ω = PMF.pure () := rfl

@[simp] theorem fullInformation_kernel (ω : Ω) :
    (fullInformation Ω).kernel ω = PMF.pure ω := rfl

/-- Pointwise formula for the induced joint law. -/
theorem joint_apply (S : SignalStructure Ω Msg) (prior : PMF Ω)
    (ω : Ω) (m : Msg) :
    S.joint prior (ω, m) = prior ω * S.kernel ω m := by
  classical
  unfold joint
  rw [PMF.bind_apply]
  rw [tsum_eq_single ω]
  · have hdiag :
        (S.kernel ω).map (fun m' => (ω, m')) (ω, m) = S.kernel ω m := by
      rw [PMF.map_apply]
      rw [tsum_eq_single m]
      · simp
      · intro m' hm'
        split_ifs with hpair
        · cases hpair
          exact (hm' rfl).elim
        · rfl
    rw [hdiag]
  · intro ω' hω'
    have hmap : (S.kernel ω').map (fun m' => (ω', m')) (ω, m) = 0 := by
      rw [PMF.map_apply]
      refine ENNReal.tsum_eq_zero.2 ?_
      intro m'
      split_ifs with hpair
      · cases hpair
        exact (hω' rfl).elim
      · rfl
    rw [hmap, mul_zero]

/-- Finite-sum formula for the induced message marginal. -/
theorem messageMarginal_apply [Fintype Ω] [Finite Msg]
    (S : SignalStructure Ω Msg) (prior : PMF Ω) (m : Msg) :
    S.messageMarginal prior m = ∑ ω : Ω, prior ω * S.kernel ω m := by
  classical
  letI : Fintype Msg := Fintype.ofFinite Msg
  unfold messageMarginal
  rw [PMF.map_apply, tsum_fintype]
  simp [SignalStructure.joint_apply, Fintype.sum_prod_type]

end SignalStructure

/-- A finite Bayesian-persuasion problem with a single receiver.  A signal
structure is fixed; design problems can optimize over this field externally. -/
structure PersuasionProblem (Ω Msg Act : Type) where
  prior : PMF Ω
  signal : SignalStructure Ω Msg
  senderUtility : Ω → Act → ℝ
  receiverUtility : Ω → Act → ℝ

namespace PersuasionProblem

variable {Ω Msg Act : Type} [Fintype Ω] [Fintype Msg]

/-- Message-contingent receiver objective, written without normalizing by the
message probability.  This is equivalent to posterior expected utility when the
message has positive probability, and remains well-defined at zero-probability
messages. -/
noncomputable def receiverScore (P : PersuasionProblem Ω Msg Act) (m : Msg) (a : Act) : ℝ :=
  ∑ ω : Ω, ((P.prior ω).toReal * (P.signal.kernel ω m).toReal) * P.receiverUtility ω a

/-- Message-contingent sender objective under the same unnormalized weights. -/
noncomputable def senderScore (P : PersuasionProblem Ω Msg Act) (m : Msg) (a : Act) : ℝ :=
  ∑ ω : Ω, ((P.prior ω).toReal * (P.signal.kernel ω m).toReal) * P.senderUtility ω a

/-- Receiver optimality after message `m`. -/
def IsReceiverOptimal (P : PersuasionProblem Ω Msg Act) (m : Msg) (a : Act) : Prop :=
  ∀ a' : Act, P.receiverScore m a ≥ P.receiverScore m a'

/-- A decision rule maps each public message to the receiver action it induces. -/
abbrev DecisionRule (_P : PersuasionProblem Ω Msg Act) := Msg → Act

/-- A decision rule is persuasive when every recommended action is receiver
optimal at the message that recommends it. -/
def IsPersuasive (P : PersuasionProblem Ω Msg Act) (r : P.DecisionRule) : Prop :=
  ∀ m : Msg, P.IsReceiverOptimal m (r m)

/-- Sender expected utility from a decision rule. -/
noncomputable def senderEU (P : PersuasionProblem Ω Msg Act) (r : P.DecisionRule) : ℝ :=
  expect (P.signal.joint P.prior) fun p : Ω × Msg => P.senderUtility p.1 (r p.2)

/-- Finite-sum expression for sender expected utility. -/
theorem senderEU_eq_sum (P : PersuasionProblem Ω Msg Act) (r : P.DecisionRule) :
    P.senderEU r =
      ∑ ω : Ω, ∑ m : Msg,
        ((P.prior ω).toReal * (P.signal.kernel ω m).toReal) *
          P.senderUtility ω (r m) := by
  classical
  unfold senderEU
  rw [expect_eq_sum]
  calc
    ∑ p : Ω × Msg,
        ((P.signal.joint P.prior p).toReal) * P.senderUtility p.1 (r p.2)
        = ∑ p : Ω × Msg,
            ((P.prior p.1 * P.signal.kernel p.1 p.2).toReal) *
              P.senderUtility p.1 (r p.2) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [SignalStructure.joint_apply]
    _ = ∑ p : Ω × Msg,
          (((P.prior p.1).toReal * (P.signal.kernel p.1 p.2).toReal)) *
            P.senderUtility p.1 (r p.2) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [ENNReal.toReal_mul]
    _ = ∑ ω : Ω, ∑ m : Msg,
        ((P.prior ω).toReal * (P.signal.kernel ω m).toReal) *
          P.senderUtility ω (r m) := by
          simpa using
            (Fintype.sum_prod_type fun p : Ω × Msg =>
              ((P.prior p.1).toReal * (P.signal.kernel p.1 p.2).toReal) *
                P.senderUtility p.1 (r p.2))

/-- Sender value as the sum of message-contingent sender scores. -/
theorem senderEU_eq_sum_senderScore
    (P : PersuasionProblem Ω Msg Act) (r : P.DecisionRule) :
    P.senderEU r = ∑ m : Msg, P.senderScore m (r m) := by
  classical
  rw [senderEU_eq_sum]
  unfold senderScore
  exact Finset.sum_comm

/-- Among persuasive decision rules, `r` is sender-optimal if it maximizes
sender expected utility. -/
def IsOptimalPersuasive (P : PersuasionProblem Ω Msg Act) (r : P.DecisionRule) : Prop :=
  P.IsPersuasive r ∧ ∀ r' : P.DecisionRule, P.IsPersuasive r' → P.senderEU r ≥ P.senderEU r'

end PersuasionProblem

end GameTheory
