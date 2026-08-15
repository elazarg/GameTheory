/-
# Finite information design

A signal structure is a finite-support Markov kernel from states to public
messages.  Its induced joint law is Bayes plausible by construction.  A
single-receiver persuasion problem then evaluates receiver obedience and
sender value directly through `FinDist`, without a second probability or
equilibrium layer.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uω um ua

/-- A public signal sampled conditionally on the realized state. -/
structure SignalStructure (State : Type uω) (Message : Type um) where
  kernel : State → FinDist Message

namespace SignalStructure

variable {State : Type uω} {Message : Type um}

/-- The joint state-message law induced by a prior and a signal structure. -/
def joint (S : SignalStructure State Message) (prior : FinDist State) :
    FinDist (State × Message) :=
  prior.bind fun state => (S.kernel state).map fun message => (state, message)

/-- The public-message marginal induced by a prior. -/
def messageMarginal (S : SignalStructure State Message) (prior : FinDist State) :
    FinDist Message :=
  (S.joint prior).map Prod.snd

/-- Every signal structure preserves the prior as the state marginal. -/
theorem map_fst_joint (S : SignalStructure State Message) (prior : FinDist State) :
    (S.joint prior).map Prod.fst = prior := by
  unfold joint
  rw [FinDist.map_bind]
  simp only [FinDist.map_comp, Function.comp_def, FinDist.map_const,
    FinDist.bind_pure]

/-- The message marginal is the prior mixture of the conditional kernels. -/
theorem messageMarginal_eq_bind
    (S : SignalStructure State Message) (prior : FinDist State) :
    S.messageMarginal prior = prior.bind S.kernel := by
  unfold messageMarginal joint
  rw [FinDist.map_bind]
  apply FinDist.bind_congr
  intro state _
  rw [FinDist.map_comp,
    show Prod.snd ∘ (fun message => (state, message)) = id from rfl,
    FinDist.map_id]

/-- The mass of a state-message pair factors into its prior and conditional
signal masses. -/
theorem prob_joint [DecidableEq State] [DecidableEq Message]
    (S : SignalStructure State Message) (prior : FinDist State)
    (state : State) (message : Message) :
    (S.joint prior).prob (state, message) =
      prior.prob state * (S.kernel state).prob message := by
  rw [joint, FinDist.prob_bind]
  rw [show
    (fun state' =>
      ((S.kernel state').map fun message' => (state', message')).prob
        (state, message)) =
      fun state' => if state = state' then (S.kernel state).prob message else 0 by
    funext state'
    by_cases hstate : state = state'
    · subst state'
      rw [if_pos rfl]
      exact FinDist.prob_map_of_injective
        (fun message' => (state, message'))
        (fun _ _ h => (Prod.mk.inj h).2) (S.kernel state) message
    · rw [if_neg hstate, FinDist.prob_map]
      calc
        (S.kernel state').expect
              (fun message' => if (state, message) = (state', message') then 1 else 0) =
            (S.kernel state').expect (fun _ => 0) := by
          apply FinDist.expect_congr
          intro message' _
          rw [if_neg fun hpair => hstate (congrArg Prod.fst hpair)]
        _ = 0 := FinDist.expect_const (S.kernel state') 0]
  exact FinDist.expect_ite_eq prior state ((S.kernel state).prob message)

/-- Finite-sum formula for the induced message marginal. -/
theorem prob_messageMarginal [Fintype State]
    (S : SignalStructure State Message) (prior : FinDist State)
    (message : Message) :
    (S.messageMarginal prior).prob message =
      ∑ state : State, prior.prob state * (S.kernel state).prob message := by
  rw [S.messageMarginal_eq_bind, FinDist.prob_bind, FinDist.expect_eq_sum]

/-- The uninformative signal with one public message. -/
def uninformative (State : Type uω) : SignalStructure State Unit where
  kernel _ := FinDist.pure ()

/-- The full-information signal that reports the realized state. -/
def fullInformation (State : Type uω) : SignalStructure State State where
  kernel state := FinDist.pure state

@[simp]
theorem uninformative_kernel (state : State) :
    (uninformative State).kernel state = FinDist.pure () :=
  rfl

@[simp]
theorem fullInformation_kernel (state : State) :
    (fullInformation State).kernel state = FinDist.pure state :=
  rfl

end SignalStructure

/-- Finite-support Bayesian persuasion primitives for a single receiver. -/
structure PersuasionProblem (State : Type uω) (Message : Type um) (Action : Type ua) where
  prior : FinDist State
  signal : SignalStructure State Message
  senderUtility : State → Action → ℝ
  receiverUtility : State → Action → ℝ

namespace PersuasionProblem

variable {State : Type uω} {Message : Type um} {Action : Type ua}

/-- The receiver's unnormalized expected payoff from choosing an action after
a message.  Zero-probability messages remain well-defined. -/
def receiverScore (P : PersuasionProblem State Message Action)
    (message : Message) (action : Action) : ℝ :=
  P.prior.expect fun state =>
    (P.signal.kernel state).prob message * P.receiverUtility state action

/-- The sender's unnormalized payoff contribution at a message. -/
def senderScore (P : PersuasionProblem State Message Action)
    (message : Message) (action : Action) : ℝ :=
  P.prior.expect fun state =>
    (P.signal.kernel state).prob message * P.senderUtility state action

/-- Receiver optimality after a public message. -/
def IsReceiverOptimal (P : PersuasionProblem State Message Action)
    (message : Message) (action : Action) : Prop :=
  ∀ alternative, P.receiverScore message alternative ≤
    P.receiverScore message action

/-- A public-message contingent receiver decision rule. -/
abbrev DecisionRule (_P : PersuasionProblem State Message Action) :=
  Message → Action

/-- A rule is persuasive when it is receiver-optimal according to the
unnormalized receiver score after every message.  At a zero-mass message all
such scores vanish, so the quantified condition is automatic there. -/
def IsPersuasive (P : PersuasionProblem State Message Action)
    (rule : P.DecisionRule) : Prop :=
  ∀ message, P.IsReceiverOptimal message (rule message)

/-- On a finite nonempty action space, receiver obedience is automatic to
make feasible: choose a receiver-score maximizer independently after each
message.  Message finiteness is not needed for this pointwise construction. -/
theorem exists_isPersuasive [Finite Action] [Nonempty Action]
    (P : PersuasionProblem State Message Action) :
    ∃ rule : P.DecisionRule, P.IsPersuasive rule := by
  let rule : P.DecisionRule := fun message =>
    Classical.choose
      (Finite.exists_max fun action : Action => P.receiverScore message action)
  refine ⟨rule, fun message alternative => ?_⟩
  simpa only [rule] using
    (Classical.choose_spec
      (Finite.exists_max fun action : Action => P.receiverScore message action)
      alternative)

/-- Sender expected utility under a decision rule. -/
def senderEU (P : PersuasionProblem State Message Action)
    (rule : P.DecisionRule) : ℝ :=
  (P.signal.joint P.prior).expect fun outcome =>
    P.senderUtility outcome.1 (rule outcome.2)

/-- Sender value as iterated finite-support expectation. -/
theorem senderEU_eq_expect (P : PersuasionProblem State Message Action)
    (rule : P.DecisionRule) :
    P.senderEU rule = P.prior.expect fun state =>
      (P.signal.kernel state).expect fun message =>
        P.senderUtility state (rule message) := by
  unfold senderEU SignalStructure.joint
  rw [FinDist.expect_bind]
  apply FinDist.expect_congr
  intro state _
  rw [FinDist.expect_map]

/-- Finite-sum expression for sender expected utility. -/
theorem senderEU_eq_sum [Fintype State] [Fintype Message]
    (P : PersuasionProblem State Message Action) (rule : P.DecisionRule) :
    P.senderEU rule =
      ∑ state : State, ∑ message : Message,
        (P.prior.prob state * (P.signal.kernel state).prob message) *
          P.senderUtility state (rule message) := by
  rw [P.senderEU_eq_expect, FinDist.expect_eq_sum]
  apply Finset.sum_congr rfl
  intro state _
  rw [FinDist.expect_eq_sum]
  rw [Finset.mul_sum]
  simp only [mul_assoc]

/-- Sender value is the sum of its message-contingent scores. -/
theorem senderEU_eq_sum_senderScore [Fintype State] [Fintype Message]
    (P : PersuasionProblem State Message Action) (rule : P.DecisionRule) :
    P.senderEU rule = ∑ message : Message, P.senderScore message (rule message) := by
  rw [P.senderEU_eq_sum]
  unfold senderScore
  simp_rw [FinDist.expect_eq_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- Sender optimality among persuasive rules. -/
def IsOptimalPersuasive (P : PersuasionProblem State Message Action)
    (rule : P.DecisionRule) : Prop :=
  P.IsPersuasive rule ∧
    ∀ alternative, P.IsPersuasive alternative →
      P.senderEU alternative ≤ P.senderEU rule

/-- A sender-optimal persuasive rule exists on finite message and action
spaces whenever persuasion is feasible.  This is proof-level existence, not an
executable selector. -/
theorem exists_optimalPersuasive [Finite Message] [Finite Action]
    (P : PersuasionProblem State Message Action)
    (hfeasible : ∃ rule : P.DecisionRule, P.IsPersuasive rule) :
    ∃ rule : P.DecisionRule, P.IsOptimalPersuasive rule := by
  let FeasibleRule := {rule : P.DecisionRule // P.IsPersuasive rule}
  letI : Nonempty FeasibleRule :=
    ⟨⟨Classical.choose hfeasible, Classical.choose_spec hfeasible⟩⟩
  obtain ⟨best, hbest⟩ :=
    Finite.exists_max fun rule : FeasibleRule => P.senderEU rule.1
  exact ⟨best.1, best.2, fun alternative halternative =>
    hbest ⟨alternative, halternative⟩⟩

/-- A sender-optimal persuasive rule therefore exists on finite message and
nonempty finite action spaces without a separate feasibility premise. -/
theorem exists_optimalPersuasive_of_nonempty [Finite Message] [Finite Action]
    [Nonempty Action] (P : PersuasionProblem State Message Action) :
    ∃ rule : P.DecisionRule, P.IsOptimalPersuasive rule :=
  P.exists_optimalPersuasive P.exists_isPersuasive

end PersuasionProblem

end GameTheory
