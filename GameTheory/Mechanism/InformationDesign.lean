/-
# Information design over ordinary PMFs

A signal is a Markov kernel from states to public messages. Receiver scores
integrate the actual message-weighted state payoff, so a null message has zero
score even when an unweighted payoff is not integrable.
-/

import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.Joint

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uω um ua

/-- A public signal sampled conditionally on the realized state. -/
structure SignalStructure (State : Type uω) (Message : Type um) where
  /-- Conditional message law at each true state. -/
  kernel : State → PMF Message

namespace SignalStructure

variable {State : Type uω} {Message : Type um}

/-- Joint state-message law. -/
def joint (S : SignalStructure State Message) (prior : PMF State) :
    PMF (State × Message) :=
  bindPairLaw prior S.kernel

/-- Public-message marginal. -/
def messageMarginal (S : SignalStructure State Message) (prior : PMF State) :
    PMF Message :=
  (S.joint prior).map Prod.snd

theorem map_fst_joint (S : SignalStructure State Message) (prior : PMF State) :
    (S.joint prior).map Prod.fst = prior :=
  bindPairLaw_map_fst prior S.kernel

theorem messageMarginal_eq_bind
    (S : SignalStructure State Message) (prior : PMF State) :
    S.messageMarginal prior = prior.bind S.kernel :=
  bindPairLaw_map_snd prior S.kernel

/-- Native mass of a state-message pair. -/
theorem joint_apply (S : SignalStructure State Message) (prior : PMF State)
    (state : State) (message : Message) :
    S.joint prior (state, message) =
      prior state * S.kernel state message :=
  bindPairLaw_apply prior S.kernel state message

/-- Native message mass is the sum of all state contributions. -/
theorem messageMarginal_apply
    (S : SignalStructure State Message) (prior : PMF State)
    (message : Message) :
    S.messageMarginal prior message =
      ∑' state, prior state * S.kernel state message := by
  rw [S.messageMarginal_eq_bind, PMF.bind_apply]

/-- A signal with one public message. -/
def uninformative (State : Type uω) : SignalStructure State Unit where
  kernel _ := PMF.pure ()

/-- A signal that announces the state. -/
def fullInformation (State : Type uω) : SignalStructure State State where
  kernel state := PMF.pure state

@[simp]
theorem uninformative_kernel (state : State) :
    (uninformative State).kernel state = PMF.pure () :=
  rfl

@[simp]
theorem fullInformation_kernel (state : State) :
    (fullInformation State).kernel state = PMF.pure state :=
  rfl

end SignalStructure

/-- Bayesian persuasion primitives for a single receiver. -/
structure PersuasionProblem (State : Type uω) (Message : Type um)
    (Action : Type ua) where
  /-- Prior distribution of the true state. -/
  prior : PMF State
  /-- Public message experiment observed by the receiver. -/
  signal : SignalStructure State Message
  /-- Sender payoff from the true state and the receiver's action. -/
  senderUtility : State → Action → ℝ
  /-- Receiver payoff from the true state and its chosen action. -/
  receiverUtility : State → Action → ℝ

namespace PersuasionProblem

variable {State : Type uω} {Message : Type um} {Action : Type ua}

/-- The actual receiver payoff weighted by the likelihood of a message. -/
def receiverWeighted (P : PersuasionProblem State Message Action)
    (message : Message) (action : Action) : State → ℝ :=
  fun state =>
    (P.signal.kernel state message).toReal * P.receiverUtility state action

/-- The analogous sender payoff at a message. -/
def senderWeighted (P : PersuasionProblem State Message Action)
    (message : Message) (action : Action) : State → ℝ :=
  fun state =>
    (P.signal.kernel state message).toReal * P.senderUtility state action

/-- Unnormalized receiver value at a message. -/
def receiverScore (P : PersuasionProblem State Message Action)
    (message : Message) (action : Action)
    (hscore : PayoffIntegrable P.prior (P.receiverWeighted message action)) : ℝ :=
  expect P.prior (P.receiverWeighted message action) hscore

/-- Unnormalized sender contribution at a message. -/
def senderScore (P : PersuasionProblem State Message Action)
    (message : Message) (action : Action)
    (hscore : PayoffIntegrable P.prior (P.senderWeighted message action)) : ℝ :=
  expect P.prior (P.senderWeighted message action) hscore

/-- A null message has zero weighted payoff on every reached state. -/
private theorem weighted_zero_of_null
    (P : PersuasionProblem State Message Action) (message : Message)
    (hnull : P.signal.messageMarginal P.prior message = 0)
    (value : State → ℝ) :
    ∀ state ∈ P.prior.support,
      (P.signal.kernel state message).toReal * value state = 0 := by
  intro state hs
  have hsum := P.signal.messageMarginal_apply P.prior message
  rw [hsum] at hnull
  have hterm : P.prior state * P.signal.kernel state message = 0 :=
    (ENNReal.tsum_eq_zero.mp hnull) state
  have hprior : P.prior state ≠ 0 := (P.prior.mem_support_iff state).mp hs
  have hkernel : P.signal.kernel state message = 0 :=
    (mul_eq_zero.mp hterm).resolve_left hprior
  simp [hkernel]

/-- A null message has a defined zero receiver score even when the receiver's
unweighted payoff under the prior is not integrable. -/
theorem receiverScore_null
    (P : PersuasionProblem State Message Action)
    (message : Message) (action : Action)
    (hnull : P.signal.messageMarginal P.prior message = 0) :
    ∃ hscore : PayoffIntegrable P.prior (P.receiverWeighted message action),
      P.receiverScore message action hscore = 0 := by
  have hzero : ∀ state ∈ P.prior.support,
      P.receiverWeighted message action state = 0 :=
    P.weighted_zero_of_null message hnull
      (fun state => P.receiverUtility state action)
  have hscore : PayoffIntegrable P.prior (P.receiverWeighted message action) :=
    payoffIntegrable_congr_on_support
      (fun state hs => (hzero state hs).symm)
      (payoffIntegrable_zero P.prior)
  refine ⟨hscore, ?_⟩
  unfold receiverScore
  calc
    expect P.prior (P.receiverWeighted message action) hscore =
        expect P.prior (fun _ => 0) (payoffIntegrable_zero P.prior) :=
      expect_congr_on_support hzero hscore (payoffIntegrable_zero P.prior)
    _ = 0 := expect_zero _ _

/-- The sender's contribution at a null message is also defined and zero. -/
theorem senderScore_null
    (P : PersuasionProblem State Message Action)
    (message : Message) (action : Action)
    (hnull : P.signal.messageMarginal P.prior message = 0) :
    ∃ hscore : PayoffIntegrable P.prior (P.senderWeighted message action),
      P.senderScore message action hscore = 0 := by
  have hzero : ∀ state ∈ P.prior.support,
      P.senderWeighted message action state = 0 :=
    P.weighted_zero_of_null message hnull
      (fun state => P.senderUtility state action)
  have hscore : PayoffIntegrable P.prior (P.senderWeighted message action) :=
    payoffIntegrable_congr_on_support
      (fun state hs => (hzero state hs).symm)
      (payoffIntegrable_zero P.prior)
  refine ⟨hscore, ?_⟩
  unfold senderScore
  calc
    expect P.prior (P.senderWeighted message action) hscore =
        expect P.prior (fun _ => 0) (payoffIntegrable_zero P.prior) :=
      expect_congr_on_support hzero hscore (payoffIntegrable_zero P.prior)
    _ = 0 := expect_zero _ _

/-- An optimal receiver action requires defined scores for every alternative.
Undefined alternatives are not silently removed from the comparison. -/
def IsReceiverOptimal (P : PersuasionProblem State Message Action)
    (message : Message) (action : Action) : Prop :=
  ∃ hscore : ∀ alternative,
      PayoffIntegrable P.prior (P.receiverWeighted message alternative),
    ∀ alternative,
      P.receiverScore message alternative (hscore alternative) ≤
        P.receiverScore message action (hscore action)

/-- Receiver obedience is automatic at a null message. -/
theorem isReceiverOptimal_null (P : PersuasionProblem State Message Action)
    (message : Message) (action : Action)
    (hnull : P.signal.messageMarginal P.prior message = 0) :
    P.IsReceiverOptimal message action := by
  let hscore : ∀ alternative,
      PayoffIntegrable P.prior (P.receiverWeighted message alternative) :=
    fun alternative => (P.receiverScore_null message alternative hnull).choose
  refine ⟨hscore, ?_⟩
  intro alternative
  have hfirst := (P.receiverScore_null message alternative hnull).choose_spec
  have hsecond := (P.receiverScore_null message action hnull).choose_spec
  simpa only [hfirst, hsecond] using (le_refl (0 : ℝ))

/-- A public-message contingent receiver decision rule. -/
abbrev DecisionRule (_P : PersuasionProblem State Message Action) :=
  Message → Action

/-- Receiver obedience at every message. -/
def IsPersuasive (P : PersuasionProblem State Message Action)
    (rule : P.DecisionRule) : Prop :=
  ∀ message, P.IsReceiverOptimal message (rule message)

/-- A score maximizer gives a persuasive rule on finite nonempty action
spaces, provided every actual message-weighted comparison is integrable. -/
theorem exists_isPersuasive [Finite Action] [Nonempty Action]
    (P : PersuasionProblem State Message Action)
    (hscore : ∀ message alternative,
      PayoffIntegrable P.prior (P.receiverWeighted message alternative)) :
    ∃ rule : P.DecisionRule, P.IsPersuasive rule := by
  let rule : P.DecisionRule := fun message =>
    Classical.choose
      (Finite.exists_max fun action : Action =>
        P.receiverScore message action (hscore message action))
  refine ⟨rule, fun message => ⟨hscore message, ?_⟩⟩
  intro alternative
  simpa only [rule] using
    (Classical.choose_spec
      (Finite.exists_max fun action : Action =>
        P.receiverScore message action (hscore message action))
      alternative)

/-- The sender payoff under the actual joint state-message law. -/
def senderEU (P : PersuasionProblem State Message Action)
    (rule : P.DecisionRule)
    (hactual : PayoffIntegrable (P.signal.joint P.prior)
      (fun outcome => P.senderUtility outcome.1 (rule outcome.2))) : ℝ :=
  expect (P.signal.joint P.prior)
    (fun outcome => P.senderUtility outcome.1 (rule outcome.2)) hactual

/-- An actual joint-law guard supplies conditional integration at every
reached state. -/
theorem senderConditionalIntegrable
    (P : PersuasionProblem State Message Action) (rule : P.DecisionRule)
    (hactual : PayoffIntegrable (P.signal.joint P.prior)
      (fun outcome => P.senderUtility outcome.1 (rule outcome.2)))
    (state : State) (hs : state ∈ P.prior.support) :
    PayoffIntegrable (P.signal.kernel state)
      (fun message => P.senderUtility state (rule message)) := by
  have hmap := payoffIntegrable_bind_conditional_on_support P.prior
    (fun state => (P.signal.kernel state).map (state, ·))
    (fun outcome => P.senderUtility outcome.1 (rule outcome.2))
    hactual state hs
  exact (payoffIntegrable_map_iff (fun message => (state, message))
    (P.signal.kernel state)
    (fun outcome => P.senderUtility outcome.1 (rule outcome.2))).mp hmap

/-- The supported conditional sender values are integrable under the prior. -/
theorem senderOuterIntegrable
    (P : PersuasionProblem State Message Action) (rule : P.DecisionRule)
    (hactual : PayoffIntegrable (P.signal.joint P.prior)
      (fun outcome => P.senderUtility outcome.1 (rule outcome.2))) :
    PayoffIntegrable P.prior (extendFromSupport P.prior
      (fun state hs =>
        expect (P.signal.kernel state)
          (fun message => P.senderUtility state (rule message))
          (P.senderConditionalIntegrable rule hactual state hs))) := by
  let kernel : State → PMF (State × Message) :=
    fun state => (P.signal.kernel state).map (state, ·)
  let payoff : State × Message → ℝ :=
    fun outcome => P.senderUtility outcome.1 (rule outcome.2)
  have hcond (state : State) (hs : state ∈ P.prior.support) :
      expect (P.signal.kernel state)
          (fun message => P.senderUtility state (rule message))
          (P.senderConditionalIntegrable rule hactual state hs) =
        expect (kernel state) payoff
          (payoffIntegrable_bind_conditional_on_support
            P.prior kernel payoff hactual state hs) := by
    exact (expect_map (fun message => (state, message))
      (P.signal.kernel state) payoff
      (P.senderConditionalIntegrable rule hactual state hs) _).symm
  apply payoffIntegrable_bind_conditionalValue_on_support
    P.prior kernel payoff hactual
  intro state hs
  simp only [extendFromSupport, dite_eq_left hs]
  exact hcond state hs

/-- Iterated sender expectation, using only the actual joint-law guard. -/
theorem senderEU_eq_expect
    (P : PersuasionProblem State Message Action) (rule : P.DecisionRule)
    (hactual : PayoffIntegrable (P.signal.joint P.prior)
      (fun outcome => P.senderUtility outcome.1 (rule outcome.2))) :
    P.senderEU rule hactual =
      expect P.prior (extendFromSupport P.prior
        (fun state hs =>
          expect (P.signal.kernel state)
            (fun message => P.senderUtility state (rule message))
            (P.senderConditionalIntegrable rule hactual state hs)))
        (P.senderOuterIntegrable rule hactual) := by
  let kernel : State → PMF (State × Message) :=
    fun state => (P.signal.kernel state).map (state, ·)
  let payoff : State × Message → ℝ :=
    fun outcome => P.senderUtility outcome.1 (rule outcome.2)
  unfold senderEU
  apply expect_bind_tower_on_support P.prior kernel payoff hactual
  intro state hs
  simp only [extendFromSupport, dite_eq_left hs]
  exact (expect_map (fun message => (state, message))
    (P.signal.kernel state) payoff
    (P.senderConditionalIntegrable rule hactual state hs) _).symm

/-- Finite-state and finite-message sender payoff formula. -/
theorem senderEU_eq_sum [Fintype State] [Fintype Message]
    (P : PersuasionProblem State Message Action) (rule : P.DecisionRule)
    (hactual : PayoffIntegrable (P.signal.joint P.prior)
      (fun outcome => P.senderUtility outcome.1 (rule outcome.2))) :
    P.senderEU rule hactual =
      ∑ state : State, ∑ message : Message,
        ((P.prior state).toReal * (P.signal.kernel state message).toReal) *
          P.senderUtility state (rule message) := by
  unfold senderEU
  rw [expect_eq_sum]
  simp only [Fintype.sum_prod_type, SignalStructure.joint, bindPairLaw_apply,
    ENNReal.toReal_mul, mul_assoc]

/-- A defined joint sender payoff supplies each actual message-weighted score. -/
theorem senderScore_integrable_of_senderEU
    (P : PersuasionProblem State Message Action) (rule : P.DecisionRule)
    (hactual : PayoffIntegrable (P.signal.joint P.prior)
      (fun outcome => P.senderUtility outcome.1 (rule outcome.2)))
    (message : Message) :
    PayoffIntegrable P.prior (P.senderWeighted message (rule message)) := by
  have hslice : Summable (fun state : State =>
      ((P.signal.joint P.prior) (state, message)).toReal *
        |P.senderUtility state (rule message)|) := by
    simpa only [PayoffIntegrable, Function.comp_def] using
      (hactual.comp_injective (i := fun state : State => (state, message))
        (fun state₁ state₂ heq => congrArg Prod.fst heq))
  simpa only [PayoffIntegrable, SignalStructure.joint_apply,
    ENNReal.toReal_mul, senderWeighted, abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg, mul_assoc] using hslice

/-- Sender value is the sum of its message-contingent scores, even for an
infinite state space. -/
theorem senderEU_eq_sum_senderScore [Fintype Message]
    (P : PersuasionProblem State Message Action) (rule : P.DecisionRule)
    (hactual : PayoffIntegrable (P.signal.joint P.prior)
      (fun outcome => P.senderUtility outcome.1 (rule outcome.2))) :
    P.senderEU rule hactual =
      ∑ message : Message, P.senderScore message (rule message)
        (P.senderScore_integrable_of_senderEU rule hactual message) := by
  let term : Message → State → ℝ := fun message state =>
    ((P.signal.joint P.prior) (state, message)).toReal *
      P.senderUtility state (rule message)
  have hterm (message : Message) : Summable (term message) := by
    have hscore := P.senderScore_integrable_of_senderEU rule hactual message
    simpa only [term, PayoffIntegrable, SignalStructure.joint_apply,
      ENNReal.toReal_mul, senderWeighted, mul_assoc] using hscore.summable
  unfold senderEU senderScore expect
  rw [Summable.tsum_prod hactual.summable]
  simp only [tsum_fintype]
  rw [Summable.tsum_finsetSum (s := Finset.univ)
    (f := term) (fun message _ => hterm message)]
  apply Finset.sum_congr rfl
  intro message _
  apply tsum_congr
  intro state
  simp only [term, SignalStructure.joint_apply, ENNReal.toReal_mul,
    senderWeighted, mul_assoc]

/-- Sender optimality requires a defined value for every persuasive
alternative, including alternatives with otherwise divergent outcomes. -/
def IsOptimalPersuasive (P : PersuasionProblem State Message Action)
    (rule : P.DecisionRule) : Prop :=
  P.IsPersuasive rule ∧
    ∃ hactual : PayoffIntegrable (P.signal.joint P.prior)
        (fun outcome => P.senderUtility outcome.1 (rule outcome.2)),
      ∀ alternative, P.IsPersuasive alternative →
        ∃ halt : PayoffIntegrable (P.signal.joint P.prior)
            (fun outcome => P.senderUtility outcome.1 (alternative outcome.2)),
          P.senderEU alternative halt ≤ P.senderEU rule hactual

/-- Existence requires actual-law integration throughout the feasible family
being compared. -/
theorem exists_optimalPersuasive [Finite Message] [Finite Action]
    (P : PersuasionProblem State Message Action)
    (hfeasible : ∃ rule : P.DecisionRule, P.IsPersuasive rule)
    (hall : ∀ rule : P.DecisionRule, P.IsPersuasive rule →
      PayoffIntegrable (P.signal.joint P.prior)
        (fun outcome => P.senderUtility outcome.1 (rule outcome.2))) :
    ∃ rule : P.DecisionRule, P.IsOptimalPersuasive rule := by
  let FeasibleRule := {rule : P.DecisionRule // P.IsPersuasive rule}
  let : Nonempty FeasibleRule :=
    ⟨⟨Classical.choose hfeasible, Classical.choose_spec hfeasible⟩⟩
  obtain ⟨best, hbest⟩ :=
    Finite.exists_max fun candidate : FeasibleRule =>
      P.senderEU candidate.1 (hall candidate.1 candidate.2)
  exact ⟨best.1, best.2, hall best.1 best.2,
    fun alternative halternative =>
      ⟨hall alternative halternative, hbest ⟨alternative, halternative⟩⟩⟩

theorem exists_optimalPersuasive_of_nonempty [Finite Message] [Finite Action]
    [Nonempty Action] (P : PersuasionProblem State Message Action)
    (hscore : ∀ message alternative,
      PayoffIntegrable P.prior (P.receiverWeighted message alternative))
    (hall : ∀ rule : P.DecisionRule, P.IsPersuasive rule →
      PayoffIntegrable (P.signal.joint P.prior)
        (fun outcome => P.senderUtility outcome.1 (rule outcome.2))) :
    ∃ rule : P.DecisionRule, P.IsOptimalPersuasive rule :=
  P.exists_optimalPersuasive (P.exists_isPersuasive hscore) hall

end PersuasionProblem

end GameTheory
