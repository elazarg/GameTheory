/-
# Behavioral assessments

A behavioral assessment pairs information-local randomized play with one
belief at every reached decision information site. Beliefs range over complete
histories, not only terminal states: two histories may merge into one execution
state while remaining distinguishable to an analyst.

This stable module contains the finite Bayes and predicate-parametric limit
interfaces. Pointwise convergence and Kreps-Wilson consistency live in the
one-way analytic bridge `GameTheory.Analysis.Protocol.Sequential`.
-/

import GameTheory.Protocol.Assessment

noncomputable section

namespace GameTheory.Protocol

open GameTheory Probability

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace InformationModel

variable (M : InformationModel E)

/-- Complete histories belonging to one information state. The support
invariant for beliefs is carried by this subtype. -/
abbrev InformationHistory (i : ι) (info : M.InfoState i) :=
  { history : E.History // M.infoOf i history.trace = info }

/-- A reached information-state value at which the player has a genuine action.
Models may contain unreachable values and observations at which the player is
inactive; neither is an information set requiring an assessment belief. -/
def InformationSite (i : ι) :=
  { info : M.InfoState i //
    ∃ history : M.InformationHistory i info,
      ¬ E.terminal history.1.state ∧
        ∃ action : E.Action i, some action ∈ M.menu i info }

/-- A complete decision history determines an information site. -/
def informationSite (i : ι) (history : E.History) (action : E.Action i)
    (hnonterminal : ¬ E.terminal history.state)
    (hmenu : some action ∈ M.menu i (M.infoOf i history.trace)) :
    M.InformationSite i :=
  ⟨M.infoOf i history.trace,
    ⟨⟨history, rfl⟩, hnonterminal, action, hmenu⟩⟩

/-- A behavioral strategy profile together with a supported belief at every
reached decision information site. Policies still receive only `InfoState`;
full histories occur only in the analyst's belief field. -/
structure BehavioralAssessment where
  /-- Independent local randomization at each player's information states. -/
  strategy : (i : ι) → M.BehavioralPolicy i
  /-- A belief over precisely the histories in the given information set. -/
  belief : (i : ι) → (site : M.InformationSite i) →
    FinDist (M.InformationHistory i site.1)

namespace BehavioralAssessment

variable {M}

/-- Any behavioral strategy admits an assessment. This also witnesses why
beliefs are indexed by reachable sites rather than every raw `InfoState`
value: each indexed history fiber is inhabited by construction. -/
def ofStrategy (strategy : (i : ι) → M.BehavioralPolicy i) :
    M.BehavioralAssessment where
  strategy := strategy
  belief := fun _ site => FinDist.pure (Classical.choose site.2)

@[simp]
theorem ofStrategy_strategy
    (strategy : (i : ι) → M.BehavioralPolicy i) :
    (ofStrategy strategy).strategy = strategy :=
  rfl

/-- Forget a history belief to the existing state-belief presentation. -/
def stateBelief (A : M.BehavioralAssessment)
    (i : ι) (site : M.InformationSite i) : FinDist E.State :=
  FinDist.map (fun history : M.InformationHistory i site.1 =>
    history.1.state) (A.belief i site)

/-- The induced state belief satisfies the existing `BeliefOn` predicate.
History beliefs therefore refine rather than replace Protocol's state beliefs. -/
theorem stateBelief_onInfoSet (A : M.BehavioralAssessment)
    (i : ι) (site : M.InformationSite i) :
    M.BeliefOn i site.1 (A.stateBelief i site) := by
  intro state hstate
  rw [stateBelief, FinDist.support_map] at hstate
  rcases hstate with ⟨history, _hsupport, rfl⟩
  exact ⟨history.1.trace, history.2⟩

/-- Sequential rationality of a behavioral assessment at one information
site is the existing context-local optimality predicate, specialized to the
player's whole continuation policy. Comparing only the current local law would
need a separate one-shot-deviation theorem. -/
def IsSequentiallyRationalAt (A : M.BehavioralAssessment)
    {i : ι} (_site : M.InformationSite i)
    (ctx : GameTheory.Protocol.Context
      (M.BehavioralPolicy i) E.History) : Prop :=
  ctx.IsLocallyOptimal Set.univ (A.strategy i)

/-- Sequential rationality at every information state for a supplied family of
continuation contexts. The contexts are the only game-specific input; the
optimality predicate is not redefined. -/
def IsSequentiallyRational (A : M.BehavioralAssessment)
    (context : (i : ι) → (site : M.InformationSite i) →
      GameTheory.Protocol.Context
        (M.BehavioralPolicy i) E.History) : Prop :=
  ∀ (i : ι) (site : M.InformationSite i),
    A.IsSequentiallyRationalAt site (context i site)

/-- The continuation context induced by an assessment belief. An alternative
is a whole behavioral policy for the player; all other policies remain fixed,
and play begins from the history sampled by the belief. -/
def continuationContext [Fintype ι] [DecidableEq ι]
    (A : M.BehavioralAssessment) {i : ι}
    (site : M.InformationSite i) (payoff : E.History → ℝ) (fuel : ℕ) :
    GameTheory.Protocol.Context (M.BehavioralPolicy i) E.History where
  outcome alternative :=
    (A.belief i site).bind fun history =>
      M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature)
          A.strategy i alternative) fuel history.1
  continuation := payoff

@[simp]
theorem continuationContext_value [Fintype ι] [DecidableEq ι]
    (A : M.BehavioralAssessment) {i : ι}
    (site : M.InformationSite i) (payoff : E.History → ℝ) (fuel : ℕ)
    (alternative : M.BehavioralPolicy i) :
    (A.continuationContext site payoff fuel).value alternative =
      ((A.belief i site).bind fun history =>
        M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature)
            A.strategy i alternative) fuel history.1).expect
            payoff :=
  rfl

/-- Sequential rationality in the assessment's own finite-horizon
continuation contexts. -/
def IsSequentiallyRationalWithin [Fintype ι] [DecidableEq ι]
    (A : M.BehavioralAssessment)
    (payoff : ι → E.History → ℝ) (fuel : ℕ) : Prop :=
  A.IsSequentiallyRational fun i site =>
    A.continuationContext site (payoff i) fuel

/-- A topology-free limit schema. The analytic bridge supplies pointwise
convergence; other consumers may supply a different convergence relation
without making Protocol import it. -/
def IsLimitConsistent (A : M.BehavioralAssessment)
    (Admissible StepConsistent : M.BehavioralAssessment → Prop)
    (ConvergesTo :
      (ℕ → M.BehavioralAssessment) → M.BehavioralAssessment → Prop) : Prop :=
  ∃ approximating : ℕ → M.BehavioralAssessment,
    (∀ n, Admissible (approximating n) ∧
      StepConsistent (approximating n)) ∧
    ConvergesTo approximating A

theorem IsLimitConsistent.exists_sequence
    {A : M.BehavioralAssessment}
    {Admissible StepConsistent : M.BehavioralAssessment → Prop}
    {ConvergesTo :
      (ℕ → M.BehavioralAssessment) → M.BehavioralAssessment → Prop}
    (h : A.IsLimitConsistent Admissible StepConsistent ConvergesTo) :
    ∃ approximating : ℕ → M.BehavioralAssessment,
      (∀ n, Admissible (approximating n) ∧
        StepConsistent (approximating n)) ∧
      ConvergesTo approximating A :=
  h

end BehavioralAssessment

section Bayes

variable [Fintype ι]

/-- Probability of one complete history under a behavioral profile. Its trace
length supplies exactly the amount of fuel needed to reach it. -/
def historyReachProbability
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (history : E.History) : ℝ :=
  (M.runBehavioral strategy history.trace.length).prob history

/-- Total reach probability of the histories in one finite information set. -/
def informationMass
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (i : ι) (site : M.InformationSite i)
    [Fintype (M.InformationHistory i site.1)] : ℝ :=
  ∑ history : M.InformationHistory i site.1,
    M.historyReachProbability strategy history

/-- Bayes' rule at one finite information set. -/
def BehavioralAssessment.IsBayesConsistentAt
    (A : M.BehavioralAssessment)
    (i : ι) (site : M.InformationSite i)
    [Fintype (M.InformationHistory i site.1)] : Prop :=
  ∀ history : M.InformationHistory i site.1,
    (A.belief i site).prob history =
      M.historyReachProbability A.strategy history /
        M.informationMass A.strategy i site

/-- Bayes' rule at every information state. Finiteness is a capability of this
operation, not stored in the information model or assessment. -/
def BehavioralAssessment.IsBayesConsistent
    (A : M.BehavioralAssessment)
    [∀ (i : ι) (site : M.InformationSite i),
      Fintype (M.InformationHistory i site.1)] : Prop :=
  ∀ (i : ι) (site : M.InformationSite i),
    BehavioralAssessment.IsBayesConsistentAt (M := M) A i site

end Bayes

end InformationModel

end GameTheory.Protocol
