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

import GameTheory.Protocol.Context
import GameTheory.Protocol.Information
import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.ExpectationBind

noncomputable section

namespace GameTheory.Protocol

open GameTheory GameTheory.Math.Probability

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

/-- Every history in this information fiber occurs at one trace depth. -/
def InformationSite.CommonDepth {i : ι}
    (site : M.InformationSite i) (depth : ℕ) : Prop :=
  ∀ history : M.InformationHistory i site.1,
    history.1.trace.length = depth

/-- Every history in this decision information fiber is nonterminal.  This is
stronger than `InformationSite`: Protocol deliberately permits a terminal
history to share an information state and nominal activity with a nonterminal
decision history, even though execution will not consult it. -/
def InformationSite.AllNonterminal {i : ι}
    (site : M.InformationSite i) : Prop :=
  ∀ history : M.InformationHistory i site.1,
    ¬ E.terminal history.1.state

/-- A decision site's information-local menu makes its player active at every
history in the fiber, including a nominally active terminal history. -/
theorem InformationSite.active {i : ι} (site : M.InformationSite i)
    (history : M.InformationHistory i site.1) :
    E.active history.1.state i := by
  obtain ⟨_witness, _hnonterminal, action, haction⟩ := site.2
  have hmenu : some action ∈ M.menu i (M.infoOf i history.1.trace) := by
    simpa only [history.2] using haction
  exact ((M.menu_adequate i history.1.trace (some action)).mp hmenu).1

/-- Histories in one decision information fiber form an antichain: if one can
continue to another, they were already the same history.  This is the minimal
semantic premise under which summing their reach probabilities describes the
probability of a disjoint information event. -/
def InformationSite.IsHistoryAntichain {i : ι}
    (site : M.InformationSite i) : Prop :=
  ∀ (first second : M.InformationHistory i site.1)
    (joint : ∀ j, Option (E.Action j))
    (isLegal : E.Legal first.1.state joint) (reached : E.State)
    (realized : reached ∈ (E.step first.1.state ⟨joint, isLegal⟩).support)
    (fuel : ℕ),
    ¬ E.ReachesWithin fuel (first.1.extend isLegal realized) second.1

/-- Every reached decision information fiber is a history antichain. -/
def DecisionInformationAntichain : Prop :=
  ∀ (i : ι) (site : M.InformationSite i), site.IsHistoryAntichain

/-- Perfect recall is sufficient for the exact antichain premise used by
finite Bayes conditioning. -/
theorem decisionInformationAntichain_of_perfectRecall
    (hrecall : M.PerfectRecall) : M.DecisionInformationAntichain := by
  intro i site first second joint isLegal reached realized fuel hreach
  obtain ⟨_witness, _hnonterminal, action, haction⟩ := site.2
  have hmenu : some action ∈ M.menu i (M.infoOf i first.1.trace) := by
    simpa only [first.2] using haction
  have hactive : E.active first.1.state i :=
    ((M.menu_adequate i first.1.trace (some action)).mp hmenu).1
  exact (M.infoOf_ne_of_perfectRecall_after_step hrecall i isLegal
    realized hactive hreach) (second.2.trans first.2.symm)

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
    PMF (M.InformationHistory i site.1)

namespace BehavioralAssessment

variable {M}

/-- Any behavioral strategy admits an assessment. This also witnesses why
beliefs are indexed by reachable sites rather than every raw `InfoState`
value: each indexed history fiber is inhabited by construction. -/
def ofStrategy (strategy : (i : ι) → M.BehavioralPolicy i) :
    M.BehavioralAssessment where
  strategy := strategy
  belief := fun _ site => PMF.pure (Classical.choose site.2)

@[simp]
theorem ofStrategy_strategy
    (strategy : (i : ι) → M.BehavioralPolicy i) :
    (ofStrategy strategy).strategy = strategy :=
  rfl

/-- Forget a history belief to the existing state-belief presentation. -/
def stateBelief (A : M.BehavioralAssessment)
    (i : ι) (site : M.InformationSite i) : PMF E.State :=
  PMF.map (fun history : M.InformationHistory i site.1 =>
    history.1.state) (A.belief i site)

/-- The induced state belief satisfies the existing `BeliefOn` predicate.
History beliefs therefore refine rather than replace Protocol's state beliefs. -/
theorem stateBelief_onInfoSet (A : M.BehavioralAssessment)
    (i : ι) (site : M.InformationSite i) :
    M.BeliefOn i site.1 (A.stateBelief i site) := by
  intro state hstate
  rw [stateBelief, PMF.support_map] at hstate
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
    GameTheory.Protocol.Context (M.BehavioralPolicy i) E.History :=
  GameTheory.Protocol.Context.ofBelief (A.belief i site)
    (fun history alternative =>
      M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature)
          A.strategy i alternative) fuel history.1) payoff

@[simp]
theorem continuationContext_value [Fintype ι] [DecidableEq ι]
    (A : M.BehavioralAssessment) {i : ι}
    (site : M.InformationSite i) (payoff : E.History → ℝ) (fuel : ℕ)
    (alternative : M.BehavioralPolicy i)
    (h : (A.continuationContext site payoff fuel).IntegrableAt alternative) :
    (A.continuationContext site payoff fuel).value alternative h =
      expect ((A.belief i site).bind fun history =>
        M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature)
            A.strategy i alternative) fuel history.1) payoff h :=
  rfl

/-- The belief average of conditional continuation values equals the guarded
value of the whole policy deviation. -/
theorem continuationContext_value_tower [Fintype ι] [DecidableEq ι]
    (A : M.BehavioralAssessment) {i : ι}
    (site : M.InformationSite i) (payoff : E.History → ℝ) (fuel : ℕ)
    (alternative : M.BehavioralPolicy i)
    (hbind : (A.continuationContext site payoff fuel).IntegrableAt alternative)
    (hcond : ∀ history : M.InformationHistory i site.1,
      PayoffIntegrable
        (M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature)
            A.strategy i alternative) fuel history.1) payoff) :
    (A.continuationContext site payoff fuel).value alternative hbind =
      expect (A.belief i site)
        (fun history => expect
          (M.runBehavioralFrom
            (Profile.update (sig := M.behavioralSignature)
              A.strategy i alternative) fuel history.1)
          payoff (hcond history))
        (payoffIntegrable_bind_conditionalExpectation
          (A.belief i site)
          (fun history => M.runBehavioralFrom
            (Profile.update (sig := M.behavioralSignature)
              A.strategy i alternative) fuel history.1)
          payoff hbind hcond) := by
  exact expect_bind_tower _ _ _ hbind hcond

/-- Once every legal history has stopped by `bound`, extra fuel leaves every
whole-policy continuation law and its guarded value domain unchanged. -/
theorem continuationContext_bound_add [Fintype ι] [DecidableEq ι]
    (A : M.BehavioralAssessment) (bound : ℕ)
    (hbound : E.BoundedHorizon bound)
    (extra : ℕ) {i : ι} (site : M.InformationSite i)
    (payoff : E.History → ℝ) :
    A.continuationContext site payoff (bound + extra) =
      A.continuationContext site payoff bound := by
  apply congrArg₂ (fun outcome continuation =>
    GameTheory.Protocol.Context.mk outcome continuation)
  · funext alternative
    apply bind_congr_on_support
    intro history _
    exact M.runBehavioralFrom_bound_add
      (Profile.update (sig := M.behavioralSignature)
        A.strategy i alternative) hbound extra history.1
  · rfl

/-- Sequential rationality in the assessment's own finite-horizon
continuation contexts. -/
def IsSequentiallyRationalWithin [Fintype ι] [DecidableEq ι]
    (A : M.BehavioralAssessment)
    (payoff : ι → E.History → ℝ) (fuel : ℕ) : Prop :=
  A.IsSequentiallyRational fun i site =>
    A.continuationContext site (payoff i) fuel

/-- Certified horizon stabilization also stabilizes the guarded whole-policy
sequential-rationality predicate, including its integrability obligations. -/
theorem isSequentiallyRationalWithin_bound_add
    [Fintype ι] [DecidableEq ι]
    (A : M.BehavioralAssessment) (bound : ℕ)
    (hbound : E.BoundedHorizon bound)
    (extra : ℕ) (payoff : ι → E.History → ℝ) :
    A.IsSequentiallyRationalWithin payoff (bound + extra) ↔
      A.IsSequentiallyRationalWithin payoff bound := by
  simp only [IsSequentiallyRationalWithin, IsSequentiallyRational,
    IsSequentiallyRationalAt]
  constructor <;> intro h i site
  · simpa only [A.continuationContext_bound_add bound hbound extra site (payoff i)]
      using h i site
  · simpa only [A.continuationContext_bound_add bound hbound extra site (payoff i)]
      using h i site

/-- With identically zero continuation payoff, every behavioral assessment is
sequentially rational against whole continuation-policy deviations. -/
theorem isSequentiallyRationalWithin_zero [Fintype ι] [DecidableEq ι]
    (A : M.BehavioralAssessment) (fuel : ℕ) :
    A.IsSequentiallyRationalWithin (fun _ _ => 0) fuel := by
  intro i site
  refine ⟨payoffIntegrable_zero _, ?_, ?_⟩
  · intro alternative _
    exact payoffIntegrable_zero _
  · intro alternative _ hchoice halt
    rw [continuationContext_value, continuationContext_value]
    simp [expect]

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

end InformationModel

end GameTheory.Protocol
