/-
# Behavioral assessments

A behavioral assessment pairs information-local randomized play with one
belief at every reachable information site. Beliefs range over complete
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

/-- An information-state value that some complete history actually produces.
Models may contain unreachable `InfoState` values so that policies stay total;
an assessment must not be forced to invent a belief over an empty fiber. -/
def InformationSite (i : ι) :=
  { info : M.InfoState i // Nonempty (M.InformationHistory i info) }

/-- The information site reached by a complete history. -/
def informationSite (i : ι) (history : E.History) : M.InformationSite i :=
  ⟨M.infoOf i history.trace, ⟨⟨history, rfl⟩⟩⟩

/-- A behavioral strategy profile together with a supported belief at every
reachable information site. Policies still receive only `InfoState`; full
histories occur only in the analyst's belief field. -/
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
  belief := fun _ site => FinDist.pure site.2.some

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
state is the existing context-local optimality predicate, specialized to the
local law actually played there. -/
def IsSequentiallyRationalAt (A : M.BehavioralAssessment)
    {i : ι} (site : M.InformationSite i)
    (ctx : GameTheory.Protocol.Context
      (FinDist (M.Choice i site.1)) E.History) : Prop :=
  ctx.IsLocallyOptimal Set.univ (A.strategy i site.1)

/-- Sequential rationality at every information state for a supplied family of
continuation contexts. The contexts are the only game-specific input; the
optimality predicate is not redefined. -/
def IsSequentiallyRational (A : M.BehavioralAssessment)
    (context : (i : ι) → (site : M.InformationSite i) →
      GameTheory.Protocol.Context
        (FinDist (M.Choice i site.1)) E.History) : Prop :=
  ∀ (i : ι) (site : M.InformationSite i),
    A.IsSequentiallyRationalAt site (context i site)

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
