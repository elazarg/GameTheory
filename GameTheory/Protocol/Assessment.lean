/-
# Assessments, contexts, and one-shot deviations

An open game bundles three separable things, which are worth different amounts:

* the *context* — a component together with a continuation — is the idea worth
  taking, because quantifying over the continuation is exactly what upgrades a
  static equilibrium to a sequential one;
* an equilibrium predicate carried as *data* would force each constructor to
  hand-write its own optimality condition, giving one duplicate solution concept
  per constructor, so optimality is derived here instead;
* a contravariant co-outcome channel has no consumer here, so there is none.

So `Context` below is the open-game context with the co-outcome channel dropped
and the equilibrium *derived* rather than stored. It has exactly two fields: what
each of the deviator's choices leads to, and what the rest of the game is worth.
`IsLocallyOptimal` is then a definition over those fields, not a field.

The point of keeping the interface this small is that it is what a one-shot
deviation actually consumes. A one-shot deviation changes one player's call at
one information state and leaves everything else alone; `Context` is precisely
the data that change is evaluated against.
-/

import GameTheory.Protocol.Information
import GameTheory.Protocol.Context
import GameTheory.Math.Probability.ExpectationBind

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι us ua uc uo

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

variable (E) in
/-- The state-continuation specialization used by state-indexed protocols and
beliefs. Information-local play uses the same generic `Context` with histories
as outcomes. -/
abbrev Context (i : ι) :=
  GameTheory.Protocol.Context (Option (E.Action i)) E.State

namespace Context

variable {i : ι}

/-- Build a context from an assessment: a belief over hidden states, and a
branch giving the law that follows each choice at each state. The branch is
total; `ofBelief_congr` says only its behaviour on the belief's support
matters, which is what lets a caller supply any default off-support. -/
def ofBelief (belief : PMF E.State)
    (branch : E.State → Option (E.Action i) → PMF E.State)
    (continuation : E.State → ℝ) : E.Context i :=
  GameTheory.Protocol.Context.ofBelief belief branch continuation

@[simp]
theorem ofBelief_outcome (belief : PMF E.State)
    (branch : E.State → Option (E.Action i) → PMF E.State)
    (continuation : E.State → ℝ) (choice : Option (E.Action i)) :
    (ofBelief belief branch continuation).outcome choice =
      belief.bind fun state => branch state choice := rfl

/-- Off the belief's support the branch is invisible. -/
theorem ofBelief_congr {belief : PMF E.State}
    {first second : E.State → Option (E.Action i) → PMF E.State}
    {continuation : E.State → ℝ}
    (hagree : ∀ state ∈ belief.support, first state = second state)
    (choice : Option (E.Action i)) :
    (ofBelief belief first continuation).outcome choice =
      (ofBelief belief second continuation).outcome choice := by
  have hbind : (belief.bind fun state => first state choice) =
      belief.bind fun state => second state choice :=
    bind_congr_on_support belief fun state hstate => by rw [hagree state hstate]
  exact hbind

/-- The value under a belief is the belief-average of the state-wise values. -/
theorem ofBelief_value (belief : PMF E.State)
    (branch : E.State → Option (E.Action i) → PMF E.State)
    (continuation : E.State → ℝ) (choice : Option (E.Action i))
    (hintegrable : (ofBelief belief branch continuation).IntegrableAt choice) :
    (ofBelief belief branch continuation).value choice hintegrable =
      expect (belief.bind fun state => branch state choice) continuation
        hintegrable := rfl

/-- A guarded belief average of conditional continuation values. Only states
in the belief's support need conditional values. -/
theorem ofBelief_value_tower (belief : PMF E.State)
    (branch : E.State → Option (E.Action i) → PMF E.State)
    (continuation : E.State → ℝ) (choice : Option (E.Action i))
    (hintegrable : (ofBelief belief branch continuation).IntegrableAt choice)
    (stateValue : E.State → ℝ)
    (hvalue : ∀ state, ∀ hs : state ∈ belief.support,
      stateValue state = expect (branch state choice) continuation
        (payoffIntegrable_bind_conditional_on_support belief
          (fun state => branch state choice) continuation hintegrable state hs)) :
    ∃ houter : PayoffIntegrable belief stateValue,
      (ofBelief belief branch continuation).value choice hintegrable =
        expect belief stateValue houter := by
  let houter : PayoffIntegrable belief stateValue :=
    payoffIntegrable_bind_conditionalValue_on_support belief
      (fun state => branch state choice) continuation hintegrable stateValue hvalue
  refine ⟨houter, ?_⟩
  simpa only [ofBelief_value] using
    (expect_bind_tower_on_support belief (fun state => branch state choice)
      continuation hintegrable stateValue hvalue)

end Context

end ExecutionProtocol

namespace InformationModel

open ExecutionProtocol

variable {M : InformationModel E}

/-- Sequential rationality at one information state: the policy's own typed
choice is locally optimal in the context the assessment induces.

Nothing here is carried. `Policy` supplies a choice whose menu membership is
already enforced by its type, and `Context` supplies the value; sequential
rationality is defined once for any continuation-outcome type. -/
def IsSequentiallyRationalAt {i : ι} (policy : M.Policy i) (info : M.InfoState i)
    {Outcome : Type uo}
    (ctx : GameTheory.Protocol.Context (M.Choice i info) Outcome) : Prop :=
  ctx.IsLocallyOptimal Set.univ (policy info)

/-- A policy's call is always in its own menu, so sequential rationality is a
statement about a genuinely allowed choice. -/
theorem act_mem_allowed {i : ι} (policy : M.Policy i) (info : M.InfoState i) :
    policy.act info ∈ M.menu i info :=
  policy.act_mem_menu info

/-- Sequential rationality is the absence of a profitable typed one-shot
deviation. -/
theorem isSequentiallyRationalAt_iff {i : ι} (policy : M.Policy i)
    (info : M.InfoState i) {Outcome : Type uo}
    (ctx : GameTheory.Protocol.Context (M.Choice i info) Outcome) :
    M.IsSequentiallyRationalAt policy info ctx ↔
      ctx.IntegrableAt (policy info) ∧
        (∀ alternative, ctx.IntegrableAt alternative) ∧
          ¬ ∃ alternative,
            ctx.IsProfitableDeviation Set.univ (policy info) alternative := by
  simpa [IsSequentiallyRationalAt] using
    (GameTheory.Protocol.Context.isLocallyOptimal_iff_no_profitable_deviation
      ctx Set.univ (policy info))

/-- Every alternative the deviator may consider is legal at every state its
belief considers possible. This is what makes a one-shot deviation *feasible*
without ever handing the policy a state. -/
theorem deviation_legalOption {i : ι} {info : M.InfoState i} {belief : PMF E.State}
    (hbelief : M.BeliefOn i info belief) {alternative : Option (E.Action i)}
    (hmem : alternative ∈ M.menu i info) {state : E.State}
    (hstate : state ∈ belief.support) :
    LegalOption E state i alternative :=
  (M.legalOption_of_mem_menu info (hbelief hstate) alternative).mp hmem


end InformationModel

end GameTheory.Protocol
