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

import GameTheory.Protocol.Backward
import GameTheory.Protocol.Information

noncomputable section

namespace GameTheory.Protocol

open Probability

universe uι us ua

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

variable (E) in
/-- What a deviator faces at one decision point: where each of its choices
leads, and what the rest of the game is worth from there.

This is the open-game context `X × (Y → R)` with the co-outcome channel `S`
removed, because nothing consumes that channel. The
belief over hidden states and the other players' behaviour are folded into
`outcome`; `Context.ofBelief` builds one that way. -/
structure Context (i : ι) where
  /-- The law over next states induced by each of the deviator's choices, with
  everyone else's behaviour already folded in. -/
  outcome : Option (E.Action i) → FinDist E.State
  /-- What the rest of the game is worth from each state. -/
  continuation : E.State → ℝ

namespace Context

variable {i : ι}

/-- The value of a choice: its induced law, evaluated against the
continuation. -/
def value (ctx : E.Context i) (choice : Option (E.Action i)) : ℝ :=
  (ctx.outcome choice).expect ctx.continuation

/-- A choice is locally optimal among `allowed` when nothing allowed is worth
more. This is a *definition* over the context's two fields — the contrast with
v1, where each open-game constructor stored its own equilibrium predicate. -/
def IsLocallyOptimal (ctx : E.Context i) (allowed : Set (Option (E.Action i)))
    (choice : Option (E.Action i)) : Prop :=
  ∀ alternative ∈ allowed, ctx.value alternative ≤ ctx.value choice

/-- A one-shot deviation is profitable when some allowed alternative is worth
strictly more than the call actually made. -/
def IsProfitableDeviation (ctx : E.Context i) (allowed : Set (Option (E.Action i)))
    (choice alternative : Option (E.Action i)) : Prop :=
  alternative ∈ allowed ∧ ctx.value choice < ctx.value alternative

/-- **The one-shot-deviation interface.** Local optimality is exactly the
absence of a profitable one-shot deviation. Both sides are derived from
`value`; neither is stored. -/
theorem isLocallyOptimal_iff_no_profitable_deviation (ctx : E.Context i)
    (allowed : Set (Option (E.Action i))) (choice : Option (E.Action i)) :
    ctx.IsLocallyOptimal allowed choice ↔
      ¬ ∃ alternative, ctx.IsProfitableDeviation allowed choice alternative := by
  constructor
  · rintro hopt ⟨alternative, hmem, hlt⟩
    exact absurd (hopt alternative hmem) (not_le.2 hlt)
  · intro hnone alternative hmem
    by_contra hgt
    exact hnone ⟨alternative, hmem, not_le.1 hgt⟩

/-- Local optimality only depends on the context through `value`. -/
theorem isLocallyOptimal_congr {first second : E.Context i}
    {allowed : Set (Option (E.Action i))} {choice : Option (E.Action i)}
    (hvalue : ∀ option, first.value option = second.value option) :
    first.IsLocallyOptimal allowed choice ↔ second.IsLocallyOptimal allowed choice := by
  constructor <;> intro hopt alternative hmem
  · rw [← hvalue, ← hvalue]; exact hopt alternative hmem
  · rw [hvalue, hvalue]; exact hopt alternative hmem

/-! ## The context a one-shot deviation is evaluated in

The principle proved for choosers compares whole joint actions. A deviator
compares its own choices, and the two meet once the caller says how a choice
becomes a joint action — which a concrete game supplies anyway, and which cannot
be built generically here, since substituting one player's contribution is a
pointwise update of a dependent function. -/

/-- The context at one state: each of the deviator's choices is turned into a
joint action, and continued play is worth `continuation`. -/
def ofDeviation {state : E.State}
    (deviate : Option (E.Action i) → { joint : ∀ j, Option (E.Action j) // E.Legal state joint })
    (continuation : E.State → ℝ) : E.Context i where
  outcome choice := E.step state (deviate choice)
  continuation := continuation

@[simp]
theorem ofDeviation_value {state : E.State}
    (deviate : Option (E.Action i) → { joint : ∀ j, Option (E.Action j) // E.Legal state joint })
    (continuation : E.State → ℝ) (choice : Option (E.Action i)) :
    (ofDeviation deviate continuation).value choice =
      (E.step state (deviate choice)).expect continuation := rfl

/-- **The one-shot deviation principle, read as local optimality.** A chooser no
single action improves is locally optimal in the context its own continued play
induces — whatever set of choices the deviator is allowed, and however its
choices are turned into joint actions. -/
theorem isLocallyOptimal_ofDeviation {certificate : E.WellFoundedPlay} {chooser : E.Chooser}
    {payoff : E.State → ℝ} (hopt : E.IsOneShotOptimal certificate chooser payoff)
    {state : E.State} (hterm : ¬ E.terminal state)
    (deviate : Option (E.Action i) → { joint : ∀ j, Option (E.Action j) // E.Legal state joint })
    (allowed : Set (Option (E.Action i))) (own : Option (E.Action i))
    (hown : deviate own = chooser state hterm) :
    (ofDeviation deviate (E.backwardValue certificate chooser payoff)).IsLocallyOptimal
      allowed own := by
  intro alternative _
  rw [ofDeviation_value, ofDeviation_value, hown]
  exact hopt state hterm (deviate alternative)

/-- Build a context from an assessment: a belief over hidden states, and a
branch giving the law that follows each choice at each state. The branch is
total; `ofBelief_congr` says only its behaviour on the belief's support
matters, which is what lets a caller supply any default off-support. -/
def ofBelief (belief : FinDist E.State)
    (branch : E.State → Option (E.Action i) → FinDist E.State)
    (continuation : E.State → ℝ) : E.Context i where
  outcome choice := belief.bind fun state => branch state choice
  continuation := continuation

@[simp]
theorem ofBelief_outcome (belief : FinDist E.State)
    (branch : E.State → Option (E.Action i) → FinDist E.State)
    (continuation : E.State → ℝ) (choice : Option (E.Action i)) :
    (ofBelief belief branch continuation).outcome choice =
      belief.bind fun state => branch state choice := rfl

/-- Off the belief's support the branch is invisible. -/
theorem ofBelief_congr {belief : FinDist E.State}
    {first second : E.State → Option (E.Action i) → FinDist E.State}
    {continuation : E.State → ℝ}
    (hagree : ∀ state ∈ belief.support, first state = second state)
    (choice : Option (E.Action i)) :
    (ofBelief belief first continuation).value choice =
      (ofBelief belief second continuation).value choice := by
  have hbind : (belief.bind fun state => first state choice) =
      belief.bind fun state => second state choice :=
    FinDist.bind_congr fun state hstate => by rw [hagree state hstate]
  unfold value
  rw [ofBelief_outcome, ofBelief_outcome, hbind]
  rfl

/-- The value under a belief is the belief-average of the state-wise values. -/
theorem ofBelief_value (belief : FinDist E.State)
    (branch : E.State → Option (E.Action i) → FinDist E.State)
    (continuation : E.State → ℝ) (choice : Option (E.Action i)) :
    (ofBelief belief branch continuation).value choice =
      belief.expect fun state => (branch state choice).expect continuation := by
  unfold value
  rw [ofBelief_outcome, FinDist.expect_bind]
  rfl

end Context

end ExecutionProtocol

namespace InformationModel

open ExecutionProtocol

variable {M : InformationModel E}

/-- Sequential rationality at one information state: the policy's own call is
locally optimal in the context the assessment induces, among the menu the
information state allows.

Nothing here is carried. `Policy` supplies the call, `menu` supplies the
allowed set, and `Context` supplies the value; sequential rationality is the
conjunction, defined once. -/
def IsSequentiallyRationalAt {i : ι} (policy : M.Policy i) (info : M.InfoState i)
    (ctx : E.Context i) : Prop :=
  ctx.IsLocallyOptimal (M.menu i info) (policy.act info)

/-- A policy's call is always in its own menu, so sequential rationality is a
statement about a genuinely allowed choice. -/
theorem act_mem_allowed {i : ι} (policy : M.Policy i) (info : M.InfoState i) :
    policy.act info ∈ M.menu i info :=
  policy.act_mem_menu info

/-- Sequential rationality is the absence of a profitable one-shot deviation
inside the menu. -/
theorem isSequentiallyRationalAt_iff {i : ι} (policy : M.Policy i)
    (info : M.InfoState i) (ctx : E.Context i) :
    M.IsSequentiallyRationalAt policy info ctx ↔
      ¬ ∃ alternative,
        ctx.IsProfitableDeviation (M.menu i info) (policy.act info) alternative :=
  Context.isLocallyOptimal_iff_no_profitable_deviation ..

/-- Every alternative the deviator may consider is legal at every state its
belief considers possible. This is what makes a one-shot deviation *feasible*
without ever handing the policy a state. -/
theorem deviation_legalOption {i : ι} {info : M.InfoState i} {belief : FinDist E.State}
    (hbelief : M.BeliefOn i info belief) {alternative : Option (E.Action i)}
    (hmem : alternative ∈ M.menu i info) {state : E.State}
    (hstate : state ∈ belief.support) :
    LegalOption E state i alternative :=
  (M.legalOption_of_mem_menu info (hbelief hstate) alternative).mp hmem

end InformationModel

end GameTheory.Protocol
