/-
# Backward induction over a general-state protocol

`GameTheory.Protocol.Execution` evaluates a protocol forwards: `StopsWithin`
plus two stabilization theorems turn the fuelled `runFor` into a total
evaluator. This module goes the other way, recursing from terminal states
backwards.

A general state space has no inductive structure to recurse on, so the recursion
needs a certificate. The one it needs is small: `WellFoundedPlay`, that no play
continues forever. Terminal states are its minimal elements automatically,
because legality already contains non-terminality, so there is no separate base
case to state.

The module is organised so that the cost is readable off its structure.

* `Successor` is the one-step realized-transition relation, oriented the way
  `WellFounded` consumes a relation. It is `StepEvent` with the data forgotten,
  not a new notion of "one step".
* `WellFoundedPlay` is the entire certificate: one `WellFounded`. It is a `Prop`
  about the protocol, never a stored horizon, and `wellFoundedPlay_of_rank`
  discharges it from an ordinary ranking argument.
* `backwardRec` is `WellFounded.fix` at that relation, plus its unfolding
  equation. There is no inductive tree, no second transition relation, and no
  fuel.
* `backwardValue` is the substantive instantiation: the value of a **fixed
  chooser**, that is, the expected terminal payoff when the given policy is
  followed. It is deliberately *not* a max-over-actions optimum. Optimizing
  would need a supremum over the legal-action set together with a boundedness
  hypothesis — a preference and order question rather than an execution
  question, and this module is about execution. The honest scope of this file is
  therefore "backward induction exists and computes", not "backward induction
  optimizes".
* `backwardValue_eq_expect_runFor` joins the two halves: wherever the fuelled
  runner has already stopped, the backward-induction value *is* the expected
  payoff of the run law. That is the sharpest available evidence that backward
  induction is not a second semantics for the same protocol but a second view of
  the same one.

The discriminating fixture lives in `GameTheory.Tests.Backward`, so stable
importers compile only the semantic definitions and proofs in this module.
-/

import GameTheory.Protocol.Execution

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι us ua uv

variable {ι : Type uι}

namespace ExecutionProtocol

variable {E : ExecutionProtocol ι}

/-! ## The successor relation

Backward induction recurses *forward* in play, so the relation it descends must
make successors smaller and terminal states minimal. -/

variable (E) in
/-- One realized legal step, oriented for well-founded recursion. Read
`E.Successor target source` as "`target` succeeds `source`": some legal joint
action at `source` gives `target` positive probability under the transition law.

The successor is the first argument on purpose. `WellFounded.fix` treats its
first argument as the smaller element, and backward induction must bottom out at
terminal states, so successors have to be the descending side. -/
def Successor (target source : E.State) : Prop :=
  ∃ (joint : ∀ i, Option (E.Action i)) (isLegal : E.Legal source joint),
    target ∈ (E.step source ⟨joint, isLegal⟩).support

/-- A realized transition is exactly a witness for `Successor`. The relation is
`StepEvent` with its data forgotten, not a second notion of "one step". -/
theorem successor_of_stepEvent (event : StepEvent E) :
    E.Successor event.target event.source :=
  ⟨event.joint, event.isLegal, event.realized⟩

/-- Terminal states have no successors, so they are the minimal elements of
`Successor`. Backward induction therefore stops exactly where execution stops,
and no separate base-case predicate has to be supplied. -/
theorem not_successor_of_terminal {source target : E.State} (hterm : E.terminal source) :
    ¬ E.Successor target source := by
  rintro ⟨joint, isLegal, -⟩
  exact E.terminal_no_legal hterm joint isLegal

/-! ## The certificate -/

variable (E) in
/-- **The backward-induction certificate.** One `WellFounded`, and nothing else:
every play descends. Like `BoundedHorizon` and unlike a stored horizon field,
this is a proposition about the protocol; unlike `StopsWithin` it is independent
of any chooser, which is what backward induction over *all* successors needs. -/
def WellFoundedPlay : Prop := WellFounded E.Successor

/-- The practical way to discharge the certificate: a natural-number rank that
strictly drops along every realized legal step. Two lines, and the protocol is
ready for backward induction. -/
theorem wellFoundedPlay_of_rank (rank : E.State → ℕ)
    (hdrop : ∀ source target : E.State, E.Successor target source →
      rank target < rank source) : E.WellFoundedPlay := by
  have hsub : Subrelation E.Successor (measure rank).rel :=
    fun {target source} hsucc => hdrop source target hsucc
  exact hsub.wf (measure rank).wf

/-! ## The recursor -/

variable (E) in
/-- **Backward induction.** Well-founded recursion along `Successor`: a value at
every state, computed from the values at that state's successors. The certificate
plus `WellFounded.fix` is the whole implementation. -/
def backwardRec {motive : E.State → Sort uv} (certificate : E.WellFoundedPlay)
    (rule : (source : E.State) →
      ((target : E.State) → E.Successor target source → motive target) →
      motive source) (state : E.State) : motive state :=
  WellFounded.fix (r := E.Successor) certificate rule state

/-- The unfolding equation for `backwardRec`. It is what every downstream
computation rule is proved from. -/
theorem backwardRec_eq {motive : E.State → Sort uv} (certificate : E.WellFoundedPlay)
    (rule : (source : E.State) →
      ((target : E.State) → E.Successor target source → motive target) →
      motive source) (source : E.State) :
    E.backwardRec certificate rule source =
      rule source fun target _ => E.backwardRec certificate rule target :=
  WellFounded.fix_eq (r := E.Successor) certificate rule source

/-! ## The value of a fixed chooser

The substantive instantiation: a real payoff collected at terminal states, and
elsewhere the expected successor value under the law the chooser induces. -/

variable (E) in
open Classical in
/-- `FinDist.expect` consumes a *total* observable, while backward induction
supplies values only at successors. Padding every non-successor with `0` closes
that gap, and `FinDist.expect_congr` then discards the padding, because
everything in a transition law's support is by definition a successor. This
adapter is the entire representational cost of running backward induction
through the probability layer. -/
def padSuccessorValues (source : E.State)
    (successorValue : (reached : E.State) → E.Successor reached source → ℝ)
    (target : E.State) : ℝ :=
  if hsucc : E.Successor target source then successorValue target hsucc else 0

/-- On successors the padding is invisible. -/
theorem padSuccessorValues_of_successor {source target : E.State}
    {successorValue : (reached : E.State) → E.Successor reached source → ℝ}
    (hsucc : E.Successor target source) :
    E.padSuccessorValues source successorValue target = successorValue target hsucc :=
  dif_pos hsucc

variable (E) in
open Classical in
/-- The backward-induction rule for a terminal payoff: collect at a terminal
state, and otherwise average the successor values under the law the chooser
induces. Terminality is inspected before the chooser is consulted, exactly as in
`runFor`, so no total legal-action chooser is required. -/
def backwardStep (chooser : E.Chooser) (payoff : E.State → ℝ) (source : E.State)
    (successorValue : (reached : E.State) → E.Successor reached source → ℝ) : ℝ :=
  if hterm : E.terminal source then payoff source
  else (E.step source (chooser source hterm)).expect
    (E.padSuccessorValues source successorValue)

variable (E) in
/-- The backward-induction value of a *fixed* chooser: the expected terminal
payoff of following `chooser`, defined by recursion on the protocol rather than
by running it. This is not an optimum over actions; see the module docstring. -/
def backwardValue (certificate : E.WellFoundedPlay) (chooser : E.Chooser)
    (payoff : E.State → ℝ) : E.State → ℝ :=
  E.backwardRec (motive := fun _ => ℝ) certificate (E.backwardStep chooser payoff)

variable {certificate : E.WellFoundedPlay} {chooser : E.Chooser} {payoff : E.State → ℝ}

/-- `backwardValue` unfolded one level, still mentioning the padding. -/
theorem backwardValue_eq (source : E.State) :
    E.backwardValue certificate chooser payoff source =
      E.backwardStep chooser payoff source
        fun reached _ => E.backwardValue certificate chooser payoff reached :=
  backwardRec_eq certificate (E.backwardStep chooser payoff) source

/-- At a terminal state the value is the payoff. -/
theorem backwardValue_of_terminal {source : E.State} (hterm : E.terminal source) :
    E.backwardValue certificate chooser payoff source = payoff source := by
  rw [backwardValue_eq]
  exact dif_pos hterm

/-- **The computation rule that matters.** Away from terminal states the value is
the expected successor value under the transition law, with no padding left in
the statement. -/
theorem backwardValue_of_not_terminal {source : E.State} (hterm : ¬ E.terminal source) :
    E.backwardValue certificate chooser payoff source =
      (E.step source (chooser source hterm)).expect
        (E.backwardValue certificate chooser payoff) := by
  have hstep : E.backwardStep chooser payoff source
      (fun reached _ => E.backwardValue certificate chooser payoff reached) =
      (E.step source (chooser source hterm)).expect
        (E.padSuccessorValues source
          fun reached _ => E.backwardValue certificate chooser payoff reached) :=
    dif_neg hterm
  rw [backwardValue_eq, hstep]
  refine FinDist.expect_congr fun reached hreached => ?_
  exact padSuccessorValues_of_successor
    ⟨(chooser source hterm).1, (chooser source hterm).2, hreached⟩

/-! ## The one-shot deviation principle

Checking a strategy against every alternative strategy is checking infinitely
many things; checking it against every alternative *action*, one step at a time,
is checking finitely many. The principle below says the two tests are
equivalent, and the certificate that makes the sufficient direction work is the
same well-foundedness the backward recursion already needs — nothing further is
assumed.

What makes it non-circular is that the one-step comparison is made against the
chooser's *own* continuation value. A chooser that cannot improve on itself by
changing one action, given that it will go on playing as it does, cannot be
improved on by any other chooser at all. -/

variable (E) in
/-- No single legal action, substituted at one state and followed by the
chooser's own continued play, does better than the action the chooser takes. -/
def IsOneShotOptimal (certificate : E.WellFoundedPlay) (chooser : E.Chooser)
    (payoff : E.State → ℝ) : Prop :=
  ∀ (state : E.State) (hterm : ¬ E.terminal state)
    (alternative : { joint : ∀ i, Option (E.Action i) // E.Legal state joint }),
    (E.step state alternative).expect (E.backwardValue certificate chooser payoff) ≤
      (E.step state (chooser state hterm)).expect
        (E.backwardValue certificate chooser payoff)

/-- **The one-shot deviation principle.** A chooser that no single-action change
improves is better than every other chooser, everywhere.

The induction is along the same `Successor` relation the value recursion uses,
so the certificate carries both and no second hypothesis appears. -/
theorem backwardValue_le_of_isOneShotOptimal {certificate : E.WellFoundedPlay}
    {optimal : E.Chooser} {payoff : E.State → ℝ}
    (hopt : E.IsOneShotOptimal certificate optimal payoff) (other : E.Chooser)
    (state : E.State) :
    E.backwardValue certificate other payoff state ≤
      E.backwardValue certificate optimal payoff state := by
  induction state using certificate.induction with
  | _ source ih =>
    by_cases hterm : E.terminal source
    · rw [backwardValue_of_terminal hterm, backwardValue_of_terminal hterm]
    · rw [backwardValue_of_not_terminal hterm, backwardValue_of_not_terminal hterm]
      refine le_trans (FinDist.expect_mono fun reached hreached => ?_)
        (hopt source hterm (other source hterm))
      exact ih reached ⟨(other source hterm).1, (other source hterm).2, hreached⟩

/-! ### The converse

The one-step condition is not merely sufficient. Recovering it from global
optimality needs a chooser that plays one action at one state and follows the
original everywhere else, and that is constructible here: a chooser's *answer*
is a joint action, whose type does not mention the state, so only the legality
certificate has to be repaired. Nothing is transported.

What makes the recovery work is the certificate again. A state cannot be reached
from its own successors — that would be an infinite descending chain — so the
deviant agrees with the original everywhere the value recursion looks after the
first step. -/

variable (E) in
/-- States reachable from `source` by realized legal steps, `source` included. -/
def Reaches (source target : E.State) : Prop :=
  Relation.ReflTransGen (fun earlier later => E.Successor later earlier) source target

theorem Reaches.refl (state : E.State) : E.Reaches state state := Relation.ReflTransGen.refl

theorem Reaches.step {source middle target : E.State} (hstep : E.Successor middle source)
    (hrest : E.Reaches middle target) : E.Reaches source target :=
  Relation.ReflTransGen.head hstep hrest

open Classical in
variable (E) in
/-- The chooser that answers `replacement` at one state and follows `chooser`
everywhere else. The answer's type does not mention the state, so the branch
needs no transport of data; only the legality certificate is repaired. -/
def deviateAt (state : E.State)
    (replacement : { joint : ∀ i, Option (E.Action i) // E.Legal state joint })
    (chooser : E.Chooser) : E.Chooser := fun source hterm =>
  if hsame : source = state then ⟨replacement.1, by rw [hsame]; exact replacement.2⟩
  else chooser source hterm

theorem deviateAt_self {state : E.State}
    {replacement : { joint : ∀ i, Option (E.Action i) // E.Legal state joint }}
    {chooser : E.Chooser} (hterm : ¬ E.terminal state) :
    E.deviateAt state replacement chooser state hterm = replacement := by
  classical
  show (if hsame : state = state then _ else _) = _
  rw [dif_pos rfl]

theorem deviateAt_of_ne {state source : E.State}
    {replacement : { joint : ∀ i, Option (E.Action i) // E.Legal state joint }}
    {chooser : E.Chooser} (hne : source ≠ state) (hterm : ¬ E.terminal source) :
    E.deviateAt state replacement chooser source hterm = chooser source hterm := by
  classical
  exact dif_neg hne

/-- Choosers agreeing everywhere the recursion can look from `start` give the
same value there. -/
theorem backwardValue_congr_of_reaches {certificate : E.WellFoundedPlay}
    {first second : E.Chooser} {payoff : E.State → ℝ} :
    ∀ (start : E.State),
      (∀ source, E.Reaches start source → ∀ hterm : ¬ E.terminal source,
        first source hterm = second source hterm) →
      E.backwardValue certificate first payoff start =
        E.backwardValue certificate second payoff start := by
  intro start
  induction start using certificate.induction with
  | _ source ih =>
    intro hagree
    by_cases hterm : E.terminal source
    · rw [backwardValue_of_terminal hterm, backwardValue_of_terminal hterm]
    · rw [backwardValue_of_not_terminal hterm, backwardValue_of_not_terminal hterm,
        hagree source (Reaches.refl source) hterm]
      refine FinDist.expect_congr fun reached hreached => ?_
      have hstep : E.Successor reached source :=
        ⟨(second source hterm).1, (second source hterm).2, hreached⟩
      exact ih reached hstep fun later hlater =>
        hagree later (Reaches.step hstep hlater)

/-- No state is reachable from its own successors: that would be a descending
chain the certificate forbids. -/
theorem not_reaches_of_successor {certificate : E.WellFoundedPlay} {source target : E.State}
    (hstep : E.Successor target source) : ¬ E.Reaches target source := by
  intro hback
  have hforward : Relation.ReflTransGen E.Successor source target := by
    clear hstep
    induction hback with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hlast ih => exact Relation.ReflTransGen.head hlast ih
  have hcycle : Relation.TransGen E.Successor source source :=
    Relation.TransGen.tail' hforward hstep
  exact (certificate.transGen).irrefl.irrefl source hcycle

/-- **The converse.** A chooser better than every other is unimprovable by any
single action, so the one-step condition is not merely sufficient. -/
theorem isOneShotOptimal_of_backwardValue_le {certificate : E.WellFoundedPlay}
    {optimal : E.Chooser} {payoff : E.State → ℝ}
    (hbest : ∀ (other : E.Chooser) (state : E.State),
      E.backwardValue certificate other payoff state ≤
        E.backwardValue certificate optimal payoff state) :
    E.IsOneShotOptimal certificate optimal payoff := by
  intro state hterm alternative
  have hdeviant := hbest (E.deviateAt state alternative optimal) state
  rw [backwardValue_of_not_terminal (chooser := E.deviateAt state alternative optimal) hterm,
    deviateAt_self hterm,
    backwardValue_of_not_terminal (chooser := optimal) hterm] at hdeviant
  refine le_trans (le_of_eq ?_) hdeviant
  refine (FinDist.expect_congr fun reached hreached => ?_).symm
  refine backwardValue_congr_of_reaches reached fun source hreaches hsourceTerm => ?_
  refine deviateAt_of_ne (fun hsame => ?_) hsourceTerm
  rw [hsame] at hreaches
  exact not_reaches_of_successor (certificate := certificate)
    (⟨alternative.1, alternative.2, hreached⟩ : E.Successor reached state) hreaches

/-! ## Backward induction computes the forward semantics

The fuelled evaluator and this recursion describe the same number. That is
what distinguishes "a small certificate over one semantics" from "a second
parallel semantics". -/

/-- Wherever the fuelled runner has already stopped, the backward-induction value
of a chooser equals the expected payoff of its run law. Neither side is defined
in terms of the other: `backwardValue` recurses on `Successor`, `runFor` recurses
on fuel, and `StopsWithin` is the bounded certificate that makes them meet. -/
theorem backwardValue_eq_expect_runFor {horizon : ℕ} {state : E.State}
    (hstop : E.StopsWithin chooser horizon state) :
    E.backwardValue certificate chooser payoff state =
      (E.runFor chooser horizon state).expect payoff := by
  induction horizon generalizing state with
  | zero =>
    have hterm : E.terminal state :=
      hstop state (by rw [runFor_zero]; exact FinDist.mem_support_pure.2 rfl)
    rw [backwardValue_of_terminal hterm, runFor_zero, FinDist.expect_pure]
  | succ horizon ih =>
    by_cases hterm : E.terminal state
    · rw [backwardValue_of_terminal hterm, runFor_of_terminal chooser _ hterm,
        FinDist.expect_pure]
    · rw [backwardValue_of_not_terminal hterm,
        runFor_succ_of_not_terminal chooser horizon hterm, FinDist.expect_bind]
      refine FinDist.expect_congr fun reached hreached => ih fun final hfinal => ?_
      refine hstop final ?_
      rw [runFor_succ_of_not_terminal chooser horizon hterm, FinDist.support_bind]
      exact Set.mem_biUnion hreached hfinal

/-- **The forward reading.** Where both choosers have stopped, the principle is a
statement about run laws: the locally unimprovable chooser's expected payoff is
at least any other's. Nothing new is proved here — the two semantics were already
known to agree — but this is the form a caller quotes. -/
theorem expect_runFor_le_of_isOneShotOptimal {certificate : E.WellFoundedPlay}
    {optimal : E.Chooser} {payoff : E.State → ℝ}
    (hopt : E.IsOneShotOptimal certificate optimal payoff) (other : E.Chooser)
    {horizon : ℕ} {state : E.State}
    (hother : E.StopsWithin other horizon state) (hoptimal : E.StopsWithin optimal horizon state) :
    (E.runFor other horizon state).expect payoff ≤
      (E.runFor optimal horizon state).expect payoff := by
  rw [← backwardValue_eq_expect_runFor (certificate := certificate) hother,
    ← backwardValue_eq_expect_runFor (certificate := certificate) hoptimal]
  exact backwardValue_le_of_isOneShotOptimal hopt other state

end ExecutionProtocol

end GameTheory.Protocol
