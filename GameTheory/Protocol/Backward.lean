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
* `backwardLaw` is the substantive instantiation: the terminal PMF of a fixed
  chooser, assembled through support-dependent continuation kernels. It needs
  neither finite branching nor a real payoff.
* `backwardValue` reads that law through a finite-real integrability guard.
  The one-shot context compares actual terminal laws, never padded successor
  values or a totalized divergent real sum.
* `backwardLaw_eq_runFor` joins the two halves before any payoff is introduced:
  wherever the fuelled runner has stopped, its law is the backward law.

The discriminating fixture lives in `GameTheory.Tests.Backward`, so stable
importers compile only the semantic definitions and proofs in this module.
-/

import GameTheory.Protocol.Execution
import GameTheory.Protocol.Context
import GameTheory.Math.Probability.ExpectationBind

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

/-! ## Terminal laws by well-founded recursion -/

variable (E) in
open Classical in
/-- The terminal-state law induced by a fixed chooser. The continuation
kernel receives exactly the proof that each drawn target is a successor. -/
def backwardLaw (certificate : E.WellFoundedPlay) (chooser : E.Chooser) :
    E.State → PMF E.State :=
  E.backwardRec certificate fun source successorLaw =>
    if hterm : E.terminal source then PMF.pure source
    else (E.step source (chooser source hterm)).bindOnSupport
      fun target realized =>
        successorLaw target
          ⟨(chooser source hterm).1, (chooser source hterm).2, realized⟩

variable {certificate : E.WellFoundedPlay} {chooser : E.Chooser}

open Classical in
/-- The law unfolds through the same successor relation as `backwardRec`. -/
theorem backwardLaw_eq (source : E.State) :
    E.backwardLaw certificate chooser source =
      if hterm : E.terminal source then PMF.pure source
      else (E.step source (chooser source hterm)).bindOnSupport
        fun target _ => E.backwardLaw certificate chooser target := by
  rw [backwardLaw, backwardRec_eq]

/-- Terminal states are absorbed without consulting the chooser. -/
theorem backwardLaw_of_terminal {source : E.State}
    (hterm : E.terminal source) :
    E.backwardLaw certificate chooser source = PMF.pure source := by
  rw [backwardLaw_eq, dite_eq_left hterm]

/-- A nonterminal law binds exactly the realized successor continuations. -/
theorem backwardLaw_of_not_terminal {source : E.State}
    (hterm : ¬ E.terminal source) :
    E.backwardLaw certificate chooser source =
      (E.step source (chooser source hterm)).bindOnSupport
        fun target _ => E.backwardLaw certificate chooser target := by
  rw [backwardLaw_eq, dite_eq_right hterm]

theorem backwardLaw_of_not_terminal_bind {source : E.State}
    (hterm : ¬ E.terminal source) :
    E.backwardLaw certificate chooser source =
      (E.step source (chooser source hterm)).bind
        (E.backwardLaw certificate chooser) := by
  rw [backwardLaw_of_not_terminal hterm, PMF.bindOnSupport_eq_bind]

/-- Whenever the forward run has stopped, its law is the backward law.
The equality is unconditional on the payoff and has no branching finiteness
assumption. -/
theorem backwardLaw_eq_runFor {horizon : ℕ} {state : E.State}
    (hstop : E.StopsWithin chooser horizon state) :
    E.backwardLaw certificate chooser state =
      E.runFor chooser horizon state := by
  induction horizon generalizing state with
  | zero =>
      have hterm : E.terminal state :=
        hstop state (by simp [runFor])
      rw [backwardLaw_of_terminal hterm, runFor_zero]
  | succ horizon ih =>
      by_cases hterm : E.terminal state
      · rw [backwardLaw_of_terminal hterm,
          runFor_of_terminal chooser _ hterm]
      · rw [backwardLaw_of_not_terminal hterm,
          runFor_succ_of_not_terminal chooser horizon hterm]
        apply bindOnSupport_eq_bind_of_eq_on_support
        intro target htarget
        apply ih
        intro final hfinal
        apply hstop final
        rw [runFor_succ_of_not_terminal chooser horizon hterm,
          PMF.support_bind]
        exact Set.mem_iUnion₂.mpr ⟨target, htarget, hfinal⟩

/-- Every state supported by the well-founded backward law is terminal,
including when no uniform stopping horizon exists. -/
theorem backwardLaw_support_terminal (state : E.State) :
    ∀ target ∈ (E.backwardLaw certificate chooser state).support,
      E.terminal target := by
  induction state using certificate.induction with
  | _ source ih =>
      intro target htarget
      by_cases hterm : E.terminal source
      · rw [backwardLaw_of_terminal hterm,
          PMF.mem_support_pure_iff] at htarget
        subst target
        exact hterm
      · rw [backwardLaw_of_not_terminal hterm,
          PMF.mem_support_bindOnSupport_iff] at htarget
        obtain ⟨reached, hrealized, hcontinue⟩ := htarget
        apply ih reached
          ⟨(chooser source hterm).1, (chooser source hterm).2, hrealized⟩
        exact hcontinue

/-- A finite real backward value exists only for an integrable terminal-law
payoff. The terminal law remains meaningful when this guard fails. -/
def backwardValue (certificate : E.WellFoundedPlay) (chooser : E.Chooser)
    (payoff : E.State → ℝ) (state : E.State)
    (hintegrable : PayoffIntegrable (E.backwardLaw certificate chooser state) payoff) :
    ℝ :=
  expect (E.backwardLaw certificate chooser state) payoff hintegrable

theorem backwardValue_eq_expect_runFor
    {certificate : E.WellFoundedPlay} {chooser : E.Chooser}
    {payoff : E.State → ℝ} {horizon : ℕ} {state : E.State}
    (hstop : E.StopsWithin chooser horizon state)
    (hback : PayoffIntegrable (E.backwardLaw certificate chooser state) payoff)
    (hforward : PayoffIntegrable (E.runFor chooser horizon state) payoff) :
    E.backwardValue certificate chooser payoff state hback =
      expect (E.runFor chooser horizon state) payoff hforward := by
  unfold backwardValue expect
  rw [E.backwardLaw_eq_runFor hstop]

theorem backwardValue_of_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.Chooser}
    {payoff : E.State → ℝ} {source : E.State}
    (hterm : E.terminal source)
    (hintegrable : PayoffIntegrable
      (E.backwardLaw certificate chooser source) payoff) :
    E.backwardValue certificate chooser payoff source hintegrable =
      payoff source := by
  have hpure : PayoffIntegrable (PMF.pure source) payoff := by
    rw [← E.backwardLaw_of_terminal hterm]
    exact hintegrable
  calc
    E.backwardValue certificate chooser payoff source hintegrable =
        expect (PMF.pure source) payoff hpure := by
          unfold backwardValue expect
          rw [E.backwardLaw_of_terminal hterm]
    _ = payoff source := expect_pure source payoff hpure

/-- Numerical Bellman equation at the supported successors of a nonterminal
state. The joint terminal-law guard derives every conditional and outer guard. -/
theorem backwardValue_of_not_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.Chooser}
    {payoff : E.State → ℝ} {source : E.State}
    (hterm : ¬ E.terminal source)
    (hsource : PayoffIntegrable (E.backwardLaw certificate chooser source) payoff)
    (successorValue : E.State → ℝ)
    (hvalue : ∀ target, ∀ ht :
      target ∈ (E.step source (chooser source hterm)).support,
      successorValue target =
        E.backwardValue certificate chooser payoff target
          (payoffIntegrable_bind_conditional_on_support
            (E.step source (chooser source hterm))
            (E.backwardLaw certificate chooser) payoff
            (by rwa [← E.backwardLaw_of_not_terminal_bind hterm]) target ht)) :
    ∃ houter : PayoffIntegrable
        (E.step source (chooser source hterm)) successorValue,
      E.backwardValue certificate chooser payoff source hsource =
        expect (E.step source (chooser source hterm)) successorValue houter := by
  let p := E.step source (chooser source hterm)
  let q := E.backwardLaw certificate chooser
  have hbind : PayoffIntegrable (p.bind q) payoff := by
    rw [← E.backwardLaw_of_not_terminal_bind hterm]
    exact hsource
  have hcond : ∀ target, ∀ ht : target ∈ p.support,
      successorValue target = expect (q target) payoff
        (payoffIntegrable_bind_conditional_on_support p q payoff hbind target ht) := by
    intro target ht
    simpa only [backwardValue] using hvalue target ht
  let houter := payoffIntegrable_bind_conditionalValue_on_support
    p q payoff hbind successorValue hcond
  refine ⟨houter, ?_⟩
  have htower := expect_bind_tower_on_support
    p q payoff hbind successorValue hcond
  unfold backwardValue expect at htower ⊢
  rw [E.backwardLaw_of_not_terminal_bind hterm]
  exact htower

/-- One legal action followed by the incumbent chooser's backward terminal
law. The context compares actual outcome laws under the same payoff. -/
def oneShotContext (certificate : E.WellFoundedPlay) (chooser : E.Chooser)
    (payoff : E.State → ℝ) (source : E.State)
    (_hterm : ¬ E.terminal source) :
    GameTheory.Protocol.Context
      { joint : ∀ i, Option (E.Action i) // E.Legal source joint } E.State where
  outcome alternative :=
    (E.step source alternative).bind (E.backwardLaw certificate chooser)
  continuation := payoff

/-- At a nonterminal state, the incumbent one-shot law is precisely its
backward law. -/
theorem oneShotContext_incumbentLaw
    {certificate : E.WellFoundedPlay} {chooser : E.Chooser}
    {payoff : E.State → ℝ} {source : E.State}
    (hterm : ¬ E.terminal source) :
    (E.oneShotContext certificate chooser payoff source hterm).outcome
        (chooser source hterm) =
      E.backwardLaw certificate chooser source := by
  rw [backwardLaw_of_not_terminal hterm]
  simpa only [oneShotContext] using
    (bindOnSupport_eq_bind_of_eq_on_support
      (μ := E.step source (chooser source hterm))
      (g := E.backwardLaw certificate chooser)
      (fun _ _ => rfl)).symm

/-- Every legal one-step replacement has a defined finite real payoff, and
none improves over the incumbent's whole continuation law. -/
def IsOneShotOptimal (certificate : E.WellFoundedPlay)
    (chooser : E.Chooser) (payoff : E.State → ℝ) : Prop :=
  ∀ (source : E.State) (hterm : ¬ E.terminal source),
    (E.oneShotContext certificate chooser payoff source hterm).IsLocallyOptimal
      Set.univ (chooser source hterm)

/-- The incumbent law is integrable at every state under guarded one-shot
optimality. At terminal states this follows from the pure law. -/
theorem IsOneShotOptimal.integrable
    {certificate : E.WellFoundedPlay} {chooser : E.Chooser}
    {payoff : E.State → ℝ}
    (hoptimal : E.IsOneShotOptimal certificate chooser payoff)
    (source : E.State) :
    PayoffIntegrable (E.backwardLaw certificate chooser source) payoff := by
  by_cases hterm : E.terminal source
  · rw [E.backwardLaw_of_terminal hterm]
    exact payoffIntegrable_pure source payoff
  · have hctx : PayoffIntegrable
        ((E.oneShotContext certificate chooser payoff source hterm).outcome
          (chooser source hterm)) payoff :=
      (hoptimal source hterm).1
    rwa [E.oneShotContext_incumbentLaw hterm] at hctx

/-- Guarded one-shot optimality compares the incumbent with any chooser whose
terminal law has a finite real value at each state. -/
theorem backwardValue_le_of_isOneShotOptimal
    {certificate : E.WellFoundedPlay} {optimal : E.Chooser}
    {payoff : E.State → ℝ}
    (hopt : E.IsOneShotOptimal certificate optimal payoff)
    (other : E.Chooser)
    (state : E.State)
    (hother : PayoffIntegrable
      (E.backwardLaw certificate other state) payoff) :
    E.backwardValue certificate other payoff state hother ≤
      E.backwardValue certificate optimal payoff state (hopt.integrable state) := by
  induction state using certificate.induction with
  | _ source ih =>
      by_cases hterm : E.terminal source
      · unfold backwardValue expect
        rw [E.backwardLaw_of_terminal hterm,
          E.backwardLaw_of_terminal hterm]
      · let ctx := E.oneShotContext certificate optimal payoff source hterm
        have hlocal := hopt source hterm
        have hright : ctx.IntegrableAt (other source hterm) :=
          hlocal.2.1 _ (Set.mem_univ _)
        have hinc : ctx.IntegrableAt (optimal source hterm) := hlocal.1
        have hbound := hlocal.2.2 (other source hterm)
          (Set.mem_univ _) hinc hright
        have hleft : PayoffIntegrable
            ((E.step source (other source hterm)).bind
              (E.backwardLaw certificate other)) payoff := by
          rw [← E.backwardLaw_of_not_terminal_bind hterm]
          exact hother
        unfold backwardValue
        calc
          expect (E.backwardLaw certificate other source) payoff hother =
              expect ((E.step source (other source hterm)).bind
                (E.backwardLaw certificate other)) payoff hleft := by
              unfold expect
              rw [E.backwardLaw_of_not_terminal_bind hterm]
          _ ≤ expect ((E.step source (other source hterm)).bind
                (E.backwardLaw certificate optimal)) payoff hright := by
              apply expect_bind_mono_on_support
              intro reached hreached
              have hstep : E.Successor reached source :=
                ⟨(other source hterm).1, (other source hterm).2, hreached⟩
              have hconditional := payoffIntegrable_bind_conditional_on_support
                (E.step source (other source hterm))
                (E.backwardLaw certificate other) payoff hleft reached hreached
              simpa only [backwardValue] using ih reached hstep hconditional
          _ ≤ expect (E.backwardLaw certificate optimal source) payoff
                (hopt.integrable source) := by
              unfold Context.value at hbound
              unfold expect at hbound ⊢
              rw [E.oneShotContext_incumbentLaw hterm] at hbound
              exact hbound

variable (E) in
/-- States reachable from a source by realized legal steps, including the source. -/
def Reaches (source target : E.State) : Prop :=
  Relation.ReflTransGen (fun earlier later => E.Successor later earlier) source target

theorem Reaches.refl (state : E.State) : E.Reaches state state :=
  Relation.ReflTransGen.refl

theorem Reaches.step {source middle target : E.State}
    (hstep : E.Successor middle source) (hrest : E.Reaches middle target) :
    E.Reaches source target :=
  Relation.ReflTransGen.head hstep hrest

open Classical in
variable (E) in
/-- Replace one answer at `state`, preserving the chooser everywhere else. -/
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
  rw [dite_eq_left rfl]

theorem deviateAt_of_ne {state source : E.State}
    {replacement : { joint : ∀ i, Option (E.Action i) // E.Legal state joint }}
    {chooser : E.Chooser} (hne : source ≠ state) (hterm : ¬ E.terminal source) :
    E.deviateAt state replacement chooser source hterm = chooser source hterm := by
  classical
  exact dite_eq_right hne

/-- Choosers agreeing on the reachable cone induce the same backward law. -/
theorem backwardLaw_congr_of_reaches {certificate : E.WellFoundedPlay}
    {first second : E.Chooser} :
    ∀ (start : E.State),
      (∀ source, E.Reaches start source → ∀ hterm : ¬ E.terminal source,
        first source hterm = second source hterm) →
      E.backwardLaw certificate first start =
        E.backwardLaw certificate second start := by
  intro start
  induction start using certificate.induction with
  | _ source ih =>
      intro hagree
      by_cases hterm : E.terminal source
      · rw [backwardLaw_of_terminal hterm, backwardLaw_of_terminal hterm]
      · rw [backwardLaw_of_not_terminal hterm,
          backwardLaw_of_not_terminal hterm,
          hagree source (Reaches.refl source) hterm]
        refine bindOnSupport_congr _ fun reached hreached => ?_
        have hstep : E.Successor reached source :=
          ⟨(second source hterm).1, (second source hterm).2, hreached⟩
        exact ih reached hstep fun later hlater =>
          hagree later (Reaches.step hstep hlater)

/-- Numerical values agree when the terminal laws agree on a reachable cone. -/
theorem backwardValue_congr_of_reaches {certificate : E.WellFoundedPlay}
    {first second : E.Chooser} {payoff : E.State → ℝ} (start : E.State)
    (hagree : ∀ source, E.Reaches start source →
      ∀ hterm : ¬ E.terminal source,
        first source hterm = second source hterm)
    (hfirst : PayoffIntegrable (E.backwardLaw certificate first start) payoff)
    (hsecond : PayoffIntegrable (E.backwardLaw certificate second start) payoff) :
    E.backwardValue certificate first payoff start hfirst =
      E.backwardValue certificate second payoff start hsecond := by
  unfold backwardValue expect
  rw [E.backwardLaw_congr_of_reaches start hagree]

/-- A successor cannot reach its predecessor in a well-founded protocol. -/
theorem not_reaches_of_successor {certificate : E.WellFoundedPlay}
    {source target : E.State}
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

/-- A single changed answer produces exactly its one-shot continuation law.
Well-foundedness prevents that answer from being consulted again later. -/
theorem oneShotContext_deviateAtLaw
    {certificate : E.WellFoundedPlay} {chooser : E.Chooser}
    {payoff : E.State → ℝ} {source : E.State}
    (hterm : ¬ E.terminal source)
    (alternative : { joint : ∀ i, Option (E.Action i) // E.Legal source joint }) :
    (E.oneShotContext certificate chooser payoff source hterm).outcome alternative =
      E.backwardLaw certificate (E.deviateAt source alternative chooser) source := by
  rw [backwardLaw_of_not_terminal_bind hterm, deviateAt_self hterm]
  unfold oneShotContext
  apply bind_congr_on_support
  intro reached hreached
  apply E.backwardLaw_congr_of_reaches reached
  intro later hlater hlaterTerm
  symm
  apply E.deviateAt_of_ne
  intro hsame
  subst later
  exact E.not_reaches_of_successor
    (certificate := certificate)
    (⟨alternative.1, alternative.2, hreached⟩ : E.Successor reached source)
    hlater

/-- The converse needs a guarded global comparison: the assumed preference
itself certifies both compared terminal laws, including the local deviation. -/
theorem isOneShotOptimal_of_backwardValue_le
    {certificate : E.WellFoundedPlay} {optimal : E.Chooser}
    {payoff : E.State → ℝ}
    (hbest : ∀ (other : E.Chooser) (state : E.State),
      ∃ hother : PayoffIntegrable
          (E.backwardLaw certificate other state) payoff,
        ∃ hoptimal : PayoffIntegrable
          (E.backwardLaw certificate optimal state) payoff,
          E.backwardValue certificate other payoff state hother ≤
            E.backwardValue certificate optimal payoff state hoptimal) :
    E.IsOneShotOptimal certificate optimal payoff := by
  intro source hterm
  let ctx := E.oneShotContext certificate optimal payoff source hterm
  obtain ⟨_, hinc, _⟩ := hbest optimal source
  have hincCtx : ctx.IntegrableAt (optimal source hterm) := by
    show PayoffIntegrable
      ((E.oneShotContext certificate optimal payoff source hterm).outcome
        (optimal source hterm)) payoff
    rw [E.oneShotContext_incumbentLaw hterm]
    exact hinc
  refine ⟨hincCtx, ?_, ?_⟩
  · intro alternative _
    obtain ⟨hdev, _, _⟩ :=
      hbest (E.deviateAt source alternative optimal) source
    show PayoffIntegrable
      ((E.oneShotContext certificate optimal payoff source hterm).outcome
        alternative) payoff
    rw [E.oneShotContext_deviateAtLaw hterm alternative]
    exact hdev
  · intro alternative _ hinc' halt
    obtain ⟨hdev, hopt', hle⟩ :=
      hbest (E.deviateAt source alternative optimal) source
    show expect
        ((E.oneShotContext certificate optimal payoff source hterm).outcome
          alternative) payoff halt ≤
      expect
        ((E.oneShotContext certificate optimal payoff source hterm).outcome
          (optimal source hterm)) payoff hinc'
    unfold backwardValue expect at hle
    unfold expect
    rw [E.oneShotContext_deviateAtLaw hterm alternative,
      E.oneShotContext_incumbentLaw hterm]
    exact hle

/-- When both forward runs have stopped, guarded one-shot optimality compares
their actual terminal laws. The incumbent integrability certificate is derived. -/
theorem expect_runFor_le_of_isOneShotOptimal
    {certificate : E.WellFoundedPlay} {optimal : E.Chooser}
    {payoff : E.State → ℝ}
    (hopt : E.IsOneShotOptimal certificate optimal payoff)
    (other : E.Chooser) {horizon : ℕ} {state : E.State}
    (hotherStop : E.StopsWithin other horizon state)
    (hoptimalStop : E.StopsWithin optimal horizon state)
    (hother : PayoffIntegrable (E.runFor other horizon state) payoff) :
    ∃ hoptimal : PayoffIntegrable (E.runFor optimal horizon state) payoff,
      expect (E.runFor other horizon state) payoff hother ≤
        expect (E.runFor optimal horizon state) payoff hoptimal := by
  have hotherBack : PayoffIntegrable
      (E.backwardLaw certificate other state) payoff := by
    rw [E.backwardLaw_eq_runFor hotherStop]
    exact hother
  let hoptimal : PayoffIntegrable (E.runFor optimal horizon state) payoff := by
    rw [← E.backwardLaw_eq_runFor hoptimalStop]
    exact hopt.integrable state
  refine ⟨hoptimal, ?_⟩
  have hle := E.backwardValue_le_of_isOneShotOptimal hopt other state hotherBack
  unfold backwardValue expect at hle
  unfold expect
  rw [E.backwardLaw_eq_runFor hotherStop,
    E.backwardLaw_eq_runFor hoptimalStop] at hle
  exact hle

end ExecutionProtocol

end GameTheory.Protocol
