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
import GameTheory.Protocol.Strategic
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Protocol

open Probability

universe uι us ua uc uo

variable {ι : Type uι} {E : ExecutionProtocol ι}

/-- What a deviator faces at one decision point: where each of its choices
leads, and what the rest of the game is worth from there.

This is the open-game context `X × (Y → R)` with the co-outcome channel `S`
removed, because nothing consumes that channel. The
belief over hidden states and the other players' behaviour are folded into
`outcome`; `ExecutionProtocol.Context.ofBelief` builds one that way. -/
structure Context (Choice : Type uc) (Outcome : Type uo) where
  /-- The outcome law induced by each of the deviator's choices, with everyone
  else's behaviour already folded in. -/
  outcome : Choice → FinDist Outcome
  /-- What the rest of the game is worth from each outcome. -/
  continuation : Outcome → ℝ

namespace Context

variable {Choice : Type uc} {Outcome : Type uo}

/-- The value of a choice: its induced law, evaluated against the
continuation. -/
def value (ctx : Context Choice Outcome) (choice : Choice) : ℝ :=
  (ctx.outcome choice).expect ctx.continuation

/-- A choice is locally optimal among `allowed` when nothing allowed is worth
more. This is a definition over the context's two fields. -/
def IsLocallyOptimal (ctx : Context Choice Outcome) (allowed : Set Choice)
    (choice : Choice) : Prop :=
  ∀ alternative ∈ allowed, ctx.value alternative ≤ ctx.value choice

/-- A one-shot deviation is profitable when some allowed alternative is worth
strictly more than the call actually made. -/
def IsProfitableDeviation (ctx : Context Choice Outcome) (allowed : Set Choice)
    (choice alternative : Choice) : Prop :=
  alternative ∈ allowed ∧ ctx.value choice < ctx.value alternative

/-- **The one-shot-deviation interface.** Local optimality is exactly the
absence of a profitable one-shot deviation. Both sides are derived from
`value`; neither is stored. -/
theorem isLocallyOptimal_iff_no_profitable_deviation (ctx : Context Choice Outcome)
    (allowed : Set Choice) (choice : Choice) :
    ctx.IsLocallyOptimal allowed choice ↔
      ¬ ∃ alternative, ctx.IsProfitableDeviation allowed choice alternative := by
  constructor
  · rintro hopt ⟨alternative, hmem, hlt⟩
    exact absurd (hopt alternative hmem) (not_le.2 hlt)
  · intro hnone alternative hmem
    by_contra hgt
    exact hnone ⟨alternative, hmem, not_le.1 hgt⟩

/-- Local optimality only depends on the context through `value`. -/
theorem isLocallyOptimal_congr {first second : Context Choice Outcome}
    {allowed : Set Choice} {choice : Choice}
    (hvalue : ∀ option, first.value option = second.value option) :
    first.IsLocallyOptimal allowed choice ↔ second.IsLocallyOptimal allowed choice := by
  constructor <;> intro hopt alternative hmem
  · rw [← hvalue, ← hvalue]; exact hopt alternative hmem
  · rw [hvalue, hvalue]; exact hopt alternative hmem

end Context

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
  unfold GameTheory.Protocol.Context.value
  rw [ofBelief_outcome, ofBelief_outcome, hbind]
  rfl

/-- The value under a belief is the belief-average of the state-wise values. -/
theorem ofBelief_value (belief : FinDist E.State)
    (branch : E.State → Option (E.Action i) → FinDist E.State)
    (continuation : E.State → ℝ) (choice : Option (E.Action i)) :
    (ofBelief belief branch continuation).value choice =
      belief.expect fun state => (branch state choice).expect continuation := by
  unfold GameTheory.Protocol.Context.value
  rw [ofBelief_outcome, FinDist.expect_bind]
  rfl

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
      ¬ ∃ alternative,
        ctx.IsProfitableDeviation Set.univ (policy info) alternative :=
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

/-! ## Information-local one-shot deviations

The state-indexed principle in `Backward` is deliberately not reused here:
information-local policies are run on histories, and a finite horizon supplies
the induction measure directly. A one-shot change replaces one typed choice at
the current information state, takes exactly one protocol step, and then
returns to the original profile. -/

variable [DecidableEq ι]

/-- Replace one player's choice at the information state reached by `h`, without
changing that player's policy anywhere else. -/
def oneShotProfile (profile : Profile M.strategicSignature) (h : E.History)
    (who : ι) [DecidableEq (M.InfoState who)]
    (choice : M.Choice who (M.infoOf who h.trace)) :
    Profile M.strategicSignature :=
  Profile.update profile who
    ((profile who).replaceAt (M.infoOf who h.trace) choice)

@[simp]
theorem oneShotProfile_same (profile : Profile M.strategicSignature)
    (h : E.History) (who : ι) [DecidableEq (M.InfoState who)]
    (choice : M.Choice who (M.infoOf who h.trace)) :
    M.oneShotProfile profile h who choice who =
      (profile who).replaceAt (M.infoOf who h.trace) choice :=
  Profile.update_same ..

@[simp]
theorem oneShotProfile_of_ne (profile : Profile M.strategicSignature)
    (h : E.History) (who : ι) [DecidableEq (M.InfoState who)]
    (choice : M.Choice who (M.infoOf who h.trace))
    {other : ι} (hne : other ≠ who) :
    M.oneShotProfile profile h who choice other = profile other :=
  Profile.update_of_ne _ _ hne

@[simp]
theorem oneShotProfile_eq_self (profile : Profile M.strategicSignature)
    (h : E.History) (who : ι) [DecidableEq (M.InfoState who)] :
    M.oneShotProfile profile h who
        (profile who (M.infoOf who h.trace)) =
      profile := by
  simp [InformationModel.oneShotProfile]

/-- At the current history, replacing a whole policy is observationally the
same as replacing just the choice that policy makes there. -/
theorem historyChooser_update_eq_oneShotProfile
    (profile : Profile M.strategicSignature) (h : E.History)
    (hterm : ¬ E.terminal h.state) (who : ι)
    [DecidableEq (M.InfoState who)] (alternative : M.Policy who) :
    M.historyChooser (Profile.update profile who alternative) h hterm =
      M.historyChooser
        (M.oneShotProfile profile h who
          (alternative (M.infoOf who h.trace))) h hterm := by
  apply Subtype.ext
  funext other
  by_cases hwho : other = who
  · subst other
    simp [InformationModel.historyChooser, InformationModel.jointAt,
      Policy.act]
  · simp [InformationModel.historyChooser, InformationModel.jointAt,
      Policy.act, hwho]

/-- The history law of one information-local deviation now: take the altered
joint action once, then continue with the original profile for `fuel` steps. -/
def oneShotLaw (profile : Profile M.strategicSignature) (fuel : ℕ)
    (h : E.History) (hterm : ¬ E.terminal h.state) (who : ι)
    [DecidableEq (M.InfoState who)]
    (choice : M.Choice who (M.infoOf who h.trace)) : FinDist E.History :=
  let changed := M.oneShotProfile profile h who choice
  let chosen := M.historyChooser changed h hterm
  (E.step h.state chosen).bindOnSupport fun _ realized =>
    M.runFrom profile fuel (h.extend chosen.2 realized)

/-- The actual assessment faced at one history. Its outcome is the next
history, not merely the next state, so continuation play may distinguish two
histories that merge into the same execution state without exposing either
history or state to the policy. -/
def historyContext (profile : Profile M.strategicSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (payoff : E.History → ℝ) (fuel : ℕ) (h : E.History)
    (hterm : ¬ E.terminal h.state) :
    GameTheory.Protocol.Context
      (M.Choice who (M.infoOf who h.trace)) E.History where
  outcome choice :=
    let changed := M.oneShotProfile profile h who choice
    let chosen := M.historyChooser changed h hterm
    (E.step h.state chosen).bindOnSupport fun _ realized =>
      FinDist.pure (h.extend chosen.2 realized)
  continuation next := (M.runFrom profile fuel next).expect payoff

/-- Evaluating a typed choice in the history context is exactly evaluating its
one-shot law. This is the profile-plus-continuation bridge that the earlier
state-only context could not express after histories merge. -/
theorem historyContext_value (profile : Profile M.strategicSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (payoff : E.History → ℝ) (fuel : ℕ) (h : E.History)
    (hterm : ¬ E.terminal h.state)
    (choice : M.Choice who (M.infoOf who h.trace)) :
    (M.historyContext profile who payoff fuel h hterm).value choice =
      (M.oneShotLaw profile fuel h hterm who choice).expect payoff := by
  let changed := M.oneShotProfile profile h who choice
  let chosen := M.historyChooser changed h hterm
  show
    ((E.step h.state chosen).bindOnSupport fun _ realized =>
      FinDist.pure (h.extend chosen.2 realized)).expect
        (fun next => (M.runFrom profile fuel next).expect payoff) =
      ((E.step h.state chosen).bindOnSupport fun _ realized =>
        M.runFrom profile fuel (h.extend chosen.2 realized)).expect payoff
  exact FinDist.expect_bindOnSupport_congr fun _ _ => FinDist.expect_pure ..

/-- Replacing the current choice by the choice already prescribed by the
profile leaves the current joint action unchanged. -/
theorem historyChooser_oneShotProfile_self
    (profile : Profile M.strategicSignature) (h : E.History)
    (hterm : ¬ E.terminal h.state) (who : ι)
    [DecidableEq (M.InfoState who)] :
    M.historyChooser profile h hterm =
      M.historyChooser
        (M.oneShotProfile profile h who
          (profile who (M.infoOf who h.trace))) h hterm := by
  rw [M.oneShotProfile_eq_self]

/-- The one-shot law for the profile's own current choice is exactly its
ordinary successor run. -/
theorem oneShotLaw_self (profile : Profile M.strategicSignature) (fuel : ℕ)
    (h : E.History) (hterm : ¬ E.terminal h.state) (who : ι)
    [DecidableEq (M.InfoState who)] :
    M.oneShotLaw profile fuel h hterm who
        (profile who (M.infoOf who h.trace)) =
      M.runFrom profile (fuel + 1) h := by
  let changed :=
    M.oneShotProfile profile h who (profile who (M.infoOf who h.trace))
  let chosen := M.historyChooser changed h hterm
  have hchosen : M.historyChooser profile h hterm = chosen := by
    dsimp only [chosen, changed]
    exact M.historyChooser_oneShotProfile_self profile h hterm who
  rw [M.runFrom_succ_of_chooser_eq profile hterm chosen hchosen fuel]
  rfl

/-- Every information-local one-shot deviation within the compiled horizon is
weakly worse than following `profile` immediately.

The continuation fuel is coupled to the history depth: a history of depth `d`
is compared with `fuel + 1` steps remaining only when
`d + fuel + 1 = horizon`.  Thus unfinished histories are never evaluated as if
they occurred at several incompatible times in the same finite game.  The
condition is still sequential: it quantifies over every legal history at the
appropriate depth, not only histories reached by `profile`. -/
def IsOneShotOptimalWithin (profile : Profile M.strategicSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (payoff : E.History → ℝ) (horizon : ℕ) : Prop :=
  ∀ fuel (h : E.History), h.trace.length + fuel + 1 = horizon →
    ∀ (hterm : ¬ E.terminal h.state)
    (choice : M.Choice who (M.infoOf who h.trace)),
      (M.oneShotLaw profile fuel h hterm who choice).expect payoff ≤
        (M.runFrom profile (fuel + 1) h).expect payoff

/-- The quantified one-shot condition is exactly sequential rationality in the
history context at every decision history and remaining horizon. -/
theorem isOneShotOptimalWithin_iff_sequentiallyRationalAt_historyContext
    (profile : Profile M.strategicSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (payoff : E.History → ℝ) (horizon : ℕ) :
    M.IsOneShotOptimalWithin profile who payoff horizon ↔
      ∀ fuel (h : E.History), h.trace.length + fuel + 1 = horizon →
        ∀ (hterm : ¬ E.terminal h.state),
        M.IsSequentiallyRationalAt
          (profile who) (M.infoOf who h.trace)
          (M.historyContext profile who payoff fuel h hterm) := by
  constructor
  · intro hopt fuel h hdepth hterm alternative _
    rw [M.historyContext_value, M.historyContext_value, M.oneShotLaw_self]
    exact hopt fuel h hdepth hterm alternative
  · intro hseq fuel h hdepth hterm choice
    have hlocal := hseq fuel h hdepth hterm choice (Set.mem_univ _)
    rw [M.historyContext_value, M.historyContext_value, M.oneShotLaw_self] at hlocal
    exact hlocal

/-- **Finite-horizon information-local one-shot principle, forward
direction.** If no current information-local choice improves play at any
history, then no replacement policy for that player improves the induced
history law. -/
theorem expect_runFrom_update_le_of_isOneShotOptimalWithin
    (profile : Profile M.strategicSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (payoff : E.History → ℝ) (horizon : ℕ)
    (hopt : M.IsOneShotOptimalWithin profile who payoff horizon)
    (alternative : M.Policy who) {fuel : ℕ} (h : E.History)
    (hdepth : h.trace.length + fuel = horizon) :
    (M.runFrom (Profile.update profile who alternative) fuel h).expect payoff ≤
      (M.runFrom profile fuel h).expect payoff := by
  induction fuel generalizing h with
  | zero =>
      simp [InformationModel.runFrom, ExecutionProtocol.runHistoryFor]
  | succ fuel ih =>
      by_cases hterm : E.terminal h.state
      · rw [InformationModel.runFrom, InformationModel.runFrom,
          ExecutionProtocol.runHistoryFor_of_terminal _ _ hterm,
          ExecutionProtocol.runHistoryFor_of_terminal _ _ hterm]
      · let choice := alternative (M.infoOf who h.trace)
        let changed := M.oneShotProfile profile h who choice
        let chosen := M.historyChooser changed h hterm
        have hchosen :
            M.historyChooser (Profile.update profile who alternative) h hterm =
              chosen := by
          dsimp only [chosen, changed, choice]
          exact M.historyChooser_update_eq_oneShotProfile profile h hterm who alternative
        rw [M.runFrom_succ_of_chooser_eq
          (Profile.update profile who alternative) hterm chosen hchosen fuel]
        calc
          ((E.step h.state chosen).bindOnSupport fun _ realized =>
              M.runFrom (Profile.update profile who alternative) fuel
                (h.extend chosen.2 realized)).expect payoff
              ≤ ((E.step h.state chosen).bindOnSupport fun _ realized =>
                  M.runFrom profile fuel (h.extend chosen.2 realized)).expect payoff :=
            FinDist.expect_bindOnSupport_mono fun _ realized =>
              ih (h.extend chosen.2 realized) (by
                simp only [ExecutionProtocol.History.extend,
                  ExecutionProtocol.Trace.length]
                omega)
          _ = (M.oneShotLaw profile fuel h hterm who choice).expect payoff := by
            rfl
          _ ≤ (M.runFrom profile (fuel + 1) h).expect payoff :=
            hopt fuel h (by omega) hterm choice

/-- The static consequence of the information-local one-shot principle.
Compiling the same policy profile introduces no new equilibrium notion: local
optimality at every history implies ordinary expected-utility Nash in the
finite-horizon `GameForm`. -/
theorem isNash_toGameForm_of_isOneShotOptimalWithin
    [∀ i, DecidableEq (M.InfoState i)]
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ) (horizon : ℕ)
    (hopt : ∀ who,
      M.IsOneShotOptimalWithin profile who (fun h => utility h who) horizon) :
    IsNash (M.toGameForm horizon) (euPreference utility) profile := by
  rw [isNash_iff]
  intro who alternative
  simpa [expectedUtility, InformationModel.run] using
    M.expect_runFrom_update_le_of_isOneShotOptimalWithin
      profile who (fun h => utility h who) horizon (hopt who) alternative
      E.initHistory (by
        simp [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length])

end InformationModel

end GameTheory.Protocol
