/-
# Strategic-form compilation

The bridge from the protocol layer to the static core. There are two entry
points, reflecting two genuinely different strategy types already present in
the sequential layer.

* An `ExecutionProtocol` compiles state-indexed `StatePolicy` strategies through
  `runFor`. This is the perfect-information presentation retained for users
  whose strategy really may read the execution state.
* An `InformationModel` compiles information-local `Policy` strategies through
  the history-indexed `run`. Its outcomes are full histories: forgetting to the
  terminal state is then the ordinary `GameForm.mapOutcome History.state`, while
  compiling directly to states would irreversibly discard observable history.

The information-local mixed presentation is not a second compiler:
`GameForm.mixed` of the pure-policy form reduces exactly to `runMixed`.
Behavioral strategies are a distinct presentation because they draw locally
during play, and their form uses `runBehavioral`. The existing behavioral/mixed
law theorems connect those presentations under exactly their respective
conditions.

Every static concept applies unchanged to either compiled form. The compiler
knows about strategies and induced laws; it introduces no protocol-specific
equilibrium predicate.
-/

import GameTheory.Protocol.Extraction
import GameTheory.Protocol.Information
import GameTheory.Core.Form
import GameTheory.Core.Equilibrium
import GameTheory.Protocol.DecisionPlan

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability GameTheory

universe uι us ua

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

variable (E) in
/-- What one player does wherever it is active. This is the
perfect-information strategy: it may read the state, because at perfect
information the state is what the player knows. -/
def StatePolicy (i : ι) : Type _ :=
  (state : E.State) → E.active state i → { a : E.Action i // a ∈ E.available state i }

open Classical in
/-- The joint action a profile of state policies produces: active players act,
inactive players stand down. -/
def jointOf (profile : (i : ι) → E.StatePolicy i) (state : E.State) :
    ∀ i, Option (E.Action i) :=
  fun i => if hactive : E.active state i then some (profile i state hactive).1 else none

open Classical in
theorem jointOf_isLegal (profile : (i : ι) → E.StatePolicy i) (state : E.State) :
    IsLegalJoint (E.active state) (E.available state) (E.jointOf profile state) := by
  intro i
  by_cases hactive : E.active state i
  · simp [jointOf, hactive, (profile i state hactive).2]
  · simp [jointOf, hactive]

/-- A profile of state policies is a chooser. -/
def chooserOf (profile : (i : ι) → E.StatePolicy i) : E.Chooser :=
  fun state hterm => ⟨E.jointOf profile state, hterm, E.jointOf_isLegal profile state⟩

variable (E) in
/-- The signature of the compiled game: strategies are state policies, outcomes
are the states play can stop in. -/
abbrev strategicSignature : GameSignature ι where
  Strategy := E.StatePolicy
  Outcome := E.State

variable (E) in
/-- **The compilation.** A protocol and a horizon become a `GameForm`.

Reducible so that the compiled form's outcome carrier reduces to the protocol's
state type; without it, static concepts stated over the carrier do not match. -/
@[reducible]
def toGameForm (horizon : ℕ) : GameForm ι where
  sig := E.strategicSignature
  play profile := E.runFor (E.chooserOf profile) horizon E.init

/-- The named evaluation fact. A certificate consumer must reuse *this* rather
than reprove the run law. -/
@[simp]
theorem toGameForm_play (horizon : ℕ) (profile : Profile E.strategicSignature) :
    (E.toGameForm horizon).play profile =
      E.runFor (E.chooserOf profile) horizon E.init := rfl

@[simp]
theorem toGameForm_sig (horizon : ℕ) :
    (E.toGameForm horizon).sig = E.strategicSignature := rfl

/-- Past a horizon at which play has stopped, the compiled form no longer
depends on the horizon. This is what turns a fuelled compilation into a
well-defined strategic form. -/
theorem toGameForm_play_eq_of_stopsWithin {horizon fuel : ℕ}
    (profile : Profile E.strategicSignature)
    (hstop : E.StopsWithin (E.chooserOf profile) horizon E.init) (hle : horizon ≤ fuel) :
    (E.toGameForm fuel).play profile = (E.toGameForm horizon).play profile :=
  runFor_eq_of_stopsWithin_le hstop hle

/-- Only behaviour at reachable decision sites is visible in the compiled form.
This is the compiled counterpart of `runFor_congr_of_restrict_eq`. -/
theorem toGameForm_play_congr {horizon : ℕ}
    {first second : Profile E.strategicSignature}
    (hagree : Chooser.restrict (E.chooserOf first) = Chooser.restrict (E.chooserOf second)) :
    (E.toGameForm horizon).play first = (E.toGameForm horizon).play second :=
  runFor_congr_of_restrict_eq hagree horizon reachable_init

end ExecutionProtocol

namespace InformationModel

variable {E : ExecutionProtocol ι} (M : InformationModel E)

/-- The signature of the information-local strategic form. Strategies receive
only a player's information state, and outcomes retain the realized history. -/
abbrev strategicSignature : GameSignature ι where
  Strategy := M.Policy
  Outcome := E.History

/-- Compile information-local pure policies through the canonical
history-indexed evaluator. Reducibility keeps the strategy and outcome carriers
available to the static core without transports. -/
@[reducible]
def toGameForm (horizon : ℕ) : GameForm ι where
  sig := M.strategicSignature
  play profile := M.run profile horizon

/-- The named evaluation fact for information-local pure strategies. Compiler
consumers should quote this theorem rather than unfold the form. -/
@[simp]
theorem toGameForm_play (horizon : ℕ) (profile : Profile M.strategicSignature) :
    (M.toGameForm horizon).play profile = M.run profile horizon := rfl

@[simp]
theorem toGameForm_sig (horizon : ℕ) :
    (M.toGameForm horizon).sig = M.strategicSignature := rfl

variable [Fintype ι]

/-- Present behavioral strategies to the static core without defining another
runner: evaluation is exactly `InformationModel.runBehavioral`. -/
@[reducible]
def toBehavioralGameForm (horizon : ℕ) : GameForm ι where
  sig := M.behavioralSignature
  play profile := M.runBehavioral profile horizon

/-- The named evaluation fact for behavioral strategies. -/
@[simp]
theorem toBehavioralGameForm_play (horizon : ℕ)
    (profile : Profile M.behavioralSignature) :
    (M.toBehavioralGameForm horizon).play profile = M.runBehavioral profile horizon := rfl

@[simp]
theorem toBehavioralGameForm_sig (horizon : ℕ) :
    (M.toBehavioralGameForm horizon).sig = M.behavioralSignature := rfl

/-! ## The two randomization presentations

A `MixedPolicy i` is definitionally `PMF (M.Policy i)`. Consequently the
ordinary static mixed extension of `M.toGameForm` already has exactly the right
strategy type and evaluator: draw one pure policy profile, then call `M.run`.
There is deliberately no `toMixedGameForm`.

A behavioral policy instead draws whenever its information state is consulted.
That is not `GameForm.mixed` in general. The equalities below state precisely
when the two presentations induce the same law; the hypotheses cannot be
dropped, as the repeated-information-set test demonstrates.
-/

/-- Static mixing of the pure-policy compilation is exactly the existing mixed
history evaluator, not a parallel semantics. -/
@[simp]
theorem toGameForm_mixed_play (horizon : ℕ)
    (mixed : (i : ι) → M.MixedPolicy i) :
    ((M.toGameForm horizon).mixed).play mixed = M.runMixed mixed horizon := rfl

/-- Behavioral play restricts to pure play when every local law is a point
mass. -/
@[simp]
theorem toBehavioralGameForm_play_toBehavioral
    (profile : Profile M.strategicSignature) (horizon : ℕ) :
    (M.toBehavioralGameForm horizon).play (fun i => (profile i).toBehavioral) =
      (M.toGameForm horizon).play profile := by
  rw [toBehavioralGameForm_play, toGameForm_play]
  simpa only [runBehavioral, run] using
    M.runBehavioralFrom_toBehavioral profile horizon E.initHistory


omit [Fintype ι] in
/-- Agreement at decision sites preserves every pure strategic outcome law. -/
theorem toGameForm_play_eq_of_agreesAtDecisions
    {first second : Profile M.strategicSignature}
    (agree : ∀ who, (first who).AgreesAtDecisions (second who)) (horizon : ℕ) :
    (M.toGameForm horizon).play first = (M.toGameForm horizon).play second :=
  M.runFrom_eq_of_agreesAtDecisions agree horizon E.initHistory

/-- Agreement at decision sites preserves every behavioral strategic outcome law. -/
theorem toBehavioralGameForm_play_eq_of_agreesAtDecisions
    {first second : Profile M.behavioralSignature}
    (agree : ∀ who, (first who).AgreesAtDecisions (second who)) (horizon : ℕ) :
    (M.toBehavioralGameForm horizon).play first =
      (M.toBehavioralGameForm horizon).play second :=
  M.runBehavioralFrom_eq_of_agreesAtDecisions agree horizon E.initHistory

omit [Fintype ι] in
/-- Pure Nash equilibrium depends only on the policies' decision-site choices. -/
theorem isNash_toGameForm_iff_of_agreesAtDecisions [DecidableEq ι]
    {first second : Profile M.strategicSignature}
    (agree : ∀ who, (first who).AgreesAtDecisions (second who))
    (horizon : ℕ) (preference : WeakPreference ι E.History) :
    IsNash (M.toGameForm horizon) preference first ↔
      IsNash (M.toGameForm horizon) preference second := by
  rw [isNash_iff, isNash_iff]
  have incumbent : M.run first horizon = M.run second horizon :=
    M.toGameForm_play_eq_of_agreesAtDecisions agree horizon
  have deviations : ∀ who replacement,
      M.run (Profile.update first who replacement) horizon =
        M.run (Profile.update second who replacement) horizon := by
    intro who replacement
    apply M.toGameForm_play_eq_of_agreesAtDecisions
    intro player
    by_cases same : player = who
    · subst player
      simp [Policy.AgreesAtDecisions]
    · simpa only [Profile.update_of_ne _ _ same] using agree player
  simp only [incumbent, deviations]

/-- Behavioral Nash equilibrium depends only on the laws at decision sites. -/
theorem isNash_toBehavioralGameForm_iff_of_agreesAtDecisions [DecidableEq ι]
    {first second : Profile M.behavioralSignature}
    (agree : ∀ who, (first who).AgreesAtDecisions (second who))
    (horizon : ℕ) (preference : WeakPreference ι E.History) :
    IsNash (M.toBehavioralGameForm horizon) preference first ↔
      IsNash (M.toBehavioralGameForm horizon) preference second := by
  rw [isNash_iff, isNash_iff]
  have incumbent : M.runBehavioral first horizon = M.runBehavioral second horizon :=
    M.toBehavioralGameForm_play_eq_of_agreesAtDecisions agree horizon
  have deviations : ∀ who replacement,
      M.runBehavioral (Profile.update first who replacement) horizon =
        M.runBehavioral (Profile.update second who replacement) horizon := by
    intro who replacement
    apply M.toBehavioralGameForm_play_eq_of_agreesAtDecisions
    intro player
    by_cases same : player = who
    · subst player
      simp [BehavioralPolicy.AgreesAtDecisions]
    · simpa only [Profile.update_of_ne _ _ same] using agree player
  simp only [incumbent, deviations]

end InformationModel

end GameTheory.Protocol
