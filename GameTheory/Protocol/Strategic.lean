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

/-- The signature for local randomization at information states. It has the
same history outcomes as the pure-policy strategic form. -/
abbrev behavioralSignature : GameSignature ι where
  Strategy := M.BehavioralPolicy
  Outcome := E.History

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

A `MixedPolicy i` is definitionally `FinDist (M.Policy i)`. Consequently the
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
theorem toBehavioralGameForm_play_toBehavioral [DecidableEq ι]
    (profile : Profile M.strategicSignature) (horizon : ℕ) :
    (M.toBehavioralGameForm horizon).play (fun i => (profile i).toBehavioral) =
      (M.toGameForm horizon).play profile := by
  rw [toBehavioralGameForm_play, toGameForm_play]
  simpa only [runBehavioral, run] using
    M.runBehavioralFrom_toBehavioral profile horizon E.initHistory

/-- If no player is asked twice at an information state where its answer can
vary, pre-drawing every behavioral choice commutes with compilation. -/
theorem toGameForm_mixed_play_toMixed
    [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (behavioral : Profile M.behavioralSignature) (horizon : ℕ) :
    ((M.toGameForm horizon).mixed).play (fun i => (behavioral i).toMixed) =
      (M.toBehavioralGameForm horizon).play behavioral := by
  rw [toGameForm_mixed_play, toBehavioralGameForm_play]
  exact M.runMixed_toMixed hactsOnce behavioral horizon

/-- If histories with the same information state constrain a player's drawn
policy alike, reading a mixed policy behaviorally commutes with compilation. -/
theorem toGameForm_mixed_play_toBehavioral
    (hconstrain : M.ConstrainsAlike) (mixed : (i : ι) → M.MixedPolicy i)
    (horizon : ℕ) :
    ((M.toGameForm horizon).mixed).play mixed =
      (M.toBehavioralGameForm horizon).play
        (fun i => (mixed i).toBehavioral) := by
  rw [toGameForm_mixed_play, toBehavioralGameForm_play]
  exact M.runMixed_toBehavioral hconstrain horizon mixed

/-- Under both sharp hypotheses, behavioral profiles and static mixed profiles
describe exactly the same set of compiled history laws. -/
theorem toBehavioralGameForm_play_image_eq_mixed_play_image
    (hactsOnce : M.ActsOnceWhereItMatters) (hconstrain : M.ConstrainsAlike)
    (horizon : ℕ) :
    { law | ∃ behavioral : Profile M.behavioralSignature,
        (M.toBehavioralGameForm horizon).play behavioral = law } =
      { law | ∃ mixed : (i : ι) → M.MixedPolicy i,
        ((M.toGameForm horizon).mixed).play mixed = law } := by
  show
    { law | ∃ behavioral : (i : ι) → M.BehavioralPolicy i,
        M.runBehavioral behavioral horizon = law } =
      { law | ∃ mixed : (i : ι) → M.MixedPolicy i,
        M.runMixed mixed horizon = law }
  exact M.runBehavioral_image_eq_runMixed_image hactsOnce hconstrain horizon

/-! ## Unilateral realization

Whole-profile law equality is insufficient for strategic transfer: a
unilateral theorem must keep every opponent coordinate fixed. The proof
factors the independent pure-policy draw at the deviator, establishes the
round trip against pure opponents, and integrates over arbitrary opponent
laws. -/

section UnilateralRealization

variable [DecidableEq ι]
  [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)]

omit [∀ i, Fintype (M.InfoState i)]
  [∀ i, DecidableEq (M.InfoState i)] in
private theorem runMixed_update_eq_opponents_bind
    (mixed : Profile M.strategicSignature.mixed) (who : ι)
    (replacement : M.MixedPolicy who) (horizon : ℕ) :
    M.runMixed (Profile.update mixed who replacement) horizon =
      (FinDist.pi fun other : {other // other ≠ who} => mixed other.1).bind
        fun opponents =>
          replacement.bind fun policy =>
            M.run
              ((Equiv.piSplitAt who fun i => M.Policy i).symm
                (policy, opponents)) horizon := by
  rw [runMixed, runMixedFrom, FinDist.pi_eq_map_product who,
    Profile.update_same]
  have hothers :
      (fun other : {other // other ≠ who} =>
          Profile.update mixed who replacement other.1) =
        (fun other : {other // other ≠ who} => mixed other.1) := by
    funext other
    exact Profile.update_of_ne mixed replacement other.2
  rw [hothers, FinDist.bind_map]
  unfold FinDist.product
  rw [FinDist.bind_bind]
  calc
    _ = replacement.bind fun policy =>
        (FinDist.pi fun other : {other // other ≠ who} => mixed other.1).bind
          fun opponents =>
            M.run
              ((Equiv.piSplitAt who fun i => M.Policy i).symm
                (policy, opponents)) horizon := by
          refine FinDist.bind_congr fun policy _ => ?_
          rw [FinDist.bind_map]
          rfl
    _ = _ := FinDist.bind_comm replacement
      (FinDist.pi fun other : {other // other ≠ who} => mixed other.1) _

private theorem kuhn_mixed_roundTrip_against_pure
    (hrecall : M.PerfectRecall) (who : ι)
    (replacement : M.MixedPolicy who)
    (opponents : ∀ other : {other // other ≠ who}, M.Policy other.1)
    (horizon : ℕ) :
    (((InformationModel.MixedPolicy.toBehavioral
        (M := M) replacement).toMixed).bind fun policy =>
        M.run
          ((Equiv.piSplitAt who fun i => M.Policy i).symm
            (policy, opponents)) horizon) =
      (replacement.bind fun policy =>
        M.run
          ((Equiv.piSplitAt who fun i => M.Policy i).symm
            (policy, opponents)) horizon) := by
  let pureProfile : Profile M.strategicSignature :=
    (Equiv.piSplitAt who fun i => M.Policy i).symm
      (replacement.support_nonempty.choose, opponents)
  let pureMixed : Profile M.strategicSignature.mixed :=
    fun i => FinDist.pure (pureProfile i)
  let roundTrip : M.MixedPolicy who :=
    (InformationModel.MixedPolicy.toBehavioral
      (M := M) replacement).toMixed
  let mixedProfile : Profile M.strategicSignature.mixed :=
    Profile.update (sig := M.strategicSignature.mixed)
      pureMixed who replacement
  let behavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioral
      (M := M) (mixedProfile i)
  have hroundTrip :=
    (M.runMixed_toMixed
      (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
      behavioral horizon).trans
      (M.runMixed_toBehavioral
        (InformationModel.constrainsAlike_of_perfectRecall hrecall)
        horizon mixedProfile).symm
  have hroundProfile :
      (fun i =>
        (InformationModel.MixedPolicy.toBehavioral
          (M := M) (mixedProfile i)).toMixed) =
        Profile.update (sig := M.strategicSignature.mixed)
          pureMixed who roundTrip := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [mixedProfile, pureMixed, roundTrip]
    · simp [mixedProfile, pureMixed, roundTrip, hi,
        InformationModel.MixedPolicy.toBehavioral_pure,
        InformationModel.Policy.toBehavioral_toMixed]
  have hpureProfile :
      (fun other : {other // other ≠ who} => pureProfile other.1) =
        opponents := by
    funext other
    simp [pureProfile, other.2]
  rw [hroundProfile,
    runMixed_update_eq_opponents_bind (M := M)
      pureMixed who roundTrip horizon,
    runMixed_update_eq_opponents_bind (M := M)
      pureMixed who replacement horizon,
    FinDist.pi_pure] at hroundTrip
  simp only [FinDist.pure_bind] at hroundTrip
  rw [hpureProfile] at hroundTrip
  simpa [roundTrip] using hroundTrip

/-- A player's mixed strategy may be read behaviorally and redrawn as mixed
without changing the history law against the other players' fixed mixed
strategies. -/
theorem kuhn_mixed_roundTrip_update
    (hrecall : M.PerfectRecall)
    (mixed : Profile M.strategicSignature.mixed) (who : ι)
    (replacement : M.MixedPolicy who) (horizon : ℕ) :
    M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed) mixed who
          (InformationModel.MixedPolicy.toBehavioral
            (M := M) replacement).toMixed) horizon =
      M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          mixed who replacement) horizon := by
  rw [runMixed_update_eq_opponents_bind (M := M)
      mixed who (InformationModel.MixedPolicy.toBehavioral
        (M := M) replacement).toMixed horizon,
    runMixed_update_eq_opponents_bind (M := M)
      mixed who replacement horizon]
  refine FinDist.bind_congr fun opponents _ => ?_
  exact kuhn_mixed_roundTrip_against_pure
    (M := M) hrecall who replacement opponents horizon

omit [Fintype ι] [∀ i, DecidableEq (M.InfoState i)] in
private theorem toMixed_update
    (behavioral : Profile M.behavioralSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) :
    (fun i => ((Profile.update behavioral who replacement) i).toMixed) =
      Profile.update (sig := M.strategicSignature.mixed)
        (fun i => (behavioral i).toMixed) who
        replacement.toMixed := by
  funext i
  by_cases hi : i = who
  · subst i
    rw [Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne _ _ hi, Profile.update_of_ne _ _ hi]

omit [Fintype ι] [∀ i, Fintype (M.InfoState i)]
  [∀ i, DecidableEq (M.InfoState i)] in
private theorem toBehavioral_update
    (mixed : Profile M.strategicSignature.mixed) (who : ι)
    (replacement : M.MixedPolicy who) :
    (fun i => InformationModel.MixedPolicy.toBehavioral
        (M := M) (Profile.update mixed who replacement i)) =
      Profile.update (sig := M.behavioralSignature)
        (fun i => InformationModel.MixedPolicy.toBehavioral
          (M := M) (mixed i)) who
        (InformationModel.MixedPolicy.toBehavioral
          (M := M) replacement) := by
  funext i
  by_cases hi : i = who
  · subst i
    rw [Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne _ _ hi, Profile.update_of_ne _ _ hi]

/-- A behavioral policy and its behavioral-to-mixed-to-behavioral round trip
are realization-equivalent for one player while every other behavioral policy
is held fixed. -/
theorem kuhn_behavioral_roundTrip_update
    (hrecall : M.PerfectRecall)
    (behavioral : Profile M.behavioralSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) (horizon : ℕ) :
    M.runBehavioral
        (Profile.update behavioral who
          (InformationModel.MixedPolicy.toBehavioral
            (M := M) replacement.toMixed))
        horizon =
      M.runBehavioral (Profile.update behavioral who replacement) horizon := by
  let roundTrip : M.BehavioralPolicy who :=
    InformationModel.MixedPolicy.toBehavioral
      (M := M) replacement.toMixed
  have hleft := M.runMixed_toMixed
    (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    (Profile.update behavioral who roundTrip) horizon
  have hright := M.runMixed_toMixed
    (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    (Profile.update behavioral who replacement) horizon
  rw [toMixed_update (M := M) behavioral who roundTrip] at hleft
  rw [toMixed_update (M := M) behavioral who replacement] at hright
  have hlocal := M.kuhn_mixed_roundTrip_update hrecall
    (fun i => (behavioral i).toMixed) who replacement.toMixed horizon
  have hresult := hleft.symm.trans (hlocal.trans hright)
  simpa [roundTrip] using hresult

/-- Replacing one player's mixed strategy by an arbitrary behavioral strategy
commutes with the conditional behavioral reading while every nondeviator keeps
its induced behavior. -/
theorem kuhn_mixed_update_toBehavioral
    (hrecall : M.PerfectRecall)
    (mixed : Profile M.strategicSignature.mixed) (who : ι)
    (replacement : M.BehavioralPolicy who) (horizon : ℕ) :
    M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          (fun i => InformationModel.MixedPolicy.toBehavioral
            (M := M) (mixed i)) who replacement)
        horizon =
      M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          mixed who replacement.toMixed) horizon := by
  let behavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioral
      (M := M) (mixed i)
  have hback := M.runMixed_toBehavioral
    (InformationModel.constrainsAlike_of_perfectRecall hrecall) horizon
    (Profile.update mixed who replacement.toMixed)
  rw [toBehavioral_update (M := M)
    mixed who replacement.toMixed] at hback
  have hround := M.kuhn_behavioral_roundTrip_update
    hrecall behavioral who replacement horizon
  exact hround.symm.trans hback.symm

/-- Starting from a behavioral profile, an arbitrary mixed deviation is
realized by its behavioral reading without changing any nondeviator's
behavioral policy. -/
theorem kuhn_behavioral_update_toMixed
    (hrecall : M.PerfectRecall)
    (behavioral : Profile M.behavioralSignature) (who : ι)
    (replacement : M.MixedPolicy who) (horizon : ℕ) :
    M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          (fun i => (behavioral i).toMixed) who replacement)
        horizon =
      M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          behavioral who
            (InformationModel.MixedPolicy.toBehavioral
              (M := M) replacement)) horizon := by
  let deviation : M.BehavioralPolicy who :=
    InformationModel.MixedPolicy.toBehavioral (M := M) replacement
  let roundBehavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioral
      (M := M) (behavioral i).toMixed
  have hforward := M.runMixed_toMixed
    (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    (Profile.update behavioral who deviation) horizon
  rw [toMixed_update (M := M) behavioral who deviation] at hforward
  have hbackBase := M.runMixed_toBehavioral
    (InformationModel.constrainsAlike_of_perfectRecall hrecall) horizon
    (Profile.update (sig := M.strategicSignature.mixed)
      (fun i => (behavioral i).toMixed) who deviation.toMixed)
  rw [toBehavioral_update (M := M)
    (fun i => (behavioral i).toMixed) who deviation.toMixed] at hbackBase
  have hbaseToRound :
      M.runBehavioral (Profile.update behavioral who deviation) horizon =
        M.runBehavioral
          (Profile.update roundBehavioral who
            (InformationModel.MixedPolicy.toBehavioral
              (M := M) deviation.toMixed))
          horizon :=
    hforward.symm.trans hbackBase
  have hplayer := M.kuhn_behavioral_roundTrip_update
    hrecall roundBehavioral who deviation horizon
  have hbaseToDeviation := hbaseToRound.trans hplayer
  have hbackDeviation := M.runMixed_toBehavioral
    (InformationModel.constrainsAlike_of_perfectRecall hrecall) horizon
    (Profile.update (sig := M.strategicSignature.mixed)
      (fun i => (behavioral i).toMixed) who replacement)
  rw [toBehavioral_update (M := M)
    (fun i => (behavioral i).toMixed) who replacement] at hbackDeviation
  have hresult := hbackDeviation.trans hbaseToDeviation.symm
  simpa [deviation, roundBehavioral] using hresult

end UnilateralRealization

end InformationModel

end GameTheory.Protocol
