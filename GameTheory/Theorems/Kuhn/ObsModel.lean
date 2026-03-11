import Math.ParameterizedChain
import Semantics.DSMachine

/-! # Observation model

Multi-player observation model over a `DSMachine` with observation-indexed actions.
This is the canonical game model above which Kuhn's theorem holds.

Note: technically the action family only needs to be indexed by the player's
information state summary. This file keeps an explicit `Obs` projection because
the current theorem stack still formulates recall and transition compatibility
through a distinguished "current observation" readout from that summary. We do
not currently generalize further, to avoid widening the refactor beyond what
the proofs use.

## Structure

- `ObsModel`: DSMachine + per-player observations → obs-indexed actions
- Profile types: `PureProfile`, `BehavioralProfile`, `LocalStrategy`
- Execution: `stepDist`, `runDist`, `pureStep`
- Reachability: `ReachActionTrace`, `StepReachable`
- Recall predicates: `PerStepActionRecall`, `PlayerStepRecall`, `TracePlayerStepRecall`
- Information structure: `ObsRecall`, `ActionRecall`, `PerfectRecall`
-/

open Math.ProbabilityMassFunction Math.ParameterizedChain

/-- Abstract player information-state interface over observations.

The strategic state carries the current observation together with whatever
path summary the model wants to retain from earlier observations. The
`snapshot` field is proof-facing: the current Kuhn proofs still use a faithful
list view to recover prefix/current decomposition, even though the strategic
meaning is "current observation plus summary", not "raw list". -/
structure InfoStateSpec (α : Type) where
  Carrier : Type
  start : α → Carrier
  push : Carrier → α → Carrier
  current : Carrier → α
  snapshot : Carrier → List α
  snapshot_injective : Function.Injective snapshot
  current_start : ∀ a, current (start a) = a
  current_push : ∀ h a, current (push h a) = a
  snapshot_start : ∀ a, snapshot (start a) = [a]
  snapshot_push : ∀ h a, snapshot (push h a) = snapshot h ++ [a]

namespace InfoStateSpec

/-- Canonical information-state implementation by nonempty lists. -/
def list (α : Type) : InfoStateSpec α where
  Carrier := {l : List α // l ≠ []}
  start a := ⟨[a], by simp⟩
  push h a := ⟨h.1 ++ [a], by simp⟩
  current h := h.1.getLast h.2
  snapshot h := h.1
  snapshot_injective := by
    intro h₁ h₂ h
    exact Subtype.ext h
  current_start := by
    intro a
    simp
  current_push := by
    intro h a
    simp
  snapshot_start := by
    intro a
    rfl
  snapshot_push := by
    intro h a
    rfl

end InfoStateSpec

/-- Multi-player observation model over a `DSMachine` with observation-indexed actions.
The label at state `s` is the joint action `∀ i, Act i (observe i s)`. -/
structure ObsModel (ι σ : Type) (Obs : ι → Type) (Act : (i : ι) → Obs i → Type) where
  /-- Per-player information-state representation of observation traces. -/
  infoState : (i : ι) → InfoStateSpec (Obs i)
  /-- Per-player observation function on states. -/
  observe : (i : ι) → σ → Obs i
  /-- Underlying dependent stochastic machine. -/
  machine : DSMachine σ (fun s => ∀ i, Act i (observe i s))

namespace ObsModel

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}

/-- Initial state (delegated to `machine`). -/
abbrev init (O : ObsModel ι σ Obs Act) : σ := O.machine.init

/-- Stochastic step (delegated to `machine`). -/
abbrev step (O : ObsModel ι σ Obs Act) (s : σ) : (∀ i, Act i (O.observe i s)) → PMF σ :=
  O.machine.step s

/-- Joint action profile at state `s`. -/
abbrev JointActionAt (O : ObsModel ι σ Obs Act) (s : σ) := ∀ i, Act i (O.observe i s)

/-! ### Observations and projections -/

/-- Last state of a trace (or initial state for empty traces). -/
def lastState (O : ObsModel ι σ Obs Act) (ss : List σ) : σ :=
  ss.getLast?.getD O.init

/-- Player-local information state, represented by the model's chosen carrier. -/
abbrev InfoState (O : ObsModel ι σ Obs Act) (i : ι) := (O.infoState i).Carrier

/-- Proof-facing snapshot view of a player-local information state. -/
abbrev stateSnapshot (O : ObsModel ι σ Obs Act) (i : ι) (v : O.InfoState i) : List (Obs i) :=
  (O.infoState i).snapshot v

/-- Semantic depth of a player-local information state, discounting the distinguished
initial observation. -/
def stateDepth (O : ObsModel ι σ Obs Act) (i : ι) (v : O.InfoState i) : Nat :=
  (O.stateSnapshot i v).length - 1

/-- Current observation stored in a player-local information state. -/
def currentObs (O : ObsModel ι σ Obs Act) (i : ι) (v : O.InfoState i) : Obs i :=
  (O.infoState i).current v

/-- Extend a local information state by projecting additional states. -/
def projectStatesFrom (O : ObsModel ι σ Obs Act) (i : ι) (v : O.InfoState i) :
    List σ → O.InfoState i
  | [] => v
  | s :: ss => O.projectStatesFrom i ((O.infoState i).push v (O.observe i s)) ss

/-- Project a state trace to player `i`'s local observation trace. -/
def projectStates (O : ObsModel ι σ Obs Act) (i : ι) (ss : List σ) : O.InfoState i :=
  O.projectStatesFrom i ((O.infoState i).start (O.observe i O.init)) ss

/-- The snapshot view of `projectStatesFrom` appends the projected observations. -/
theorem stateSnapshot_projectStatesFrom (O : ObsModel ι σ Obs Act) (i : ι)
    (v : O.InfoState i) (ss : List σ) :
    O.stateSnapshot i (O.projectStatesFrom i v ss) =
      O.stateSnapshot i v ++ ss.map (O.observe i) := by
  induction ss generalizing v with
  | nil =>
      simp [projectStatesFrom, stateSnapshot]
  | cons s ss ih =>
      simpa [projectStatesFrom, stateSnapshot, (O.infoState i).snapshot_push, List.map]
        using ih ((O.infoState i).push v (O.observe i s))

/-- The snapshot view of `projectStates` prepends the initial observation and then
records the projected observation list. -/
theorem stateSnapshot_projectStates (O : ObsModel ι σ Obs Act) (i : ι) (ss : List σ) :
    O.stateSnapshot i (O.projectStates i ss) = O.observe i O.init :: ss.map (O.observe i) := by
  simp [projectStates, stateSnapshot_projectStatesFrom, stateSnapshot,
    (O.infoState i).snapshot_start]

/-- Projected information states have semantic depth equal to the underlying
state trace length. -/
theorem stateDepth_projectStates (O : ObsModel ι σ Obs Act) (i : ι) (ss : List σ) :
    O.stateDepth i (O.projectStates i ss) = ss.length := by
  simp [stateDepth, stateSnapshot, O.stateSnapshot_projectStates i ss,
    List.length_map]

/-- Current observation after extending a local information state. -/
theorem currentObs_projectStatesFrom (O : ObsModel ι σ Obs Act) (i : ι)
    (v : O.InfoState i) (ss : List σ) :
    O.currentObs i (O.projectStatesFrom i v ss) =
      match ss.getLast? with
      | some s => O.observe i s
      | none => O.currentObs i v := by
  induction ss generalizing v with
  | nil =>
      simp [projectStatesFrom, currentObs]
  | cons s ss ih =>
      cases ss with
      | nil =>
          simp [projectStatesFrom, currentObs, (O.infoState i).current_push]
      | cons t ts =>
          simpa [projectStatesFrom] using
            ih ((O.infoState i).push v (O.observe i s))

/-- Observation equivalence: two states look the same to player `i`. -/
def obsEq (O : ObsModel ι σ Obs Act) (i : ι) (s t : σ) : Prop :=
  O.observe i s = O.observe i t

/-- The current observation of a projected information state is the observation at
the last state. -/
theorem currentObs_projectStates (O : ObsModel ι σ Obs Act) (i : ι) (ss : List σ) :
    O.currentObs i (O.projectStates i ss) = O.observe i (O.lastState ss) := by
  cases h : ss.getLast? with
  | none =>
      have hnil : ss = [] := List.getLast?_eq_none_iff.mp h
      subst hnil
      simp [currentObs, lastState, projectStates, projectStatesFrom,
        (O.infoState i).current_start]
  | some s =>
      have hlast : O.lastState ss = s := by simp [lastState, h]
      rw [hlast]
      simp [projectStates, currentObs_projectStatesFrom, h]

theorem obsEq_of_projectStates_getLast (O : ObsModel ι σ Obs Act) (i : ι) {ss ss' : List σ}
    (hproj : O.projectStates i ss = O.projectStates i ss') :
    O.obsEq i (O.lastState ss) (O.lastState ss') := by
  have hlast := congrArg (O.currentObs i) hproj
  simpa [obsEq, O.currentObs_projectStates i ss, O.currentObs_projectStates i ss'] using hlast

/-! ### Profile types -/

/-- A single player's local strategy: information-state-dependent action
selection, with the action type determined by the current observation exposed
by that state. -/
abbrev LocalStrategy (O : ObsModel ι σ Obs Act) (i : ι) : Type :=
  (v : O.InfoState i) → Act i (O.currentObs i v)

/-- Deterministic profile over local information states.
The return type depends on the current observation exposed by the state. -/
abbrev PureProfile (O : ObsModel ι σ Obs Act) : Type :=
  ∀ (i : ι), O.LocalStrategy i

/-- Behavioral (stochastic) profile over local information states.
The distribution is over actions at the current observation. -/
abbrev BehavioralProfile (O : ObsModel ι σ Obs Act) : Type :=
  ∀ (i : ι) (v : O.InfoState i), PMF (Act i (O.currentObs i v))

/-- Correlated behavioral profile over the full local information-state context. -/
abbrev BehavioralProfileCorr (O : ObsModel ι σ Obs Act) : Type :=
  (v : ∀ i, O.InfoState i) → PMF (∀ i, Act i (O.currentObs i (v i)))

/-- Lift a deterministic profile to a behavioral one. -/
noncomputable def pureToBehavioral (O : ObsModel ι σ Obs Act)
    (π : PureProfile O) : BehavioralProfile O :=
  fun i v => PMF.pure (π i v)

section FintypeInstances

open Classical in
/-- Finite information states and finite action alphabets give finitely many
local strategies. -/
noncomputable instance localStrategyFintype (O : ObsModel ι σ Obs Act)
    [∀ i, Fintype (O.InfoState i)] [∀ i o, Fintype (Act i o)] (i : ι) :
    Fintype (O.LocalStrategy i) := by
  unfold LocalStrategy
  infer_instance

end FintypeInstances

/-- Cast a profile's action from information-state world to step world. -/
def castProfileAction (O : ObsModel ι σ Obs Act) (i : ι) (ss : List σ)
    (a : Act i (O.currentObs i (O.projectStates i ss))) :
    Act i (O.observe i (O.lastState ss)) :=
  O.currentObs_projectStates i ss ▸ a

/-- Embed an independent behavioral profile as a correlated one by product sampling. -/
noncomputable def behavioralToCorr
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (O : ObsModel ι σ Obs Act) (b : BehavioralProfile O) : BehavioralProfileCorr O :=
  fun v => Math.PMFProduct.pmfPi (fun i => b i (v i))

/-! ### Stochastic execution -/

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- Independent joint-action distribution induced by a behavioral profile,
in information-state world types indexed by the current observation of the
projected state summary. -/
noncomputable def jointActionDist (O : ObsModel ι σ Obs Act)
    (b : BehavioralProfile O) (ss : List σ) :
    PMF (∀ i, Act i (O.currentObs i (O.projectStates i ss))) :=
  Math.PMFProduct.pmfPi (fun i => b i (O.projectStates i ss))

/-- Cast a profile-world joint action to step-world (observation at the last state). -/
def castJointAction (O : ObsModel ι σ Obs Act) (ss : List σ)
    (a : ∀ i, Act i (O.currentObs i (O.projectStates i ss))) :
    ∀ i, Act i (O.observe i (O.lastState ss)) :=
  fun i => O.currentObs_projectStates i ss ▸ a i

/-- One stochastic step: sample action from profile, cast to step-world, then step. -/
noncomputable def stepDist (O : ObsModel ι σ Obs Act)
    (b : BehavioralProfile O) (ss : List σ) : PMF σ :=
  let s := O.lastState ss
  (O.jointActionDist b ss).bind fun a => O.step s (O.castJointAction ss a)

/-- Bounded run distribution under behavioral profile. -/
noncomputable def runDist (O : ObsModel ι σ Obs Act)
    (k : Nat) (b : BehavioralProfile O) : PMF (List σ) :=
  Nat.rec (PMF.pure [O.init])
    (fun _ rec =>
      rec.bind (fun ss =>
        pushforward (O.stepDist b ss) (fun t => ss ++ [t])))
    k

/-- Pure-profile run distribution via `pureToBehavioral`. -/
noncomputable def runDistPure (O : ObsModel ι σ Obs Act)
    (k : Nat) (π : PureProfile O) : PMF (List σ) :=
  O.runDist k (O.pureToBehavioral π)

/-- The pure step function: directly applies `O.step` at the deterministic action. -/
noncomputable def pureStep (O : ObsModel ι σ Obs Act) (π : PureProfile O)
    (ss : List σ) : PMF σ :=
  O.stepDist (O.pureToBehavioral π) ss

/-- `runDistPure` equals `pureRun` applied to `pureStep`. -/
theorem runDistPure_eq_pureRun (O : ObsModel ι σ Obs Act) (k : Nat)
    (π : PureProfile O) :
    O.runDistPure k π = pureRun (O.pureStep) O.init k π := rfl

/-! ### Reachability -/

/-- Reachability witness via nonzero-probability transitions (Type-valued).
Stores the action at each step with the correct dependent type. -/
inductive ReachActionTrace (O : ObsModel ι σ Obs Act) : List σ → Type
  | init : ReachActionTrace O [O.init]
  | snoc {ss : List σ} {s t : σ} (a : O.JointActionAt s) :
      ReachActionTrace O ss →
      ss.getLast? = some s →
      (O.step s a) t ≠ 0 →
      ReachActionTrace O (ss ++ [t])

/-- A state is reachable if it appears at the end of some nonzero-probability trace. -/
def StepReachable (O : ObsModel ι σ Obs Act) (s : σ) : Prop :=
  ∃ (ss : List σ), Nonempty (O.ReachActionTrace ss) ∧ ss.getLast? = some s

/-! ### Recall predicates -/

/-- Per-step action recall: any two transitions with observation-equivalent
source and target must use the same joint action (up to obs-transport).
The `▸` transport uses the observation-equivalence proof to cast
actions from `Act i (observe i s)` to `Act i (observe i s')`. -/
def PerStepActionRecall (O : ObsModel ι σ Obs Act) : Prop :=
  ∀ (s s' t t' : σ) (a : O.JointActionAt s) (a' : O.JointActionAt s'),
    (O.step s a) t ≠ 0 → (O.step s' a') t' ≠ 0 →
    (hobs : ∀ i, O.observe i s = O.observe i s') →
    (∀ i, O.observe i t = O.observe i t') →
    ∀ i, (hobs i) ▸ (a i) = a' i

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] in
/-- Transported actions agree automatically on subsingleton action spaces. -/
theorem cast_eq_of_subsingleton
    {i : ι} {o o' : Obs i} (h : o = o') (a : Act i o) (a' : Act i o')
    (hsub : Subsingleton (Act i o)) :
    h ▸ a = a' := by
  cases h
  exact hsub.elim _ _

/-- Per-step player recall (all players).

This only imposes content on nontrivial action spaces. If
`Act i (observe i s)` is subsingleton, the action equality is automatic. -/
def PerStepPlayerRecall (O : ObsModel ι σ Obs Act) : Prop :=
  ∀ (i : ι) (s s' t t' : σ) (a : O.JointActionAt s) (a' : O.JointActionAt s'),
    (O.step s a) t ≠ 0 → (O.step s' a') t' ≠ 0 →
    (hobs_i : O.observe i s = O.observe i s') →
    O.observe i t = O.observe i t' →
    ¬ Subsingleton (Act i (O.observe i s)) →
    hobs_i ▸ (a i) = a' i

/-- Per-step recall for a single player.

This only imposes content on nontrivial action spaces. -/
def PlayerStepRecall (O : ObsModel ι σ Obs Act) (i : ι) : Prop :=
  ∀ (s s' t t' : σ) (a : O.JointActionAt s) (a' : O.JointActionAt s'),
    (O.step s a) t ≠ 0 → (O.step s' a') t' ≠ 0 →
    (hobs_i : O.observe i s = O.observe i s') →
    O.observe i t = O.observe i t' →
    ¬ Subsingleton (Act i (O.observe i s)) →
    hobs_i ▸ (a i) = a' i

/-- Trace-level per-step player recall: weakest syntactic condition for Kuhn.
The obs-transport proof `hobs_s` is an explicit hypothesis (derived from
`projectStates` equality + `getLast?` at call sites). -/
def TracePlayerStepRecall (O : ObsModel ι σ Obs Act) (i : ι) : Prop :=
  ∀ (s s' t t' : σ) (a : O.JointActionAt s) (a' : O.JointActionAt s')
    (ss ss' : List σ),
    Nonempty (O.ReachActionTrace ss) →
    Nonempty (O.ReachActionTrace ss') →
    ss.getLast? = some s → ss'.getLast? = some s' →
    O.projectStates i ss = O.projectStates i ss' →
    (O.step s a) t ≠ 0 →
    (O.step s' a') t' ≠ 0 →
    O.observe i t = O.observe i t' →
    (hobs_s : O.observe i s = O.observe i s') →
    ¬ Subsingleton (Act i (O.observe i s)) →
    hobs_s ▸ (a i) = a' i

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] in
/-- Recover unconditional player-action equality from `PerStepPlayerRecall`
by discharging trivial coordinates via `Subsingleton.elim`. -/
theorem PerStepPlayerRecall.action_eq {O : ObsModel ι σ Obs Act}
    (h : O.PerStepPlayerRecall)
    (i : ι) {s s' t t' : σ} {a : O.JointActionAt s} {a' : O.JointActionAt s'}
    (hs : (O.step s a) t ≠ 0) (hs' : (O.step s' a') t' ≠ 0)
    (hobs_i : O.observe i s = O.observe i s')
    (hobst_i : O.observe i t = O.observe i t') :
    hobs_i ▸ (a i) = a' i := by
  by_cases hsub : Subsingleton (Act i (O.observe i s))
  · exact cast_eq_of_subsingleton hobs_i (a i) (a' i) hsub
  · exact h i s s' t t' a a' hs hs' hobs_i hobst_i hsub

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] in
/-- Recover unconditional player-action equality from `PlayerStepRecall`
by discharging trivial coordinates via `Subsingleton.elim`. -/
theorem PlayerStepRecall.action_eq {O : ObsModel ι σ Obs Act} {i : ι}
    (h : O.PlayerStepRecall i)
    {s s' t t' : σ} {a : O.JointActionAt s} {a' : O.JointActionAt s'}
    (hs : (O.step s a) t ≠ 0) (hs' : (O.step s' a') t' ≠ 0)
    (hobs_i : O.observe i s = O.observe i s')
    (hobst_i : O.observe i t = O.observe i t') :
    hobs_i ▸ (a i) = a' i := by
  by_cases hsub : Subsingleton (Act i (O.observe i s))
  · exact cast_eq_of_subsingleton hobs_i (a i) (a' i) hsub
  · exact h s s' t t' a a' hs hs' hobs_i hobst_i hsub

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] in
/-- Recover unconditional player-action equality from `TracePlayerStepRecall`
by discharging trivial coordinates via `Subsingleton.elim`. -/
theorem TracePlayerStepRecall.action_eq {O : ObsModel ι σ Obs Act} {i : ι}
    (h : O.TracePlayerStepRecall i)
    {s s' t t' : σ} {a : O.JointActionAt s} {a' : O.JointActionAt s'}
    {ss ss' : List σ}
    (hreach : Nonempty (O.ReachActionTrace ss))
    (hreach' : Nonempty (O.ReachActionTrace ss'))
    (hlast : ss.getLast? = some s) (hlast' : ss'.getLast? = some s')
    (hproj : O.projectStates i ss = O.projectStates i ss')
    (hs : (O.step s a) t ≠ 0) (hs' : (O.step s' a') t' ≠ 0)
    (hobst_i : O.observe i t = O.observe i t')
    (hobs_i : O.observe i s = O.observe i s') :
    hobs_i ▸ (a i) = a' i := by
  by_cases hsub : Subsingleton (Act i (O.observe i s))
  · exact cast_eq_of_subsingleton hobs_i (a i) (a' i) hsub
  · exact h s s' t t' a a' ss ss' hreach hreach' hlast hlast' hproj hs hs' hobst_i hobs_i hsub

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] in
/-- `PerStepPlayerRecall` implies `PerStepActionRecall`. -/
theorem PerStepPlayerRecall.toAction {O : ObsModel ι σ Obs Act}
    (h : O.PerStepPlayerRecall) : O.PerStepActionRecall :=
  fun _ _ _ _ _ _ hs hs' hobs hobst i =>
    h.action_eq i hs hs' (hobs i) (hobst i)

/-! ### ProjectStates API -/

section NoFintype

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- Player-local projected own-action trace from a `ReachActionTrace`.
Returns a list of observation-action pairs using sigma types. -/
def projectActions (O : ObsModel ι σ Obs Act) (i : ι) :
    {ss : List σ} → O.ReachActionTrace ss → List (Σ o : Obs i, Act i o)
  | _, .init => []
  | _, .snoc (s := s) a prev _ _ =>
      projectActions O i prev ++ [⟨O.observe i s, a i⟩]

theorem projectStates_eq_length (O : ObsModel ι σ Obs Act) (i : ι) {ss₁ ss₂ : List σ}
    (h : O.projectStates i ss₁ = O.projectStates i ss₂) :
    ss₁.length = ss₂.length := by
  have hlist := congrArg (O.stateSnapshot i) h
  have := congrArg List.length hlist
  simpa [O.stateSnapshot_projectStates i ss₁, O.stateSnapshot_projectStates i ss₂,
    List.length_map] using this

theorem projectStates_prefix_of_append (O : ObsModel ι σ Obs Act)
    (i : ι) {p p' : List σ} {t t' : σ}
    (h : O.projectStates i (p ++ [t]) = O.projectStates i (p' ++ [t'])) :
    O.projectStates i p = O.projectStates i p' := by
  have hlist := congrArg (O.stateSnapshot i) h
  have hmap :
      O.stateSnapshot i (O.projectStates i p) ++ [O.observe i t] =
        O.stateSnapshot i (O.projectStates i p') ++ [O.observe i t'] := by
    simpa [O.stateSnapshot_projectStates i (p ++ [t]), O.stateSnapshot_projectStates i (p' ++ [t']),
      O.stateSnapshot_projectStates i p, O.stateSnapshot_projectStates i p',
      List.map_append, List.map] using hlist
  have hprefix := List.append_inj_left' hmap (by simp)
  exact (O.infoState i).snapshot_injective hprefix

theorem obsEq_of_projectStates_append (O : ObsModel ι σ Obs Act)
    (i : ι) {p p' : List σ} {t t' : σ}
    (h : O.projectStates i (p ++ [t]) = O.projectStates i (p' ++ [t'])) :
    O.obsEq i t t' := by
  have hlist := congrArg (O.stateSnapshot i) h
  have hmap :
      O.stateSnapshot i (O.projectStates i p) ++ [O.observe i t] =
        O.stateSnapshot i (O.projectStates i p') ++ [O.observe i t'] := by
    simpa [O.stateSnapshot_projectStates i (p ++ [t]), O.stateSnapshot_projectStates i (p' ++ [t']),
      O.stateSnapshot_projectStates i p, O.stateSnapshot_projectStates i p',
      List.map_append, List.map] using hlist
  have hlast := List.append_inj_right' hmap (by simp)
  simpa [obsEq] using hlast

/-! ### Observation recall -/

/-- Observation recall: indistinguishable terminal states imply identical
player-local visible histories. -/
def ObsRecall (O : ObsModel ι σ Obs Act) : Prop :=
  ∀ (i : ι) (ss₁ ss₂ : List σ),
    Nonempty (O.ReachActionTrace ss₁) →
    Nonempty (O.ReachActionTrace ss₂) →
    O.obsEq i (O.lastState ss₁) (O.lastState ss₂) →
    O.projectStates i ss₁ = O.projectStates i ss₂

/-- Action recall: indistinguishable terminal visible states imply identical
player-local own-action traces on the corresponding action-annotated reaches. -/
def ActionRecall (O : ObsModel ι σ Obs Act) : Prop :=
  ∀ (i : ι) (ss₁ ss₂ : List σ)
    (rat₁ : O.ReachActionTrace ss₁) (rat₂ : O.ReachActionTrace ss₂),
    O.obsEq i (O.lastState ss₁) (O.lastState ss₂) →
    O.projectActions i rat₁ = O.projectActions i rat₂

/-- Perfect recall is the conjunction of observation recall and action recall. -/
def PerfectRecall (O : ObsModel ι σ Obs Act) : Prop :=
  O.ObsRecall ∧ O.ActionRecall

end NoFintype

/-! ### Additional execution -/

/-- One stochastic step under a correlated behavioral profile. -/
noncomputable def stepDistCorr (O : ObsModel ι σ Obs Act)
    [Fintype ι] [∀ i o, Fintype (Act i o)]
    (b : BehavioralProfileCorr O) (ss : List σ) : PMF σ :=
  let s := O.lastState ss
  let v : ∀ i, O.InfoState i := fun i => O.projectStates i ss
  (b v).bind fun a => O.step s (fun i => O.currentObs_projectStates i ss ▸ a i)

/-! ### StepReachable lemmas -/

section NoFintype2

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- The initial state is always step-reachable. -/
theorem stepReachable_init (O : ObsModel ι σ Obs Act) :
    O.StepReachable O.init :=
  ⟨[O.init], ⟨.init⟩, rfl⟩

/-- If `s` is step-reachable and the transition has nonzero probability,
then `t` is step-reachable. -/
theorem stepReachable_step {O : ObsModel ι σ Obs Act} {s t : σ} {a : O.JointActionAt s}
    (hs : O.StepReachable s) (hstep : (O.step s a) t ≠ 0) :
    O.StepReachable t := by
  obtain ⟨ss, ⟨rat⟩, hlast⟩ := hs
  exact ⟨ss ++ [t], ⟨.snoc a rat hlast hstep⟩, List.getLast?_concat ..⟩

/-! ### Additional recall predicates -/

/-- Reachable per-step player recall for a single player `i`:
`PlayerStepRecall` restricted to step-reachable source states. -/
def ReachablePlayerStepRecall (O : ObsModel ι σ Obs Act) (i : ι) : Prop :=
  ∀ (s s' t t' : σ) (a : O.JointActionAt s) (a' : O.JointActionAt s'),
    (O.step s a) t ≠ 0 → (O.step s' a') t' ≠ 0 →
    (hobs_i : O.observe i s = O.observe i s') →
    O.observe i t = O.observe i t' →
    O.StepReachable s → O.StepReachable s' →
    ¬ Subsingleton (Act i (O.observe i s)) →
    hobs_i ▸ (a i) = a' i

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] in
/-- Recover unconditional player-action equality from `ReachablePlayerStepRecall`
by discharging trivial coordinates via `Subsingleton.elim`. -/
theorem ReachablePlayerStepRecall.action_eq {O : ObsModel ι σ Obs Act} {i : ι}
    (h : O.ReachablePlayerStepRecall i)
    {s s' t t' : σ} {a : O.JointActionAt s} {a' : O.JointActionAt s'}
    (hs : (O.step s a) t ≠ 0) (hs' : (O.step s' a') t' ≠ 0)
    (hobs_i : O.observe i s = O.observe i s')
    (hobst_i : O.observe i t = O.observe i t')
    (hreach_s : O.StepReachable s) (hreach_s' : O.StepReachable s') :
    hobs_i ▸ (a i) = a' i := by
  by_cases hsub : Subsingleton (Act i (O.observe i s))
  · exact cast_eq_of_subsingleton hobs_i (a i) (a' i) hsub
  · exact h s s' t t' a a' hs hs' hobs_i hobst_i hreach_s hreach_s' hsub

/-- `PerStepPlayerRecall` is equivalent to every player having step recall. -/
theorem perStepPlayerRecall_iff_forall {O : ObsModel ι σ Obs Act} :
    O.PerStepPlayerRecall ↔ ∀ i, O.PlayerStepRecall i :=
  ⟨fun h i => h i, fun h i => h i⟩

/-- `PlayerStepRecall` implies `ReachablePlayerStepRecall` (drop reachability). -/
theorem PlayerStepRecall.toReachable {O : ObsModel ι σ Obs Act} {i : ι}
    (h : O.PlayerStepRecall i) : O.ReachablePlayerStepRecall i :=
  fun _ _ _ _ _ _ hs hs' hobs hobst _ _ hnontriv =>
    h _ _ _ _ _ _ hs hs' hobs hobst hnontriv

/-- `PlayerStepRecall` implies `TracePlayerStepRecall` (drop trace witnesses). -/
theorem PlayerStepRecall.toTrace {O : ObsModel ι σ Obs Act} {i : ι}
    (h : O.PlayerStepRecall i) : O.TracePlayerStepRecall i :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hs hs' hobst hobs hnontriv =>
    h _ _ _ _ _ _ hs hs' hobs hobst hnontriv

end NoFintype2

/-! ### Mediator construction -/

/-- Mediator construction: condition `ν` on the probability of reaching
the current state trace, then extract joint actions in profile-world types. -/
noncomputable def mixedToMediator (O : ObsModel ι σ Obs Act)
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    [Fintype (PureProfile O)]
    (ν : PMF (PureProfile O))
    (n : Nat) (ss : List σ) :
    PMF (∀ i, Act i (O.currentObs i (O.projectStates i ss))) :=
  (reweightPMF ν (fun π => pureRun O.pureStep O.init n π ss)).bind
    (fun π => O.jointActionDist (O.pureToBehavioral π) ss)

end ObsModel
