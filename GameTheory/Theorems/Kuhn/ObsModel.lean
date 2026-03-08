import Math.ParameterizedChain
import Semantics.DSMachine

/-! # Observation model

Multi-player observation model over a `DSMachine` with observation-indexed actions.
This is the canonical game model above which Kuhn's theorem holds.

## Structure

- `ObsModel`: DSMachine + per-player observations → obs-indexed actions
- Profile types: `PureProfile`, `BehavioralProfile`, `LocalStrategy`
- Execution: `stepDist`, `runDist`, `pureStep`
- Reachability: `ReachActionTrace`, `StepReachable`
- Recall predicates: `PerStepActionRecall`, `PlayerStepRecall`, `TracePlayerStepRecall`
- Information structure: `ObsRecall`, `ActionRecall`, `PerfectRecall`
-/

open Math.ProbabilityMassFunction Math.ParameterizedChain

/-- Multi-player observation model over a `DSMachine` with observation-indexed actions.
The label at state `s` is the joint action `∀ i, Act i (observe i s)`. -/
structure ObsModel (ι σ : Type) (Obs : ι → Type) (Act : (i : ι) → Obs i → Type) where
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

/-- Player-local visible trace: list of per-step observations. -/
abbrev LocalTrace (_ : ObsModel ι σ Obs Act) (i : ι) := List (Obs i)

/-- Last observation in a local trace (or the initial observation as default). -/
def lastObs (O : ObsModel ι σ Obs Act) (i : ι) (v : O.LocalTrace i) : Obs i :=
  v.getLast?.getD (O.observe i O.init)

/-- Project a state trace to player `i`'s local observation trace. -/
def projectStates (O : ObsModel ι σ Obs Act) (i : ι) (ss : List σ) : O.LocalTrace i :=
  ss.map (O.observe i)

/-- Observation equivalence: two states look the same to player `i`. -/
def obsEq (O : ObsModel ι σ Obs Act) (i : ι) (s t : σ) : Prop :=
  O.observe i s = O.observe i t

/-- `lastObs` of a projected state trace equals the observation at the last state. -/
theorem lastObs_projectStates (O : ObsModel ι σ Obs Act) (i : ι) (ss : List σ) :
    O.lastObs i (O.projectStates i ss) = O.observe i (O.lastState ss) := by
  simp only [lastObs, lastState, projectStates, List.getLast?_map]
  cases ss.getLast? <;> simp [Option.map]

theorem obsEq_of_projectStates_getLast (O : ObsModel ι σ Obs Act) (i : ι) {ss ss' : List σ}
    (hproj : O.projectStates i ss = O.projectStates i ss') :
    O.obsEq i (O.lastState ss) (O.lastState ss') := by
  simp only [projectStates] at hproj
  simp only [obsEq, lastState]
  have := congr_arg List.getLast? hproj
  simp only [List.getLast?_map] at this
  cases hss : ss.getLast? <;> cases hss' : ss'.getLast? <;> simp_all [Option.map]

/-! ### Profile types -/

/-- A single player's local strategy: observation-dependent action selection. -/
abbrev LocalStrategy (O : ObsModel ι σ Obs Act) (i : ι) : Type :=
  (v : O.LocalTrace i) → Act i (O.lastObs i v)

/-- Deterministic profile over local visible history.
The return type depends on the last observation in the trace. -/
abbrev PureProfile (O : ObsModel ι σ Obs Act) : Type :=
  ∀ (i : ι), O.LocalStrategy i

/-- Behavioral (stochastic) profile over local visible history.
The distribution is over actions at the last observation. -/
abbrev BehavioralProfile (O : ObsModel ι σ Obs Act) : Type :=
  ∀ (i : ι) (v : O.LocalTrace i), PMF (Act i (O.lastObs i v))

/-- Correlated behavioral profile over the full visible history context. -/
abbrev BehavioralProfileCorr (O : ObsModel ι σ Obs Act) : Type :=
  (v : ∀ i, O.LocalTrace i) → PMF (∀ i, Act i (O.lastObs i (v i)))

/-- Lift a deterministic profile to a behavioral one. -/
noncomputable def pureToBehavioral (O : ObsModel ι σ Obs Act)
    (π : PureProfile O) : BehavioralProfile O :=
  fun i v => PMF.pure (π i v)

/-- Cast a profile's action from `lastObs`-indexed to `observe`-indexed. -/
def castProfileAction (O : ObsModel ι σ Obs Act) (i : ι) (ss : List σ)
    (a : Act i (O.lastObs i (O.projectStates i ss))) :
    Act i (O.observe i (O.lastState ss)) :=
  O.lastObs_projectStates i ss ▸ a

/-- Embed an independent behavioral profile as a correlated one by product sampling. -/
noncomputable def behavioralToCorr
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (O : ObsModel ι σ Obs Act) (b : BehavioralProfile O) : BehavioralProfileCorr O :=
  fun v => Math.PMFProduct.pmfPi (fun i => b i (v i))

/-! ### Stochastic execution -/

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- Independent joint-action distribution induced by a behavioral profile,
in profile-world types (indexed by `lastObs` of the projected observation trace). -/
noncomputable def jointActionDist (O : ObsModel ι σ Obs Act)
    (b : BehavioralProfile O) (ss : List σ) :
    PMF (∀ i, Act i (O.lastObs i (O.projectStates i ss))) :=
  Math.PMFProduct.pmfPi (fun i => b i (O.projectStates i ss))

/-- Cast a profile-world joint action to step-world (observation at the last state). -/
def castJointAction (O : ObsModel ι σ Obs Act) (ss : List σ)
    (a : ∀ i, Act i (O.lastObs i (O.projectStates i ss))) :
    ∀ i, Act i (O.observe i (O.lastState ss)) :=
  fun i => O.lastObs_projectStates i ss ▸ a i

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

/-- Per-step player recall (all players). -/
def PerStepPlayerRecall (O : ObsModel ι σ Obs Act) : Prop :=
  ∀ (i : ι) (s s' t t' : σ) (a : O.JointActionAt s) (a' : O.JointActionAt s'),
    (O.step s a) t ≠ 0 → (O.step s' a') t' ≠ 0 →
    (hobs_i : O.observe i s = O.observe i s') →
    O.observe i t = O.observe i t' →
    hobs_i ▸ (a i) = a' i

/-- Per-step recall for a single player. -/
def PlayerStepRecall (O : ObsModel ι σ Obs Act) (i : ι) : Prop :=
  ∀ (s s' t t' : σ) (a : O.JointActionAt s) (a' : O.JointActionAt s'),
    (O.step s a) t ≠ 0 → (O.step s' a') t' ≠ 0 →
    (hobs_i : O.observe i s = O.observe i s') →
    O.observe i t = O.observe i t' →
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
    hobs_s ▸ (a i) = a' i

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] in
/-- `PerStepPlayerRecall` implies `PerStepActionRecall`. -/
theorem PerStepPlayerRecall.toAction {O : ObsModel ι σ Obs Act}
    (h : O.PerStepPlayerRecall) : O.PerStepActionRecall :=
  fun s s' t t' a a' hs hs' hobs hobst i =>
    h i s s' t t' a a' hs hs' (hobs i) (hobst i)

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
  have := congr_arg List.length h
  simp only [projectStates, List.length_map] at this
  exact this

theorem projectStates_prefix_of_append (O : ObsModel ι σ Obs Act)
    (i : ι) {p p' : List σ} {t t' : σ}
    (h : O.projectStates i (p ++ [t]) = O.projectStates i (p' ++ [t'])) :
    O.projectStates i p = O.projectStates i p' := by
  simp only [projectStates, List.map_append, List.map_cons, List.map_nil] at h
  exact List.append_inj_left' h (by simp)

theorem obsEq_of_projectStates_append (O : ObsModel ι σ Obs Act)
    (i : ι) {p p' : List σ} {t t' : σ}
    (h : O.projectStates i (p ++ [t]) = O.projectStates i (p' ++ [t'])) :
    O.obsEq i t t' := by
  simp only [projectStates, List.map_append, List.map_cons, List.map_nil] at h
  simp only [obsEq]
  have := List.append_inj_right' h (by simp)
  simpa using this

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
  let v : ∀ i, O.LocalTrace i := fun i => O.projectStates i ss
  (b v).bind fun a => O.step s (fun i => O.lastObs_projectStates i ss ▸ a i)

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
    hobs_i ▸ (a i) = a' i

/-- `PerStepPlayerRecall` is equivalent to every player having step recall. -/
theorem perStepPlayerRecall_iff_forall {O : ObsModel ι σ Obs Act} :
    O.PerStepPlayerRecall ↔ ∀ i, O.PlayerStepRecall i :=
  ⟨fun h i => h i, fun h i => h i⟩

/-- `PlayerStepRecall` implies `ReachablePlayerStepRecall` (drop reachability). -/
theorem PlayerStepRecall.toReachable {O : ObsModel ι σ Obs Act} {i : ι}
    (h : O.PlayerStepRecall i) : O.ReachablePlayerStepRecall i :=
  fun _ _ _ _ _ _ hs hs' hobs hobst _ _ => h _ _ _ _ _ _ hs hs' hobs hobst

/-- `PlayerStepRecall` implies `TracePlayerStepRecall` (drop trace witnesses). -/
theorem PlayerStepRecall.toTrace {O : ObsModel ι σ Obs Act} {i : ι}
    (h : O.PlayerStepRecall i) : O.TracePlayerStepRecall i :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hs hs' hobst hobs => h _ _ _ _ _ _ hs hs' hobs hobst

end NoFintype2

/-! ### Mediator construction -/

/-- Mediator construction: condition `ν` on the probability of reaching
the current state trace, then extract joint actions in profile-world types. -/
noncomputable def mixedToMediator (O : ObsModel ι σ Obs Act)
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    [Fintype (PureProfile O)]
    (ν : PMF (PureProfile O))
    (n : Nat) (ss : List σ) :
    PMF (∀ i, Act i (O.lastObs i (O.projectStates i ss))) :=
  (reweightPMF ν (fun π => pureRun O.pureStep O.init n π ss)).bind
    (fun π => O.jointActionDist (O.pureToBehavioral π) ss)

end ObsModel
