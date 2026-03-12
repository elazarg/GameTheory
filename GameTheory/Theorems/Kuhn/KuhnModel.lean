import Math.ParameterizedChain
import Semantics.DSMachine

/-! # KuhnModel

Semantic core for Kuhn's theorem.

This file defines the execution model used by the generic Kuhn-theorem
development:

- per-player information states,
- observation-indexed actions,
- bounded run semantics,
- correlated mediator semantics,
- reachability-style structural conditions on traces.

`KuhnModel` is an alias of `ObsModelCore`.

The strategic object is the player-local information state. Observations are
retained as an explicit readout because action types and several semantic
constructions are indexed by the current observation.
-/

open Math.ProbabilityMassFunction Math.ParameterizedChain

/-- Player-local information state over an observation type `α`.

`start` initializes the information state from the initial observation,
`push` updates it with a newly observed value, and `current` exposes the
current observation stored in the state. The two axioms state that `current`
returns the most recently incorporated observation. -/
structure InfoStateCore (α : Type) where
  Carrier : Type
  start : α → Carrier
  push : Carrier → α → Carrier
  current : Carrier → α
  current_start : ∀ a, current (start a) = a
  current_push : ∀ h a, current (push h a) = a

/-- Multi-player information-state model over a `DSMachine` with
observation-indexed actions. The label at state `s` is the joint action
`∀ i, Act i (observe i s)`. -/
structure ObsModelCore
    (ι σ : Type) (Obs : ι → Type) (Act : (i : ι) → Obs i → Type) where
  /-- Per-player strategic information-state representation. -/
  infoState : (i : ι) → InfoStateCore (Obs i)
  /-- Per-player observation function on states. -/
  observe : (i : ι) → σ → Obs i
  /-- Underlying dependent stochastic machine. -/
  machine : DSMachine σ (fun s => ∀ i, Act i (observe i s))

/-- Preferred conceptual name for the semantic core of Kuhn's theorem. -/
abbrev KuhnModel := ObsModelCore

namespace ObsModelCore

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}

/-- Initial state (delegated to `machine`). -/
abbrev init (O : ObsModelCore ι σ Obs Act) : σ := O.machine.init

/-- Stochastic step (delegated to `machine`). -/
abbrev step (O : ObsModelCore ι σ Obs Act) (s : σ) : (∀ i, Act i (O.observe i s)) → PMF σ :=
  O.machine.step s

/-- Joint action profile at state `s`. -/
abbrev JointActionAt (O : ObsModelCore ι σ Obs Act) (s : σ) := ∀ i, Act i (O.observe i s)

/-- Last state of a trace (or initial state for empty traces). -/
def lastState (O : ObsModelCore ι σ Obs Act) (ss : List σ) : σ :=
  ss.getLast?.getD O.init

/-- Player-local strategic information state. -/
abbrev InfoState (O : ObsModelCore ι σ Obs Act) (i : ι) := (O.infoState i).Carrier

/-- Current observation stored in a player-local information state. -/
def currentObs (O : ObsModelCore ι σ Obs Act) (i : ι) (v : O.InfoState i) : Obs i :=
  (O.infoState i).current v

/-- Extend a local information state by projecting additional states. -/
def projectStatesFrom (O : ObsModelCore ι σ Obs Act) (i : ι) (v : O.InfoState i) :
    List σ → O.InfoState i
  | [] => v
  | s :: ss => O.projectStatesFrom i ((O.infoState i).push v (O.observe i s)) ss

/-- Compute player `i`'s information state after observing the states in `ss`,
starting from the initial observation at `O.init`. -/
def projectStates (O : ObsModelCore ι σ Obs Act) (i : ι) (ss : List σ) : O.InfoState i :=
  O.projectStatesFrom i ((O.infoState i).start (O.observe i O.init)) ss

/-- The current observation stored after processing `ss` is the last observed
state in `ss`, if any; otherwise it is the current observation already stored
in the starting information state `v`. -/
theorem currentObs_projectStatesFrom (O : ObsModelCore ι σ Obs Act) (i : ι)
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
def obsEq (O : ObsModelCore ι σ Obs Act) (i : ι) (s t : σ) : Prop :=
  O.observe i s = O.observe i t

/-- The current observation of a projected information state is the observation
at the last state. -/
theorem currentObs_projectStates (O : ObsModelCore ι σ Obs Act) (i : ι) (ss : List σ) :
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

/-- A single player's local strategy: information-state-dependent action
selection, with the action type determined by the current observation. -/
abbrev LocalStrategy (O : ObsModelCore ι σ Obs Act) (i : ι) : Type :=
  (v : O.InfoState i) → Act i (O.currentObs i v)

/-- Deterministic profile over local information states. -/
abbrev PureProfile (O : ObsModelCore ι σ Obs Act) : Type :=
  ∀ (i : ι), O.LocalStrategy i

/-- Independent behavioral strategy profile: for each player `i` and local
information state `v`, a distribution over actions at the current observation
stored in `v`. -/
abbrev BehavioralProfile (O : ObsModelCore ι σ Obs Act) : Type :=
  ∀ (i : ι) (v : O.InfoState i), PMF (Act i (O.currentObs i v))

/-- Correlated behavioral profile over the full information-state context. -/
abbrev BehavioralProfileCorr (O : ObsModelCore ι σ Obs Act) : Type :=
  (v : ∀ i, O.InfoState i) → PMF (∀ i, Act i (O.currentObs i (v i)))

/-- Lift a deterministic profile to a behavioral one. -/
noncomputable def pureToBehavioral (O : ObsModelCore ι σ Obs Act)
    (π : PureProfile O) : BehavioralProfile O :=
  fun i v => PMF.pure (π i v)

section FintypeInstances

open Classical in
/-- Finite information states and finite action alphabets give finitely many
local strategies. -/
noncomputable instance localStrategyFintype (O : ObsModelCore ι σ Obs Act)
    [∀ i, Fintype (O.InfoState i)] [∀ i o, Fintype (Act i o)] (i : ι) :
    Fintype (O.LocalStrategy i) := by
  unfold LocalStrategy
  infer_instance

end FintypeInstances

/-- Cast a profile's action from information-state world to step world. -/
def castProfileAction (O : ObsModelCore ι σ Obs Act) (i : ι) (ss : List σ)
    (a : Act i (O.currentObs i (O.projectStates i ss))) :
    Act i (O.observe i (O.lastState ss)) :=
  O.currentObs_projectStates i ss ▸ a

/-- Independent joint-action distribution induced by a behavioral profile. -/
noncomputable def jointActionDist (O : ObsModelCore ι σ Obs Act)
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (b : BehavioralProfile O) (ss : List σ) :
    PMF (∀ i, Act i (O.currentObs i (O.projectStates i ss))) :=
  Math.PMFProduct.pmfPi (fun i => b i (O.projectStates i ss))

/-- Cast a profile-world joint action to step-world. -/
def castJointAction (O : ObsModelCore ι σ Obs Act) (ss : List σ)
    (a : ∀ i, Act i (O.currentObs i (O.projectStates i ss))) :
    ∀ i, Act i (O.observe i (O.lastState ss)) :=
  fun i => O.currentObs_projectStates i ss ▸ a i

/-- Embed an independent behavioral profile as a correlated one by product sampling. -/
noncomputable def behavioralToCorr
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (O : ObsModelCore ι σ Obs Act) (b : BehavioralProfile O) : BehavioralProfileCorr O :=
  fun v => Math.PMFProduct.pmfPi (fun i => b i (v i))

/-- One stochastic step: sample action from profile, cast to step-world, then step. -/
noncomputable def stepDist (O : ObsModelCore ι σ Obs Act)
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (b : BehavioralProfile O) (ss : List σ) : PMF σ :=
  let s := O.lastState ss
  (O.jointActionDist b ss).bind fun a => O.step s (O.castJointAction ss a)

/-- Distribution on state traces of length `k + 1` obtained by running the
machine for `k` steps under behavioral profile `b`, starting from `[init]`. -/
noncomputable def runDist (O : ObsModelCore ι σ Obs Act)
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (k : Nat) (b : BehavioralProfile O) : PMF (List σ) :=
  Nat.rec (PMF.pure [O.init])
    (fun _ rec =>
      rec.bind (fun ss =>
        pushforward (O.stepDist b ss) (fun t => ss ++ [t])))
    k

/-- Pure-profile run distribution via `pureToBehavioral`. -/
noncomputable def runDistPure (O : ObsModelCore ι σ Obs Act)
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (k : Nat) (π : PureProfile O) : PMF (List σ) :=
  O.runDist k (O.pureToBehavioral π)

/-- The pure step function: directly applies `O.step` at the deterministic action. -/
noncomputable def pureStep (O : ObsModelCore ι σ Obs Act)
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (π : PureProfile O) (ss : List σ) : PMF σ :=
  O.stepDist (O.pureToBehavioral π) ss

/-- `runDistPure` equals `pureRun` applied to `pureStep`. -/
theorem runDistPure_eq_pureRun (O : ObsModelCore ι σ Obs Act)
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (k : Nat) (π : PureProfile O) :
    O.runDistPure k π = pureRun (O.pureStep) O.init k π := rfl

/-- Reachability witness via nonzero-probability transitions (Type-valued). -/
inductive ReachActionTrace (O : ObsModelCore ι σ Obs Act) : List σ → Type
  | init : ReachActionTrace O [O.init]
  | snoc {ss : List σ} {s t : σ} (a : O.JointActionAt s) :
      ReachActionTrace O ss →
      ss.getLast? = some s →
      (O.step s a) t ≠ 0 →
      ReachActionTrace O (ss ++ [t])

/-- A state is reachable if it appears at the end of some nonzero-probability trace. -/
def StepReachable (O : ObsModelCore ι σ Obs Act) (s : σ) : Prop :=
  ∃ (ss : List σ), Nonempty (O.ReachActionTrace ss) ∧ ss.getLast? = some s

/-- One stochastic step under a correlated behavioral profile. -/
noncomputable def stepDistCorr (O : ObsModelCore ι σ Obs Act)
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (b : BehavioralProfileCorr O) (ss : List σ) : PMF σ :=
  let s := O.lastState ss
  let v : ∀ i, O.InfoState i := fun i => O.projectStates i ss
  (b v).bind fun a => O.step s (fun i => O.currentObs_projectStates i ss ▸ a i)

/-- Per-step action recall on the core information-state model. -/
def PerStepActionRecall (O : ObsModelCore ι σ Obs Act) : Prop :=
  ∀ (s s' t t' : σ) (a : O.JointActionAt s) (a' : O.JointActionAt s'),
    (O.step s a) t ≠ 0 → (O.step s' a') t' ≠ 0 →
    (hobs : ∀ i, O.observe i s = O.observe i s') →
    (∀ i, O.observe i t = O.observe i t') →
    ∀ i, (hobs i) ▸ (a i) = a' i

/-- Mediator construction: condition `ν` on the probability of reaching
the current state trace, then extract joint actions in profile-world types. -/
noncomputable def mixedToMediator (O : ObsModelCore ι σ Obs Act)
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    [Fintype (PureProfile O)]
    (ν : PMF (PureProfile O))
    (n : Nat) (ss : List σ) :
    PMF (∀ i, Act i (O.currentObs i (O.projectStates i ss))) :=
  (reweightPMF ν (fun π => pureRun O.pureStep O.init n π ss)).bind
    (fun π => O.jointActionDist (O.pureToBehavioral π) ss)

/-- On every reachable trace, any repeated information state has trivial action space.

More precisely: if `ss` has nonzero probability under `runDistPure k π`, and
player `i` sees the same projected information state at two positions on `ss`,
then the action space at that information state is `Subsingleton`.

This condition is used in the behavioral-to-mixed direction of Kuhn's theorem
to rule out repeated nontrivial contingent choices along a reachable trace. -/
def NoNontrivialInfoStateRepeat (O : ObsModelCore ι σ Obs Act)
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] : Prop :=
  ∀ (i : ι) (π : PureProfile O) (k : Nat) (ss : List σ),
    O.runDistPure k π ss ≠ 0 →
    ∀ (j₁ j₂ : Nat), j₁ < j₂ → j₂ < ss.length →
      O.projectStates i (ss.take (j₁ + 1)) =
        O.projectStates i (ss.take (j₂ + 1)) →
      Subsingleton (Act i (O.currentObs i
        (O.projectStates i (ss.take (j₂ + 1)))))

end ObsModelCore
