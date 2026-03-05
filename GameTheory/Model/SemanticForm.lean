import Math.Probability
import Math.PMFProduct
import Math.ProbabilityMassFunction
import GameTheory.Model.FiniteRecall

/-!
# GameTheory.Model.SemanticForm

Semantics-first model decomposition:
- `LSM`: labeled nondeterministic machine with joint actions
- `InfoModel`: information structure over an `LSM`
- `ControlModel`: common-knowledge controller specifications (separate layer)

`ObsRecall`, `ActionRecall`, `PerfectRecall`, and `FiniteHorizon` are predicates,
not built-in requirements.
-/

namespace GameTheory

open Math.Probability

/-- Labeled nondeterministic machine with joint (possibly inactive) actions. -/
structure LSM (ι : Type) where
  Label : Type
  State : Type
  Act : ι → Type
  init : State
  step : Label → (∀ i, Option (Act i)) → State → State → Prop

namespace LSM

variable {ι : Type}

/-- Action-erased one-step relation. -/
def stepExists (M : LSM ι) : M.Label → M.State → M.State → Prop :=
  fun ℓ s t => ∃ a, M.step ℓ a s t

/-- Bounded-horizon predicate (theorem-local assumption). -/
def FiniteHorizon (M : LSM ι) (k : Nat) : Prop :=
  ∀ (h : List M.Label) (s : M.State),
    Semantics.Transition.ReachBy M.stepExists h M.init s → h.length ≤ k

end LSM

/-- Information structure over a fixed machine. -/
structure InfoModel {ι : Type} (M : LSM ι) where
  Obs : ι → Type
  /-- Primitive observation map from states. -/
  observe : (i : ι) → M.State → Obs i
  /-- Information partition as a state equivalence relation per controller. -/
  infoSetoid : (i : ι) → Setoid M.State

namespace InfoModel

variable {ι : Type} {M : LSM ι}

/-- Derived observation-equivalence relation from the partition. -/
def obsEq (I : InfoModel M) (i : ι) : M.State → M.State → Prop :=
  (I.infoSetoid i).r

/-- Controller-local observation-trace type. -/
abbrev LocalTrace (I : InfoModel M) (i : ι) : Type :=
  List (I.Obs i)

/-- Derived global projected-trace outcome (no primitive `Outcome` type). -/
abbrev Outcome (I : InfoModel M) : Type := ∀ i, I.LocalTrace i

/-- Local projection by mapping primitive state observations over a state trace. -/
def projectStates (I : InfoModel M) (i : ι) (ss : List M.State) : I.LocalTrace i :=
  ss.map (I.observe i)

/-- Outcome induced by a machine state trace via local projections. -/
def outcomeOfStates (I : InfoModel M) (ss : List M.State) : I.Outcome :=
  fun i => I.projectStates i ss

/-- Reachability witness carrying both labels and visited states (states include init). -/
inductive ReachStateTrace (M : LSM ι) : List M.Label → List M.State → Prop
  | nil : ReachStateTrace M [] [M.init]
  | snoc {h : List M.Label} {ss : List M.State} {s t : M.State} {ℓ : M.Label} :
      ReachStateTrace M h ss →
      ss.getLast? = some s →
      M.stepExists ℓ s t →
      ReachStateTrace M (h ++ [ℓ]) (ss ++ [t])

/-- Reachability witness carrying labels, joint actions, and visited states. -/
inductive ReachActionTrace (M : LSM ι) :
    List (M.Label × (∀ i, Option (M.Act i))) → List M.State → Prop
  | nil : ReachActionTrace M [] [M.init]
  | snoc
      {ha : List (M.Label × (∀ i, Option (M.Act i)))}
      {ss : List M.State} {s t : M.State} {ℓ : M.Label} {a : ∀ i, Option (M.Act i)} :
      ReachActionTrace M ha ss →
      ss.getLast? = some s →
      M.step ℓ a s t →
      ReachActionTrace M (ha ++ [(ℓ, a)]) (ss ++ [t])

/-- Player-local projected own-action trace from an action-annotated history. -/
def projectActions (i : ι)
    (ha : List (M.Label × (∀ j, Option (M.Act j)))) : List (Option (M.Act i)) :=
  ha.map (fun e => e.2 i)

/-- Project an action trace to a state trace by forgetting joint actions. -/
theorem ReachActionTrace.toReachStateTrace {ha : List (M.Label × (∀ i, Option (M.Act i)))}
    {ss : List M.State} (h : ReachActionTrace M ha ss) :
    ReachStateTrace M (ha.map Prod.fst) ss := by
  induction h with
  | nil => exact .nil
  | snoc _ hlast hstep ih =>
    simp only [List.map_append, List.map_cons, List.map_nil]
    exact .snoc ih hlast ⟨_, hstep⟩

/-- Observation recall: indistinguishable terminal states imply identical
player-local projected observation traces on the corresponding reaches. -/
def ObsRecall (I : InfoModel M) : Prop :=
  ∀ (i : ι) (h₁ h₂ : List M.Label) (ss₁ ss₂ : List M.State) (s₁ s₂ : M.State),
    ReachStateTrace M h₁ ss₁ →
    ReachStateTrace M h₂ ss₂ →
    ss₁.getLast? = some s₁ →
    ss₂.getLast? = some s₂ →
    I.obsEq i s₁ s₂ →
    I.projectStates i ss₁ = I.projectStates i ss₂

/-- Action recall: indistinguishable terminal states imply identical
player-local own-action traces on the corresponding action-annotated reaches. -/
def ActionRecall (I : InfoModel M) : Prop :=
  ∀ (i : ι)
    (ha₁ ha₂ : List (M.Label × (∀ j, Option (M.Act j))))
    (ss₁ ss₂ : List M.State) (s₁ s₂ : M.State),
    ReachActionTrace M ha₁ ss₁ →
    ReachActionTrace M ha₂ ss₂ →
    ss₁.getLast? = some s₁ →
    ss₂.getLast? = some s₂ →
    I.obsEq i s₁ s₂ →
    projectActions i ha₁ = projectActions i ha₂

/-- Perfect recall is the conjunction of observation recall and action recall. -/
def PerfectRecall (I : InfoModel M) : Prop :=
  I.ObsRecall ∧ I.ActionRecall

theorem perfectRecall_obs {I : InfoModel M} (hPR : I.PerfectRecall) : I.ObsRecall :=
  hPR.1

theorem perfectRecall_action {I : InfoModel M} (hPR : I.PerfectRecall) : I.ActionRecall :=
  hPR.2

end InfoModel

/-- Common-knowledge controller specification over local traces/observations. -/
inductive ControlSpec (Label Obs Act : Type) where
  | utility  : (List Obs → ℝ) → ControlSpec Label Obs Act
  | behavior : (Label → Obs → PMF (Option Act)) → ControlSpec Label Obs Act

/-- Public control layer, separated from machine and information layers. -/
structure ControlModel {ι : Type} (M : LSM ι) (I : InfoModel M) where
  control : ∀ i, ControlSpec M.Label (I.Obs i) (M.Act i)

namespace Execution

variable {ι : Type} {M : LSM ι}

/-- Joint (possibly inactive) action profile. -/
abbrev JointAction (M : LSM ι) : Type := ∀ i, Option (M.Act i)

/-- Deterministic profile over label and local trace view. -/
abbrev PureProfile (I : InfoModel M) : Type :=
  ∀ i, I.LocalTrace i → Option (M.Act i)

/-- Behavioral profile over label and local trace view. -/
abbrev BehavioralProfile (I : InfoModel M) : Type :=
  ∀ i, I.LocalTrace i → PMF (Option (M.Act i))

/-- Lift a deterministic profile to a behavioral one. -/
noncomputable def pureToBehavioral (I : InfoModel M) (π : PureProfile I) : BehavioralProfile I :=
  fun i v => PMF.pure (π i v)

/-- Stochastic execution choices on top of nondeterministic machine rules. -/
structure Dynamics (I : InfoModel M) where
  /-- Label sampling policy from current state. -/
  labelKernel : M.State → PMF M.Label
  /-- Next-state kernel, conditioned on label/joint-action/current-state. -/
  nextState : M.Label → JointAction M → M.State → PMF M.State
  /-- Soundness: sampled next states respect machine step relation. -/
  nextState_sound :
    ∀ (ℓ : M.Label) (a : JointAction M) (s t : M.State),
      (nextState ℓ a s) t ≠ 0 → M.step ℓ a s t

namespace Dynamics

variable {I : InfoModel M}

open Classical in
/-- Independent joint-action distribution induced by a behavioral profile. -/
noncomputable def jointActionDist
    [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) (ss : List M.State) : PMF (JointAction M) :=
  Math.PMFProduct.pmfPi (fun i => σ i (I.projectStates i ss))

/-- One stochastic step from a current state under behavioral profile `σ`. -/
noncomputable def stepDist (D : Dynamics I)
    [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) (ss : List M.State) : PMF (M.Label × M.State) :=
  let s := (ss.getLast?).getD M.init
  (D.labelKernel s).bind fun ℓ =>
    (jointActionDist (I := I) σ ss).bind fun a =>
      Math.ProbabilityMassFunction.pushforward (D.nextState ℓ a s) (fun t => (ℓ, t))

/-- Bounded run distribution of length exactly `k`:
stores (label-trace, state-trace). -/
noncomputable def runDist (D : Dynamics I)
    [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (σ : BehavioralProfile I) : PMF (List M.Label × List M.State) :=
  Nat.rec (PMF.pure ([], [M.init]))
    (fun _ rec =>
      rec.bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward (D.stepDist σ hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))))
    k

/-- Pure-profile run distribution via `pureToBehavioral`. -/
noncomputable def runDistPure (D : Dynamics I)
    [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (π : PureProfile I) : PMF (List M.Label × List M.State) :=
  D.runDist k (pureToBehavioral I π)

/-- Outcome distribution (projected-trace outcome) from bounded behavioral runs. -/
noncomputable def evalBehavioral (D : Dynamics I)
    [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (σ : BehavioralProfile I) : PMF I.Outcome :=
  Math.ProbabilityMassFunction.pushforward (D.runDist k σ) (fun hs => I.outcomeOfStates hs.2)

/-- Outcome distribution from bounded pure runs. -/
noncomputable def evalPure (D : Dynamics I)
    [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (π : PureProfile I) : PMF I.Outcome :=
  Math.ProbabilityMassFunction.pushforward (D.runDistPure k π) (fun hs => I.outcomeOfStates hs.2)

end Dynamics
end Execution

end GameTheory
