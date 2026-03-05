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

`PerfectRecall` and `FiniteHorizon` are predicates, not built-in requirements.
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
  /-- Information partition as a state equivalence relation per controller. -/
  infoSetoid : (i : ι) → Setoid M.State
  /-- Local projected trace for each controller. -/
  project : (i : ι) → List M.Label → List (Obs i ⊕ Option (M.Act i))

namespace InfoModel

variable {ι : Type} {M : LSM ι}

/-- Derived observation-equivalence relation from the partition. -/
def obsEq (I : InfoModel M) (i : ι) : M.State → M.State → Prop :=
  (I.infoSetoid i).r

/-- Controller-local projected-trace type. -/
abbrev LocalTrace (I : InfoModel M) (i : ι) : Type :=
  List (I.Obs i ⊕ Option (M.Act i))

/-- Derived global projected-trace outcome (no primitive `Outcome` type). -/
abbrev Outcome (I : InfoModel M) : Type := ∀ i, I.LocalTrace i

/-- Outcome induced by a machine label trace via local projections. -/
def outcomeOfTrace (I : InfoModel M) (h : List M.Label) : I.Outcome :=
  fun i => I.project i h

/-- Perfect recall as an independent predicate over `(M, I)`. -/
def PerfectRecall (I : InfoModel M) : Prop :=
  Model.FiniteRecall.PerfectRecall
    M.stepExists M.init (fun i => I.LocalTrace i)
    I.obsEq I.project

end InfoModel

/-- Common-knowledge controller specification over local traces/observations. -/
inductive ControlSpec (Label Obs Act : Type) where
  | utility  : (List (Obs ⊕ Option Act) → ℝ) → ControlSpec Label Obs Act
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
  ∀ i, M.Label → I.LocalTrace i → Option (M.Act i)

/-- Behavioral profile over label and local trace view. -/
abbrev BehavioralProfile (I : InfoModel M) : Type :=
  ∀ i, M.Label → I.LocalTrace i → PMF (Option (M.Act i))

/-- Lift a deterministic profile to a behavioral one. -/
noncomputable def pureToBehavioral (I : InfoModel M) (π : PureProfile I) : BehavioralProfile I :=
  fun i ℓ v => PMF.pure (π i ℓ v)

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
    (σ : BehavioralProfile I) (h : List M.Label) (ℓ : M.Label) : PMF (JointAction M) :=
  Math.PMFProduct.pmfPi (fun i => σ i ℓ (I.project i h))

/-- One stochastic step from a current state under behavioral profile `σ`. -/
noncomputable def stepDist (D : Dynamics I)
    [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) (h : List M.Label) (s : M.State) : PMF (M.Label × M.State) :=
  (D.labelKernel s).bind fun ℓ =>
    (jointActionDist (I := I) σ h ℓ).bind fun a =>
      Math.ProbabilityMassFunction.pushforward (D.nextState ℓ a s) (fun t => (ℓ, t))

/-- Bounded run distribution of length exactly `k`:
stores (label-trace, current-state). -/
noncomputable def runDist (D : Dynamics I)
    [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (σ : BehavioralProfile I) : PMF (List M.Label × M.State) :=
  Nat.rec (PMF.pure ([], M.init))
    (fun _ rec =>
      rec.bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward (D.stepDist σ hs.1 hs.2)
          (fun ls => (hs.1 ++ [ls.1], ls.2))))
    k

/-- Pure-profile run distribution via `pureToBehavioral`. -/
noncomputable def runDistPure (D : Dynamics I)
    [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (π : PureProfile I) : PMF (List M.Label × M.State) :=
  D.runDist k (pureToBehavioral I π)

/-- Outcome distribution (projected-trace outcome) from bounded behavioral runs. -/
noncomputable def evalBehavioral (D : Dynamics I)
    [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (σ : BehavioralProfile I) : PMF I.Outcome :=
  Math.ProbabilityMassFunction.pushforward (D.runDist k σ) (fun hs => I.outcomeOfTrace hs.1)

/-- Outcome distribution from bounded pure runs. -/
noncomputable def evalPure (D : Dynamics I)
    [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (π : PureProfile I) : PMF I.Outcome :=
  Math.ProbabilityMassFunction.pushforward (D.runDistPure k π) (fun hs => I.outcomeOfTrace hs.1)

end Dynamics
end Execution

end GameTheory
