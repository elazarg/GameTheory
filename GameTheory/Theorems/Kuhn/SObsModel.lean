import Math.ParameterizedChain
import Math.PMFProduct

/-! # Stochastic observation model (standalone)

Self-contained definition of `SObsModel` — verifies no hidden dependency on
the nondeterministic `ObsModel` or `Dynamics`.

The step function is `step : JointAction → σ → PMF σ`, a deterministic map
from (action, state) to a distribution over next states. -/

set_option autoImplicit false

namespace GameTheory

open Math.ProbabilityMassFunction Math.ParameterizedChain

/-- Stochastic observation model. The step function deterministically maps
a joint action and current state to a distribution over next states. -/
structure SObsModel (ι σ : Type) (Act : ι → Type) where
  /-- Initial state. -/
  init : σ
  /-- Stochastic transition: given joint action and state, produce a distribution
  over next states. -/
  step : (∀ i, Option (Act i)) → σ → PMF σ
  /-- Per-player observation type. -/
  Obs : ι → Type
  /-- Per-player observation function on states. -/
  observe : (i : ι) → σ → Obs i

namespace SObsModel

variable {ι σ : Type} {Act : ι → Type}

/-- Joint (possibly inactive) action profile. -/
abbrev JointAction (_ : SObsModel ι σ Act) := ∀ i, Option (Act i)

/-! ### Observations and projections -/

/-- Player-local visible trace: list of per-step observations. -/
abbrev LocalTrace (O : SObsModel ι σ Act) (i : ι) := List (O.Obs i)

/-- Project a state trace to player `i`'s local observation trace. -/
def projectStates (O : SObsModel ι σ Act) (i : ι) (ss : List σ) : O.LocalTrace i :=
  ss.map (O.observe i)

/-- Observation equivalence: two states look the same to player `i`. -/
def obsEq (O : SObsModel ι σ Act) (i : ι) (s t : σ) : Prop :=
  O.observe i s = O.observe i t

theorem obsEq_of_projectStates_getLast (O : SObsModel ι σ Act) (i : ι) {ss ss' : List σ}
    (hproj : O.projectStates i ss = O.projectStates i ss') :
    O.obsEq i (ss.getLast?.getD O.init) (ss'.getLast?.getD O.init) := by
  simp only [projectStates] at hproj
  simp only [obsEq]
  have := congr_arg List.getLast? hproj
  simp only [List.getLast?_map] at this
  cases hss : ss.getLast? <;> cases hss' : ss'.getLast? <;> simp_all [Option.map]

/-! ### Profile types -/

/-- Deterministic profile over local visible history. -/
abbrev PureProfile (O : SObsModel ι σ Act) : Type :=
  ∀ i, O.LocalTrace i → Option (Act i)

/-- Behavioral (stochastic) profile over local visible history. -/
abbrev BehavioralProfile (O : SObsModel ι σ Act) : Type :=
  ∀ i, O.LocalTrace i → PMF (Option (Act i))

/-- Correlated behavioral profile over the full visible history context. -/
abbrev BehavioralProfileCorr (O : SObsModel ι σ Act) : Type :=
  (∀ i, O.LocalTrace i) → PMF (O.JointAction)

/-- Lift a deterministic profile to a behavioral one. -/
noncomputable def pureToBehavioral (O : SObsModel ι σ Act)
    (π : PureProfile O) : BehavioralProfile O :=
  fun i v => PMF.pure (π i v)

/-- Embed an independent behavioral profile as a correlated one by product sampling. -/
noncomputable def behavioralToCorr
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (O : SObsModel ι σ Act) (b : BehavioralProfile O) : BehavioralProfileCorr O :=
  fun v => Math.PMFProduct.pmfPi (fun i => b i (v i))

/-! ### Stochastic execution -/

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (Act i))]

/-- Independent joint-action distribution induced by a behavioral profile. -/
noncomputable def jointActionDist (O : SObsModel ι σ Act)
    (b : BehavioralProfile O) (ss : List σ) : PMF O.JointAction :=
  Math.PMFProduct.pmfPi (fun i => b i (O.projectStates i ss))

/-- One stochastic step: sample action from profile, then step. -/
noncomputable def stepDist (O : SObsModel ι σ Act)
    (b : BehavioralProfile O) (ss : List σ) : PMF σ :=
  let s := (ss.getLast?).getD O.init
  (O.jointActionDist b ss).bind fun a => O.step a s

/-- Bounded run distribution under behavioral profile. -/
noncomputable def runDist (O : SObsModel ι σ Act)
    (k : Nat) (b : BehavioralProfile O) : PMF (List σ) :=
  Nat.rec (PMF.pure [O.init])
    (fun _ rec =>
      rec.bind (fun ss =>
        pushforward (O.stepDist b ss) (fun t => ss ++ [t])))
    k

/-- Pure-profile run distribution via `pureToBehavioral`. -/
noncomputable def runDistPure (O : SObsModel ι σ Act)
    (k : Nat) (π : PureProfile O) : PMF (List σ) :=
  O.runDist k (O.pureToBehavioral π)

/-- The pure step function: directly applies `O.step` at the deterministic action.
For a pure profile, `jointActionDist` is a point mass, so this simplifies to
`O.step (fun i => π i (projectStates i ss)) (last ss)`. -/
noncomputable def pureStep (O : SObsModel ι σ Act) (π : PureProfile O)
    (ss : List σ) : PMF σ :=
  O.stepDist (O.pureToBehavioral π) ss

/-- `runDistPure` equals `pureRun` applied to `pureStep`. -/
theorem runDistPure_eq_pureRun (O : SObsModel ι σ Act) (k : Nat) (π : PureProfile O) :
    O.runDistPure k π = pureRun (O.pureStep) O.init k π := rfl

/-! ### Reachability -/

/-- Reachability witness via nonzero-probability transitions. -/
inductive ReachActionTrace (O : SObsModel ι σ Act) :
    List O.JointAction → List σ → Prop
  | nil : ReachActionTrace O [] [O.init]
  | snoc {ha : List O.JointAction} {ss : List σ} {s t : σ} {a : O.JointAction} :
      ReachActionTrace O ha ss →
      ss.getLast? = some s →
      (O.step a s) t ≠ 0 →
      ReachActionTrace O (ha ++ [a]) (ss ++ [t])

/-- A state is reachable if it appears at the end of some nonzero-probability trace. -/
def StepReachable (O : SObsModel ι σ Act) (s : σ) : Prop :=
  ∃ (ha : List O.JointAction) (ss : List σ),
    O.ReachActionTrace ha ss ∧ ss.getLast? = some s

/-! ### Recall predicates -/

/-- Per-step action recall: any two transitions with observation-equivalent
source and target must use the same joint action.
Uses `(O.step a s) t ≠ 0` as the transition predicate. -/
def PerStepActionRecall (O : SObsModel ι σ Act) : Prop :=
  ∀ (a a' : O.JointAction) (s s' t t' : σ),
    (O.step a s) t ≠ 0 → (O.step a' s') t' ≠ 0 →
    (∀ i, O.obsEq i s s') → (∀ i, O.obsEq i t t') →
    a = a'

/-- Per-step player recall (all players). -/
def PerStepPlayerRecall (O : SObsModel ι σ Act) : Prop :=
  ∀ (i : ι) (a a' : O.JointAction) (s s' t t' : σ),
    (O.step a s) t ≠ 0 → (O.step a' s') t' ≠ 0 →
    O.obsEq i s s' → O.obsEq i t t' →
    a i = a' i

/-- Per-step recall for a single player. -/
def PlayerStepRecall (O : SObsModel ι σ Act) (i : ι) : Prop :=
  ∀ (a a' : O.JointAction) (s s' t t' : σ),
    (O.step a s) t ≠ 0 → (O.step a' s') t' ≠ 0 →
    O.obsEq i s s' → O.obsEq i t t' →
    a i = a' i

/-- Trace-level per-step player recall: weakest syntactic condition for Kuhn. -/
def TracePlayerStepRecall (O : SObsModel ι σ Act) (i : ι) : Prop :=
  ∀ (a a' : O.JointAction) (t t' : σ)
    (ss ss' : List σ),
    (∃ ha, O.ReachActionTrace ha ss) →
    (∃ ha', O.ReachActionTrace ha' ss') →
    O.projectStates i ss = O.projectStates i ss' →
    (O.step a (ss.getLast?.getD O.init)) t ≠ 0 →
    (O.step a' (ss'.getLast?.getD O.init)) t' ≠ 0 →
    O.obsEq i t t' →
    a i = a' i

/-- `PerStepPlayerRecall` implies `PerStepActionRecall`. -/
theorem PerStepPlayerRecall.toAction {O : SObsModel ι σ Act}
    (h : O.PerStepPlayerRecall) : O.PerStepActionRecall :=
  fun a a' s s' t t' hs hs' hobs hobst =>
    funext fun i => h i a a' s s' t t' hs hs' (hobs i) (hobst i)

set_option linter.unusedDecidableInType false in
/-- `PlayerStepRecall` implies `TracePlayerStepRecall`. -/
theorem PlayerStepRecall.toTrace {O : SObsModel ι σ Act} {i : ι}
    (h : O.PlayerStepRecall i) : O.TracePlayerStepRecall i := by
  intro a a' t t' ss ss' _ _ hproj hstep hstep' hobst
  exact h a a' _ _ t t' hstep hstep'
    (O.obsEq_of_projectStates_getLast i hproj) hobst

/-! ### Observation recall -/

/-- Observation recall: indistinguishable terminal states imply identical
player-local visible histories. -/
def ObsRecall (O : SObsModel ι σ Act) : Prop :=
  ∀ (i : ι) (ss₁ ss₂ : List σ),
    (∃ ha, O.ReachActionTrace ha ss₁) →
    (∃ ha, O.ReachActionTrace ha ss₂) →
    O.obsEq i (ss₁.getLast?.getD O.init) (ss₂.getLast?.getD O.init) →
    O.projectStates i ss₁ = O.projectStates i ss₂

/-! ### Main theorem statements -/

open Math.PMFProduct in
set_option linter.unusedFintypeInType false in
/-- **Correlated realization** on `SObsModel`: no assumptions needed. -/
theorem correlated_realization (O : SObsModel ι σ Act)
    [Fintype (PureProfile O)]
    (ν : PMF (PureProfile O)) (k : Nat) :
    ∃ m : Nat → List σ → PMF O.JointAction,
      seqRun (fun n ss =>
        (m n ss).bind (fun a => O.step a ((ss.getLast?).getD O.init)))
        O.init k =
      ν.bind (pureRun O.pureStep O.init k) := by
  sorry

open Classical Math.PMFProduct in
set_option linter.unusedFintypeInType false in
/-- **Kuhn M→B** on `SObsModel` under the weakest syntactic condition. -/
theorem kuhn_mixed_to_behavioral_trace (O : SObsModel ι σ Act)
    [∀ i, Fintype (O.LocalTrace i)]
    (hPSAR : O.PerStepActionRecall)
    (hTPSR : ∀ i, O.TracePlayerStepRecall i)
    (μ : ∀ i, PMF (O.LocalTrace i → Option (Act i)))
    (k : Nat) :
    ∃ β : BehavioralProfile O,
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) := by
  sorry

open Classical Math.PMFProduct in
set_option linter.unusedFintypeInType false in
/-- **Kuhn M→B** on `SObsModel` under PSPR. -/
theorem kuhn_mixed_to_behavioral_pspr (O : SObsModel ι σ Act)
    [∀ i, Fintype (O.LocalTrace i)]
    (hPSPR : O.PerStepPlayerRecall)
    (μ : ∀ i, PMF (O.LocalTrace i → Option (Act i)))
    (k : Nat) :
    ∃ β : BehavioralProfile O,
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) := by
  sorry

end SObsModel

end GameTheory
