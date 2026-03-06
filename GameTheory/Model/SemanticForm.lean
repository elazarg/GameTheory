import Math.Probability
import Math.PMFProduct
import Math.ProbabilityMassFunction
import GameTheory.Model.FiniteRecall

/-!
# GameTheory.Model.SemanticForm

Semantics-first model decomposition:
- `LSM`: latent-state machine with joint actions
- `InfoModel`: public and player-local visibility over an `LSM`
- `ControlModel`: common-knowledge controller specifications (separate layer)

`ObsRecall`, `ActionRecall`, `PerfectRecall`, and `FiniteHorizon` are predicates,
not built-in requirements.
-/

namespace GameTheory

open Math.Probability

/-- Latent-state machine with joint (possibly inactive) actions. -/
structure LSM (ι : Type) where
  State : Type
  Act : ι → Type
  init : State
  step : (∀ i, Option (Act i)) → State → State → Prop

/-- Joint (possibly inactive) action profile. -/
abbrev JointAction {ι : Type} (M : LSM ι) : Type :=
  ∀ i, Option (M.Act i)

namespace LSM

variable {ι : Type}

/-- Action-erased one-step relation. Since the machine is already action-indexed,
this is just `step` under the shared `JointAction` abbreviation. -/
def stepExists (M : LSM ι) : JointAction M → M.State → M.State → Prop :=
  M.step

/-- Bounded-horizon predicate (theorem-local assumption). -/
def FiniteHorizon (M : LSM ι) (k : Nat) : Prop :=
  ∀ (h : List (JointAction M)) (s : M.State),
    Semantics.Transition.ReachBy M.stepExists h M.init s → h.length ≤ k

end LSM

/-- Information structure over a fixed latent machine.

`publicView` is the common visible component of a state.
`observe i` is player `i`'s private/local visible component. -/
structure InfoModel {ι : Type} (M : LSM ι) where
  Public : Type
  publicView : M.State → Public
  Obs : ι → Type
  observe : (i : ι) → M.State → Obs i

namespace InfoModel

variable {ι : Type} {M : LSM ι}

/-- Derived player-information equivalence: same public view and same local view. -/
def obsEq (I : InfoModel M) (i : ι) : M.State → M.State → Prop :=
  fun s t => I.publicView s = I.publicView t ∧ I.observe i s = I.observe i t

/-- Common public trace induced by a state trace. -/
abbrev PublicTrace (I : InfoModel M) : Type :=
  List I.Public

/-- Controller-local private observation trace. -/
abbrev PrivateTrace (I : InfoModel M) (i : ι) : Type :=
  List (I.Obs i)

/-- Controller-local visible history: public history paired with the player's
private observation history. -/
abbrev LocalTrace (I : InfoModel M) (i : ι) : Type :=
  I.PublicTrace × I.PrivateTrace i

/-- Visible outcome induced by a state trace. -/
abbrev Outcome (I : InfoModel M) : Type :=
  I.PublicTrace × (∀ i, I.PrivateTrace i)

/-- Project the public component of a state trace. -/
def projectPublic (I : InfoModel M) (ss : List M.State) : I.PublicTrace :=
  ss.map I.publicView

/-- Project player `i`'s private component of a state trace. -/
def projectPrivate (I : InfoModel M) (i : ι) (ss : List M.State) : I.PrivateTrace i :=
  ss.map (I.observe i)

/-- Local projection by pairing the public trace with player `i`'s private trace. -/
def projectStates (I : InfoModel M) (i : ι) (ss : List M.State) : I.LocalTrace i :=
  (I.projectPublic ss, I.projectPrivate i ss)

/-- Outcome induced by a machine state trace via public/private projections. -/
def outcomeOfStates (I : InfoModel M) (ss : List M.State) : I.Outcome :=
  (I.projectPublic ss, fun i => I.projectPrivate i ss)

/-- Reachability witness carrying visited states (states include init). -/
inductive ReachStateTrace (M : LSM ι) : List M.State → Prop
  | nil : ReachStateTrace M [M.init]
  | snoc {ss : List M.State} {s t : M.State} {a : JointAction M} :
      ReachStateTrace M ss →
      ss.getLast? = some s →
      M.step a s t →
      ReachStateTrace M (ss ++ [t])

/-- Reachability witness carrying joint actions and visited states. -/
inductive ReachActionTrace (M : LSM ι) :
    List (JointAction M) → List M.State → Prop
  | nil : ReachActionTrace M [] [M.init]
  | snoc
      {ha : List (JointAction M)}
      {ss : List M.State} {s t : M.State} {a : JointAction M} :
      ReachActionTrace M ha ss →
      ss.getLast? = some s →
      M.step a s t →
      ReachActionTrace M (ha ++ [a]) (ss ++ [t])

/-- A finite local-history cover `H` is sufficient up to horizon `k` if every
reachable state trace of length at most `k + 1` projects into `H`. This is the
generic bounded object needed by the restricted-profile Kuhn theorem. -/
def CoversHistoriesUpTo
    (I : InfoModel M)
    (H : ∀ i, Finset (I.LocalTrace i))
    (k : Nat) : Prop :=
  ∀ (i : ι) {ss : List M.State},
    ReachStateTrace M ss →
    ss.length ≤ k + 1 →
    I.projectStates i ss ∈ H i

/-- Player-local projected own-action trace from an action-annotated history. -/
def projectActions (i : ι) (ha : List (JointAction M)) : List (Option (M.Act i)) :=
  ha.map (fun a => a i)

/-- Player-local history token:
visible local history paired with realized own action at that step. -/
abbrev LocalHistTok (I : InfoModel M) (i : ι) : Type :=
  I.LocalTrace i × Option (M.Act i)

/-- Build local-history tokens from action/state traces (auxiliary recursion). -/
private def localHistTokensAux
    (I : InfoModel M) (i : ι)
    (pref : List M.State)
    (ha : List (JointAction M))
    (ssTail : List M.State) :
    List (I.LocalHistTok i) :=
  match ha, ssTail with
  | [], _ => []
  | a :: ha', s' :: ss' =>
      (I.projectStates i pref, a i) ::
        localHistTokensAux I i (pref ++ [s']) ha' ss'
  | _ :: _, [] => []

/-- First-class local-history projection from action/state traces. -/
def localHistTokens
    (I : InfoModel M) (i : ι)
    (ha : List (JointAction M))
    (ss : List M.State) :
    List (I.LocalHistTok i) :=
  match ss with
  | [] => []
  | s0 :: ssTail => localHistTokensAux I i [s0] ha ssTail

/-- Local-history tokens generated by continuing after an already accumulated
state prefix `pref`. Each token records the visible local history just before
one further action together with the action taken at that point. -/
def localHistTokensFrom
    (I : InfoModel M) (i : ι)
    (pref : List M.State)
    (ha : List (JointAction M))
    (ssTail : List M.State) :
    List (I.LocalHistTok i) :=
  localHistTokensAux I i pref ha ssTail

/-- With a nonempty starting prefix, `localHistTokens` agrees with
`localHistTokensFrom`. -/
theorem localHistTokens_cons_eq_localHistTokensFrom
    (I : InfoModel M) (i : ι)
    (s₀ : M.State)
    (ha : List (JointAction M))
    (ssTail : List M.State) :
    localHistTokens I i ha (s₀ :: ssTail) =
      localHistTokensFrom I i [s₀] ha ssTail := rfl

private theorem localHistTokensAux_snoc
    (I : InfoModel M) (i : ι)
    (pref : List M.State)
    (ha : List (JointAction M))
    (ssTail : List M.State)
    (hLen : ssTail.length = ha.length)
    (a : JointAction M) (t : M.State) :
    localHistTokensAux I i pref (ha ++ [a]) (ssTail ++ [t]) =
      localHistTokensAux I i pref ha ssTail ++ [(I.projectStates i (pref ++ ssTail), a i)] := by
  induction ha generalizing pref ssTail with
  | nil =>
      cases ssTail with
      | nil =>
          simp [localHistTokensAux]
      | cons s ss =>
          cases hLen
  | cons a0 ha ih =>
      cases ssTail with
      | nil =>
          cases hLen
      | cons s ss =>
          simp at hLen
          simp [localHistTokensAux, ih (pref := pref ++ [s]) (ssTail := ss) hLen,
            List.append_assoc]

/-- Appending one step to an action/state trace appends exactly one local
history token. -/
theorem localHistTokens_snoc
    (I : InfoModel M) (i : ι)
    (ha : List (JointAction M))
    (ss : List M.State)
    (hLen : ss.length = ha.length + 1)
    (a : JointAction M) (t : M.State) :
    localHistTokens I i (ha ++ [a]) (ss ++ [t]) =
      localHistTokens I i ha ss ++ [(I.projectStates i ss, a i)] := by
  cases ss with
  | nil =>
      cases hLen
  | cons s0 ssTail =>
      have hLen' : ssTail.length = ha.length := by
        simpa using hLen
      simpa [localHistTokens, List.cons_append, List.append_assoc] using
        localHistTokensAux_snoc I i [s0] ha ssTail hLen' a t

/-- Appending one step to a continuation appends exactly one continuation local
history token. -/
theorem localHistTokensFrom_snoc
    (I : InfoModel M) (i : ι)
    (pref : List M.State)
    (ha : List (JointAction M))
    (ssTail : List M.State)
    (hLen : ssTail.length = ha.length)
    (a : JointAction M) (t : M.State) :
    localHistTokensFrom I i pref (ha ++ [a]) (ssTail ++ [t]) =
      localHistTokensFrom I i pref ha ssTail ++ [(I.projectStates i (pref ++ ssTail), a i)] := by
  simpa [localHistTokensFrom] using localHistTokensAux_snoc I i pref ha ssTail hLen a t

/-- Length relation on action/state traces induced by `ReachActionTrace`. -/
theorem ReachActionTrace.length_states_eq_succ_actions
    {ha : List (JointAction M)}
    {ss : List M.State}
    (h : ReachActionTrace M ha ss) :
    ss.length = ha.length + 1 := by
  induction h with
  | nil =>
      simp
  | snoc _ _ _ ih =>
      simp [List.length_append, ih, Nat.add_comm]

/-- Forgetting actions from an action/state witness yields a state-trace witness. -/
theorem ReachActionTrace.toReachStateTrace
    {ha : List (JointAction M)}
    {ss : List M.State} (h : ReachActionTrace M ha ss) :
    ReachStateTrace M ss := by
  induction h with
  | nil => exact .nil
  | snoc _ hlast hstep ih =>
      exact .snoc ih hlast hstep

/-- Observation recall: indistinguishable terminal visible states imply identical
player-local visible histories on the corresponding reaches. -/
def ObsRecall (I : InfoModel M) : Prop :=
  ∀ (i : ι) (ss₁ ss₂ : List M.State) (s₁ s₂ : M.State),
    ReachStateTrace M ss₁ →
    ReachStateTrace M ss₂ →
    ss₁.getLast? = some s₁ →
    ss₂.getLast? = some s₂ →
    I.obsEq i s₁ s₂ →
    I.projectStates i ss₁ = I.projectStates i ss₂

/-- Action recall: indistinguishable terminal visible states imply identical
player-local own-action traces on the corresponding action-annotated reaches. -/
def ActionRecall (I : InfoModel M) : Prop :=
  ∀ (i : ι)
    (ha₁ ha₂ : List (JointAction M))
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
inductive ControlSpec (Obs Act : Type) where
  | utility  : (List Obs → ℝ) → ControlSpec Obs Act
  | behavior : (List Obs → PMF (Option Act)) → ControlSpec Obs Act

/-- Public control layer, separated from machine and information layers. -/
structure ControlModel {ι : Type} (M : LSM ι) (I : InfoModel M) where
  control : ∀ i, ControlSpec (I.Obs i) (M.Act i)

namespace Execution

variable {ι : Type} {M : LSM ι}

/-- Deterministic profile over local visible history. -/
abbrev PureProfile (I : InfoModel M) : Type :=
  ∀ i, I.LocalTrace i → Option (M.Act i)

/-- Behavioral profile over local visible history. -/
abbrev BehavioralProfile (I : InfoModel M) : Type :=
  ∀ i, I.LocalTrace i → PMF (Option (M.Act i))

/-- Correlated behavioral profile over the full visible history context.
This is defined for future correlated-realizability developments.
Current execution semantics continues to use `BehavioralProfile` (independent). -/
abbrev BehavioralProfileCorr (I : InfoModel M) : Type :=
  (∀ i, I.LocalTrace i) → PMF (JointAction M)

/-- Embed an independent behavioral profile as a correlated one by product sampling. -/
noncomputable def behavioralToCorr
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (I : InfoModel M) (σ : BehavioralProfile I) : BehavioralProfileCorr I :=
  fun v => Math.PMFProduct.pmfPi (fun i => σ i (v i))

/-- Lift a deterministic profile to a behavioral one. -/
noncomputable def pureToBehavioral (I : InfoModel M) (π : PureProfile I) : BehavioralProfile I :=
  fun i v => PMF.pure (π i v)

/-- Stochastic execution choices on top of nondeterministic machine rules. -/
structure Dynamics (I : InfoModel M) where
  /-- Next-state kernel, conditioned on joint action and current latent state. -/
  nextState : JointAction M → M.State → PMF M.State
  /-- Soundness: sampled next states respect machine step relation. -/
  nextState_sound :
    ∀ (a : JointAction M) (s t : M.State),
      (nextState a s) t ≠ 0 → M.step a s t

namespace Dynamics

variable {I : InfoModel M}

/-- Independent joint-action distribution induced by a behavioral profile. -/
noncomputable def jointActionDist
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) (ss : List M.State) : PMF (JointAction M) :=
  Math.PMFProduct.pmfPi (fun i => σ i (I.projectStates i ss))

/-- One stochastic step from a current state under behavioral profile `σ`. -/
noncomputable def stepDist (D : Dynamics I)
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) (ss : List M.State) : PMF M.State :=
  let s := (ss.getLast?).getD M.init
  (jointActionDist (I := I) σ ss).bind fun a =>
    D.nextState a s

/-- One stochastic step from a current state under a correlated behavioral profile. -/
noncomputable def stepDistCorr (D : Dynamics I)
    [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfileCorr I) (ss : List M.State) : PMF M.State :=
  let s := (ss.getLast?).getD M.init
  let v : ∀ i, I.LocalTrace i := fun i => I.projectStates i ss
  (σ v).bind fun a =>
    D.nextState a s

/-- Bounded run distribution of length exactly `k`, storing just the state trace. -/
noncomputable def runDist (D : Dynamics I)
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (σ : BehavioralProfile I) : PMF (List M.State) :=
  Nat.rec (PMF.pure [M.init])
    (fun _ rec =>
      rec.bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward (D.stepDist σ ss)
          (fun t => ss ++ [t])))
    k

/-- Pure-profile run distribution via `pureToBehavioral`. -/
noncomputable def runDistPure (D : Dynamics I)
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (π : PureProfile I) : PMF (List M.State) :=
  D.runDist k (pureToBehavioral I π)

/-- Outcome distribution (public/private visible outcome) from bounded behavioral runs. -/
noncomputable def evalBehavioral (D : Dynamics I)
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (σ : BehavioralProfile I) : PMF I.Outcome :=
  Math.ProbabilityMassFunction.pushforward (D.runDist k σ) I.outcomeOfStates

/-- Outcome distribution from bounded pure runs. -/
noncomputable def evalPure (D : Dynamics I)
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (π : PureProfile I) : PMF I.Outcome :=
  Math.ProbabilityMassFunction.pushforward (D.runDistPure k π) I.outcomeOfStates

/-- Independent one-step realizability:
there exists an independent behavioral profile matching the mixed/pure one-step law. -/
def OneStepIndependentRealizable (D : Dynamics I)
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (ν : PMF (PureProfile I)) (n : Nat) : Prop :=
  ∃ σ : BehavioralProfile I,
    (ν.bind (fun π =>
      (D.runDistPure n π).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist σ ss)
          (fun t => ss ++ [t])))) =
    (ν.bind (fun π =>
      (D.runDistPure n π).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) ss)
          (fun t => ss ++ [t]))))

/-- Correlated one-step realizability:
there exists a correlated behavioral profile matching the mixed/pure one-step law. -/
def OneStepCorrelatedRealizable (D : Dynamics I)
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (ν : PMF (PureProfile I)) (n : Nat) : Prop :=
  ∃ σ : BehavioralProfileCorr I,
    (ν.bind (fun π =>
      (D.runDistPure n π).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDistCorr σ ss)
          (fun t => ss ++ [t])))) =
    (ν.bind (fun π =>
      (D.runDistPure n π).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) ss)
          (fun t => ss ++ [t]))))

end Dynamics
end Execution

end GameTheory
