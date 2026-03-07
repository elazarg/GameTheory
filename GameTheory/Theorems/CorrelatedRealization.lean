import GameTheory.Core.ObsModel
import Math.ParameterizedChain

/-! # Correlated realization and Kuhn M→B

All theorems are stated at the **trace distribution** level (`runDist`/`runDistPure`),
not the outcome level. This makes them independent of the outcome projection
(`outcomeOfStates`): apply any function `f : List State → X` to recover
outcome-level, utility-level, or any other derived equality.

## Correlated realization (no assumptions)

For **any** joint distribution `ν : PMF (PureProfile O)` (not necessarily a product),
there exists a **mediator** — a history-dependent correlated action recommendation —
producing the same trace distribution. No structural assumptions are needed.

## Decentralization hierarchy

Decentralizing the mediator into independent per-player behavioral strategies
requires progressively stronger conditions:

- **PSAR** (`PerStepActionRecall`): mediator factors through observations;
  product input → product output (coordination preservation)
- **PSAR + PlayerStepRecall i**: each player's factor is obs-local
- **PSPR** (`PerStepPlayerRecall = ∀ i, PlayerStepRecall O i`): full
  decentralization into independent `BehavioralProfile`

The per-player condition admits two weakenings:
- `ReachablePlayerStepRecall O i`: restricted to step-reachable states
- `TracePlayerStepRecall O i`: restricted to states reached via traces
  with equal full observation histories (tightest syntactic condition)

Both `PSPR` and `PerfectRecall` imply `∀ i, TracePlayerStepRecall O i`
(neither implies the other). See the hierarchy section at the end.

## Main theorem

`kuhn_mixed_to_behavioral_trace` is the central result: under
`PSAR + ∀ i, TracePlayerStepRecall O i` (the weakest syntactic condition),
any product distribution over pure profiles can be realized by an independent
behavioral profile. Both `kuhn_mixed_to_behavioral_pspr` and
`kuhn_mixed_to_behavioral_decomposed` are direct corollaries. -/

set_option autoImplicit false

namespace GameTheory

namespace ObsModel

variable {ι : Type} {M : LSM ι}

/-- Player-local visible trace: list of per-step observations. -/
abbrev LocalTrace (O : ObsModel M) (i : ι) := List (O.Obs i)

/-- Project a state trace to player `i`'s local observation trace. -/
def projectStates (O : ObsModel M) (i : ι) (ss : List M.State) : O.LocalTrace i :=
  ss.map (O.observe i)

/-- Observation equivalence: two states are obs-equivalent for player `i`
when `observe i` gives the same value. -/
def obsEq (O : ObsModel M) (i : ι) (s t : M.State) : Prop :=
  O.observe i s = O.observe i t

/-! ### Profile types -/

/-- Deterministic profile over local visible history. -/
abbrev PureProfile (O : ObsModel M) : Type :=
  ∀ i, O.LocalTrace i → Option (M.Act i)

/-- Behavioral (stochastic) profile over local visible history. -/
abbrev BehavioralProfile (O : ObsModel M) : Type :=
  ∀ i, O.LocalTrace i → PMF (Option (M.Act i))

/-- Correlated behavioral profile over the full visible history context. -/
abbrev BehavioralProfileCorr (O : ObsModel M) : Type :=
  (∀ i, O.LocalTrace i) → PMF (JointAction M)

/-- Lift a deterministic profile to a behavioral one. -/
noncomputable def pureToBehavioral (O : ObsModel M) (π : PureProfile O) : BehavioralProfile O :=
  fun i v => PMF.pure (π i v)

/-- Embed an independent behavioral profile as a correlated one by product sampling. -/
noncomputable def behavioralToCorr
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (O : ObsModel M) (σ : BehavioralProfile O) : BehavioralProfileCorr O :=
  fun v => Math.PMFProduct.pmfPi (fun i => σ i (v i))

/-! ### Dynamics -/

/-- Stochastic execution choices on top of nondeterministic machine rules. -/
structure Dynamics (O : ObsModel M) where
  /-- Next-state kernel, conditioned on joint action and current latent state. -/
  nextState : JointAction M → M.State → PMF M.State
  /-- Soundness: sampled next states respect machine step relation. -/
  nextState_sound :
    ∀ (a : JointAction M) (s t : M.State),
      (nextState a s) t ≠ 0 → M.step a s t

namespace Dynamics

variable {O : ObsModel M}

/-- Independent joint-action distribution induced by a behavioral profile. -/
noncomputable def jointActionDist
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile O) (ss : List M.State) : PMF (JointAction M) :=
  Math.PMFProduct.pmfPi (fun i => σ i (O.projectStates i ss))

/-- One stochastic step from a current state under behavioral profile `σ`. -/
noncomputable def stepDist (D : Dynamics O)
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile O) (ss : List M.State) : PMF M.State :=
  let s := (ss.getLast?).getD M.init
  (jointActionDist (O := O) σ ss).bind fun a =>
    D.nextState a s

/-- One stochastic step under a correlated behavioral profile. -/
noncomputable def stepDistCorr (D : Dynamics O)
    [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfileCorr O) (ss : List M.State) : PMF M.State :=
  let s := (ss.getLast?).getD M.init
  let v : ∀ i, O.LocalTrace i := fun i => O.projectStates i ss
  (σ v).bind fun a =>
    D.nextState a s

/-- Bounded run distribution of length exactly `k`, storing just the state trace. -/
noncomputable def runDist (D : Dynamics O)
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (σ : BehavioralProfile O) : PMF (List M.State) :=
  Nat.rec (PMF.pure [M.init])
    (fun _ rec =>
      rec.bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward (D.stepDist σ ss)
          (fun t => ss ++ [t])))
    k

/-- Pure-profile run distribution via `pureToBehavioral`. -/
noncomputable def runDistPure (D : Dynamics O)
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (π : PureProfile O) : PMF (List M.State) :=
  D.runDist k (pureToBehavioral O π)

end Dynamics

/-! ### ProjectStates API lemmas -/

section ProjectStatesAPI

variable (O : ObsModel M)

theorem projectStates_eq_length (i : ι) {ss₁ ss₂ : List M.State}
    (h : O.projectStates i ss₁ = O.projectStates i ss₂) :
    ss₁.length = ss₂.length := by
  have := congr_arg List.length h
  simp only [projectStates, List.length_map] at this
  exact this

theorem obsEq_of_projectStates_getLast (i : ι) {ss ss' : List M.State}
    (hproj : O.projectStates i ss = O.projectStates i ss') :
    O.obsEq i (ss.getLast?.getD M.init) (ss'.getLast?.getD M.init) := by
  simp only [projectStates] at hproj
  simp only [obsEq]
  have hlen := congr_arg List.length hproj
  simp only [List.length_map] at hlen
  have := congr_arg List.getLast? hproj
  simp only [List.getLast?_map] at this
  cases hss : ss.getLast? <;> cases hss' : ss'.getLast? <;> simp_all [Option.map]

theorem projectStates_prefix_of_append
    (i : ι) {p p' : List M.State} {t t' : M.State}
    (h : O.projectStates i (p ++ [t]) = O.projectStates i (p' ++ [t'])) :
    O.projectStates i p = O.projectStates i p' := by
  simp only [projectStates, List.map_append, List.map_cons, List.map_nil] at h
  exact List.append_inj_left' h (by simp)

theorem obsEq_of_projectStates_append
    (i : ι) {p p' : List M.State} {t t' : M.State}
    (h : O.projectStates i (p ++ [t]) = O.projectStates i (p' ++ [t'])) :
    O.obsEq i t t' := by
  simp only [projectStates, List.map_append, List.map_cons, List.map_nil] at h
  simp only [obsEq]
  have := List.append_inj_right' h (by simp)
  simpa using this

/-- `projectActions` distributes over append (LSM-only, no observation model needed). -/
theorem projectActions_snoc (i : ι) (ha : List (JointAction M)) (a : JointAction M) :
    projectActions i (ha ++ [a]) = projectActions i ha ++ [a i] := by
  simp [projectActions, List.map_append]

/-- Equal `projectActions` on appended singletons implies equal last actions. -/
theorem projectActions_last_eq (i : ι) {ha ha' : List (JointAction M)}
    {a a' : JointAction M}
    (h : projectActions i (ha ++ [a]) = projectActions i (ha' ++ [a'])) :
    a i = a' i := by
  rw [projectActions_snoc, projectActions_snoc] at h
  exact List.cons.inj (List.append_inj_right' h (by simp)) |>.1

end ProjectStatesAPI

/-! ### Recall predicates -/

/-- Observation recall: indistinguishable terminal visible states imply identical
player-local visible histories on the corresponding reaches. -/
def ObsRecall (O : ObsModel M) : Prop :=
  ∀ (i : ι) (ss₁ ss₂ : List M.State) (s₁ s₂ : M.State),
    ReachStateTrace M ss₁ →
    ReachStateTrace M ss₂ →
    ss₁.getLast? = some s₁ →
    ss₂.getLast? = some s₂ →
    O.obsEq i s₁ s₂ →
    O.projectStates i ss₁ = O.projectStates i ss₂

/-- Action recall: indistinguishable terminal visible states imply identical
player-local own-action traces on the corresponding action-annotated reaches. -/
def ActionRecall (O : ObsModel M) : Prop :=
  ∀ (i : ι)
    (ha₁ ha₂ : List (JointAction M))
    (ss₁ ss₂ : List M.State) (s₁ s₂ : M.State),
    ReachActionTrace M ha₁ ss₁ →
    ReachActionTrace M ha₂ ss₂ →
    ss₁.getLast? = some s₁ →
    ss₂.getLast? = some s₂ →
    O.obsEq i s₁ s₂ →
    projectActions i ha₁ = projectActions i ha₂

/-- Perfect recall is the conjunction of observation recall and action recall. -/
def PerfectRecall (O : ObsModel M) : Prop :=
  O.ObsRecall ∧ O.ActionRecall

end ObsModel

open Math.ProbabilityMassFunction Math.ParameterizedChain ObsModel ObsModel.Dynamics

variable {ι : Type} {M : LSM ι} {O : ObsModel M}

section

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

/-- The parameterized step function extracted from game dynamics:
maps a pure profile and a state trace to a next-state distribution. -/
noncomputable def pureStep (D : Dynamics O) (π : PureProfile O)
    (ss : List M.State) : PMF M.State :=
  D.stepDist (pureToBehavioral O π) ss

/-- `runDistPure` is definitionally equal to `pureRun` applied to `pureStep`. -/
theorem runDistPure_eq_pureRun (D : Dynamics O) (k : Nat) (π : PureProfile O) :
    D.runDistPure k π = pureRun (pureStep D) M.init k π := rfl

/-- Mediator construction: condition `ν` on the probability of reaching
the current state trace, then extract correlated joint actions. -/
noncomputable def mixedToMediator [Fintype (PureProfile O)]
    (ν : PMF (PureProfile O)) (D : Dynamics O)
    (n : Nat) (ss : List M.State) : PMF (JointAction M) :=
  (reweightPMF ν (fun π => pureRun (pureStep D) M.init n π ss)).bind
    (fun π => jointActionDist (pureToBehavioral O π) ss)

/-- The mediator's action recommendations composed with dynamics equal
the `condStep` from `ParameterizedChain` (monad associativity). -/
theorem mediator_step_eq_condStep [Fintype (PureProfile O)]
    (ν : PMF (PureProfile O)) (D : Dynamics O) (n : Nat) (ss : List M.State) :
    (mixedToMediator ν D n ss).bind
      (fun a => D.nextState a ((ss.getLast?).getD M.init)) =
      condStep ν (pureStep D) M.init n ss := by
  unfold mixedToMediator condStep pureStep stepDist
  rw [PMF.bind_bind]

set_option linter.unusedFintypeInType false in
/-- **Correlated realization theorem**: for any joint distribution `ν` over
pure profiles, there exists a mediator `m` — producing correlated action
recommendations from the state trace at each step — such that the run under `m`
(with actions converted to state transitions by the dynamics) yields the same
trace distribution as the `ν`-averaged pure runs.

No perfect recall is needed. -/
theorem correlated_realization (D : Dynamics O) [Fintype (PureProfile O)]
    (ν : PMF (PureProfile O)) (k : Nat) :
    ∃ m : Nat → List M.State → PMF (JointAction M),
      seqRun (fun n ss =>
        (m n ss).bind (fun a => D.nextState a ((ss.getLast?).getD M.init)))
        M.init k =
      ν.bind (pureRun (pureStep D) M.init k) := by
  classical
  refine ⟨mixedToMediator ν D, ?_⟩
  have hstep : (fun n ss =>
      (mixedToMediator ν D n ss).bind
        (fun a => D.nextState a ((ss.getLast?).getD M.init))) =
      condStep ν (pureStep D) M.init := by
    funext n ss
    exact mediator_step_eq_condStep ν D n ss
  rw [hstep, condRun_eq_mixedRun]

end

/-! ## Observation-level correlated realization

Under **per-step action recall** (the observation transition determines the
action), the state-trace mediator factors through observations, giving a
`BehavioralProfileCorr O` witness. -/

/-- Per-step action recall: any two transitions with observation-equivalent
source and target states must use the same joint action.  This means the
observation transition uniquely determines the action taken. -/
def PerStepActionRecall (O : ObsModel M) : Prop :=
  ∀ (a a' : JointAction M) (s s' t t' : M.State),
    M.step a s t → M.step a' s' t' →
    (∀ i, O.obsEq i s s') → (∀ i, O.obsEq i t t') →
    a = a'


/-- When `σ` is a PMF and `w x ≤ 1` for all `x`, the sum `∑ x, σ x * w x` is
not `⊤`. This is used throughout the correlated-realization proofs whenever
`reweightPMF` needs its `ne_top` premise. -/
theorem sum_mul_pmf_ne_top {α : Type*} [Fintype α] (σ : PMF α) (w : α → ENNReal)
    (hw : ∀ a, w a ≤ 1) : ∑ a, σ a * w a ≠ ⊤ :=
  ne_of_lt (calc
    ∑ a, σ a * w a ≤ ∑ a, σ a :=
      Finset.sum_le_sum fun a _ => mul_le_of_le_one_right (zero_le _) (hw a)
    _ = 1 := by have := PMF.tsum_coe σ; rwa [tsum_fintype] at this
    _ < ⊤ := ENNReal.one_lt_top)

section ObsLevel

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

/-- `jointActionDist` depends on the state trace only through observations. -/
theorem jointActionDist_obs_invariant
    (σ : BehavioralProfile O) (ss₁ ss₂ : List M.State)
    (hobs : ∀ i, O.projectStates i ss₁ = O.projectStates i ss₂) :
    jointActionDist (O := O) σ ss₁ = jointActionDist (O := O) σ ss₂ := by
  unfold jointActionDist
  congr 1; funext i; rw [hobs]

/-- For pure profiles, `pureStep` is just `D.nextState` at the deterministic
joint action. (Because `jointActionDist` on a pure profile is a point mass.) -/
theorem pureStep_eq (D : Dynamics O) (π : PureProfile O) (ss : List M.State) :
    pureStep D π ss =
      D.nextState (fun i => π i (O.projectStates i ss)) ((ss.getLast?).getD M.init) := by
  unfold pureStep stepDist jointActionDist pureToBehavioral
  simp [Math.PMFProduct.pmfPi_pure, PMF.pure_bind]

/-- Under PSAR, if two profiles produce nonzero transition at the same state
trace and target, their step distributions are equal. -/
theorem pureStep_eq_of_nonzero_same
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    {π₁ π₂ : PureProfile O} {ss : List M.State} {t : M.State}
    (h₁ : pureStep D π₁ ss t ≠ 0) (h₂ : pureStep D π₂ ss t ≠ 0) :
    pureStep D π₁ ss = pureStep D π₂ ss := by
  simp only [pureStep_eq] at h₁ h₂ ⊢
  rw [hPSAR _ _ _ _ _ _
    (D.nextState_sound _ _ _ h₁) (D.nextState_sound _ _ _ h₂)
    (fun _ => rfl) (fun _ => rfl)]

/-- Under `PerStepActionRecall`, if `pureStep` at obs-equivalent traces gives
nonzero probability to obs-equivalent next states, the actions are equal. -/
theorem pureStep_action_eq_of_psar
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    {π π' : PureProfile O} {ss ss' : List M.State} {t t' : M.State}
    (hobs : ∀ i, O.projectStates i ss = O.projectStates i ss')
    (hobst : ∀ i, O.obsEq i t t')
    (h1 : pureStep D π ss t ≠ 0) (h2 : pureStep D π' ss' t' ≠ 0) :
    (fun i => π i (O.projectStates i ss)) = (fun i => π' i (O.projectStates i ss')) := by
  rw [pureStep_eq] at h1 h2
  exact hPSAR _ _ _ _ _ _
    (D.nextState_sound _ _ _ h1) (D.nextState_sound _ _ _ h2)
    (fun i => O.obsEq_of_projectStates_getLast i (hobs i)) hobst

/-- Under PSAR, `pureStep` satisfies the cross-ratio for obs-equivalent
state traces and obs-equivalent targets. -/
theorem pureStep_cross_ratio
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    {π₁ π₂ : PureProfile O} {ss₁ ss₂ : List M.State} {t₁ t₂ : M.State}
    (hobs : ∀ i, O.projectStates i ss₁ = O.projectStates i ss₂)
    (hobst : ∀ i, O.obsEq i t₁ t₂) :
    pureStep D π₁ ss₁ t₁ * pureStep D π₂ ss₂ t₂ =
      pureStep D π₂ ss₁ t₁ * pureStep D π₁ ss₂ t₂ := by
  -- Actions are the same at obs-equivalent traces for any fixed profile
  have hact₁ : (fun i => π₁ i (O.projectStates i ss₁)) =
      (fun i => π₁ i (O.projectStates i ss₂)) := by funext i; rw [hobs]
  have hact₂ : (fun i => π₂ i (O.projectStates i ss₁)) =
      (fun i => π₂ i (O.projectStates i ss₂)) := by funext i; rw [hobs]
  simp only [pureStep_eq, ← hact₁, ← hact₂]
  -- Now: nextState(a, last ss₁)(t₁) * nextState(b, last ss₂)(t₂) = ...
  -- where a = act(π₁,ss₁), b = act(π₂,ss₁)
  by_cases hab :
      (fun i => π₁ i (O.projectStates i ss₁)) = (fun i => π₂ i (O.projectStates i ss₁))
  · rw [hab]
  · -- If a ≠ b, PSAR forces both products to be zero
    have hobss : ∀ i, O.obsEq i
        ((ss₁.getLast?).getD M.init) ((ss₂.getLast?).getD M.init) :=
      fun i => O.obsEq_of_projectStates_getLast i (hobs i)
    have hL : D.nextState (fun i => π₁ i (O.projectStates i ss₁))
          ((ss₁.getLast?).getD M.init) t₁ *
        D.nextState (fun i => π₂ i (O.projectStates i ss₁))
          ((ss₂.getLast?).getD M.init) t₂ = 0 := by
      by_contra h
      rw [mul_eq_zero, not_or] at h
      exact hab (hPSAR _ _ _ _ _ _
        (D.nextState_sound _ _ _ h.1) (D.nextState_sound _ _ _ h.2) hobss hobst)
    have hR : D.nextState (fun i => π₂ i (O.projectStates i ss₁))
          ((ss₁.getLast?).getD M.init) t₁ *
        D.nextState (fun i => π₁ i (O.projectStates i ss₁))
          ((ss₂.getLast?).getD M.init) t₂ = 0 := by
      by_contra h
      rw [mul_eq_zero, not_or] at h
      exact hab (hPSAR _ _ _ _ _ _
        (D.nextState_sound _ _ _ h.1) (D.nextState_sound _ _ _ h.2) hobss hobst).symm
    rw [hL, hR]

/-- Under PSAR, pureRun satisfies the pairwise cross-ratio for
obs-equivalent traces: the reach probability ratio is profile-independent.
Proof: by induction on k, using `pureStep_eq_of_nonzero_same` for the
same-state case and `pureStep_action_eq_of_psar` for cross-state. -/
theorem pureRun_pairwise_cross_of_psar
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    (k : Nat) (π₁ π₂ : PureProfile O) (ss₁ ss₂ : List M.State)
    (hobs : ∀ i, O.projectStates i ss₁ = O.projectStates i ss₂) :
    pureRun (pureStep D) M.init k π₁ ss₁ *
      pureRun (pureStep D) M.init k π₂ ss₂ =
    pureRun (pureStep D) M.init k π₂ ss₁ *
      pureRun (pureStep D) M.init k π₁ ss₂ := by
  induction k generalizing ss₁ ss₂ with
  | zero =>
    -- pureRun at 0 = PMF.pure [s₀], independent of π
    simp [pureRun]
  | succ n ih =>
    -- Decompose ss₁ and ss₂ as prefix ++ [last]
    rcases List.eq_nil_or_concat ss₁ with rfl | ⟨p₁, t₁, rfl⟩
    · -- ss₁ = []: pureRun at succ on [] is 0, both sides = 0
      simp only [show ∀ π, pureRun (pureStep D) M.init (n + 1) π ([] : List M.State) = 0 from
        fun π => pureRun_succ_nil (pureStep D) M.init n π, zero_mul]
    · rcases List.eq_nil_or_concat ss₂ with rfl | ⟨p₂, t₂, rfl⟩
      · -- ss₂ = []: similar
        simp only [show ∀ π, pureRun (pureStep D) M.init (n + 1) π ([] : List M.State) = 0 from
          fun π => pureRun_succ_nil (pureStep D) M.init n π, mul_zero]
      · -- Main case: ss₁ = p₁ ++ [t₁], ss₂ = p₂ ++ [t₂]
        simp only [List.concat_eq_append] at hobs ⊢
        simp only [pureRun_succ_append]
        -- Goal: R(n,π₁,p₁)*S(π₁,p₁,t₁) * (R(n,π₂,p₂)*S(π₂,p₂,t₂)) =
        --       R(n,π₂,p₁)*S(π₂,p₁,t₁) * (R(n,π₁,p₂)*S(π₁,p₂,t₂))
        -- Extract obs-equiv of prefixes and last elements
        have hobs_prefix : ∀ i, O.projectStates i p₁ = O.projectStates i p₂ :=
          fun i => O.projectStates_prefix_of_append i (hobs i)
        have hobs_last : ∀ i, O.obsEq i t₁ t₂ :=
          fun i => O.obsEq_of_projectStates_append i (hobs i)
        -- Use IH for prefixes and step cross-ratio for last elements
        have hIH := ih p₁ p₂ hobs_prefix
        have hStep := pureStep_cross_ratio hPSAR D hobs_prefix hobs_last
          (π₁ := π₁) (π₂ := π₂) (t₁ := t₁) (t₂ := t₂)
        -- Combine: (a₁*b₁)*(a₂*b₂) = (a₁*a₂)*(b₁*b₂)
        --        = (a₃*a₄)*(b₃*b₄) = (a₃*b₃)*(a₄*b₄) by rearrangement
        calc pureRun (pureStep D) M.init n π₁ p₁ * pureStep D π₁ p₁ t₁ *
              (pureRun (pureStep D) M.init n π₂ p₂ * pureStep D π₂ p₂ t₂)
            = (pureRun (pureStep D) M.init n π₁ p₁ *
                pureRun (pureStep D) M.init n π₂ p₂) *
              (pureStep D π₁ p₁ t₁ * pureStep D π₂ p₂ t₂) := by ring
          _ = (pureRun (pureStep D) M.init n π₂ p₁ *
                pureRun (pureStep D) M.init n π₁ p₂) *
              (pureStep D π₂ p₁ t₁ * pureStep D π₁ p₂ t₂) := by rw [hIH, hStep]
          _ = pureRun (pureStep D) M.init n π₂ p₁ * pureStep D π₂ p₁ t₁ *
              (pureRun (pureStep D) M.init n π₁ p₂ * pureStep D π₁ p₂ t₂) := by ring

variable [Fintype (PureProfile O)]

/-- Under `PerStepActionRecall`, for obs-equivalent state traces, the
`reweightPMF` on reach probabilities gives the same distribution. -/
theorem reweightPMF_pureRun_obs_invariant
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    (ν : PMF (PureProfile O)) (n : Nat)
    (ss₁ ss₂ : List M.State)
    (hobs : ∀ i, O.projectStates i ss₁ = O.projectStates i ss₂)
    (hreach₁ : ∑ π : PureProfile O, ν π * pureRun (pureStep D) M.init n π ss₁ ≠ 0)
    (hreach₂ : ∑ π : PureProfile O, ν π * pureRun (pureStep D) M.init n π ss₂ ≠ 0) :
    reweightPMF ν (fun π => pureRun (pureStep D) M.init n π ss₁) =
    reweightPMF ν (fun π => pureRun (pureStep D) M.init n π ss₂) := by
  have hCtop₁ : ∑ π, ν π * pureRun (pureStep D) M.init n π ss₁ ≠ ⊤ :=
    sum_mul_pmf_ne_top ν _ fun π => PMF.coe_le_one _ _
  have hCtop₂ : ∑ π, ν π * pureRun (pureStep D) M.init n π ss₂ ≠ ⊤ :=
    sum_mul_pmf_ne_top ν _ fun π => PMF.coe_le_one _ _
  apply Math.ParameterizedChain.reweightPMF_eq_of_cross_mul ν _ _ hreach₁ hCtop₁ hreach₂ hCtop₂
  intro π
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π' _
  have h := pureRun_pairwise_cross_of_psar hPSAR D n π π' ss₁ ss₂ hobs
  calc pureRun (pureStep D) M.init n π ss₁ * (ν π' * pureRun (pureStep D) M.init n π' ss₂)
      = ν π' * (pureRun (pureStep D) M.init n π ss₁ * pureRun (pureStep D) M.init n π' ss₂) :=
        by ac_rfl
    _ = ν π' * (pureRun (pureStep D) M.init n π' ss₁ * pureRun (pureStep D) M.init n π ss₂) :=
        by rw [h]
    _ = pureRun (pureStep D) M.init n π ss₂ * (ν π' * pureRun (pureStep D) M.init n π' ss₁) :=
        by ac_rfl

/-- Under `PerStepActionRecall`, the state-trace mediator at obs-equivalent
reachable traces produces the same action distribution. -/
theorem mixedToMediator_obs_invariant
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    (ν : PMF (PureProfile O)) (n : Nat)
    (ss₁ ss₂ : List M.State)
    (hobs : ∀ i, O.projectStates i ss₁ = O.projectStates i ss₂)
    (hreach₁ : ∑ π : PureProfile O, ν π * pureRun (pureStep D) M.init n π ss₁ ≠ 0)
    (hreach₂ : ∑ π : PureProfile O, ν π * pureRun (pureStep D) M.init n π ss₂ ≠ 0) :
    mixedToMediator ν D n ss₁ = mixedToMediator ν D n ss₂ := by
  unfold mixedToMediator
  rw [reweightPMF_pureRun_obs_invariant hPSAR D ν n ss₁ ss₂ hobs hreach₁ hreach₂]
  congr 1; funext π
  exact jointActionDist_obs_invariant (pureToBehavioral O π) ss₁ ss₂ hobs

end ObsLevel

section ObsCorrelatedRealization

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
variable [Fintype (PureProfile O)] [∀ i, Fintype (O.LocalTrace i)]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
open Classical in
/-- **Observation-level correlated realization**: under `PerStepActionRecall`,
a `BehavioralProfileCorr O` (observation-level mediator) produces the same
trace distribution as any mixed strategy `ν`. -/
theorem obs_correlated_realization [Inhabited ι]
    (hPSAR : PerStepActionRecall O)
    (D : Dynamics O) (ν : PMF (PureProfile O)) (k : Nat) :
    ∃ σ : BehavioralProfileCorr O,
      seqRun (fun _ ss => D.stepDistCorr σ ss) M.init k =
      ν.bind (pureRun (pureStep D) M.init k) := by
  -- Define obs-level mediator: pick a reachable representative state trace
  let σ : BehavioralProfileCorr O := fun v =>
    if h : ∃ ss : List M.State,
          (∀ i, O.projectStates i ss = v i) ∧
          ∑ π : PureProfile O, ν π * pureRun (pureStep D) M.init (ss.length - 1) π ss ≠ 0
    then mixedToMediator ν D (h.choose.length - 1) h.choose
    else PMF.pure (fun _ => none)
  refine ⟨σ, ?_⟩
  -- Suffices: seqRun under σ = seqRun under condStep
  suffices hsuff : seqRun (fun _ ss => D.stepDistCorr σ ss) M.init k =
      seqRun (condStep ν (pureStep D) M.init) M.init k by
    rw [hsuff, condRun_eq_mixedRun]
  -- Key lemma: step functions agree on the support
  suffices hfn : ∀ (n : Nat) (ss : List M.State),
      (seqRun (condStep ν (pureStep D) M.init) M.init n) ss ≠ 0 →
      D.stepDistCorr σ ss = condStep ν (pureStep D) M.init n ss by
    -- Induction on k
    induction k with
    | zero => rfl
    | succ n ih =>
      change (seqRun (fun _ ss => D.stepDistCorr σ ss) M.init n).bind
            (fun ss => pushforward (D.stepDistCorr σ ss) (fun t => ss ++ [t])) =
          (seqRun (condStep ν (pureStep D) M.init) M.init n).bind
            (fun ss => pushforward (condStep ν (pureStep D) M.init n ss)
              (fun t => ss ++ [t]))
      rw [ih]
      ext y
      simp only [PMF.bind_apply]
      apply tsum_congr
      intro ss
      by_cases hss : (seqRun (condStep ν (pureStep D) M.init) M.init n) ss = 0
      · simp [hss]
      · rw [hfn n ss hss]
  -- Prove hfn
  intro n ss hss
  -- 1. ss is reachable at step n
  have hreach : ∑ π, ν π * pureRun (pureStep D) M.init n π ss ≠ 0 := by
    rwa [condRun_eq_mixedRun, PMF.bind_apply, tsum_fintype] at hss
  -- 2. ss.length = n + 1
  have hlen : ss.length = n + 1 := by
    obtain ⟨π, _, hπ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hreach
    exact pureRun_length (pureStep D) M.init n π ss (right_ne_zero_of_mul hπ)
  -- 3. σ(projectStates(ss)) = mixedToMediator ν D n ss
  have hσ : σ (fun i => O.projectStates i ss) = mixedToMediator ν D n ss := by
    -- The existential is satisfied by ss itself
    have hexist : ∃ ss' : List M.State,
        (∀ i, O.projectStates i ss' = O.projectStates i ss) ∧
        ∑ π, ν π * pureRun (pureStep D) M.init (ss'.length - 1) π ss' ≠ 0 :=
      ⟨ss, fun _ => rfl, by rwa [show ss.length - 1 = n from by omega]⟩
    change (if h : ∃ ss' : List M.State,
        (∀ i, O.projectStates i ss' = (fun i => O.projectStates i ss) i) ∧
        ∑ π, ν π * pureRun (pureStep D) M.init (ss'.length - 1) π ss' ≠ 0
      then mixedToMediator ν D (h.choose.length - 1) h.choose
      else PMF.pure (fun _ => none)) = _
    rw [dif_pos hexist]
    -- hexist.choose has same projections and is reachable
    set ss' := hexist.choose with hss'_def
    have hobs' := hexist.choose_spec.1
    have hreach' := hexist.choose_spec.2
    -- ss'.length = ss.length (from obs-equiv via publicView)
    have hlen' : ss'.length = ss.length :=
      O.projectStates_eq_length (default : ι) (hobs' default)
    -- ss'.length - 1 = n
    have hn' : ss'.length - 1 = n := by omega
    rw [hn']
    exact mixedToMediator_obs_invariant hPSAR D ν n ss' ss hobs'
      (by rwa [hn'] at hreach') hreach
  -- 4. stepDistCorr σ ss = condStep ... n ss
  calc D.stepDistCorr σ ss
      = (σ (fun i => O.projectStates i ss)).bind
          (fun a => D.nextState a ((ss.getLast?).getD M.init)) := rfl
    _ = (mixedToMediator ν D n ss).bind
          (fun a => D.nextState a ((ss.getLast?).getD M.init)) := by rw [hσ]
    _ = condStep ν (pureStep D) M.init n ss := mediator_step_eq_condStep ν D n ss

end ObsCorrelatedRealization

/-! ## Per-step player recall

`PerStepPlayerRecall` is the per-player version of `PerStepActionRecall`:
each player's action component is determined by their own observation
transition (not requiring other players' observations). -/

/-- Per-step player recall: each player's action is determined by
their own observation transition alone. -/
def PerStepPlayerRecall (O : ObsModel M) : Prop :=
  ∀ (i : ι) (a a' : JointAction M) (s s' t t' : M.State),
    M.step a s t → M.step a' s' t' →
    O.obsEq i s s' → O.obsEq i t t' →
    a i = a' i

/-- `PerStepPlayerRecall` implies `PerStepActionRecall`. -/
theorem PerStepPlayerRecall.toAction (h : PerStepPlayerRecall O) :
    PerStepActionRecall O :=
  fun a a' s s' t t' hs hs' hobs hobst =>
    funext fun i => h i a a' s s' t t' hs hs' (hobs i) (hobst i)

/-- Per-player step recall for a **single** player `i`: player i's action
component is determined by player i's own observation transition.
`PerStepPlayerRecall O` is equivalent to `∀ i, PlayerStepRecall O i`. -/
def PlayerStepRecall (O : ObsModel M) (i : ι) : Prop :=
  ∀ (a a' : JointAction M) (s s' t t' : M.State),
    M.step a s t → M.step a' s' t' →
    O.obsEq i s s' → O.obsEq i t t' →
    a i = a' i

/-- `PerStepPlayerRecall` is equivalent to every player having step recall. -/
theorem perStepPlayerRecall_iff_forall :
    PerStepPlayerRecall O ↔ ∀ i, PlayerStepRecall O i :=
  ⟨fun h i => h i, fun h i => h i⟩

/-! ## Reachable per-step player recall

The Kuhn M→B proof only invokes `PlayerStepRecall` at states that are
reachable from `M.init` via valid transitions. This motivates a weaker
condition, `ReachablePlayerStepRecall`, that restricts the action-uniqueness
requirement to reachable source states.

The exact weakest condition for the Kuhn M→B proof is
`∀ i, ReachablePlayerStepRecall O i`. It is implied by:
- `PlayerStepRecall O i` (trivially, by dropping reachability hypotheses)
- `PerfectRecall I` (via `ActionRecall`): at obs-equivalent reachable
  endpoints, action traces are equal, hence last actions are equal.
-/

/-- A state `s` is step-reachable from `M.init` if there exists a valid
sequence of joint-action transitions from `M.init` reaching `s`. -/
def StepReachable (s : M.State) : Prop :=
  ∃ (ha : List (JointAction M)) (ss : List M.State),
    ReachActionTrace M ha ss ∧ ss.getLast? = some s

/-- The initial state is always step-reachable. -/
theorem stepReachable_init : StepReachable (M := M) M.init :=
  ⟨[], [M.init], .nil, rfl⟩

/-- If `s` is step-reachable and `M.step a s t`, then `t` is step-reachable. -/
theorem stepReachable_step {s t : M.State} {a : JointAction M}
    (hs : StepReachable (M := M) s) (hstep : M.step a s t) :
    StepReachable t := by
  obtain ⟨ha, ss, hreach, hlast⟩ := hs
  exact ⟨ha ++ [a], ss ++ [t], .snoc hreach hlast hstep, List.getLast?_concat ..⟩

/-- Reachable per-step player recall for a single player `i`:
`PlayerStepRecall O i` restricted to step-reachable source states.

This is the weakest condition under which the Kuhn M→B proof operates.
Implied by:
- `PlayerStepRecall O i` (trivially)
- `PerfectRecall I` (via `ActionRecall`) -/
def ReachablePlayerStepRecall (i : ι) : Prop :=
  ∀ (a a' : JointAction M) (s s' t t' : M.State),
    M.step a s t → M.step a' s' t' →
    O.obsEq i s s' → O.obsEq i t t' →
    StepReachable (M := M) s → StepReachable (M := M) s' →
    a i = a' i

/-- Trace-level per-step player recall: tighter than `ReachablePlayerStepRecall`.

Like `ReachablePlayerStepRecall`, but requires action agreement only when
the source states are endpoints of traces with equal **full** observation
histories (`projectStates i ss = projectStates i ss'`), not merely
obs-equivalent endpoints (`obsEq i s s'`).

This is strictly weaker than `ReachablePlayerStepRecall` because equal
full obs-traces implies endpoint obs-equivalence, but not conversely. -/
def TracePlayerStepRecall (i : ι) : Prop :=
  ∀ (a a' : JointAction M) (t t' : M.State)
    (ss ss' : List M.State),
    (∃ ha, ReachActionTrace M ha ss) →
    (∃ ha', ReachActionTrace M ha' ss') →
    O.projectStates i ss = O.projectStates i ss' →
    M.step a (ss.getLast?.getD M.init) t →
    M.step a' (ss'.getLast?.getD M.init) t' →
    O.obsEq i t t' →
    a i = a' i

/-- `PlayerStepRecall` implies `ReachablePlayerStepRecall` (drop reachability). -/
theorem PlayerStepRecall.toReachable {i : ι} (h : PlayerStepRecall O i) :
    ReachablePlayerStepRecall (O := O) i :=
  fun _ _ _ _ _ _ hs hs' hobs hobst _ _ => h _ _ _ _ _ _ hs hs' hobs hobst

/-- `ReachablePlayerStepRecall` implies `TracePlayerStepRecall`.
The obs-equivalence `obsEq i s s'` follows from the trace equality
`projectStates i ss = projectStates i ss'`. -/
theorem ReachablePlayerStepRecall.toTrace {i : ι}
    (h : ReachablePlayerStepRecall (O := O) i) :
    TracePlayerStepRecall (O := O) i := by
  intro a a' t t' ss ss' ⟨ha, hrat⟩ ⟨ha', hrat'⟩ hproj hstep hstep' hobst
  have hobss := O.obsEq_of_projectStates_getLast i hproj
  have hlast : ss.getLast? = some (ss.getLast?.getD M.init) := by
    cases hg : ss.getLast? with
    | none => cases hrat with | nil => simp at hg | snoc _ _ _ => simp at hg
    | some _ => rfl
  have hlast' : ss'.getLast? = some (ss'.getLast?.getD M.init) := by
    cases hg : ss'.getLast? with
    | none => cases hrat' with | nil => simp at hg | snoc _ _ _ => simp at hg
    | some _ => rfl
  exact h _ _ _ _ _ _ hstep hstep' hobss hobst
    ⟨ha, ss, hrat, hlast⟩ ⟨ha', ss', hrat', hlast'⟩

/-- `PlayerStepRecall` implies `TracePlayerStepRecall` (via `Reachable`). -/
theorem PlayerStepRecall.toTrace {i : ι} (h : PlayerStepRecall O i) :
    TracePlayerStepRecall (O := O) i :=
  h.toReachable.toTrace

/-- `PerfectRecall` implies `ReachablePlayerStepRecall` for all players.

The key is `ActionRecall`: obs-equivalent reachable endpoints have equal
action traces (per player), hence equal last actions. -/
theorem PerfectRecall.toReachablePlayerStepRecall (hPR : O.PerfectRecall) (i : ι) :
    ReachablePlayerStepRecall (O := O) i := by
  intro a a' s s' t t' hstep hstep' _ hobs_t hreach_s hreach_s'
  obtain ⟨ha_s, ss_s, hrat_s, hlast_s⟩ := hreach_s
  obtain ⟨ha_s', ss_s', hrat_s', hlast_s'⟩ := hreach_s'
  -- Extend the reach traces with the transitions
  have hrat_t := ReachActionTrace.snoc hrat_s hlast_s hstep
  have hrat_t' := ReachActionTrace.snoc hrat_s' hlast_s' hstep'
  -- Apply ActionRecall: obs-equiv endpoints ⟹ equal action traces
  have hact := hPR.2 i _ _ _ _ t t' hrat_t hrat_t'
    (List.getLast?_concat ..) (List.getLast?_concat ..) hobs_t
  -- Extract last action from the equal lists
  exact projectActions_last_eq i hact

/-- `PerfectRecall` implies `TracePlayerStepRecall` for all players. -/
theorem PerfectRecall.toTracePlayerStepRecall
    (hPR : O.PerfectRecall) (i : ι) :
    TracePlayerStepRecall (O := O) i :=
  (PerfectRecall.toReachablePlayerStepRecall hPR i).toTrace

/-- Under `PerStepActionRecall`, at most one action can produce a nonzero
transition probability between any pair of states. -/
theorem action_unique_of_psar
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    {a a' : JointAction M} {s t : M.State}
    (ha : D.nextState a s t ≠ 0) (ha' : D.nextState a' s t ≠ 0) :
    a = a' :=
  hPSAR a a' s s t t (D.nextState_sound a s t ha) (D.nextState_sound a' s t ha')
    (fun _ => rfl) (fun _ => rfl)

/-- Under `PerStepPlayerRecall`, player `i`'s action component is determined by
their own observation at source and target. -/
theorem action_component_unique_of_pspr
    (hPSPR : PerStepPlayerRecall O) (D : Dynamics O)
    (i : ι) {a a' : JointAction M} {s s' t t' : M.State}
    (ha : D.nextState a s t ≠ 0) (ha' : D.nextState a' s' t' ≠ 0)
    (hobs : O.obsEq i s s') (hobst : O.obsEq i t t') :
    a i = a' i :=
  hPSPR i a a' s s' t t' (D.nextState_sound a s t ha) (D.nextState_sound a' s' t' ha')
    hobs hobst

/-! ## Bridge: pureRun reachability

The `pureRun` chain produces traces where every state is step-reachable.
This bridges the `Math.ParameterizedChain` execution model with the
`ReachActionTrace` witnesses from `SemanticForm`. -/

section PureRunBridge

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

/-- If `pureRun` reaches a trace with nonzero probability, there exists a
corresponding `ReachActionTrace`. -/
theorem pureRun_nonzero_to_reachActionTrace
    (D : Dynamics O) (n : Nat)
    (π : PureProfile O) (ss : List M.State)
    (h : pureRun (pureStep D) M.init n π ss ≠ 0) :
    ∃ ha : List (JointAction M), ReachActionTrace M ha ss := by
  induction n generalizing ss with
  | zero =>
    have hss : ss = [M.init] := by
      by_contra hne; exact h (by simp [pureRun, PMF.pure_apply, hne])
    subst hss; exact ⟨[], .nil⟩
  | succ m ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h
    · simp only [List.concat_eq_append] at h ⊢
      have hp := left_ne_zero_of_mul (pureRun_succ_append .. ▸ h)
      have ht := right_ne_zero_of_mul (pureRun_succ_append .. ▸ h)
      obtain ⟨ha_p, hrat_p⟩ := ih p hp
      rw [pureStep_eq] at ht
      have hstep := D.nextState_sound _ _ _ ht
      have hlen_p := pureRun_length _ _ m π p hp
      have hp_ne : p ≠ [] := by intro h'; simp [h'] at hlen_p
      have hlast : p.getLast? = some (p.getLast?.getD M.init) := by
        cases hg : p.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hp_ne
        | some _ => rfl
      exact ⟨ha_p ++ [_], .snoc hrat_p hlast hstep⟩

/-- If `pureRun` reaches `ss` with nonzero probability, the last state of `ss`
is step-reachable from `M.init`. -/
theorem pureRun_nonzero_last_stepReachable
    (D : Dynamics O) (n : Nat)
    (π : PureProfile O) (ss : List M.State)
    (h : pureRun (pureStep D) M.init n π ss ≠ 0) :
    StepReachable (M := M) (ss.getLast?.getD M.init) := by
  obtain ⟨ha, hrat⟩ := pureRun_nonzero_to_reachActionTrace D n π ss h
  have hlen := pureRun_length _ _ n π ss h
  have hne : ss ≠ [] := by intro h'; simp [h'] at hlen
  have hlast : ss.getLast? = some (ss.getLast?.getD M.init) := by
    cases hg : ss.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hne
    | some _ => rfl
  exact ⟨ha, ss, hrat, hlast⟩

end PureRunBridge

/-! ## Reach factoring under PSAR

Under `PerStepActionRecall`, the reach probability `pureRun(pureStep D, s₀, n, π, ss)`
depends on `π` only through whether `π` produces the uniquely forced action at each
step. This gives:

1. **Constancy**: nonzero reach probabilities are equal across all profiles
2. **Per-player factoring**: the nonzero condition factors as `∀ i, π_i consistent`
3. **Product preservation**: reweighting a product measure by reach gives a product -/

section ReachFactor

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

/-- Under PSAR, nonzero reach probabilities at the same trace are equal.
If two profiles both reach `ss` with nonzero probability, they must produce
the same action at every step, hence have the same reach probability. -/
theorem pureRun_const_of_psar
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    (n : Nat) {π π' : PureProfile O} {ss : List M.State}
    (h : pureRun (pureStep D) M.init n π ss ≠ 0)
    (h' : pureRun (pureStep D) M.init n π' ss ≠ 0) :
    pureRun (pureStep D) M.init n π ss =
      pureRun (pureStep D) M.init n π' ss := by
  induction n generalizing ss with
  | zero => simp [pureRun] at h h' ⊢
  | succ k ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h
    · simp only [List.concat_eq_append, pureRun_succ_append] at h h' ⊢
      have hp := left_ne_zero_of_mul h
      have hp' := left_ne_zero_of_mul h'
      have ht := right_ne_zero_of_mul h
      have ht' := right_ne_zero_of_mul h'
      rw [ih hp hp',
          pureStep_eq_of_nonzero_same hPSAR D ht ht']

/-- Under PSAR, at a reachable transition, `pureStep` is nonzero iff
the profile produces the same action as any fixed witness profile. -/
theorem pureStep_nonzero_iff_action_eq
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    {π₀ : PureProfile O} {ss : List M.State} {t : M.State}
    (h₀ : pureStep D π₀ ss t ≠ 0) (π : PureProfile O) :
    pureStep D π ss t ≠ 0 ↔
      (fun i => π i (O.projectStates i ss)) =
        (fun i => π₀ i (O.projectStates i ss)) := by
  constructor
  · intro hne
    rw [pureStep_eq] at hne h₀
    exact hPSAR _ _ _ _ _ _
      (D.nextState_sound _ _ _ hne) (D.nextState_sound _ _ _ h₀)
      (fun _ => rfl) (fun _ => rfl)
  · intro heq
    rwa [pureStep_eq, heq, ← pureStep_eq]

/-- Under PSAR, `pureRun` is nonzero iff the profile produces the same
action as the witness at every step (prefix). The condition is:
at each prefix `p ++ [t]` of `ss`, the profile agrees on the action at `p`. -/
theorem pureRun_nonzero_iff_action_eq
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    (n : Nat) {π₀ : PureProfile O} {ss : List M.State}
    (h₀ : pureRun (pureStep D) M.init n π₀ ss ≠ 0) (π : PureProfile O) :
    pureRun (pureStep D) M.init n π ss ≠ 0 ↔
      (pureRun (pureStep D) M.init n π ss =
        pureRun (pureStep D) M.init n π₀ ss) := by
  constructor
  · exact fun h => pureRun_const_of_psar hPSAR D n h h₀
  · intro heq; rw [heq]; exact h₀

/-- Under PSAR, `pureStep D π ss t` factors per-player: it is nonzero iff
each player `i` individually produces the forced action component. -/
theorem pureStep_nonzero_iff_forall_player
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    {π₀ : PureProfile O} {ss : List M.State} {t : M.State}
    (h₀ : pureStep D π₀ ss t ≠ 0) (π : PureProfile O) :
    pureStep D π ss t ≠ 0 ↔
      ∀ i, π i (O.projectStates i ss) = π₀ i (O.projectStates i ss) := by
  rw [pureStep_nonzero_iff_action_eq hPSAR D h₀]
  exact ⟨fun h i => congr_fun h i, funext⟩

/-- Under PSAR, `pureRun` factors into a trace-dependent constant times a
per-player consistency indicator. If `π` is consistent (nonzero reach),
the reach value equals the witness; otherwise it's zero. -/
theorem pureRun_eq_const_mul_indicator
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    (n : Nat) (π₀ : PureProfile O) (ss : List M.State)
    (h₀ : pureRun (pureStep D) M.init n π₀ ss ≠ 0)
    (π : PureProfile O) :
    pureRun (pureStep D) M.init n π ss =
      if pureRun (pureStep D) M.init n π ss ≠ 0
      then pureRun (pureStep D) M.init n π₀ ss
      else 0 := by
  split
  · exact pureRun_const_of_psar hPSAR D n ‹_› h₀
  · push_neg at *; exact le_antisymm (le_of_eq ‹_›) (zero_le _)

/-- Under PSAR, `pureRun` nonzero is equivalent to matching the witness action
at every prefix. Stated inductively: nonzero at `p ++ [t]` iff nonzero at `p`
and action matches at `p`. -/
theorem pureRun_succ_nonzero_iff
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    (m : Nat) {π₀ : PureProfile O} {p : List M.State} {t : M.State}
    (h₀ : pureRun (pureStep D) M.init (m + 1) π₀ (p ++ [t]) ≠ 0)
    (π : PureProfile O) :
    pureRun (pureStep D) M.init (m + 1) π (p ++ [t]) ≠ 0 ↔
      pureRun (pureStep D) M.init m π p ≠ 0 ∧
        ∀ i, π i (O.projectStates i p) = π₀ i (O.projectStates i p) := by
  simp only [pureRun_succ_append] at h₀ ⊢
  have hp₀ := left_ne_zero_of_mul h₀
  have ht₀ := right_ne_zero_of_mul h₀
  constructor
  · intro hne
    exact ⟨left_ne_zero_of_mul hne,
      (pureStep_nonzero_iff_forall_player hPSAR D ht₀ π).mp
        (right_ne_zero_of_mul hne)⟩
  · intro ⟨hp, hall⟩
    exact mul_ne_zero hp
      ((pureStep_nonzero_iff_forall_player hPSAR D ht₀ π).mpr hall)

/-- Under PSAR, `pureStep` is invariant under changing players who produce
the same action. If `π` and `π'` agree on the action at `ss` (all players
give the same action component), then `pureStep D π ss = pureStep D π' ss`. -/
theorem pureStep_eq_of_action_eq (D : Dynamics O)
    {π π' : PureProfile O} {ss : List M.State}
    (h : ∀ i, π i (O.projectStates i ss) = π' i (O.projectStates i ss)) :
    pureStep D π ss = pureStep D π' ss := by
  simp only [pureStep_eq, funext h]

open Classical in
/-- Under PSAR, reach factors per-player via `Function.update`:
`pureRun π ss ≠ 0` iff for each player `i`, swapping just player `i`'s
component from `π` into the witness `π₀` still gives nonzero reach.

This is the cleanest per-player factoring: each player's consistency
can be tested independently. -/
theorem pureRun_nonzero_iff_update
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    (n : Nat) {π₀ : PureProfile O} {ss : List M.State}
    (h₀ : pureRun (pureStep D) M.init n π₀ ss ≠ 0)
    (π : PureProfile O) :
    pureRun (pureStep D) M.init n π ss ≠ 0 ↔
      ∀ i, pureRun (pureStep D) M.init n
        (Function.update π₀ i (π i)) ss ≠ 0 := by
  induction n generalizing ss with
  | zero =>
    simp only [pureRun, ne_eq] at h₀ ⊢
    exact ⟨fun _ _ => h₀, fun _ => h₀⟩
  | succ m ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h₀
    · simp only [List.concat_eq_append] at h₀ ⊢
      have hp₀ : pureRun (pureStep D) M.init m π₀ p ≠ 0 := by
        rw [pureRun_succ_append] at h₀; exact left_ne_zero_of_mul h₀
      rw [pureRun_succ_nonzero_iff hPSAR D m h₀]
      constructor
      · -- Forward: π consistent → each update consistent
        intro ⟨hp, hact⟩ i
        exact (pureRun_succ_nonzero_iff hPSAR D m h₀
          (Function.update π₀ i (π i))).mpr
          ⟨(ih hp₀).mp hp i, fun j => by
            by_cases hij : j = i
            · subst hij; simp [Function.update_self, hact]
            · simp [Function.update_of_ne hij]⟩
      · -- Backward: each update consistent → π consistent
        intro hall
        constructor
        · exact (ih hp₀).mpr fun i =>
            ((pureRun_succ_nonzero_iff hPSAR D m h₀ _).mp (hall i)).1
        · intro i
          have := ((pureRun_succ_nonzero_iff hPSAR D m h₀ _).mp (hall i)).2 i
          simp only [Function.update_self] at this
          exact this

end ReachFactor

section Decentralization

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

/-- Generalized step-independence-to-trace theorem: if a behavioral profile
`σ` satisfies the step-independence property with respect to any
`ν : PMF (PureProfile O)` (not necessarily a product), then
`runDist k σ = ν.bind (runDistPure k)`.

This generalizes the step-independence theorem from
`KuhnCore.lean` by replacing `mixedJoint μ` with an arbitrary `ν`. -/
theorem runDist_eq_of_stepIndependence
    (D : Dynamics O) (ν : PMF (PureProfile O))
    (σ : BehavioralProfile O)
    (hStep : ∀ n,
      ν.bind (fun π =>
        (D.runDistPure n π).bind (fun ss =>
          pushforward (D.stepDist σ ss) (fun t => ss ++ [t]))) =
      ν.bind (fun π =>
        (D.runDistPure n π).bind (fun ss =>
          pushforward (D.stepDist (pureToBehavioral O π) ss)
            (fun t => ss ++ [t])))) (k : Nat) :
    D.runDist k σ = ν.bind (fun π => D.runDistPure k π) := by
  induction k with
  | zero => simp [runDist, runDistPure]
  | succ n ih =>
    calc D.runDist (n + 1) σ
        = (D.runDist n σ).bind (fun ss =>
            pushforward (D.stepDist σ ss) (fun t => ss ++ [t])) := by
          simp [runDist]
      _ = (ν.bind (fun π => D.runDistPure n π)).bind (fun ss =>
            pushforward (D.stepDist σ ss) (fun t => ss ++ [t])) := by rw [ih]
      _ = ν.bind (fun π =>
            (D.runDistPure n π).bind (fun ss =>
              pushforward (D.stepDist σ ss) (fun t => ss ++ [t]))) := by
          rw [PMF.bind_bind]
      _ = ν.bind (fun π =>
            (D.runDistPure n π).bind (fun ss =>
              pushforward (D.stepDist (pureToBehavioral O π) ss)
                (fun t => ss ++ [t]))) := by simpa using hStep n
      _ = ν.bind (fun π => D.runDistPure (n + 1) π) := by
          simp [runDist, runDistPure]

/-- Under `PerStepPlayerRecall`, the pure-step action component for player `i`
depends only on player `i`'s observation at obs-equivalent traces. -/
theorem pureStep_component_eq_of_pspr
    (hPSPR : PerStepPlayerRecall O) (D : Dynamics O)
    (i : ι) {π π' : PureProfile O} {ss ss' : List M.State} {t t' : M.State}
    (hobs_i : O.projectStates i ss = O.projectStates i ss')
    (hobst_i : O.obsEq i t t')
    (h1 : pureStep D π ss t ≠ 0) (h2 : pureStep D π' ss' t' ≠ 0) :
    π i (O.projectStates i ss) = π' i (O.projectStates i ss') := by
  rw [pureStep_eq] at h1 h2
  exact hPSPR i _ _ _ _ _ _
    (D.nextState_sound _ _ _ h1) (D.nextState_sound _ _ _ h2)
    (O.obsEq_of_projectStates_getLast i hobs_i) hobst_i

/-- Per-player version of `pureStep_component_eq_of_pspr`:
only needs `PlayerStepRecall O i` for the specific player `i`,
not the full `PerStepPlayerRecall` for all players. -/
theorem pureStep_component_eq_of_playerRecall
    (i : ι) (hPSR_i : PlayerStepRecall O i) (D : Dynamics O)
    {π π' : PureProfile O} {ss ss' : List M.State} {t t' : M.State}
    (hobs_i : O.projectStates i ss = O.projectStates i ss')
    (hobst_i : O.obsEq i t t')
    (h1 : pureStep D π ss t ≠ 0) (h2 : pureStep D π' ss' t' ≠ 0) :
    π i (O.projectStates i ss) = π' i (O.projectStates i ss') := by
  rw [pureStep_eq] at h1 h2
  exact hPSR_i _ _ _ _ _ _
    (D.nextState_sound _ _ _ h1) (D.nextState_sound _ _ _ h2)
    (O.obsEq_of_projectStates_getLast i hobs_i) hobst_i

end Decentralization

section ProductPreservation

open Math.PMFProduct

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
variable [∀ i, Fintype (O.LocalTrace i)]

open Classical in
/-- Under PSAR, the reach weight `pureRun π ss` satisfies the cross-multiplication
identity with the per-player product weight `∏ᵢ pureRun (update π₀ i (π i)) ss`.
This allows switching between them via `reweightPMF_eq_of_cross_mul`. -/
theorem pureRun_cross_mul_product
    (hPSAR : PerStepActionRecall O) (D : Dynamics O) (ν : PMF (PureProfile O))
    (n : Nat) {π₀ : PureProfile O} {ss : List M.State}
    (h₀ : pureRun (pureStep D) M.init n π₀ ss ≠ 0) (π : PureProfile O) :
    pureRun (pureStep D) M.init n π ss *
      (∑ π' : PureProfile O, ν π' *
        ∏ i, pureRun (pureStep D) M.init n (Function.update π₀ i (π' i)) ss) =
    (∏ i, pureRun (pureStep D) M.init n (Function.update π₀ i (π i)) ss) *
      (∑ π' : PureProfile O, ν π' *
        pureRun (pureStep D) M.init n π' ss) := by
  set C₀ := pureRun (pureStep D) M.init n π₀ ss with hC₀_def
  -- Helper: for consistent π', the reach equals C₀
  have hconst : ∀ π', pureRun (pureStep D) M.init n π' ss ≠ 0 →
      pureRun (pureStep D) M.init n π' ss = C₀ :=
    fun π' h => pureRun_const_of_psar hPSAR D n h h₀
  -- Helper: for consistent π', each per-player weight equals C₀
  have hconst_upd : ∀ (π' : PureProfile O) (i : ι),
      pureRun (pureStep D) M.init n (Function.update π₀ i (π' i)) ss ≠ 0 →
      pureRun (pureStep D) M.init n (Function.update π₀ i (π' i)) ss = C₀ :=
    fun π' i h => pureRun_const_of_psar hPSAR D n h h₀
  -- Distribute multiplication into sums
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro π' _
  -- Pointwise: w(π) * (ν π' * ∏ wᵢ(π'ᵢ)) = (∏ wᵢ(πᵢ)) * (ν π' * w(π'))
  -- Case split on consistency of π and π'
  by_cases hπ : pureRun (pureStep D) M.init n π ss = 0
  · -- π not consistent: w(π) = 0 and ∏ wᵢ(πᵢ) = 0
    rw [hπ, zero_mul]
    have := mt (pureRun_nonzero_iff_update hPSAR D n h₀ π).mpr
      (not_not.mpr hπ)
    push_neg at this; obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
  · by_cases hπ' : pureRun (pureStep D) M.init n π' ss = 0
    · -- π' not consistent: w(π') = 0 and ∏ wᵢ(π'ᵢ) = 0
      rw [hπ', mul_zero, mul_zero]
      have := mt (pureRun_nonzero_iff_update hPSAR D n h₀ π').mpr
        (not_not.mpr hπ')
      push_neg at this; obtain ⟨j, hj⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, mul_zero, mul_zero]
    · -- Both consistent: all values equal C₀
      have hw := hconst π hπ; have hw' := hconst π' hπ'
      have hwi : ∀ i, pureRun (pureStep D) M.init n
          (Function.update π₀ i (π i)) ss = C₀ :=
        fun i => hconst_upd π i
          ((pureRun_nonzero_iff_update hPSAR D n h₀ π).mp hπ i)
      have hwi' : ∀ i, pureRun (pureStep D) M.init n
          (Function.update π₀ i (π' i)) ss = C₀ :=
        fun i => hconst_upd π' i
          ((pureRun_nonzero_iff_update hPSAR D n h₀ π').mp hπ' i)
      rw [hw, hw']; simp_rw [hwi, hwi']; ring

open Classical in
set_option linter.unusedFintypeInType false in
/-- Under PSAR, when `ν = pmfPi σ` (product of per-player strategy distributions)
and the trace `ss` is reachable, the mediator `mixedToMediator ν D n ss` produces
a **product** action distribution: the recommended actions are independent across
players.

This is the "product in → product out" property: independence of the input
strategy distribution is preserved by the mediator construction. Combined with
the observation-level realization, this gives the independent behavioral profile
(Kuhn's theorem for the mixed → behavioral direction). -/
theorem mediator_product_of_product
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    (σ : ∀ i, PMF (O.LocalTrace i → Option (M.Act i)))
    (n : Nat) (ss : List M.State)
    {π₀ : PureProfile O}
    (h₀ : pureRun (pureStep D) M.init n π₀ ss ≠ 0) :
    ∃ τ : ∀ i, PMF (Option (M.Act i)),
      mixedToMediator (pmfPi σ) D n ss = pmfPi τ := by
  set ν := pmfPi σ with hν_def
  set w : PureProfile O → ENNReal :=
    fun π => pureRun (pureStep D) M.init n π ss
  set wᵢ : ∀ i, (O.LocalTrace i → Option (M.Act i)) → ENNReal :=
    fun i πᵢ => pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss
  -- Reduce to: reweightPMF ν w is a product PMF
  -- The mediator is a pushforward of (reweightPMF ν w) through the coordwise map
  -- fun π i => π i (projectStates i ss), and pushforward of product
  -- = product (pmfPi_push_coordwise)
  suffices hprod : ∃ ρ : ∀ i, PMF (O.LocalTrace i → Option (M.Act i)),
      reweightPMF ν w = pmfPi ρ by
    obtain ⟨ρ, hρ⟩ := hprod
    exact ⟨fun i => Math.PMFProduct.pushforward (ρ i) (fun πᵢ => πᵢ (O.projectStates i ss)), by
      unfold mixedToMediator; rw [hρ]
      simp only [jointActionDist, pureToBehavioral]
      conv_lhs => arg 2; ext π; rw [pmfPi_pure]
      exact pmfPi_push_coordwise ρ (fun i πᵢ => πᵢ (O.projectStates i ss))⟩
  -- Case split on mass condition for reweightPMF
  by_cases hmass : (∑ π, ν π * w π) = 0 ∨ (∑ π, ν π * w π) = ⊤
  · -- Degenerate: reweightPMF falls back to ν = pmfPi σ
    exact ⟨σ, by rw [reweightPMF_degenerate _ _ hmass, hν_def]⟩
  · -- Non-degenerate: use cross-multiplication to factor the reweighted PMF
    push_neg at hmass; obtain ⟨hCw0, hCwt⟩ := hmass
    -- Extract a witness with nonzero mass
    have ⟨π_w, hπw⟩ : ∃ π, ν π * w π ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hCw0 (Finset.sum_eq_zero fun a _ => hall a)
    have hν_ne : ν π_w ≠ 0 := left_ne_zero_of_mul hπw
    have hw_ne : w π_w ≠ 0 := right_ne_zero_of_mul hπw
    -- Per-player non-degeneracy from the witness
    have hσ_ne : ∀ i, σ i (π_w i) ≠ 0 := by
      intro i hi; apply hν_ne
      rw [hν_def, pmfPi_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have hwi_ne : ∀ i, wᵢ i (π_w i) ≠ 0 := by
      intro i; exact ((pureRun_nonzero_iff_update hPSAR D n h₀ π_w).mp hw_ne) i
    have hCwi0 : ∀ i, ∑ a, σ i a * wᵢ i a ≠ 0 := fun i => by
      apply ne_of_gt
      exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero (hσ_ne i) (hwi_ne i)))
        (Finset.single_le_sum (f := fun a => σ i a * wᵢ i a)
          (fun _ _ => zero_le _) (Finset.mem_univ (π_w i)))
    have hCwit : ∀ i, ∑ a, σ i a * wᵢ i a ≠ ⊤ := fun i =>
      sum_mul_pmf_ne_top (σ i) _ fun a => PMF.coe_le_one _ ss
    -- Non-degeneracy for the product weight ∏ wᵢ
    have hsum_eq : ∑ π, ν π * ∏ i, wᵢ i (π i) = ∏ i, ∑ a, σ i a * wᵢ i a := by
      rw [hν_def]; conv_lhs => arg 2; ext π; rw [pmfPi_apply, ← Finset.prod_mul_distrib]
      exact (Fintype.prod_sum (fun i a => σ i a * wᵢ i a)).symm
    have hCprod0 : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ 0 := by
      rw [hsum_eq]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hCwi0 i)
    have hCprodt : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ ⊤ := by
      rw [hsum_eq]
      exact ne_of_lt (ENNReal.prod_lt_top (fun i _ => (hCwit i).lt_top))
    -- Cross-multiplication identity → reweightPMF w = reweightPMF ∏ wᵢ
    have hreweight : reweightPMF ν w = reweightPMF ν (fun π => ∏ i, wᵢ i (π i)) :=
      reweightPMF_eq_of_cross_mul ν w (fun π => ∏ i, wᵢ i (π i))
        hCw0 hCwt hCprod0 hCprodt (pureRun_cross_mul_product hPSAR D ν n h₀)
    -- Factor the product-weighted reweightPMF via reweightPMF_pmfPi
    exact ⟨fun i => reweightPMF (σ i) (wᵢ i), by
      rw [hreweight, hν_def]; exact reweightPMF_pmfPi σ wᵢ hCwi0 hCwit⟩

end ProductPreservation

/-! ## Product preservation at the strategy level

Under PSAR, the reach weight `w(π) = pureRun π ss` is cross-multiplicatively
equivalent to the per-player product weight `∏ᵢ wᵢ(πᵢ)` (proved in
`pureRun_cross_mul_product`). This cross-multiplicative equivalence means
that for product distributions, reweighting by `w` gives a product:
independence in → independence out.

This is **product in → product out**, not a general "coordination preservation"
for arbitrary joint laws. For non-product `ν`, conditioning by `w` does
reweight by something cross-multiplicatively equivalent to a product weight,
but that does not imply the correlation structure of `ν` is preserved in any
precise sense. -/

section CoordinationPreservation

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
variable [∀ i, Fintype (O.LocalTrace i)]

open Math.PMFProduct

open Classical in
/-- **Product in → product out**: Under PSAR, if the ex ante distribution
is a product `ν = pmfPi σ`, then conditioning on reaching any reachable
trace `ss` gives a product at the strategy level:

  `reweightPMF (pmfPi σ) w = pmfPi (reweightPMF σᵢ wᵢ)`

Each player's conditional strategy `reweightPMF (σ i) wᵢ` depends only
on their own per-player reach weight. Pushing forward through the action
map gives the action-level product (`mediator_product_of_product`).

The mechanism: under PSAR, `pureRun_cross_mul_product` shows the reach
weight is cross-multiplicatively equivalent to `∏ᵢ wᵢ(πᵢ)`, and
`reweightPMF_pmfPi` factors reweighting by a product weight. -/
theorem conditioning_preserves_product
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    (σ : ∀ i, PMF (O.LocalTrace i → Option (M.Act i)))
    (n : Nat) {ss : List M.State}
    {π₀ : PureProfile O}
    (h₀ : pureRun (pureStep D) M.init n π₀ ss ≠ 0) :
    ∃ τ : ∀ i, PMF (O.LocalTrace i → Option (M.Act i)),
      reweightPMF (pmfPi σ)
        (fun π => pureRun (pureStep D) M.init n π ss) =
          pmfPi τ := by
  set ν := pmfPi σ
  set w : PureProfile O → ENNReal :=
    fun π => pureRun (pureStep D) M.init n π ss
  set wᵢ : ∀ i, (O.LocalTrace i → Option (M.Act i)) → ENNReal :=
    fun i πᵢ => pureRun (pureStep D) M.init n
      (Function.update π₀ i πᵢ) ss
  -- Mass conditions
  by_cases hmass : (∑ π, ν π * w π) = 0 ∨ (∑ π, ν π * w π) = ⊤
  · exact ⟨σ, by rw [reweightPMF_degenerate _ _ hmass]⟩
  · push_neg at hmass; obtain ⟨hCw0, hCwt⟩ := hmass
    -- Witness with nonzero mass
    have ⟨π_w, hπw⟩ : ∃ π, ν π * w π ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hCw0 (Finset.sum_eq_zero fun a _ => hall a)
    have hν_ne : ν π_w ≠ 0 := left_ne_zero_of_mul hπw
    have hw_ne : w π_w ≠ 0 := right_ne_zero_of_mul hπw
    -- Per-player non-degeneracy
    have hσ_ne : ∀ i, σ i (π_w i) ≠ 0 := by
      intro i hi; apply hν_ne
      rw [pmfPi_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have hwi_ne : ∀ i, wᵢ i (π_w i) ≠ 0 := by
      intro i
      exact ((pureRun_nonzero_iff_update hPSAR D n h₀ π_w).mp hw_ne) i
    have hCwi0 : ∀ i, ∑ a, σ i a * wᵢ i a ≠ 0 := fun i => by
      apply ne_of_gt
      exact lt_of_lt_of_le
        (pos_iff_ne_zero.mpr (mul_ne_zero (hσ_ne i) (hwi_ne i)))
        (Finset.single_le_sum (f := fun a => σ i a * wᵢ i a)
          (fun _ _ => zero_le _) (Finset.mem_univ (π_w i)))
    have hCwit : ∀ i, ∑ a, σ i a * wᵢ i a ≠ ⊤ := fun i =>
      sum_mul_pmf_ne_top (σ i) _ fun a => PMF.coe_le_one _ ss
    -- Product weight sum factorization
    have hsum_eq : ∑ π, ν π * ∏ i, wᵢ i (π i) =
        ∏ i, ∑ a, σ i a * wᵢ i a := by
      conv_lhs => arg 2; ext π; rw [pmfPi_apply, ← Finset.prod_mul_distrib]
      exact (Fintype.prod_sum (fun i a => σ i a * wᵢ i a)).symm
    have hCprod0 : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ 0 := by
      rw [hsum_eq]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hCwi0 i)
    have hCprodt : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ ⊤ := by
      rw [hsum_eq]
      exact ne_of_lt (ENNReal.prod_lt_top (fun i _ => (hCwit i).lt_top))
    -- Step 1: reach weight ≡ product weight (cross-multiplicatively)
    have hreweight : reweightPMF ν w =
        reweightPMF ν (fun π => ∏ i, wᵢ i (π i)) :=
      reweightPMF_eq_of_cross_mul ν w (fun π => ∏ i, wᵢ i (π i))
        hCw0 hCwt hCprod0 hCprodt
        (pureRun_cross_mul_product hPSAR D ν n h₀)
    -- Step 2: product weight on product dist = product of per-player
    exact ⟨fun i => reweightPMF (σ i) (wᵢ i), by
      rw [hreweight]; exact reweightPMF_pmfPi σ wᵢ hCwi0 hCwit⟩

end CoordinationPreservation

/-! ## Observation-locality of per-player consistency

Under PSAR, the consistency condition `pureRun (update π₀ i πᵢ) ss ≠ 0` depends
on the trace `ss` only through `projectStates i ss`: it reduces to requiring
`πᵢ` to agree with `π₀ i` at each observation prefix, and these prefixes are
determined by player i's projection of the trace.

Combined with `pureRun_const_of_psar` (all nonzero values are equal), this means
the per-player reweighted PMF `reweightPMF (σ i) (wᵢ_ss)` depends on `ss` only
through `projectStates i ss`, giving **obs-locality of the mediator factors**. -/

section ObsLocality

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

open Classical in
/-- Generic obs-locality of `pureRun (update π₀ i πᵢ)`, parameterized by a
step-level hypothesis `hStep` that says: given obs-equal prefixes and obs-equal
endpoints with nonzero steps, `π₀ i` and `π₀' i` agree on their respective
projections.

All concrete variants (`pureRun_update_obs_local`, `_pspr`, `_player`) are
one-line corollaries that supply the appropriate `hStep`. -/
theorem pureRun_update_obs_local_of
    (hPSAR : PerStepActionRecall O) (D : Dynamics O) (n : Nat)
    (i : ι) {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List M.State}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (pureStep D) M.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (pureStep D) M.init n π₀' ss₂ ≠ 0)
    (hStep : ∀ (m : Nat) (p₁ p₂ : List M.State) (t₁ t₂ : M.State),
      O.projectStates i p₁ = O.projectStates i p₂ →
      O.obsEq i t₁ t₂ →
      pureRun (pureStep D) M.init m π₀ p₁ ≠ 0 →
      pureRun (pureStep D) M.init m π₀' p₂ ≠ 0 →
      pureStep D π₀ p₁ t₁ ≠ 0 → pureStep D π₀' p₂ t₂ ≠ 0 →
      π₀ i (O.projectStates i p₁) = π₀' i (O.projectStates i p₂))
    (πᵢ : O.LocalTrace i → Option (M.Act i)) :
    pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
    pureRun (pureStep D) M.init n (Function.update π₀' i πᵢ) ss₂ ≠ 0 := by
  induction n generalizing ss₁ ss₂ with
  | zero =>
    simp only [pureRun, ne_eq] at h₁ h₂ ⊢
    exact ⟨fun _ => h₂, fun _ => h₁⟩
  | succ m ih =>
    rcases List.eq_nil_or_concat ss₁ with rfl | ⟨p₁, t₁, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h₁
    rcases List.eq_nil_or_concat ss₂ with rfl | ⟨p₂, t₂, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h₂
    simp only [List.concat_eq_append] at hobs_i h₁ h₂ ⊢
    have hobs_p : O.projectStates i p₁ = O.projectStates i p₂ :=
      O.projectStates_prefix_of_append i hobs_i
    have hobst : O.obsEq i t₁ t₂ := O.obsEq_of_projectStates_append i hobs_i
    have hp₁ := left_ne_zero_of_mul (pureRun_succ_append .. ▸ h₁)
    have hp₂ := left_ne_zero_of_mul (pureRun_succ_append .. ▸ h₂)
    have ht₁ := right_ne_zero_of_mul (pureRun_succ_append .. ▸ h₁)
    have ht₂ := right_ne_zero_of_mul (pureRun_succ_append .. ▸ h₂)
    rw [pureRun_succ_nonzero_iff hPSAR D m h₁,
        pureRun_succ_nonzero_iff hPSAR D m h₂]
    have hforced : π₀ i (O.projectStates i p₁) = π₀' i (O.projectStates i p₂) :=
      hStep m p₁ p₂ t₁ t₂ hobs_p hobst hp₁ hp₂ ht₁ ht₂
    have hact_transfer :
        (∀ j, Function.update π₀ i πᵢ j (O.projectStates j p₁) =
          π₀ j (O.projectStates j p₁)) ↔
        (∀ j, Function.update π₀' i πᵢ j (O.projectStates j p₂) =
          π₀' j (O.projectStates j p₂)) := by
      constructor <;> intro h
      · intro j; by_cases hij : j = i
        · rw [hij, Function.update_self, ← hforced, ← hobs_p]
          have := h i; rwa [Function.update_self] at this
        · rw [Function.update_of_ne hij]
      · intro j; by_cases hij : j = i
        · rw [hij, Function.update_self, hforced, hobs_p]
          have := h i; rwa [Function.update_self] at this
        · rw [Function.update_of_ne hij]
    constructor
    · exact fun ⟨hrec, hact⟩ =>
        ⟨(ih hobs_p hp₁ hp₂).mp hrec, hact_transfer.mp hact⟩
    · exact fun ⟨hrec, hact⟩ =>
        ⟨(ih hobs_p hp₁ hp₂).mpr hrec, hact_transfer.mpr hact⟩

open Classical in
/-- Under PSAR, the per-player consistency condition `pureRun (update π₀ i πᵢ) ss ≠ 0`
depends on `ss` only through `projectStates i ss`. If two traces have the same
player-i projection and both are reachable under π₀, then `update π₀ i πᵢ` reaches
one iff it reaches the other.

Corollary of `pureRun_update_obs_local_of` with trivial `hStep` (same π₀). -/
theorem pureRun_update_obs_local
    (hPSAR : PerStepActionRecall O) (D : Dynamics O) (n : Nat)
    (i : ι) {π₀ : PureProfile O} {ss₁ ss₂ : List M.State}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (pureStep D) M.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (pureStep D) M.init n π₀ ss₂ ≠ 0)
    (πᵢ : O.LocalTrace i → Option (M.Act i)) :
    pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
    pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₂ ≠ 0 :=
  pureRun_update_obs_local_of hPSAR D n i hobs_i h₁ h₂
    (fun _ _ _ _ _ hobs_p _ _ _ _ _ => by rw [hobs_p]) πᵢ

set_option linter.unusedFintypeInType false in
open Classical in
/-- Generic obs-locality of `reweightPMF`, parameterized by a support-equivalence
hypothesis `hiff` between two weight functions `w₁` and `w₂`. Under PSAR,
nonzero weights are constant (`pureRun_const_of_psar`), so the cross-multiplication
identity holds and `reweightPMF_eq_of_cross_mul` closes the goal.

All concrete variants (`reweightPMF_update_obs_local`, `_pspr`, `_player`) are
one-line corollaries that supply the appropriate `hiff`. -/
theorem reweightPMF_update_obs_local_of
    [∀ i, Fintype (O.LocalTrace i)]
    (hPSAR : PerStepActionRecall O) (D : Dynamics O) (n : Nat)
    (i : ι) (σ_i : PMF (O.LocalTrace i → Option (M.Act i)))
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List M.State}
    (h₁ : pureRun (pureStep D) M.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (pureStep D) M.init n π₀' ss₂ ≠ 0)
    (hiff : ∀ πᵢ,
      pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
      pureRun (pureStep D) M.init n (Function.update π₀' i πᵢ) ss₂ ≠ 0) :
    reweightPMF σ_i
      (fun πᵢ => pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₁) =
    reweightPMF σ_i
      (fun πᵢ => pureRun (pureStep D) M.init n (Function.update π₀' i πᵢ) ss₂) := by
  set w₁ := fun πᵢ => pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₁
  set w₂ := fun πᵢ => pureRun (pureStep D) M.init n (Function.update π₀' i πᵢ) ss₂
  have hsum_zero_iff : (∑ πᵢ, σ_i πᵢ * w₁ πᵢ) = 0 ↔ (∑ πᵢ, σ_i πᵢ * w₂ πᵢ) = 0 := by
    simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies, mul_eq_zero]
    constructor
    · intro h πᵢ; rcases h πᵢ with h | h
      · exact Or.inl h
      · exact Or.inr (of_not_not (mt (hiff πᵢ).mpr (not_not.mpr h)))
    · intro h πᵢ; rcases h πᵢ with h | h
      · exact Or.inl h
      · exact Or.inr (of_not_not (mt (hiff πᵢ).mp (not_not.mpr h)))
  have htop₁ : (∑ πᵢ, σ_i πᵢ * w₁ πᵢ) ≠ ⊤ :=
    sum_mul_pmf_ne_top σ_i _ fun πᵢ => PMF.coe_le_one _ ss₁
  have htop₂ : (∑ πᵢ, σ_i πᵢ * w₂ πᵢ) ≠ ⊤ :=
    sum_mul_pmf_ne_top σ_i _ fun πᵢ => PMF.coe_le_one _ ss₂
  by_cases hC₁ : (∑ πᵢ, σ_i πᵢ * w₁ πᵢ) = 0
  · rw [reweightPMF_fallback _ _ hC₁, reweightPMF_fallback _ _ (hsum_zero_iff.mp hC₁)]
  · have hC₂ : (∑ πᵢ, σ_i πᵢ * w₂ πᵢ) ≠ 0 := mt hsum_zero_iff.mpr hC₁
    exact reweightPMF_eq_of_cross_mul σ_i w₁ w₂ hC₁ htop₁ hC₂ htop₂ (fun πᵢ => by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro πᵢ' _
      by_cases hw : w₁ πᵢ = 0
      · have hw2 : w₂ πᵢ = 0 := of_not_not (mt (hiff πᵢ).mpr (not_not.mpr hw))
        simp [hw, hw2]
      · by_cases hw' : w₁ πᵢ' = 0
        · have hw2' : w₂ πᵢ' = 0 := of_not_not (mt (hiff πᵢ').mpr (not_not.mpr hw'))
          simp [hw', hw2']
        · have eq1 : w₁ πᵢ = pureRun (pureStep D) M.init n π₀ ss₁ :=
            pureRun_const_of_psar hPSAR D n hw h₁
          have eq2 : w₂ πᵢ = pureRun (pureStep D) M.init n π₀' ss₂ :=
            pureRun_const_of_psar hPSAR D n ((hiff πᵢ).mp hw) h₂
          have eq3 : w₁ πᵢ' = pureRun (pureStep D) M.init n π₀ ss₁ :=
            pureRun_const_of_psar hPSAR D n hw' h₁
          have eq4 : w₂ πᵢ' = pureRun (pureStep D) M.init n π₀' ss₂ :=
            pureRun_const_of_psar hPSAR D n ((hiff πᵢ').mp hw') h₂
          rw [eq1, eq2, eq3, eq4]; ring)

set_option linter.unusedFintypeInType false in
open Classical in
/-- Under PSAR, the per-player reweighted PMF depends on `ss` only through
`projectStates i ss`. Corollary of `reweightPMF_update_obs_local_of`. -/
theorem reweightPMF_update_obs_local
    [∀ i, Fintype (O.LocalTrace i)]
    (hPSAR : PerStepActionRecall O) (D : Dynamics O) (n : Nat)
    (i : ι) (σ_i : PMF (O.LocalTrace i → Option (M.Act i)))
    {π₀ : PureProfile O} {ss₁ ss₂ : List M.State}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (pureStep D) M.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (pureStep D) M.init n π₀ ss₂ ≠ 0) :
    reweightPMF σ_i
      (fun πᵢ => pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₁) =
    reweightPMF σ_i
      (fun πᵢ => pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₂) :=
  reweightPMF_update_obs_local_of hPSAR D n i σ_i h₁ h₂
    fun πᵢ => pureRun_update_obs_local hPSAR D n i hobs_i h₁ h₂ πᵢ

open Classical in
/-- Under PSPR, obs-locality with **different** reference profiles.
Corollary of `pureRun_update_obs_local_of` with `hStep` from `pureStep_component_eq_of_pspr`. -/
theorem pureRun_update_obs_local_pspr
    (hPSPR : PerStepPlayerRecall O) (D : Dynamics O) (n : Nat)
    (i : ι) {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List M.State}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (pureStep D) M.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (pureStep D) M.init n π₀' ss₂ ≠ 0)
    (πᵢ : O.LocalTrace i → Option (M.Act i)) :
    pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
    pureRun (pureStep D) M.init n (Function.update π₀' i πᵢ) ss₂ ≠ 0 :=
  pureRun_update_obs_local_of (hPSPR.toAction) D n i hobs_i h₁ h₂
    (fun _ _ _ _ _ hobs_p hobst _ _ ht₁ ht₂ =>
      pureStep_component_eq_of_pspr hPSPR D i hobs_p hobst ht₁ ht₂) πᵢ

set_option linter.unusedFintypeInType false in
open Classical in
/-- Under PSPR, obs-locality with **different** reference profiles.
Corollary of `reweightPMF_update_obs_local_of` with `hiff` from
`pureRun_update_obs_local_pspr`. -/
theorem reweightPMF_update_obs_local_pspr
    [∀ i, Fintype (O.LocalTrace i)]
    (hPSPR : PerStepPlayerRecall O) (D : Dynamics O) (n : Nat)
    (i : ι) (σ_i : PMF (O.LocalTrace i → Option (M.Act i)))
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List M.State}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (pureStep D) M.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (pureStep D) M.init n π₀' ss₂ ≠ 0) :
    reweightPMF σ_i
      (fun πᵢ => pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₁) =
    reweightPMF σ_i
      (fun πᵢ => pureRun (pureStep D) M.init n (Function.update π₀' i πᵢ) ss₂) :=
  reweightPMF_update_obs_local_of (hPSPR.toAction) D n i σ_i h₁ h₂
    fun πᵢ => pureRun_update_obs_local_pspr hPSPR D n i hobs_i h₁ h₂ πᵢ

end ObsLocality

/-! ## Per-player obs-locality under PSAR + PlayerStepRecall

The obs-locality lemmas in the previous section use `PerStepPlayerRecall O`
(which equals `∀ i, PlayerStepRecall O i`). But each player's factor only
needs their OWN recall condition. This section isolates the per-player
requirement.

The per-player chain is:
1. `pureRun_succ_nonzero_iff` — needs `PerStepActionRecall` (joint, not per-player)
2. `pureStep_component_eq_of_playerRecall` — needs `PlayerStepRecall O i` (only player i)
3. `pureRun_update_obs_local_player` — needs PSAR + `PlayerStepRecall O i`
4. `reweightPMF_update_obs_local_player` — needs PSAR + `PlayerStepRecall O i`

This shows that `PerStepPlayerRecall O` in the main Kuhn theorem decomposes
cleanly: the global PSAR handles the reach structure, while each player's
factor needs only their own `PlayerStepRecall`. -/

section PerPlayerObsLocality

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

open Classical in
/-- Under PSAR + `PlayerStepRecall O i`, obs-locality with **different** reference profiles.
Corollary of `pureRun_update_obs_local_of` with `hStep` from
`pureStep_component_eq_of_playerRecall`. -/
theorem pureRun_update_obs_local_player
    (hPSAR : PerStepActionRecall O) (i : ι) (hPSR_i : PlayerStepRecall O i)
    (D : Dynamics O) (n : Nat)
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List M.State}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (pureStep D) M.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (pureStep D) M.init n π₀' ss₂ ≠ 0)
    (πᵢ : O.LocalTrace i → Option (M.Act i)) :
    pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
    pureRun (pureStep D) M.init n (Function.update π₀' i πᵢ) ss₂ ≠ 0 :=
  pureRun_update_obs_local_of hPSAR D n i hobs_i h₁ h₂
    (fun _ _ _ _ _ hobs_p hobst _ _ ht₁ ht₂ =>
      pureStep_component_eq_of_playerRecall i hPSR_i D hobs_p hobst ht₁ ht₂) πᵢ

set_option linter.unusedFintypeInType false in
open Classical in
/-- Under PSAR + `PlayerStepRecall O i`, obs-locality with different reference profiles.
Corollary of `reweightPMF_update_obs_local_of` with `hiff` from
`pureRun_update_obs_local_player`. -/
theorem reweightPMF_update_obs_local_player
    [∀ i, Fintype (O.LocalTrace i)]
    (hPSAR : PerStepActionRecall O) (i : ι) (hPSR_i : PlayerStepRecall O i)
    (D : Dynamics O) (n : Nat)
    (σ_i : PMF (O.LocalTrace i → Option (M.Act i)))
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List M.State}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (pureStep D) M.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (pureStep D) M.init n π₀' ss₂ ≠ 0) :
    reweightPMF σ_i
      (fun πᵢ => pureRun (pureStep D) M.init n
        (Function.update π₀ i πᵢ) ss₁) =
    reweightPMF σ_i
      (fun πᵢ => pureRun (pureStep D) M.init n
        (Function.update π₀' i πᵢ) ss₂) :=
  reweightPMF_update_obs_local_of hPSAR D n i σ_i h₁ h₂
    fun πᵢ => pureRun_update_obs_local_player hPSAR i hPSR_i D n hobs_i h₁ h₂ πᵢ

end PerPlayerObsLocality

/-! ## Decentralization bridge

The final step of Kuhn's theorem (M→B direction) decomposes as:
1. **Correlated realization** (`correlated_realization`): any ν → correlated mediator
2. **Product preservation** (`mediator_product_of_product`): product ν + PSAR →
   product mediator output at each reachable trace
3. **Decentralization**: product-valued correlated profile → independent behavioral

Step 3 reduces to **observation-locality**: each factor τᵢ of the product must
depend only on player i's observation, not on the full state trace.

The bridge theorem below handles step 3, assuming observation-locality.
The observation-locality itself requires per-step player recall + the conditioning
argument (see `KuhnMixedToBehavioral.lean`). -/

section Decentralization

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

open Math.PMFProduct

/-- If a correlated behavioral profile factors as `pmfPi (fun i => β i (v i))`
at every observation tuple `v`, then its step distribution equals that of the
independent behavioral profile `β`. -/
theorem stepDistCorr_eq_stepDist_of_product
    (D : Dynamics O) (β : BehavioralProfile O) (σ : BehavioralProfileCorr O)
    (hprod : ∀ v, σ v = pmfPi (fun i => β i (v i)))
    (ss : List M.State) :
    D.stepDistCorr σ ss = D.stepDist β ss := by
  simp only [Dynamics.stepDistCorr, Dynamics.stepDist, jointActionDist, hprod]

/-- Independent behavioral realization from correlated one: if a correlated profile
always outputs products with observation-local factors, the independent profile
produces the same trace distribution. -/
theorem runDist_eq_of_corrProduct
    (D : Dynamics O) (β : BehavioralProfile O) (σ : BehavioralProfileCorr O)
    (hprod : ∀ v, σ v = pmfPi (fun i => β i (v i)))
    (k : Nat) :
    D.runDist k β =
      seqRun (fun _ ss => D.stepDistCorr σ ss) M.init k := by
  -- runDist D k β is definitionally seqRun (fun _ ss => D.stepDist β ss) M.init k
  change seqRun (fun _ ss => D.stepDist β ss) M.init k =
       seqRun (fun _ ss => D.stepDistCorr σ ss) M.init k
  congr 1
  funext _ ss
  exact (stepDistCorr_eq_stepDist_of_product D β σ hprod ss).symm

end Decentralization

/-! ## Generalized Kuhn (M→B) under PSPR

The full mixed-to-behavioral direction of Kuhn's theorem under
`PerStepPlayerRecall`. Given a product distribution `ν = pmfPi σ` over
pure profiles, we construct an independent behavioral profile `β`
with `runDist k β = ν.bind (runDistPure k)`.

**Proof structure**:
1. Correlated realization gives a mediator matching the mixed trace distribution.
2. Product preservation (PSAR) gives per-player factors at each reachable trace.
3. Per-player obs-locality (PSPR) makes these factors depend only on player i's
   local trace, giving a well-defined behavioral profile.
4. The behavioral profile's step distribution matches the conditional step
   at supported traces, completing the induction. -/

section KuhnMtoB

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
variable [∀ i, Fintype (O.LocalTrace i)]

open Math.PMFProduct

set_option linter.unusedFintypeInType false in
open Classical in
/-- Non-existential version of `mediator_product_of_product`:
the mediator output equals the product of per-player factors. -/
private theorem mixedToMediator_eq_pmfPi_factor
    (hPSAR : PerStepActionRecall O) (D : Dynamics O)
    (σ : ∀ i, PMF (O.LocalTrace i → Option (M.Act i)))
    (n : Nat) (ss : List M.State) {π₀ : PureProfile O}
    (h₀ : pureRun (pureStep D) M.init n π₀ ss ≠ 0)
    (hν₀ : (pmfPi σ) π₀ ≠ 0) :
    mixedToMediator (pmfPi σ) D n ss = pmfPi (fun i =>
      Math.PMFProduct.pushforward
        (reweightPMF (σ i)
          (fun πᵢ => pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss))
        (fun πᵢ => πᵢ (O.projectStates i ss))) := by
  set ν := pmfPi σ with hν_def
  set w := fun π => pureRun (pureStep D) M.init n π ss
  set wᵢ := fun i (πᵢ : O.LocalTrace i → Option (M.Act i)) =>
    pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss
  suffices hprod : reweightPMF ν w = pmfPi (fun i => reweightPMF (σ i) (wᵢ i)) by
    unfold mixedToMediator; rw [hprod]
    simp only [jointActionDist, pureToBehavioral]
    conv_lhs => arg 2; ext π; rw [pmfPi_pure]
    exact pmfPi_push_coordwise _ (fun i (πᵢ : O.LocalTrace i → Option (M.Act i)) =>
      πᵢ (O.projectStates i ss))
  -- Non-degeneracy setup
  have hσ_ne : ∀ i, σ i (π₀ i) ≠ 0 := by
    intro i hi; apply hν₀; rw [hν_def, pmfPi_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hwi_ne : ∀ i, wᵢ i (π₀ i) ≠ 0 :=
    fun i => ((pureRun_nonzero_iff_update hPSAR D n h₀ π₀).mp h₀) i
  have hCwi0 : ∀ i, ∑ a, σ i a * wᵢ i a ≠ 0 := fun i => by
    apply ne_of_gt
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero (hσ_ne i) (hwi_ne i)))
      (Finset.single_le_sum (f := fun a => σ i a * wᵢ i a)
        (fun _ _ => zero_le _) (Finset.mem_univ (π₀ i)))
  have hCwit : ∀ i, ∑ a, σ i a * wᵢ i a ≠ ⊤ := fun i =>
    sum_mul_pmf_ne_top (σ i) _ fun a => PMF.coe_le_one _ ss
  have hCw0 : ∑ π, ν π * w π ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero hν₀ h₀))
      (Finset.single_le_sum (f := fun π => ν π * w π)
        (fun _ _ => zero_le _) (Finset.mem_univ π₀))
  have hCwt : ∑ π, ν π * w π ≠ ⊤ :=
    sum_mul_pmf_ne_top ν _ fun π => PMF.coe_le_one _ ss
  have hsum_eq : ∑ π, ν π * ∏ i, wᵢ i (π i) = ∏ i, ∑ a, σ i a * wᵢ i a := by
    rw [hν_def]; conv_lhs => arg 2; ext π; rw [pmfPi_apply, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i a => σ i a * wᵢ i a)).symm
  have hCprod0 : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ 0 := by
    rw [hsum_eq]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hCwi0 i)
  have hCprodt : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ ⊤ := by
    rw [hsum_eq]; exact ne_of_lt (ENNReal.prod_lt_top (fun i _ => (hCwit i).lt_top))
  rw [reweightPMF_eq_of_cross_mul ν w (fun π => ∏ i, wᵢ i (π i))
      hCw0 hCwt hCprod0 hCprodt (pureRun_cross_mul_product hPSAR D ν n h₀),
    hν_def]
  exact reweightPMF_pmfPi σ wᵢ hCwi0 hCwit

end KuhnMtoB

/-! ## Semantic vs syntactic conditions

The Kuhn M→B proof uses two kinds of conditions:

**Syntactic conditions** — structural properties of the game model `M` and info structure `I`,
independent of dynamics `D`:
- `PerStepActionRecall O` (PSAR): joint action determined by joint obs transition
- `PlayerStepRecall O i`: player i's action determined by own obs transition
- `PerStepPlayerRecall O` (PSPR = ∀ i, PlayerStepRecall O i)
- `ReachablePlayerStepRecall O i`: PlayerStepRecall restricted to step-reachable states
- `PerfectRecall I`: full history reconstruction from observations

**Semantic conditions** — properties of the execution semantics, depending on dynamics `D`:
- `ObsLocalFeasibility D i`: whether a continuation πᵢ is feasible at a reachable trace
  depends only on player i's observation
- `StepActionDeterminism D`: at any reachable transition, the joint action that
  caused the transition is uniquely determined

The key relationships:

```
Syntactic → Semantic (always holds):
  PSAR + PlayerStepRecall O i  →  ObsLocalFeasibility D i  (for all D)
  PSAR                         →  StepActionDeterminism D   (for all D)

Semantic ↛ Syntactic (converse fails):
  ObsLocalFeasibility may hold for specific D without PlayerStepRecall
  (e.g., dynamics that make certain transitions impossible)
```
-/

section SemanticConditions

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

/-- **Semantic condition**: Whether a continuation strategy `πᵢ` for player `i` is feasible
(has nonzero probability of reaching a given trace) depends only on player `i`'s observation
of that trace, not on the full state trace.

This is the semantic content of what `PlayerStepRecall O i` provides in the Kuhn proof.
Unlike `PlayerStepRecall`, this condition depends on the dynamics `D`. -/
def ObsLocalFeasibility (D : Dynamics O) (i : ι) : Prop :=
  ∀ (n : Nat) (π₀ π₀' : PureProfile O) (ss₁ ss₂ : List M.State),
    O.projectStates i ss₁ = O.projectStates i ss₂ →
    pureRun (pureStep D) M.init n π₀ ss₁ ≠ 0 →
    pureRun (pureStep D) M.init n π₀' ss₂ ≠ 0 →
    ∀ (πᵢ : O.LocalTrace i → Option (M.Act i)),
      pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
      pureRun (pureStep D) M.init n (Function.update π₀' i πᵢ) ss₂ ≠ 0

/-- **Semantic condition**: At any reachable transition `(s, a, t)`, the joint action `a`
is uniquely determined by the source-target pair `(s, t)`.

This is the semantic content of what `PerStepActionRecall` provides: at reachable
transitions with the same obs-equivalence classes, the action must be the same.
Since `StepActionDeterminism` applies to the *same* states (reflexive obs-equivalence),
it is strictly weaker than PSAR. -/
def StepActionDeterminism (_ : Dynamics O) : Prop :=
  ∀ (a a' : JointAction M) (s t : M.State),
    M.step a s t → M.step a' s t → a = a'

omit [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))] in
/-- PSAR implies step action determinism for any dynamics.
PSAR with reflexive obs-equivalence (same source, same target) gives action uniqueness. -/
theorem PerStepActionRecall.toStepActionDeterminism
    (hPSAR : PerStepActionRecall O) (D : Dynamics O) :
    StepActionDeterminism (O := O) D :=
  fun _ _ _ _ h1 h2 => hPSAR _ _ _ _ _ _ h1 h2 (fun _ => rfl) (fun _ => rfl)

open Classical in
/-- **Syntactic → Semantic**: PSAR + `PlayerStepRecall O i` implies `ObsLocalFeasibility D i`
for any dynamics `D`.

This is exactly `pureRun_update_obs_local_player`, restated as an implication between
named conditions. -/
theorem obsLocalFeasibility_of_playerStepRecall
    (hPSAR : PerStepActionRecall O) (i : ι) (hPSR_i : PlayerStepRecall O i)
    (D : Dynamics O) : ObsLocalFeasibility (O := O) D i :=
  fun n _ _ _ _ hobs h₁ h₂ πᵢ =>
    pureRun_update_obs_local_player hPSAR i hPSR_i D n hobs h₁ h₂ πᵢ

/-- Under `PerStepPlayerRecall` (= ∀ i, PlayerStepRecall O i), obs-local feasibility
holds for every player and any dynamics. -/
theorem obsLocalFeasibility_of_pspr
    (hPSPR : PerStepPlayerRecall O) (D : Dynamics O) (i : ι) :
    ObsLocalFeasibility (O := O) D i :=
  obsLocalFeasibility_of_playerStepRecall
    hPSPR.toAction i (perStepPlayerRecall_iff_forall.mp hPSPR i) D

/-- Per-player step action equality at reachable states: like
`pureStep_component_eq_of_playerRecall` but using the weaker
`ReachablePlayerStepRecall` with explicit step-reachability witnesses. -/
theorem pureStep_component_eq_of_reachablePlayerRecall
    (i : ι) (hRPSR_i : ReachablePlayerStepRecall (O := O) i) (D : Dynamics O)
    {π π' : PureProfile O} {ss ss' : List M.State} {t t' : M.State}
    (hobs_i : O.projectStates i ss = O.projectStates i ss')
    (hobst_i : O.obsEq i t t')
    (h1 : pureStep D π ss t ≠ 0) (h2 : pureStep D π' ss' t' ≠ 0)
    (hreach_s : StepReachable (M := M) (ss.getLast?.getD M.init))
    (hreach_s' : StepReachable (M := M) (ss'.getLast?.getD M.init)) :
    π i (O.projectStates i ss) = π' i (O.projectStates i ss') := by
  rw [pureStep_eq] at h1 h2
  exact hRPSR_i _ _ _ _ _ _
    (D.nextState_sound _ _ _ h1) (D.nextState_sound _ _ _ h2)
    (O.obsEq_of_projectStates_getLast i hobs_i) hobst_i hreach_s hreach_s'

open Classical in
/-- **Weakest syntactic → semantic**: PSAR + `ReachablePlayerStepRecall O i`
implies `ObsLocalFeasibility D i`. This uses the weakest syntactic condition
that the Kuhn proof actually needs.

The key insight: `pureRun_update_obs_local_player` only invokes
`PlayerStepRecall` at states reached via `pureRun` with nonzero probability,
which are exactly the step-reachable states. -/
theorem obsLocalFeasibility_of_reachablePlayerStepRecall
    (hPSAR : PerStepActionRecall O) (i : ι)
    (hRPSR_i : ReachablePlayerStepRecall (O := O) i)
    (D : Dynamics O) : ObsLocalFeasibility (O := O) D i :=
  fun n _ _ _ _ hobs h₁ h₂ πᵢ =>
    pureRun_update_obs_local_of hPSAR D n i hobs h₁ h₂
      (fun m p₁ p₂ _ _ hobs_p hobst hp₁ hp₂ ht₁ ht₂ =>
        pureStep_component_eq_of_reachablePlayerRecall i hRPSR_i D
          hobs_p hobst ht₁ ht₂
          (pureRun_nonzero_last_stepReachable D m _ p₁ hp₁)
          (pureRun_nonzero_last_stepReachable D m _ p₂ hp₂)) πᵢ

/-- Step-level action equality under `TracePlayerStepRecall`:
at pureStep-supported transitions from traces with equal obs-projections,
the player-i action components agree. -/
theorem pureStep_component_eq_of_tracePlayerRecall
    (i : ι) (hTPSR : TracePlayerStepRecall (O := O) i) (D : Dynamics O)
    {π π' : PureProfile O} {ss ss' : List M.State} {t t' : M.State}
    (hproj : O.projectStates i ss = O.projectStates i ss')
    (hobst : O.obsEq i t t')
    (h1 : pureStep D π ss t ≠ 0) (h2 : pureStep D π' ss' t' ≠ 0)
    (hreach : ∃ ha, ReachActionTrace M ha ss)
    (hreach' : ∃ ha', ReachActionTrace M ha' ss') :
    π i (O.projectStates i ss) = π' i (O.projectStates i ss') := by
  rw [pureStep_eq] at h1 h2
  exact hTPSR _ _ _ _ _ _ hreach hreach' hproj
    (D.nextState_sound _ _ _ h1) (D.nextState_sound _ _ _ h2) hobst

open Classical in
/-- **Tightest syntactic → semantic**: PSAR + `TracePlayerStepRecall O i`
implies `ObsLocalFeasibility D i`.

This is strictly tighter than `obsLocalFeasibility_of_reachablePlayerStepRecall`
because `TracePlayerStepRecall` only requires action agreement at states
reached via traces with equal full observation histories, not at all
obs-equivalent reachable states. The proof's induction naturally maintains
the stronger `projectStates i p₁ = projectStates i p₂` invariant. -/
theorem obsLocalFeasibility_of_tracePlayerStepRecall
    (hPSAR : PerStepActionRecall O) (i : ι)
    (hTPSR : TracePlayerStepRecall (O := O) i)
    (D : Dynamics O) : ObsLocalFeasibility (O := O) D i :=
  fun n _ _ _ _ hobs h₁ h₂ πᵢ =>
    pureRun_update_obs_local_of hPSAR D n i hobs h₁ h₂
      (fun m p₁ p₂ _ _ hobs_p hobst hp₁ hp₂ ht₁ ht₂ =>
        pureStep_component_eq_of_tracePlayerRecall i hTPSR D
          hobs_p hobst ht₁ ht₂
          (pureRun_nonzero_to_reachActionTrace D m _ p₁ hp₁)
          (pureRun_nonzero_to_reachActionTrace D m _ p₂ hp₂)) πᵢ

end SemanticConditions

/-! ### Trace-level obs-locality

The following theorems establish obs-locality under `TracePlayerStepRecall`,
the weakest syntactic condition in the hierarchy. They are placed after
`SemanticConditions` because they depend on `pureStep_component_eq_of_tracePlayerRecall`
and `pureRun_nonzero_to_reachActionTrace` from that section. -/

set_option linter.unusedFintypeInType false in
open Classical in
/-- Under PSAR + `TracePlayerStepRecall O i`, updating player `i`'s strategy
preserves feasibility across obs-equivalent traces. -/
theorem pureRun_update_obs_local_trace
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (hPSAR : PerStepActionRecall O) (i : ι)
    (hTPSR : TracePlayerStepRecall (O := O) i)
    (D : Dynamics O) (n : Nat)
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List M.State}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (pureStep D) M.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (pureStep D) M.init n π₀' ss₂ ≠ 0)
    (πᵢ : O.LocalTrace i → Option (M.Act i)) :
    pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
    pureRun (pureStep D) M.init n (Function.update π₀' i πᵢ) ss₂ ≠ 0 :=
  pureRun_update_obs_local_of hPSAR D n i hobs_i h₁ h₂
    (fun m p₁ p₂ _ _ hobs_p hobst hp₁ hp₂ ht₁ ht₂ =>
      pureStep_component_eq_of_tracePlayerRecall i hTPSR D
        hobs_p hobst ht₁ ht₂
        (pureRun_nonzero_to_reachActionTrace D m _ p₁ hp₁)
        (pureRun_nonzero_to_reachActionTrace D m _ p₂ hp₂)) πᵢ

set_option linter.unusedFintypeInType false in
open Classical in
/-- Under PSAR + `TracePlayerStepRecall O i`, `reweightPMF` is obs-local for player `i`. -/
theorem reweightPMF_update_obs_local_trace
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (O.LocalTrace i)]
    (hPSAR : PerStepActionRecall O) (i : ι)
    (hTPSR : TracePlayerStepRecall (O := O) i)
    (D : Dynamics O) (n : Nat)
    (σ_i : PMF (O.LocalTrace i → Option (M.Act i)))
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List M.State}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (pureStep D) M.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (pureStep D) M.init n π₀' ss₂ ≠ 0) :
    reweightPMF σ_i
      (fun πᵢ => pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₁) =
    reweightPMF σ_i
      (fun πᵢ => pureRun (pureStep D) M.init n (Function.update π₀' i πᵢ) ss₂) :=
  reweightPMF_update_obs_local_of hPSAR D n i σ_i h₁ h₂
    fun πᵢ => pureRun_update_obs_local_trace hPSAR i hTPSR D n hobs_i h₁ h₂ πᵢ

/-! ## Kuhn theorem hierarchy

The results in this file form a hierarchy of increasingly specific realization
theorems:

### Level 0: Correlated realization (no recall needed)
`correlated_realization`: For any `ν : PMF (PureProfile O)`, there exists a
state-trace mediator producing the same outcome distribution. No structural
assumptions on the game.

### Level 1: Observation-level correlated realization (PSAR)
`obs_correlated_realization`: Under `PerStepActionRecall`, the state-trace
mediator factors through observations, giving a `BehavioralProfileCorr O`
(correlated behavioral profile).

### Level 2: Product preservation (PSAR)
`conditioning_preserves_product`: Under PSAR, if the ex ante
distribution is a product (`pmfPi σ`), conditioning on reaching any
trace gives a product at the strategy level. The reach weight is
cross-multiplicatively equivalent to a per-player product weight
(`pureRun_cross_mul_product`), and product weights on product
distributions factor (`reweightPMF_pmfPi`).

`mediator_product_of_product`: The action-level corollary — product
ν gives product mediator output at each reachable trace.

### Level 3: Per-player obs-locality (PSAR + PlayerStepRecall i)
`reweightPMF_update_obs_local_player`: Under PSAR + `PlayerStepRecall O i`,
the i-th factor of the product mediator depends only on player i's
observation. This is the per-player content — each player's decentralization
needs only their own recall condition.

### Level 4: Full decentralization (PSAR + ∀ i, TracePlayerStepRecall O i)
`kuhn_mixed_to_behavioral_trace`: Under the weakest syntactic condition
(PSAR + per-player trace step recall), the product mediator fully
decentralizes into an independent `BehavioralProfile O`.

`kuhn_mixed_to_behavioral_pspr`: PSPR corollary (via PlayerStepRecall → TracePlayerStepRecall).
`kuhn_mixed_to_behavioral_decomposed`: Per-player corollary.

### Weakening the per-player condition

`ReachablePlayerStepRecall O i`: `PlayerStepRecall O i` restricted to
step-reachable source states.

`TracePlayerStepRecall O i`: Even tighter — requires action agreement
only at reachable states reached via traces with equal **full**
observation histories (`projectStates i ss = projectStates i ss'`),
not merely obs-equivalent endpoints (`obsEq i s s'`).

Syntactic implication chain:
```
  PSPR = ∀ i, PlayerStepRecall O i
               ↓ (drop reachability req)
         ∀ i, ReachablePlayerStepRecall O i
               ↓ (strengthen hyp: obsEq → full trace eq)
         ∀ i, TracePlayerStepRecall O i
               ↑ (PerfectRecall → Reachable → Trace)
         PerfectRecall = ObsRecall ∧ ActionRecall
```

Neither PSPR nor PerfectRecall implies the other:
- PSPR constrains ALL transitions; PerfectRecall only reachable traces
- PerfectRecall reconstructs full history; PSPR is one-step

### Semantic conditions

`ObsLocalFeasibility D i`: whether continuation πᵢ is feasible at a
reachable trace depends only on player i's observation. Depends on `D`.

`StepActionDeterminism D`: at any transition, the action is determined
by the source-target pair. Semantic content of PSAR (reflexive case).

Full syntactic → semantic implication graph:
```
  PlayerStepRecall O i → ReachablePlayerStepRecall O i
    → TracePlayerStepRecall O i → (+ PSAR) ObsLocalFeasibility D i

  PerfectRecall → ReachablePlayerStepRecall O i (via ActionRecall)
  PSAR → StepActionDeterminism D
```

The semantic conditions depend on D; syntactic ones do not. The converse
(semantic → syntactic) does not hold: dynamics-specific feasibility can
make obs-locality hold without the syntactic action-uniqueness property. -/

section Hierarchy

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
variable [∀ i, Fintype (O.LocalTrace i)]

open Math.PMFProduct

open Classical in
/-- **Kuhn M→B under the weakest syntactic condition**: `PSAR + ∀ i, TracePlayerStepRecall O i`.

`TracePlayerStepRecall` requires that player i's action is determined by their
own observation only at states reached via traces with equal **full** observation
histories, not at all obs-equivalent states. This is strictly weaker than both
`PlayerStepRecall` and `ReachablePlayerStepRecall`, and is the weakest syntactic
condition under which the mixed-to-behavioral direction of Kuhn's theorem holds.

Both `kuhn_mixed_to_behavioral_pspr` and `kuhn_mixed_to_behavioral_decomposed`
are corollaries of this theorem. -/
theorem kuhn_mixed_to_behavioral_trace
    (hPSAR : PerStepActionRecall O)
    (hTPSR : ∀ i, TracePlayerStepRecall (O := O) i)
    (D : Dynamics O) (σ : ∀ i, PMF (O.LocalTrace i → Option (M.Act i)))
    (k : Nat) :
    ∃ β : BehavioralProfile O,
      D.runDist k β = (pmfPi σ).bind (D.runDistPure k) := by
  set ν := pmfPi σ with hν_def
  -- Abbreviation for the per-player factor at a specific trace
  let factorAt (i : ι) (n : Nat) (ss : List M.State) (π₀ : PureProfile O) :
      PMF (Option (M.Act i)) :=
    Math.PMFProduct.pushforward
      (reweightPMF (σ i)
        (fun πᵢ => pureRun (pureStep D) M.init n
          (Function.update π₀ i πᵢ) ss))
      (fun πᵢ => πᵢ (O.projectStates i ss))
  -- Standalone: factorAt is obs-local under PSAR + TracePlayerStepRecall
  have factorAt_obs_local :
      ∀ (i : ι) (n₁ n₂ : Nat) (ss₁ ss₂ : List M.State)
        (π₁ π₂ : PureProfile O),
      O.projectStates i ss₁ = O.projectStates i ss₂ →
      pureRun (pureStep D) M.init n₁ π₁ ss₁ ≠ 0 →
      pureRun (pureStep D) M.init n₂ π₂ ss₂ ≠ 0 →
      factorAt i n₁ ss₁ π₁ = factorAt i n₂ ss₂ π₂ := by
    intro i n₁ n₂ ss₁ ss₂ π₁ π₂ hobs h₁ h₂
    have hn : n₁ = n₂ := by
      have := O.projectStates_eq_length i hobs
      have := pureRun_length _ _ _ _ _ h₁
      have := pureRun_length _ _ _ _ _ h₂
      omega
    subst hn
    simp only [factorAt]
    congr 1
    · exact reweightPMF_update_obs_local_trace hPSAR i (hTPSR i) D n₁ (σ i) hobs h₁ h₂
    · exact funext fun πᵢ => by rw [hobs]
  -- Key property: β is well-defined
  let β : BehavioralProfile O := fun i v_i =>
    if h : ∃ (n : Nat) (ss : List M.State) (π₀ : PureProfile O),
        O.projectStates i ss = v_i ∧
        pureRun (pureStep D) M.init n π₀ ss ≠ 0
    then factorAt i h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose
    else PMF.pure none
  have β_eq : ∀ (i : ι) (n : Nat) (ss : List M.State) (π₀ : PureProfile O),
      pureRun (pureStep D) M.init n π₀ ss ≠ 0 →
      β i (O.projectStates i ss) = factorAt i n ss π₀ := by
    intro i n ss π₀ hreach
    have hexist : ∃ (n' : Nat) (ss' : List M.State) (π₀' : PureProfile O),
        O.projectStates i ss' = O.projectStates i ss ∧
        pureRun (pureStep D) M.init n' π₀' ss' ≠ 0 :=
      ⟨n, ss, π₀, rfl, hreach⟩
    change (if h : _ then _ else _) = _
    rw [dif_pos hexist]
    exact factorAt_obs_local i _ n _ ss _ π₀
      hexist.choose_spec.choose_spec.choose_spec.1
      hexist.choose_spec.choose_spec.choose_spec.2 hreach
  refine ⟨β, ?_⟩
  -- Main proof: runDist k β = ν.bind (runDistPure k)
  suffices hfn : ∀ (n : Nat) (ss : List M.State),
      (seqRun (condStep ν (pureStep D) M.init) M.init n) ss ≠ 0 →
      D.stepDist β ss = condStep ν (pureStep D) M.init n ss by
    have hrun : ∀ m, D.runDist m β = seqRun (condStep ν (pureStep D) M.init) M.init m := by
      intro m; induction m with
      | zero => simp [Dynamics.runDist, seqRun]
      | succ n ih =>
        change (D.runDist n β).bind
            (fun ss => Math.ProbabilityMassFunction.pushforward
              (D.stepDist β ss) (fun t => ss ++ [t])) =
          (seqRun (condStep ν (pureStep D) M.init) M.init n).bind
            (fun ss => Math.ProbabilityMassFunction.pushforward
              (condStep ν (pureStep D) M.init n ss) (fun t => ss ++ [t]))
        rw [ih]; ext y; simp only [PMF.bind_apply]
        apply tsum_congr; intro ss
        by_cases hss : (seqRun (condStep ν (pureStep D) M.init) M.init n) ss = 0
        · simp [hss]
        · rw [hfn n ss hss]
    change D.runDist k β = ν.bind (pureRun (pureStep D) M.init k)
    rw [hrun, condRun_eq_mixedRun]
  -- Prove the step function equality at supported traces
  intro n ss hss
  have hreach : ∑ π, ν π * pureRun (pureStep D) M.init n π ss ≠ 0 := by
    rwa [condRun_eq_mixedRun, PMF.bind_apply, tsum_fintype] at hss
  obtain ⟨π_w, _, hπw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hreach
  have hw_ne : pureRun (pureStep D) M.init n π_w ss ≠ 0 :=
    right_ne_zero_of_mul hπw
  have hν_ne : ν π_w ≠ 0 := left_ne_zero_of_mul hπw
  suffices haction : jointActionDist β ss = mixedToMediator ν D n ss by
    change D.stepDist β ss = condStep ν (pureStep D) M.init n ss
    unfold Dynamics.stepDist
    rw [haction, mediator_step_eq_condStep]
  rw [mixedToMediator_eq_pmfPi_factor hPSAR D σ n ss hw_ne (hν_def ▸ hν_ne)]
  simp only [jointActionDist]
  congr 1; funext i
  exact β_eq i n ss π_w hw_ne

open Classical in
/-- **Generalized Kuhn (M→B) under PSPR**: For any product distribution over
pure profiles, there exists an independent behavioral profile producing the
same trace distribution.

Corollary of `kuhn_mixed_to_behavioral_trace` via
`PlayerStepRecall → ReachablePlayerStepRecall → TracePlayerStepRecall`. -/
theorem kuhn_mixed_to_behavioral_pspr
    (hPSPR : PerStepPlayerRecall O) (D : Dynamics O)
    (σ : ∀ i, PMF (O.LocalTrace i → Option (M.Act i)))
    (k : Nat) :
    ∃ β : BehavioralProfile O,
      D.runDist k β = (pmfPi σ).bind (D.runDistPure k) :=
  kuhn_mixed_to_behavioral_trace hPSPR.toAction
    (fun i => ((perStepPlayerRecall_iff_forall.mp hPSPR i).toReachable).toTrace) D σ k

open Classical in
/-- **Per-player Kuhn M→B**: each player individually needs `PlayerStepRecall`.
Logically equivalent to `kuhn_mixed_to_behavioral_pspr` since
`PSPR ↔ ∀ i, PlayerStepRecall O i` (and PSPR → PSAR).

The conceptual value is that it shows the proof decomposes cleanly per player:
the global PSAR handles the reach structure (derived from the per-player
conditions), while each player's factor obs-locality uses only their own
`PlayerStepRecall`. See `reweightPMF_update_obs_local_player` for the
per-player lemma. -/
theorem kuhn_mixed_to_behavioral_decomposed
    (hPSR : ∀ i, PlayerStepRecall O i)
    (D : Dynamics O) (σ : ∀ i, PMF (O.LocalTrace i → Option (M.Act i)))
    (k : Nat) :
    ∃ β : BehavioralProfile O,
      D.runDist k β = (pmfPi σ).bind (D.runDistPure k) :=
  kuhn_mixed_to_behavioral_pspr
    (perStepPlayerRecall_iff_forall.mpr hPSR) D σ k

end Hierarchy

end GameTheory
