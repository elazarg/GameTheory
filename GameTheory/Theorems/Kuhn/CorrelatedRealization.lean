import GameTheory.Theorems.Kuhn.ObsModel

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
`kuhn_mixed_to_behavioral_decomposed` are direct corollaries.

## Design notes: action type parameterization

The current `Act : ι → Type` is a per-player action alphabet that is state-independent.
This is a simplification: in general, a player's available actions depend on the game
state (or at least on the information set). Three alternative designs are worth considering:

**B. Bundled action type with feasibility predicate.**
Use a single type `Action` for all actions, with a predicate `Feasible : ι → σ → Action → Prop`
constraining which actions are available at each state. The step function gives zero probability
to infeasible actions. Profiles map `LocalTrace i → Action`, and recall predicates compare
actions as elements of the same type. This is the standard game-theory encoding and avoids
dependent types entirely. The tradeoff: `Action` is a "universal" type that may contain
actions irrelevant to some players/states, and feasibility must be tracked as a side condition.

**C. Observation-indexed action types.**
The correct mathematical decomposition is `Act : ι → Obs i → Type`, where actions depend
on the player's *observation* (information set), not the raw state. This avoids the type-theoretic
problems of state-dependent actions (`Act : ι → σ → Type`) — since observations are the same
within an information set, actions at obs-equivalent states share the same type. The structure
becomes an observation predicate `Obs : ι → Type` paired with an LSM (labeled state machine)
parameterized by per-observation actions. Recall predicates compare actions within the same
observation type, eliminating the need for `HEq` or transport. The tradeoff: the `ObsModel`
structure must be split into an observation layer and an action layer, with the action layer
parameterized by observation values. This is architecturally cleaner but requires restructuring
the `ObsModel` definition. -/

set_option autoImplicit false

namespace ObsModel

open Math.ProbabilityMassFunction Math.ParameterizedChain

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}
variable {O : ObsModel ι σ Obs Act}

section

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- The mediator's action recommendations composed with step equal
the `condStep` from `ParameterizedChain` (monad associativity). -/
theorem mediator_step_eq_condStep [Fintype (PureProfile O)]
    (ν : PMF (PureProfile O)) (n : Nat) (ss : List σ) :
    (O.mixedToMediator ν n ss).bind
      (fun a => O.step (O.lastState ss) (O.castJointAction ss a)) =
      condStep ν O.pureStep O.init n ss := by
  unfold mixedToMediator condStep pureStep stepDist castJointAction
  rw [PMF.bind_bind]

set_option linter.unusedFintypeInType false in
/-- **Correlated realization theorem**: for any joint distribution `ν` over
pure profiles, there exists a mediator `m` — producing correlated action
recommendations from the state trace at each step — such that the run under `m`
(with actions converted to state transitions by the step function) yields the same
trace distribution as the `ν`-averaged pure runs.

No perfect recall is needed. -/
theorem correlated_realization [Fintype (PureProfile O)]
    (ν : PMF (PureProfile O)) (k : Nat) :
    ∃ m : (n : Nat) → (ss : List σ) →
        PMF (∀ i, Act i (O.lastObs i (O.projectStates i ss))),
      seqRun (fun n ss =>
        (m n ss).bind (fun a =>
          O.step (O.lastState ss) (O.castJointAction ss a)))
        O.init k =
      ν.bind (pureRun O.pureStep O.init k) := by
  classical
  refine ⟨O.mixedToMediator ν, ?_⟩
  have hstep : (fun n ss =>
      (O.mixedToMediator ν n ss).bind
        (fun a => O.step (O.lastState ss) (O.castJointAction ss a))) =
      condStep ν O.pureStep O.init := by
    funext n ss
    exact mediator_step_eq_condStep ν n ss
  rw [hstep, condRun_eq_mixedRun]

end

/-! ## Observation-level correlated realization

Under **per-step action recall** (the observation transition determines the
action), the state-trace mediator factors through observations, giving a
`BehavioralProfileCorr O` witness. -/

/-- When `d` is a PMF and `w x ≤ 1` for all `x`, the sum `∑ x, d x * w x` is
not `⊤`. This is used throughout the correlated-realization proofs whenever
`reweightPMF` needs its `ne_top` premise. -/
theorem sum_mul_pmf_ne_top {α : Type*} [Fintype α] (d : PMF α) (w : α → ENNReal)
    (hw : ∀ a, w a ≤ 1) : ∑ a, d a * w a ≠ ⊤ :=
  ne_of_lt (calc
    ∑ a, d a * w a ≤ ∑ a, d a :=
      Finset.sum_le_sum fun a _ => mul_le_of_le_one_right (zero_le _) (hw a)
    _ = 1 := by have := PMF.tsum_coe d; rwa [tsum_fintype] at this
    _ < ⊤ := ENNReal.one_lt_top)

section ObsLevel

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] in
private theorem pmfPi_heq_of_eq {O : ObsModel ι σ Obs Act}
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    {b : BehavioralProfile O} {v₁ v₂ : ∀ i, O.LocalTrace i} (h : v₁ = v₂) :
    HEq (Math.PMFProduct.pmfPi (fun i => b i (v₁ i)))
        (Math.PMFProduct.pmfPi (fun i => b i (v₂ i))) := by
  subst h; rfl

/-- `jointActionDist` depends on the state trace only through observations (HEq version). -/
theorem jointActionDist_obs_heq
    (b : BehavioralProfile O) (ss₁ ss₂ : List σ)
    (hobs : ∀ i, O.projectStates i ss₁ = O.projectStates i ss₂) :
    HEq (O.jointActionDist b ss₁) (O.jointActionDist b ss₂) :=
  pmfPi_heq_of_eq (funext hobs)

/-- For pure profiles, `pureStep` is just `O.step` with the cast action. -/
theorem pureStep_eq (π : PureProfile O) (ss : List σ) :
    O.pureStep π ss =
      O.step (O.lastState ss)
        (fun i => O.lastObs_projectStates i ss ▸ π i (O.projectStates i ss)) := by
  unfold pureStep stepDist jointActionDist pureToBehavioral castJointAction
  simp [Math.PMFProduct.pmfPi_pure, PMF.pure_bind]

/-- Under PSAR, if two profiles produce nonzero transition at the same state
trace and target, their step distributions are equal. -/
theorem pureStep_eq_of_nonzero_same
    (hPSAR : PerStepActionRecall O) {π₁ π₂ : PureProfile O} {ss : List σ} {t : σ}
    (h₁ : O.pureStep π₁ ss t ≠ 0) (h₂ : O.pureStep π₂ ss t ≠ 0) :
    O.pureStep π₁ ss = O.pureStep π₂ ss := by
  simp only [pureStep_eq] at h₁ h₂ ⊢
  congr 1; funext i
  have := hPSAR _ _ _ _ _ _ h₁ h₂ (fun _ => rfl) (fun _ => rfl) i
  simpa using this

/-- Under `PerStepActionRecall`, if `pureStep` at obs-equivalent traces gives
nonzero probability to obs-equivalent next states, the cast actions are equal. -/
theorem pureStep_action_eq_of_psar
    (hPSAR : PerStepActionRecall O) {π π' : PureProfile O} {ss ss' : List σ} {t t' : σ}
    (hobs : ∀ i, O.projectStates i ss = O.projectStates i ss')
    (hobst : ∀ i, O.obsEq i t t')
    (h1 : O.pureStep π ss t ≠ 0) (h2 : O.pureStep π' ss' t' ≠ 0)
    (i : ι) :
    (O.obsEq_of_projectStates_getLast i (hobs i)) ▸
      (O.lastObs_projectStates i ss ▸ π i (O.projectStates i ss)) =
      (O.lastObs_projectStates i ss' ▸ π' i (O.projectStates i ss')) := by
  rw [pureStep_eq] at h1 h2
  exact hPSAR _ _ _ _ _ _
    h1 h2
    (fun j => O.obsEq_of_projectStates_getLast j (hobs j)) hobst i

/-- Two composed transports to the same target type are equal when the source values are HEq. -/
private theorem transport_composed {α : Type} {P : α → Type} {a₁ a₂ b₁ b₂ : α}
    (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (hb : b₁ = b₂)
    (x₁ : P a₁) (x₂ : P a₂) (hx : HEq x₁ x₂) :
    (h₁ ▸ x₁ : P b₁) = (hb ▸ (h₂ ▸ x₂ : P b₂) : P b₁) := by
  subst h₁; subst h₂; subst hb; exact eq_of_heq hx

/-- `▸`-transport is HEq to the original value. -/
private theorem subst_heq' {α : Type} {P : α → Type} {a b : α}
    (h : a = b) (x : P b) : HEq (h ▸ x : P a) x := by subst h; rfl

/-- Forward `▸`-transport is HEq to the original value. -/
private theorem fwd_subst_heq {α : Type} {P : α → Type} {a b : α}
    (h : a = b) (x : P a) : HEq x (h ▸ x : P b) := by subst h; rfl

/-- `▸`-transport is injective. -/
private theorem transport_inj {α : Type} {P : α → Type} {a b : α}
    (h : a = b) {x y : P b} (hxy : (h ▸ x : P a) = h ▸ y) : x = y :=
  eq_of_heq ((subst_heq' h x).symm.trans (hxy ▸ subst_heq' h y))

/-- A dependent function applied to equal arguments yields a transported result. -/
private theorem dep_congr_subst {α : Type} {P : α → Type}
    (f : (a : α) → P a) {a₁ a₂ : α} (h : a₁ = a₂) :
    f a₁ = h ▸ f a₂ := by subst h; rfl

/-- `PMF.bind` is HEq-compatible when binding functions are pointwise HEq. -/
private theorem pmf_bind_heq {α β₁ β₂ : Type} (hβ : β₁ = β₂)
    (p : PMF α) (f₁ : α → PMF β₁) (f₂ : α → PMF β₂)
    (hf : ∀ a, HEq (f₁ a) (f₂ a)) :
    HEq (p.bind f₁) (p.bind f₂) := by
  subst hβ; exact heq_of_eq (congrArg p.bind (funext fun a => eq_of_heq (hf a)))

/-- `PMF.bind` HEq when both base measure and binding function change. -/
private theorem pmf_bind_heq' {α β₁ β₂ : Type} (hβ : β₁ = β₂)
    (p₁ p₂ : PMF α) (hp : p₁ = p₂) (f₁ : α → PMF β₁) (f₂ : α → PMF β₂)
    (hf : ∀ a, HEq (f₁ a) (f₂ a)) :
    HEq (p₁.bind f₁) (p₂.bind f₂) := by
  subst hp; exact pmf_bind_heq hβ p₁ f₁ f₂ hf

omit [DecidableEq ι] [Fintype ι] [(i : ι) → (o : Obs i) → Fintype (Act i o)] in
/-- The cast action from a profile at obs-equivalent traces are related by transport. -/
private theorem castJointAction_obs_eq (O : ObsModel ι σ Obs Act)
    (π : PureProfile O) {ss₁ ss₂ : List σ}
    (hobs : ∀ i, O.projectStates i ss₁ = O.projectStates i ss₂)
    (i : ι) :
    O.castJointAction ss₁ (fun j => π j (O.projectStates j ss₁)) i =
      (O.obsEq_of_projectStates_getLast i (hobs i)) ▸
        O.castJointAction ss₂ (fun j => π j (O.projectStates j ss₂)) i := by
  simp only [castJointAction]
  exact transport_composed
    (O.lastObs_projectStates i ss₁) (O.lastObs_projectStates i ss₂)
    (O.obsEq_of_projectStates_getLast i (hobs i))
    _ _ (hobs i ▸ HEq.rfl)

/-- Under PSAR, `pureStep` satisfies the cross-ratio for obs-equivalent
state traces and obs-equivalent targets. -/
theorem pureStep_cross_ratio
    (hPSAR : PerStepActionRecall O) {π₁ π₂ : PureProfile O} {ss₁ ss₂ : List σ} {t₁ t₂ : σ}
    (hobs : ∀ i, O.projectStates i ss₁ = O.projectStates i ss₂)
    (hobst : ∀ i, O.obsEq i t₁ t₂) :
    O.pureStep π₁ ss₁ t₁ * O.pureStep π₂ ss₂ t₂ =
      O.pureStep π₂ ss₁ t₁ * O.pureStep π₁ ss₂ t₂ := by
  simp only [pureStep_eq]
  -- Abbreviate the step-world actions
  let s₁ := O.lastState ss₁
  let s₂ := O.lastState ss₂
  let a₁ : O.JointActionAt s₁ := O.castJointAction ss₁ (fun i => π₁ i (O.projectStates i ss₁))
  let b₁ : O.JointActionAt s₁ := O.castJointAction ss₁ (fun i => π₂ i (O.projectStates i ss₁))
  let a₂ : O.JointActionAt s₂ := O.castJointAction ss₂ (fun i => π₁ i (O.projectStates i ss₂))
  let b₂ : O.JointActionAt s₂ := O.castJointAction ss₂ (fun i => π₂ i (O.projectStates i ss₂))
  -- The goal is: step s₁ a₁ t₁ * step s₂ b₂ t₂ = step s₁ b₁ t₁ * step s₂ a₂ t₂
  change (O.step s₁ a₁) t₁ * (O.step s₂ b₂) t₂ = (O.step s₁ b₁) t₁ * (O.step s₂ a₂) t₂
  have hobss : ∀ i, O.obsEq i s₁ s₂ :=
    fun i => O.obsEq_of_projectStates_getLast i (hobs i)
  -- Key facts: cast actions at ss₁ and ss₂ are related by transport
  have ha_rel : ∀ i, a₁ i = (hobss i) ▸ a₂ i := castJointAction_obs_eq O π₁ hobs
  have hb_rel : ∀ i, b₁ i = (hobss i) ▸ b₂ i := castJointAction_obs_eq O π₂ hobs
  -- Helper: a₁ i ≅ a₂ i and b₁ i ≅ b₂ i (from castJointAction_obs_eq)
  have ha_heq : ∀ i, HEq (a₁ i) (a₂ i) := fun i => by
    have := ha_rel i; rw [this]; exact subst_heq' (hobss i) (a₂ i)
  have hb_heq : ∀ i, HEq (b₁ i) (b₂ i) := fun i => by
    have := hb_rel i; rw [this]; exact subst_heq' (hobss i) (b₂ i)
  by_cases hab : a₁ = b₁
  · -- Same action at s₁ implies same action at s₂ (by HEq)
    have hab₂ : a₂ = b₂ := funext fun i =>
      eq_of_heq ((ha_heq i).symm.trans (congr_fun hab i ▸ hb_heq i))
    simp [hab, hab₂]
  · -- Different actions at s₁: PSAR forces both sides to be zero
    have hL : (O.step s₁ a₁) t₁ * (O.step s₂ b₂) t₂ = 0 := by
      by_contra h
      rw [mul_eq_zero, not_or] at h
      -- PSAR gives: (hobss i) ▸ a₁ i = b₂ i (forward transport)
      -- Chain: a₁ i ≅ fwd(a₁ i) = b₂ i ≅ b₁ i  →  a₁ i = b₁ i
      have hpsar := fun i => hPSAR s₁ s₂ t₁ t₂ a₁ b₂ h.1 h.2 hobss hobst i
      exact hab (funext fun i => eq_of_heq
        ((fwd_subst_heq (hobss i) (a₁ i)).trans (heq_of_eq (hpsar i)) |>.trans (hb_heq i).symm))
    have hR : (O.step s₁ b₁) t₁ * (O.step s₂ a₂) t₂ = 0 := by
      by_contra h
      rw [mul_eq_zero, not_or] at h
      have hpsar := fun i => hPSAR s₁ s₂ t₁ t₂ b₁ a₂ h.1 h.2 hobss hobst i
      exact hab (funext fun i => eq_of_heq ((fwd_subst_heq (hobss i) (b₁ i)).trans
        (heq_of_eq (hpsar i)) |>.trans (ha_heq i).symm).symm)
    rw [hL, hR]

/-- Under PSAR, pureRun satisfies the pairwise cross-ratio for
obs-equivalent traces: the reach probability ratio is profile-independent.
Proof: by induction on k, using `pureStep_eq_of_nonzero_same` for the
same-state case and `pureStep_action_eq_of_psar` for cross-state. -/
theorem pureRun_pairwise_cross_of_psar
    (hPSAR : PerStepActionRecall O) (k : Nat) (π₁ π₂ : PureProfile O) (ss₁ ss₂ : List σ)
    (hobs : ∀ i, O.projectStates i ss₁ = O.projectStates i ss₂) :
    pureRun (O.pureStep) O.init k π₁ ss₁ *
      pureRun (O.pureStep) O.init k π₂ ss₂ =
    pureRun (O.pureStep) O.init k π₂ ss₁ *
      pureRun (O.pureStep) O.init k π₁ ss₂ := by
  induction k generalizing ss₁ ss₂ with
  | zero =>
    -- pureRun at 0 = PMF.pure [s₀], independent of π
    simp [pureRun]
  | succ n ih =>
    -- Decompose ss₁ and ss₂ as prefix ++ [last]
    rcases List.eq_nil_or_concat ss₁ with rfl | ⟨p₁, t₁, rfl⟩
    · -- ss₁ = []: pureRun at succ on [] is 0, both sides = 0
      simp only [show ∀ π, pureRun (O.pureStep) O.init (n + 1) π ([] : List σ) = 0 from
        fun π => pureRun_succ_nil (O.pureStep) O.init n π, zero_mul]
    · rcases List.eq_nil_or_concat ss₂ with rfl | ⟨p₂, t₂, rfl⟩
      · -- ss₂ = []: similar
        simp only [show ∀ π, pureRun (O.pureStep) O.init (n + 1) π ([] : List σ) = 0 from
          fun π => pureRun_succ_nil (O.pureStep) O.init n π, mul_zero]
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
        have hStep := pureStep_cross_ratio hPSAR hobs_prefix hobs_last
          (π₁ := π₁) (π₂ := π₂) (t₁ := t₁) (t₂ := t₂)
        -- Combine: (a₁*b₁)*(a₂*b₂) = (a₁*a₂)*(b₁*b₂)
        --        = (a₃*a₄)*(b₃*b₄) = (a₃*b₃)*(a₄*b₄) by rearrangement
        calc pureRun (O.pureStep) O.init n π₁ p₁ * O.pureStep π₁ p₁ t₁ *
              (pureRun (O.pureStep) O.init n π₂ p₂ * O.pureStep π₂ p₂ t₂)
            = (pureRun (O.pureStep) O.init n π₁ p₁ *
                pureRun (O.pureStep) O.init n π₂ p₂) *
              (O.pureStep π₁ p₁ t₁ * O.pureStep π₂ p₂ t₂) := by ring
          _ = (pureRun (O.pureStep) O.init n π₂ p₁ *
                pureRun (O.pureStep) O.init n π₁ p₂) *
              (O.pureStep π₂ p₁ t₁ * O.pureStep π₁ p₂ t₂) := by rw [hIH, hStep]
          _ = pureRun (O.pureStep) O.init n π₂ p₁ * O.pureStep π₂ p₁ t₁ *
              (pureRun (O.pureStep) O.init n π₁ p₂ * O.pureStep π₁ p₂ t₂) := by ring

variable [Fintype (PureProfile O)]

/-- Under `PerStepActionRecall`, for obs-equivalent state traces, the
`reweightPMF` on reach probabilities gives the same distribution. -/
theorem reweightPMF_pureRun_obs_invariant
    (hPSAR : PerStepActionRecall O) (ν : PMF (PureProfile O)) (n : Nat)
    (ss₁ ss₂ : List σ)
    (hobs : ∀ i, O.projectStates i ss₁ = O.projectStates i ss₂)
    (hreach₁ : ∑ π : PureProfile O, ν π * pureRun (O.pureStep) O.init n π ss₁ ≠ 0)
    (hreach₂ : ∑ π : PureProfile O, ν π * pureRun (O.pureStep) O.init n π ss₂ ≠ 0) :
    reweightPMF ν (fun π => pureRun (O.pureStep) O.init n π ss₁) =
    reweightPMF ν (fun π => pureRun (O.pureStep) O.init n π ss₂) := by
  have hCtop₁ : ∑ π, ν π * pureRun (O.pureStep) O.init n π ss₁ ≠ ⊤ :=
    sum_mul_pmf_ne_top ν _ fun π => PMF.coe_le_one _ _
  have hCtop₂ : ∑ π, ν π * pureRun (O.pureStep) O.init n π ss₂ ≠ ⊤ :=
    sum_mul_pmf_ne_top ν _ fun π => PMF.coe_le_one _ _
  apply Math.ParameterizedChain.reweightPMF_eq_of_cross_mul ν _ _ hreach₁ hCtop₁ hreach₂ hCtop₂
  intro π
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π' _
  have h := pureRun_pairwise_cross_of_psar hPSAR n π π' ss₁ ss₂ hobs
  calc pureRun (O.pureStep) O.init n π ss₁ * (ν π' * pureRun (O.pureStep) O.init n π' ss₂)
      = ν π' * (pureRun (O.pureStep) O.init n π ss₁ * pureRun (O.pureStep) O.init n π' ss₂) :=
        by ac_rfl
    _ = ν π' * (pureRun (O.pureStep) O.init n π' ss₁ * pureRun (O.pureStep) O.init n π ss₂) :=
        by rw [h]
    _ = pureRun (O.pureStep) O.init n π ss₂ * (ν π' * pureRun (O.pureStep) O.init n π' ss₁) :=
        by ac_rfl

/-- Under `PerStepActionRecall`, the state-trace mediator at obs-equivalent
reachable traces produces HEq action distributions (types differ by observation). -/
theorem mixedToMediator_obs_heq
    (hPSAR : PerStepActionRecall O) (ν : PMF (PureProfile O)) (n : Nat)
    (ss₁ ss₂ : List σ)
    (hobs : ∀ i, O.projectStates i ss₁ = O.projectStates i ss₂)
    (hreach₁ : ∑ π : PureProfile O, ν π * pureRun (O.pureStep) O.init n π ss₁ ≠ 0)
    (hreach₂ : ∑ π : PureProfile O, ν π * pureRun (O.pureStep) O.init n π ss₂ ≠ 0) :
    HEq (O.mixedToMediator ν n ss₁) (O.mixedToMediator ν n ss₂) := by
  unfold mixedToMediator
  rw [reweightPMF_pureRun_obs_invariant hPSAR ν n ss₁ ss₂ hobs hreach₁ hreach₂]
  exact pmf_bind_heq
    (congrArg (fun f => ∀ i, Act i (O.lastObs i (f i))) (funext hobs))
    _ _ _ (fun π => jointActionDist_obs_heq (O.pureToBehavioral π) ss₁ ss₂ hobs)

end ObsLevel

section ObsCorrelatedRealization

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [Fintype (PureProfile O)] [∀ i, Fintype (O.LocalTrace i)]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
open Classical in
/-- **Observation-level correlated realization**: under `PerStepActionRecall`,
a `BehavioralProfileCorr O` (observation-level mediator) produces the same
trace distribution as any mixed strategy `ν`. -/
theorem obs_correlated_realization [Inhabited ι] [∀ i o, Nonempty (Act i o)]
    (hPSAR : PerStepActionRecall O)
    (ν : PMF (PureProfile O)) (k : Nat) :
    ∃ bc : BehavioralProfileCorr O,
      seqRun (fun _ ss => O.stepDistCorr bc ss) O.init k =
      ν.bind (fun π => pureRun (O.pureStep) O.init k π) := by
  -- Define obs-level mediator: pick a reachable representative state trace
  -- The `▸` casts from projectStates-indexed type to v-indexed type.
  let bc : BehavioralProfileCorr O := fun v =>
    if h : ∃ ss : List σ,
          (∀ i, O.projectStates i ss = v i) ∧
          ∑ π : PureProfile O, ν π * pureRun (O.pureStep) O.init (ss.length - 1) π ss ≠ 0
    then (funext h.choose_spec.1) ▸
      O.mixedToMediator ν (h.choose.length - 1) h.choose
    else PMF.pure (fun _ => Classical.arbitrary _)
  use bc
  -- Suffices: seqRun under bc = seqRun under condStep
  suffices hsuff : seqRun (fun _ ss => O.stepDistCorr bc ss) O.init k =
      seqRun (condStep ν (O.pureStep) O.init) O.init k by
    rw [hsuff, condRun_eq_mixedRun]
  -- Key lemma: step functions agree on the support
  suffices hfn : ∀ (n : Nat) (ss : List σ),
      (seqRun (condStep ν (O.pureStep) O.init) O.init n) ss ≠ 0 →
      O.stepDistCorr bc ss = condStep ν (O.pureStep) O.init n ss by
    -- Induction on k
    induction k with
    | zero => rfl
    | succ n ih =>
      change (seqRun (fun _ ss => O.stepDistCorr bc ss) O.init n).bind
            (fun ss => pushforward (O.stepDistCorr bc ss) (fun t => ss ++ [t])) =
          (seqRun (condStep ν (O.pureStep) O.init) O.init n).bind
            (fun ss => pushforward (condStep ν (O.pureStep) O.init n ss)
              (fun t => ss ++ [t]))
      rw [ih]
      ext y
      simp only [PMF.bind_apply]
      apply tsum_congr
      intro ss
      by_cases hss : (seqRun (condStep ν (O.pureStep) O.init) O.init n) ss = 0
      · simp [hss]
      · rw [hfn n ss hss]
  -- Prove hfn
  intro n ss hss
  -- 1. ss is reachable at step n
  have hreach : ∑ π, ν π * pureRun (O.pureStep) O.init n π ss ≠ 0 := by
    rwa [condRun_eq_mixedRun, PMF.bind_apply, tsum_fintype] at hss
  -- 2. ss.length = n + 1
  have hlen : ss.length = n + 1 := by
    obtain ⟨π, _, hπ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hreach
    exact pureRun_length (O.pureStep) O.init n π ss (right_ne_zero_of_mul hπ)
  -- 3. bc(projectStates(ss)) = O.mixedToMediator ν n ss
  have hbc : bc (fun i => O.projectStates i ss) = O.mixedToMediator ν n ss := by
    -- The existential is satisfied by ss itself
    have hexist : ∃ ss' : List σ,
        (∀ i, O.projectStates i ss' = O.projectStates i ss) ∧
        ∑ π, ν π * pureRun (O.pureStep) O.init (ss'.length - 1) π ss' ≠ 0 :=
      ⟨ss, fun _ => rfl, by rwa [show ss.length - 1 = n from by omega]⟩
    simp only [bc, dif_pos hexist]
    -- hexist.choose has same projections and is reachable
    set ss' := hexist.choose with hss'_def
    have hobs' := hexist.choose_spec.1
    have hreach' := hexist.choose_spec.2
    -- ss'.length = ss.length (from obs-equiv via publicView)
    have hlen' : ss'.length = ss.length :=
      O.projectStates_eq_length (default : ι) (hobs' default)
    -- ss'.length - 1 = n
    have hn' : ss'.length - 1 = n := by omega
    -- Can't use rw [hn'] directly (dependent type in ▸), use eq_of_heq chain
    have hmed_heq : HEq (O.mixedToMediator ν (ss'.length - 1) ss')
        (O.mixedToMediator ν n ss) := by
      rw [hn']
      exact mixedToMediator_obs_heq hPSAR ν n ss' ss hobs'
        (by rwa [hn'] at hreach') hreach
    apply eq_of_heq
    apply HEq.trans
    · exact (fwd_subst_heq (P := fun f => PMF (∀ i, Act i (O.lastObs i (f i))))
        (funext hobs')
        (O.mixedToMediator ν (ss'.length - 1) ss')).symm
    · exact hmed_heq
  -- 4. stepDistCorr bc ss = condStep ... n ss
  calc O.stepDistCorr bc ss
      = (bc (fun i => O.projectStates i ss)).bind
          (fun a => O.step (O.lastState ss)
            (fun i => O.lastObs_projectStates i ss ▸ a i)) := rfl
    _ = (O.mixedToMediator ν n ss).bind
          (fun a => O.step (O.lastState ss)
            (fun i => O.lastObs_projectStates i ss ▸ a i)) := by
        rw [hbc]
    _ = condStep ν (O.pureStep) O.init n ss :=
        mediator_step_eq_condStep ν n ss

end ObsCorrelatedRealization

/-- Under `PerStepActionRecall`, at most one action can produce a nonzero
transition probability between any pair of states. -/
theorem action_unique_of_psar
    (hPSAR : PerStepActionRecall O) {s t : σ} {a a' : O.JointActionAt s}
    (ha : (O.step s a) t ≠ 0) (ha' : (O.step s a') t ≠ 0) :
    a = a' :=
  funext fun i => hPSAR s s t t a a' ha ha' (fun _ => rfl) (fun _ => rfl) i

/-- Under `PerStepPlayerRecall`, player `i`'s action component is determined by
their own observation at source and target. -/
theorem action_component_unique_of_pspr
    (hPSPR : PerStepPlayerRecall O) (i : ι)
    {s s' t t' : σ} {a : O.JointActionAt s} {a' : O.JointActionAt s'}
    (ha : (O.step s a) t ≠ 0) (ha' : (O.step s' a') t' ≠ 0)
    (hobs : O.obsEq i s s') (hobst : O.obsEq i t t') :
    hobs ▸ a i = a' i :=
  hPSPR i s s' t t' a a' ha ha' hobs hobst

/-! ## Bridge: pureRun reachability

The `pureRun` chain produces traces where every state is step-reachable.
This bridges the `Math.ParameterizedChain` execution model with the
`ReachActionTrace` witnesses from `SemanticForm`. -/

section PureRunBridge

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- If `pureRun` reaches a trace with nonzero probability, there exists a
corresponding `ReachActionTrace`. -/
theorem pureRun_nonzero_to_reachActionTrace
    (n : Nat)
    (π : PureProfile O) (ss : List σ)
    (h : pureRun (O.pureStep) O.init n π ss ≠ 0) :
    Nonempty (O.ReachActionTrace ss) := by
  induction n generalizing ss with
  | zero =>
    have hss : ss = [O.init] := by
      by_contra hne; exact h (by simp [pureRun, PMF.pure_apply, hne])
    subst hss; exact ⟨.init⟩
  | succ m ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h
    · simp only [List.concat_eq_append] at h ⊢
      have hp := left_ne_zero_of_mul (pureRun_succ_append .. ▸ h)
      have ht := right_ne_zero_of_mul (pureRun_succ_append .. ▸ h)
      obtain ⟨rat_p⟩ := ih p hp
      rw [pureStep_eq] at ht
      have hlen_p := pureRun_length _ _ m π p hp
      have hp_ne : p ≠ [] := by intro h'; simp [h'] at hlen_p
      have hlast : p.getLast? = some (O.lastState p) := by
        cases hg : p.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hp_ne
        | some s => simp [lastState, hg]
      let a : O.JointActionAt (O.lastState p) :=
        fun i => O.lastObs_projectStates i p ▸ π i (O.projectStates i p)
      exact ⟨.snoc a rat_p hlast ht⟩

/-- If `pureRun` reaches `ss` with nonzero probability, the last state of `ss`
is step-reachable from `O.init`. -/
theorem pureRun_nonzero_last_stepReachable
    (n : Nat)
    (π : PureProfile O) (ss : List σ)
    (h : pureRun (O.pureStep) O.init n π ss ≠ 0) :
    O.StepReachable (O.lastState ss) := by
  obtain ⟨rat⟩ := pureRun_nonzero_to_reachActionTrace n π ss h
  have hlen := pureRun_length _ _ n π ss h
  have hne : ss ≠ [] := by intro h'; simp [h'] at hlen
  have hlast : ss.getLast? = some (O.lastState ss) := by
    cases hg : ss.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hne
    | some s => simp [lastState, hg]
  exact ⟨ss, ⟨rat⟩, hlast⟩

end PureRunBridge

/-! ## Reach factoring under PSAR

Under `PerStepActionRecall`, the reach probability `pureRun(O.pureStep, s₀, n, π, ss)`
depends on `π` only through whether `π` produces the uniquely forced action at each
step. This gives:

1. **Constancy**: nonzero reach probabilities are equal across all profiles
2. **Per-player factoring**: the nonzero condition factors as `∀ i, π_i consistent`
3. **Product preservation**: reweighting a product measure by reach gives a product -/

section ReachFactor

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- Under PSAR, nonzero reach probabilities at the same trace are equal.
If two profiles both reach `ss` with nonzero probability, they must produce
the same action at every step, hence have the same reach probability. -/
theorem pureRun_const_of_psar
    (hPSAR : PerStepActionRecall O) (n : Nat) {π π' : PureProfile O} {ss : List σ}
    (h : pureRun (O.pureStep) O.init n π ss ≠ 0)
    (h' : pureRun (O.pureStep) O.init n π' ss ≠ 0) :
    pureRun (O.pureStep) O.init n π ss =
      pureRun (O.pureStep) O.init n π' ss := by
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
          pureStep_eq_of_nonzero_same hPSAR ht ht']

/-- Under PSAR, at a reachable transition, `pureStep` is nonzero iff
the profile produces the same action as any fixed witness profile. -/
theorem pureStep_nonzero_iff_action_eq
    (hPSAR : PerStepActionRecall O) {π₀ : PureProfile O} {ss : List σ} {t : σ}
    (h₀ : O.pureStep π₀ ss t ≠ 0) (π : PureProfile O) :
    O.pureStep π ss t ≠ 0 ↔
      (fun i => π i (O.projectStates i ss)) =
        (fun i => π₀ i (O.projectStates i ss)) := by
  constructor
  · intro hne
    rw [pureStep_eq] at hne h₀
    -- PSAR gives ∀ i, rfl ▸ (▸ π i ...) = ▸ π₀ i ...
    have h := hPSAR _ _ _ _ _ _ hne h₀ (fun _ => rfl) (fun _ => rfl)
    exact funext fun i => by
      -- h i : rfl ▸ (▸ π i ...) = ▸ π₀ i ...
      -- rfl ▸ is definitionally identity, so strip it:
      have hi : (O.lastObs_projectStates i ss ▸ π i (O.projectStates i ss)) =
          O.lastObs_projectStates i ss ▸ π₀ i (O.projectStates i ss) := h i
      -- Use HEq chain: π i ... ≅ ▸ π i ... = ▸ π₀ i ... ≅ π₀ i ...
      exact eq_of_heq ((fwd_subst_heq _ _).trans
        ((heq_of_eq hi).trans (fwd_subst_heq _ _).symm))
  · intro heq
    have : O.pureStep π ss = O.pureStep π₀ ss := by
      simp only [pureStep_eq]; congr 1; funext i
      exact congrArg (O.lastObs_projectStates i ss ▸ ·) (congr_fun heq i)
    rwa [this]

/-- Under PSAR, `pureRun` is nonzero iff the profile produces the same
action as the witness at every step (prefix). The condition is:
at each prefix `p ++ [t]` of `ss`, the profile agrees on the action at `p`. -/
theorem pureRun_nonzero_iff_action_eq
    (hPSAR : PerStepActionRecall O) (n : Nat) {π₀ : PureProfile O} {ss : List σ}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0) (π : PureProfile O) :
    pureRun (O.pureStep) O.init n π ss ≠ 0 ↔
      (pureRun (O.pureStep) O.init n π ss =
        pureRun (O.pureStep) O.init n π₀ ss) := by
  constructor
  · exact fun h => pureRun_const_of_psar hPSAR n h h₀
  · intro heq; rw [heq]; exact h₀

/-- Under PSAR, `O.pureStep π ss t` factors per-player: it is nonzero iff
each player `i` individually produces the forced action component. -/
theorem pureStep_nonzero_iff_forall_player
    (hPSAR : PerStepActionRecall O) {π₀ : PureProfile O} {ss : List σ} {t : σ}
    (h₀ : O.pureStep π₀ ss t ≠ 0) (π : PureProfile O) :
    O.pureStep π ss t ≠ 0 ↔
      ∀ i, π i (O.projectStates i ss) = π₀ i (O.projectStates i ss) := by
  rw [pureStep_nonzero_iff_action_eq hPSAR h₀]
  exact ⟨fun h i => congr_fun h i, funext⟩

/-- Under PSAR, `pureRun` factors into a trace-dependent constant times a
per-player consistency indicator. If `π` is consistent (nonzero reach),
the reach value equals the witness; otherwise it's zero. -/
theorem pureRun_eq_const_mul_indicator
    (hPSAR : PerStepActionRecall O) (n : Nat) (π₀ : PureProfile O) (ss : List σ)
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0)
    (π : PureProfile O) :
    pureRun (O.pureStep) O.init n π ss =
      if pureRun (O.pureStep) O.init n π ss ≠ 0
      then pureRun (O.pureStep) O.init n π₀ ss
      else 0 := by
  split
  · exact pureRun_const_of_psar hPSAR n ‹_› h₀
  · push_neg at *; exact le_antisymm (le_of_eq ‹_›) (zero_le _)

/-- Under PSAR, `pureRun` nonzero is equivalent to matching the witness action
at every prefix. Stated inductively: nonzero at `p ++ [t]` iff nonzero at `p`
and action matches at `p`. -/
theorem pureRun_succ_nonzero_iff
    (hPSAR : PerStepActionRecall O) (m : Nat) {π₀ : PureProfile O} {p : List σ} {t : σ}
    (h₀ : pureRun (O.pureStep) O.init (m + 1) π₀ (p ++ [t]) ≠ 0)
    (π : PureProfile O) :
    pureRun (O.pureStep) O.init (m + 1) π (p ++ [t]) ≠ 0 ↔
      pureRun (O.pureStep) O.init m π p ≠ 0 ∧
        ∀ i, π i (O.projectStates i p) = π₀ i (O.projectStates i p) := by
  simp only [pureRun_succ_append] at h₀ ⊢
  have hp₀ := left_ne_zero_of_mul h₀
  have ht₀ := right_ne_zero_of_mul h₀
  constructor
  · intro hne
    exact ⟨left_ne_zero_of_mul hne,
      (pureStep_nonzero_iff_forall_player hPSAR ht₀ π).mp
        (right_ne_zero_of_mul hne)⟩
  · intro ⟨hp, hall⟩
    exact mul_ne_zero hp
      ((pureStep_nonzero_iff_forall_player hPSAR ht₀ π).mpr hall)

/-- Under PSAR, `pureStep` is invariant under changing players who produce
the same action. If `π` and `π'` agree on the action at `ss` (all players
give the same action component), then `O.pureStep π ss = O.pureStep π' ss`. -/
theorem pureStep_eq_of_action_eq {π π' : PureProfile O} {ss : List σ}
    (h : ∀ i, π i (O.projectStates i ss) = π' i (O.projectStates i ss)) :
    O.pureStep π ss = O.pureStep π' ss := by
  simp only [pureStep_eq]; congr 1; funext i
  exact congrArg (O.lastObs_projectStates i ss ▸ ·) (h i)

open Classical in
/-- Under PSAR, reach factors per-player via `Function.update`:
`pureRun π ss ≠ 0` iff for each player `i`, swapping just player `i`'s
component from `π` into the witness `π₀` still gives nonzero reach.

This is the cleanest per-player factoring: each player's consistency
can be tested independently. -/
theorem pureRun_nonzero_iff_update
    (hPSAR : PerStepActionRecall O) (n : Nat) {π₀ : PureProfile O} {ss : List σ}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0)
    (π : PureProfile O) :
    pureRun (O.pureStep) O.init n π ss ≠ 0 ↔
      ∀ i, pureRun (O.pureStep) O.init n
        (Function.update π₀ i (π i)) ss ≠ 0 := by
  induction n generalizing ss with
  | zero =>
    simp only [pureRun, ne_eq] at h₀ ⊢
    exact ⟨fun _ _ => h₀, fun _ => h₀⟩
  | succ m ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h₀
    · simp only [List.concat_eq_append] at h₀ ⊢
      have hp₀ : pureRun (O.pureStep) O.init m π₀ p ≠ 0 := by
        rw [pureRun_succ_append] at h₀; exact left_ne_zero_of_mul h₀
      rw [pureRun_succ_nonzero_iff hPSAR m h₀]
      constructor
      · -- Forward: π consistent → each update consistent
        intro ⟨hp, hact⟩ i
        exact (pureRun_succ_nonzero_iff hPSAR m h₀
          (Function.update π₀ i (π i))).mpr
          ⟨(ih hp₀).mp hp i, fun j => by
            by_cases hij : j = i
            · subst hij; simp [Function.update_self, hact]
            · simp [Function.update_of_ne hij]⟩
      · -- Backward: each update consistent → π consistent
        intro hall
        constructor
        · exact (ih hp₀).mpr fun i =>
            ((pureRun_succ_nonzero_iff hPSAR m h₀ _).mp (hall i)).1
        · intro i
          have := ((pureRun_succ_nonzero_iff hPSAR m h₀ _).mp (hall i)).2 i
          simp only [Function.update_self] at this
          exact this

end ReachFactor

section Decentralization

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- Generalized step-independence-to-trace theorem: if a behavioral profile
`b` satisfies the step-independence property with respect to any
`ν : PMF (PureProfile O)` (not necessarily a product), then
`runDist k b = ν.bind (runDistPure k)`.

This generalizes the step-independence theorem from
`KuhnCore.lean` by replacing `mixedJoint μ` with an arbitrary `ν`. -/
theorem runDist_eq_of_stepIndependence
    (ν : PMF (PureProfile O))
    (b : BehavioralProfile O)
    (hStep : ∀ n,
      ν.bind (fun π =>
        (O.runDistPure n π).bind (fun ss =>
          pushforward (O.stepDist b ss) (fun t => ss ++ [t]))) =
      ν.bind (fun π =>
        (O.runDistPure n π).bind (fun ss =>
          pushforward (O.stepDist (O.pureToBehavioral π) ss)
            (fun t => ss ++ [t])))) (k : Nat) :
    O.runDist k b = ν.bind (fun π => O.runDistPure k π) := by
  induction k with
  | zero => simp [runDist, runDistPure]
  | succ n ih =>
    calc O.runDist (n + 1) b
        = (O.runDist n b).bind (fun ss =>
            pushforward (O.stepDist b ss) (fun t => ss ++ [t])) := by
          simp [runDist]
      _ = (ν.bind (fun π => O.runDistPure n π)).bind (fun ss =>
            pushforward (O.stepDist b ss) (fun t => ss ++ [t])) := by rw [ih]
      _ = ν.bind (fun π =>
            (O.runDistPure n π).bind (fun ss =>
              pushforward (O.stepDist b ss) (fun t => ss ++ [t]))) := by
          rw [PMF.bind_bind]
      _ = ν.bind (fun π =>
            (O.runDistPure n π).bind (fun ss =>
              pushforward (O.stepDist (O.pureToBehavioral π) ss)
                (fun t => ss ++ [t]))) := by simpa using hStep n
      _ = ν.bind (fun π => O.runDistPure (n + 1) π) := by
          simp [runDist, runDistPure]

/-- Under `PerStepPlayerRecall`, the pure-step action component for player `i`
depends only on player `i`'s observation at obs-equivalent traces. -/
theorem pureStep_component_eq_of_pspr
    (hPSPR : PerStepPlayerRecall O) (i : ι) {π π' : PureProfile O} {ss ss' : List σ} {t t' : σ}
    (hobs_i : O.projectStates i ss = O.projectStates i ss')
    (hobst_i : O.obsEq i t t')
    (h1 : O.pureStep π ss t ≠ 0) (h2 : O.pureStep π' ss' t' ≠ 0) :
    π i (O.projectStates i ss) = hobs_i ▸ π' i (O.projectStates i ss') := by
  rw [pureStep_eq] at h1 h2
  have hpspr := hPSPR i _ _ _ _ _ _
    h1 h2 (O.obsEq_of_projectStates_getLast i hobs_i) hobst_i
  -- hpspr : obsEq ▸ (lastObs₁ ▸ π i ...) = lastObs₂ ▸ π' i ...
  apply eq_of_heq
  -- Chain: π i ... ≅ ▸π i... ≅ obsEq▸▸π i... = ▸π' i... ≅ π' i... ≅ hobs_i▸π' i...
  have h1' : HEq (π i (O.projectStates i ss)) (π' i (O.projectStates i ss')) :=
    (fwd_subst_heq _ (π i _)).trans
      ((fwd_subst_heq _ (O.lastObs_projectStates i ss ▸ π i _)).trans
        ((heq_of_eq hpspr).trans (fwd_subst_heq _ (π' i _)).symm))
  exact h1'.trans (subst_heq' (P := fun v => Act i (O.lastObs i v))
    hobs_i (π' i (O.projectStates i ss'))).symm

/-- Per-player version of `pureStep_component_eq_of_pspr`:
only needs `PlayerStepRecall O i` for the specific player `i`,
not the full `PerStepPlayerRecall` for all players. -/
theorem pureStep_component_eq_of_playerRecall
    (i : ι) (hPSR_i : PlayerStepRecall O i) {π π' : PureProfile O} {ss ss' : List σ} {t t' : σ}
    (hobs_i : O.projectStates i ss = O.projectStates i ss')
    (hobst_i : O.obsEq i t t')
    (h1 : O.pureStep π ss t ≠ 0) (h2 : O.pureStep π' ss' t' ≠ 0) :
    π i (O.projectStates i ss) = hobs_i ▸ π' i (O.projectStates i ss') := by
  rw [pureStep_eq] at h1 h2
  have hpspr := hPSR_i _ _ _ _ _ _
    h1 h2 (O.obsEq_of_projectStates_getLast i hobs_i) hobst_i
  apply eq_of_heq
  have h1' : HEq (π i (O.projectStates i ss)) (π' i (O.projectStates i ss')) :=
    (fwd_subst_heq _ (π i _)).trans
      ((fwd_subst_heq _ (O.lastObs_projectStates i ss ▸ π i _)).trans
        ((heq_of_eq hpspr).trans (fwd_subst_heq _ (π' i _)).symm))
  exact h1'.trans (subst_heq' (P := fun v => Act i (O.lastObs i v))
    hobs_i (π' i (O.projectStates i ss'))).symm

end Decentralization

section ProductPreservation

open Math.PMFProduct

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.LocalTrace i)]

open Classical in
/-- Under PSAR, the reach weight `pureRun π ss` satisfies the cross-multiplication
identity with the per-player product weight `∏ᵢ pureRun (update π₀ i (π i)) ss`.
This allows switching between them via `reweightPMF_eq_of_cross_mul`. -/
theorem pureRun_cross_mul_product
    (hPSAR : PerStepActionRecall O) (ν : PMF (PureProfile O))
    (n : Nat) {π₀ : PureProfile O} {ss : List σ}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0) (π : PureProfile O) :
    pureRun (O.pureStep) O.init n π ss *
      (∑ π' : PureProfile O, ν π' *
        ∏ i, pureRun (O.pureStep) O.init n (Function.update π₀ i (π' i)) ss) =
    (∏ i, pureRun (O.pureStep) O.init n (Function.update π₀ i (π i)) ss) *
      (∑ π' : PureProfile O, ν π' *
        pureRun (O.pureStep) O.init n π' ss) := by
  set C₀ := pureRun (O.pureStep) O.init n π₀ ss with hC₀_def
  -- Helper: for consistent π', the reach equals C₀
  have hconst : ∀ π', pureRun (O.pureStep) O.init n π' ss ≠ 0 →
      pureRun (O.pureStep) O.init n π' ss = C₀ :=
    fun π' h => pureRun_const_of_psar hPSAR n h h₀
  -- Helper: for consistent π', each per-player weight equals C₀
  have hconst_upd : ∀ (π' : PureProfile O) (i : ι),
      pureRun (O.pureStep) O.init n (Function.update π₀ i (π' i)) ss ≠ 0 →
      pureRun (O.pureStep) O.init n (Function.update π₀ i (π' i)) ss = C₀ :=
    fun π' i h => pureRun_const_of_psar hPSAR n h h₀
  -- Distribute multiplication into sums
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro π' _
  -- Pointwise: w(π) * (ν π' * ∏ wᵢ(π'ᵢ)) = (∏ wᵢ(πᵢ)) * (ν π' * w(π'))
  -- Case split on consistency of π and π'
  by_cases hπ : pureRun (O.pureStep) O.init n π ss = 0
  · -- π not consistent: w(π) = 0 and ∏ wᵢ(πᵢ) = 0
    rw [hπ, zero_mul]
    have := mt (pureRun_nonzero_iff_update hPSAR n h₀ π).mpr
      (not_not.mpr hπ)
    push_neg at this; obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
  · by_cases hπ' : pureRun (O.pureStep) O.init n π' ss = 0
    · -- π' not consistent: w(π') = 0 and ∏ wᵢ(π'ᵢ) = 0
      rw [hπ', mul_zero, mul_zero]
      have := mt (pureRun_nonzero_iff_update hPSAR n h₀ π').mpr
        (not_not.mpr hπ')
      push_neg at this; obtain ⟨j, hj⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, mul_zero, mul_zero]
    · -- Both consistent: all values equal C₀
      have hw := hconst π hπ; have hw' := hconst π' hπ'
      have hwi : ∀ i, pureRun (O.pureStep) O.init n
          (Function.update π₀ i (π i)) ss = C₀ :=
        fun i => hconst_upd π i
          ((pureRun_nonzero_iff_update hPSAR n h₀ π).mp hπ i)
      have hwi' : ∀ i, pureRun (O.pureStep) O.init n
          (Function.update π₀ i (π' i)) ss = C₀ :=
        fun i => hconst_upd π' i
          ((pureRun_nonzero_iff_update hPSAR n h₀ π').mp hπ' i)
      rw [hw, hw']; simp_rw [hwi, hwi']; ring

open Classical in
set_option linter.unusedFintypeInType false in
/-- Under PSAR, when `ν = pmfPi μ` (product of per-player strategy distributions)
and the trace `ss` is reachable, the mediator `O.mixedToMediator ν n ss` produces
a **product** action distribution: the recommended actions are independent across
players.

This is the "product in → product out" property: independence of the input
strategy distribution is preserved by the mediator construction. Combined with
the observation-level realization, this gives the independent behavioral profile
(Kuhn's theorem for the mixed → behavioral direction). -/
theorem mediator_product_of_product
    (hPSAR : PerStepActionRecall O) (μ : ∀ i, PMF (O.LocalStrategy i))
    (n : Nat) (ss : List σ)
    {π₀ : PureProfile O}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0) :
    ∃ τ : ∀ i, PMF (Act i (O.lastObs i (O.projectStates i ss))),
      O.mixedToMediator (pmfPi μ) n ss = pmfPi τ := by
  set ν := pmfPi μ with hν_def
  set w : PureProfile O → ENNReal :=
    fun π => pureRun (O.pureStep) O.init n π ss
  set wᵢ : ∀ i, (O.LocalStrategy i) → ENNReal :=
    fun i πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss
  -- Reduce to: reweightPMF ν w is a product PMF
  -- The mediator is a pushforward of (reweightPMF ν w) through the coordwise map
  -- fun π i => π i (projectStates i ss), and pushforward of product
  -- = product (pmfPi_push_coordwise)
  suffices hprod : ∃ ρ : ∀ i, PMF (O.LocalStrategy i),
      reweightPMF ν w = pmfPi ρ by
    obtain ⟨ρ, hρ⟩ := hprod
    exact ⟨fun i => Math.PMFProduct.pushforward (ρ i) (fun πᵢ => πᵢ (O.projectStates i ss)), by
      unfold mixedToMediator; rw [hρ]
      simp only [jointActionDist, pureToBehavioral]
      conv_lhs => arg 2; ext π; rw [pmfPi_pure]
      exact pmfPi_push_coordwise ρ (fun i πᵢ => πᵢ (O.projectStates i ss))⟩
  -- Case split on mass condition for reweightPMF
  by_cases hmass : (∑ π, ν π * w π) = 0 ∨ (∑ π, ν π * w π) = ⊤
  · -- Degenerate: reweightPMF falls back to ν = pmfPi μ
    exact ⟨μ, by rw [reweightPMF_degenerate _ _ hmass, hν_def]⟩
  · -- Non-degenerate: use cross-multiplication to factor the reweighted PMF
    push_neg at hmass; obtain ⟨hCw0, hCwt⟩ := hmass
    -- Extract a witness with nonzero mass
    have ⟨π_w, hπw⟩ : ∃ π, ν π * w π ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hCw0 (Finset.sum_eq_zero fun a _ => hall a)
    have hν_ne : ν π_w ≠ 0 := left_ne_zero_of_mul hπw
    have hw_ne : w π_w ≠ 0 := right_ne_zero_of_mul hπw
    -- Per-player non-degeneracy from the witness
    have hμ_ne : ∀ i, μ i (π_w i) ≠ 0 := by
      intro i hi; apply hν_ne
      rw [hν_def, pmfPi_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have hwi_ne : ∀ i, wᵢ i (π_w i) ≠ 0 := by
      intro i; exact ((pureRun_nonzero_iff_update hPSAR n h₀ π_w).mp hw_ne) i
    have hCwi0 : ∀ i, ∑ a, μ i a * wᵢ i a ≠ 0 := fun i => by
      apply ne_of_gt
      exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero (hμ_ne i) (hwi_ne i)))
        (Finset.single_le_sum (f := fun a => μ i a * wᵢ i a)
          (fun _ _ => zero_le _) (Finset.mem_univ (π_w i)))
    have hCwit : ∀ i, ∑ a, μ i a * wᵢ i a ≠ ⊤ := fun i =>
      sum_mul_pmf_ne_top (μ i) _ fun a => PMF.coe_le_one _ ss
    -- Non-degeneracy for the product weight ∏ wᵢ
    have hsum_eq : ∑ π, ν π * ∏ i, wᵢ i (π i) = ∏ i, ∑ a, μ i a * wᵢ i a := by
      rw [hν_def]; conv_lhs => arg 2; ext π; rw [pmfPi_apply, ← Finset.prod_mul_distrib]
      exact (Fintype.prod_sum (fun i a => μ i a * wᵢ i a)).symm
    have hCprod0 : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ 0 := by
      rw [hsum_eq]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hCwi0 i)
    have hCprodt : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ ⊤ := by
      rw [hsum_eq]
      exact ne_of_lt (ENNReal.prod_lt_top (fun i _ => (hCwit i).lt_top))
    -- Cross-multiplication identity → reweightPMF w = reweightPMF ∏ wᵢ
    have hreweight : reweightPMF ν w = reweightPMF ν (fun π => ∏ i, wᵢ i (π i)) :=
      reweightPMF_eq_of_cross_mul ν w (fun π => ∏ i, wᵢ i (π i))
        hCw0 hCwt hCprod0 hCprodt (pureRun_cross_mul_product hPSAR ν n h₀)
    -- Factor the product-weighted reweightPMF via reweightPMF_pmfPi
    exact ⟨fun i => reweightPMF (μ i) (wᵢ i), by
      rw [hreweight, hν_def]; exact reweightPMF_pmfPi μ wᵢ hCwi0 hCwit⟩

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

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.LocalTrace i)]

open Math.PMFProduct

open Classical in
/-- **Product in → product out**: Under PSAR, if the ex ante distribution
is a product `ν = pmfPi μ`, then conditioning on reaching any reachable
trace `ss` gives a product at the strategy level:

  `reweightPMF (pmfPi μ) w = pmfPi (reweightPMF μᵢ wᵢ)`

Each player's conditional strategy `reweightPMF (μ i) wᵢ` depends only
on their own per-player reach weight. Pushing forward through the action
map gives the action-level product (`mediator_product_of_product`).

The mechanism: under PSAR, `pureRun_cross_mul_product` shows the reach
weight is cross-multiplicatively equivalent to `∏ᵢ wᵢ(πᵢ)`, and
`reweightPMF_pmfPi` factors reweighting by a product weight. -/
theorem conditioning_preserves_product
    (hPSAR : PerStepActionRecall O) (μ : ∀ i, PMF (O.LocalStrategy i))
    (n : Nat) {ss : List σ}
    {π₀ : PureProfile O}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0) :
    ∃ τ : ∀ i, PMF (O.LocalStrategy i),
      reweightPMF (pmfPi μ)
        (fun π => pureRun (O.pureStep) O.init n π ss) =
          pmfPi τ := by
  set ν := pmfPi μ
  set w : PureProfile O → ENNReal :=
    fun π => pureRun (O.pureStep) O.init n π ss
  set wᵢ : ∀ i, (O.LocalStrategy i) → ENNReal :=
    fun i πᵢ => pureRun (O.pureStep) O.init n
      (Function.update π₀ i πᵢ) ss
  -- Mass conditions
  by_cases hmass : (∑ π, ν π * w π) = 0 ∨ (∑ π, ν π * w π) = ⊤
  · exact ⟨μ, by rw [reweightPMF_degenerate _ _ hmass]⟩
  · push_neg at hmass; obtain ⟨hCw0, hCwt⟩ := hmass
    -- Witness with nonzero mass
    have ⟨π_w, hπw⟩ : ∃ π, ν π * w π ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hCw0 (Finset.sum_eq_zero fun a _ => hall a)
    have hν_ne : ν π_w ≠ 0 := left_ne_zero_of_mul hπw
    have hw_ne : w π_w ≠ 0 := right_ne_zero_of_mul hπw
    -- Per-player non-degeneracy
    have hμ_ne : ∀ i, μ i (π_w i) ≠ 0 := by
      intro i hi; apply hν_ne
      rw [pmfPi_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have hwi_ne : ∀ i, wᵢ i (π_w i) ≠ 0 := by
      intro i
      exact ((pureRun_nonzero_iff_update hPSAR n h₀ π_w).mp hw_ne) i
    have hCwi0 : ∀ i, ∑ a, μ i a * wᵢ i a ≠ 0 := fun i => by
      apply ne_of_gt
      exact lt_of_lt_of_le
        (pos_iff_ne_zero.mpr (mul_ne_zero (hμ_ne i) (hwi_ne i)))
        (Finset.single_le_sum (f := fun a => μ i a * wᵢ i a)
          (fun _ _ => zero_le _) (Finset.mem_univ (π_w i)))
    have hCwit : ∀ i, ∑ a, μ i a * wᵢ i a ≠ ⊤ := fun i =>
      sum_mul_pmf_ne_top (μ i) _ fun a => PMF.coe_le_one _ ss
    -- Product weight sum factorization
    have hsum_eq : ∑ π, ν π * ∏ i, wᵢ i (π i) =
        ∏ i, ∑ a, μ i a * wᵢ i a := by
      conv_lhs => arg 2; ext π; rw [pmfPi_apply, ← Finset.prod_mul_distrib]
      exact (Fintype.prod_sum (fun i a => μ i a * wᵢ i a)).symm
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
        (pureRun_cross_mul_product hPSAR ν n h₀)
    -- Step 2: product weight on product dist = product of per-player
    exact ⟨fun i => reweightPMF (μ i) (wᵢ i), by
      rw [hreweight]; exact reweightPMF_pmfPi μ wᵢ hCwi0 hCwit⟩

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

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

open Classical in
/-- Generic obs-locality of `pureRun (update π₀ i πᵢ)`, parameterized by a
step-level hypothesis `hStep` that says: given obs-equal prefixes and obs-equal
endpoints with nonzero steps, `π₀ i` and `π₀' i` agree on their respective
projections.

All concrete variants (`pureRun_update_obs_local`, `_pspr`, `_player`) are
one-line corollaries that supply the appropriate `hStep`. -/
theorem pureRun_update_obs_local_of
    (hPSAR : PerStepActionRecall O) (n : Nat)
    (i : ι) {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List σ}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (O.pureStep) O.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (O.pureStep) O.init n π₀' ss₂ ≠ 0)
    (hStep : ∀ (m : Nat) (p₁ p₂ : List σ) (t₁ t₂ : σ)
      (hobs_p : O.projectStates i p₁ = O.projectStates i p₂),
      O.obsEq i t₁ t₂ →
      pureRun (O.pureStep) O.init m π₀ p₁ ≠ 0 →
      pureRun (O.pureStep) O.init m π₀' p₂ ≠ 0 →
      O.pureStep π₀ p₁ t₁ ≠ 0 → O.pureStep π₀' p₂ t₂ ≠ 0 →
      π₀ i (O.projectStates i p₁) = hobs_p ▸ π₀' i (O.projectStates i p₂))
    (πᵢ : O.LocalStrategy i) :
    pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
    pureRun (O.pureStep) O.init n (Function.update π₀' i πᵢ) ss₂ ≠ 0 := by
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
    rw [pureRun_succ_nonzero_iff hPSAR m h₁,
        pureRun_succ_nonzero_iff hPSAR m h₂]
    have hforced := hStep m p₁ p₂ t₁ t₂ hobs_p hobst hp₁ hp₂ ht₁ ht₂
    -- hforced : π₀ i (ps i p₁) = hobs_p ▸ π₀' i (ps i p₂)
    have hact_transfer :
        (∀ j, Function.update π₀ i πᵢ j (O.projectStates j p₁) =
          π₀ j (O.projectStates j p₁)) ↔
        (∀ j, Function.update π₀' i πᵢ j (O.projectStates j p₂) =
          π₀' j (O.projectStates j p₂)) := by
      constructor <;> intro h
      · intro j; by_cases hij : j = i
        · rw [hij, Function.update_self]
          have h_i := h i; rw [Function.update_self] at h_i
          exact eq_of_heq ((congr_arg_heq πᵢ hobs_p).symm.trans
            (heq_of_eq h_i |>.trans (heq_of_eq hforced |>.trans
              (subst_heq' (P := fun v => Act i (O.lastObs i v))
                hobs_p (π₀' i (O.projectStates i p₂))))))
        · rw [Function.update_of_ne hij]
      · intro j; by_cases hij : j = i
        · rw [hij, Function.update_self]
          have h_i := h i; rw [Function.update_self] at h_i
          -- h_i : πᵢ(p₂) = π₀'(p₂). Want: πᵢ(p₁) = π₀(p₁)
          -- Chain: πᵢ(p₁) ≅ πᵢ(p₂) = π₀'(p₂) ≅ hobs_p▸π₀'(p₂) = π₀(p₁)
          exact eq_of_heq ((congr_arg_heq πᵢ hobs_p).trans
            (heq_of_eq h_i |>.trans
              ((subst_heq' (P := fun v => Act i (O.lastObs i v))
                hobs_p (π₀' i (O.projectStates i p₂))).symm |>.trans
              (heq_of_eq hforced).symm)))
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
    (hPSAR : PerStepActionRecall O) (n : Nat)
    (i : ι) {π₀ : PureProfile O} {ss₁ ss₂ : List σ}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (O.pureStep) O.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (O.pureStep) O.init n π₀ ss₂ ≠ 0)
    (πᵢ : O.LocalStrategy i) :
    pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
    pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₂ ≠ 0 :=
  pureRun_update_obs_local_of hPSAR n i hobs_i h₁ h₂
    (fun _ _ _ _ _ hobs_p _ _ _ _ _ => dep_congr_subst (π₀ i) hobs_p) πᵢ

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
    (hPSAR : PerStepActionRecall O) (n : Nat)
    (i : ι) (b_i : PMF (O.LocalStrategy i))
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List σ}
    (h₁ : pureRun (O.pureStep) O.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (O.pureStep) O.init n π₀' ss₂ ≠ 0)
    (hiff : ∀ πᵢ,
      pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
      pureRun (O.pureStep) O.init n (Function.update π₀' i πᵢ) ss₂ ≠ 0) :
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁) =
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀' i πᵢ) ss₂) := by
  set w₁ := fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁
  set w₂ := fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀' i πᵢ) ss₂
  have hsum_zero_iff : (∑ πᵢ, b_i πᵢ * w₁ πᵢ) = 0 ↔ (∑ πᵢ, b_i πᵢ * w₂ πᵢ) = 0 := by
    simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies, mul_eq_zero]
    constructor
    · intro h πᵢ; rcases h πᵢ with h | h
      · exact Or.inl h
      · exact Or.inr (of_not_not (mt (hiff πᵢ).mpr (not_not.mpr h)))
    · intro h πᵢ; rcases h πᵢ with h | h
      · exact Or.inl h
      · exact Or.inr (of_not_not (mt (hiff πᵢ).mp (not_not.mpr h)))
  have htop₁ : (∑ πᵢ, b_i πᵢ * w₁ πᵢ) ≠ ⊤ :=
    sum_mul_pmf_ne_top b_i _ fun πᵢ => PMF.coe_le_one _ ss₁
  have htop₂ : (∑ πᵢ, b_i πᵢ * w₂ πᵢ) ≠ ⊤ :=
    sum_mul_pmf_ne_top b_i _ fun πᵢ => PMF.coe_le_one _ ss₂
  by_cases hC₁ : (∑ πᵢ, b_i πᵢ * w₁ πᵢ) = 0
  · rw [reweightPMF_fallback _ _ hC₁, reweightPMF_fallback _ _ (hsum_zero_iff.mp hC₁)]
  · have hC₂ : (∑ πᵢ, b_i πᵢ * w₂ πᵢ) ≠ 0 := mt hsum_zero_iff.mpr hC₁
    exact reweightPMF_eq_of_cross_mul b_i w₁ w₂ hC₁ htop₁ hC₂ htop₂ (fun πᵢ => by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro πᵢ' _
      by_cases hw : w₁ πᵢ = 0
      · have hw2 : w₂ πᵢ = 0 := of_not_not (mt (hiff πᵢ).mpr (not_not.mpr hw))
        simp [hw, hw2]
      · by_cases hw' : w₁ πᵢ' = 0
        · have hw2' : w₂ πᵢ' = 0 := of_not_not (mt (hiff πᵢ').mpr (not_not.mpr hw'))
          simp [hw', hw2']
        · have eq1 : w₁ πᵢ = pureRun (O.pureStep) O.init n π₀ ss₁ :=
            pureRun_const_of_psar hPSAR n hw h₁
          have eq2 : w₂ πᵢ = pureRun (O.pureStep) O.init n π₀' ss₂ :=
            pureRun_const_of_psar hPSAR n ((hiff πᵢ).mp hw) h₂
          have eq3 : w₁ πᵢ' = pureRun (O.pureStep) O.init n π₀ ss₁ :=
            pureRun_const_of_psar hPSAR n hw' h₁
          have eq4 : w₂ πᵢ' = pureRun (O.pureStep) O.init n π₀' ss₂ :=
            pureRun_const_of_psar hPSAR n ((hiff πᵢ').mp hw') h₂
          rw [eq1, eq2, eq3, eq4]; ring)

set_option linter.unusedFintypeInType false in
open Classical in
/-- Under PSAR, the per-player reweighted PMF depends on `ss` only through
`projectStates i ss`. Corollary of `reweightPMF_update_obs_local_of`. -/
theorem reweightPMF_update_obs_local
    [∀ i, Fintype (O.LocalTrace i)]
    (hPSAR : PerStepActionRecall O) (n : Nat)
    (i : ι) (b_i : PMF (O.LocalStrategy i))
    {π₀ : PureProfile O} {ss₁ ss₂ : List σ}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (O.pureStep) O.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (O.pureStep) O.init n π₀ ss₂ ≠ 0) :
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁) =
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₂) :=
  reweightPMF_update_obs_local_of hPSAR n i b_i h₁ h₂
    fun πᵢ => pureRun_update_obs_local hPSAR n i hobs_i h₁ h₂ πᵢ

open Classical in
/-- Under PSPR, obs-locality with **different** reference profiles.
Corollary of `pureRun_update_obs_local_of` with `hStep` from `pureStep_component_eq_of_pspr`. -/
theorem pureRun_update_obs_local_pspr
    (hPSPR : PerStepPlayerRecall O) (n : Nat)
    (i : ι) {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List σ}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (O.pureStep) O.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (O.pureStep) O.init n π₀' ss₂ ≠ 0)
    (πᵢ : O.LocalStrategy i) :
    pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
    pureRun (O.pureStep) O.init n (Function.update π₀' i πᵢ) ss₂ ≠ 0 :=
  pureRun_update_obs_local_of (hPSPR.toAction) n i hobs_i h₁ h₂
    (fun _ _ _ _ _ hobs_p hobst _ _ ht₁ ht₂ =>
      pureStep_component_eq_of_pspr hPSPR i hobs_p hobst ht₁ ht₂) πᵢ

set_option linter.unusedFintypeInType false in
open Classical in
/-- Under PSPR, obs-locality with **different** reference profiles.
Corollary of `reweightPMF_update_obs_local_of` with `hiff` from
`pureRun_update_obs_local_pspr`. -/
theorem reweightPMF_update_obs_local_pspr
    [∀ i, Fintype (O.LocalTrace i)]
    (hPSPR : PerStepPlayerRecall O) (n : Nat)
    (i : ι) (b_i : PMF (O.LocalStrategy i))
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List σ}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (O.pureStep) O.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (O.pureStep) O.init n π₀' ss₂ ≠ 0) :
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁) =
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀' i πᵢ) ss₂) :=
  reweightPMF_update_obs_local_of (hPSPR.toAction) n i b_i h₁ h₂
    fun πᵢ => pureRun_update_obs_local_pspr hPSPR n i hobs_i h₁ h₂ πᵢ

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

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

open Classical in
/-- Under PSAR + `PlayerStepRecall O i`, obs-locality with **different** reference profiles.
Corollary of `pureRun_update_obs_local_of` with `hStep` from
`pureStep_component_eq_of_playerRecall`. -/
theorem pureRun_update_obs_local_player
    (hPSAR : PerStepActionRecall O) (i : ι) (hPSR_i : PlayerStepRecall O i)
    (n : Nat)
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List σ}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (O.pureStep) O.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (O.pureStep) O.init n π₀' ss₂ ≠ 0)
    (πᵢ : O.LocalStrategy i) :
    pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
    pureRun (O.pureStep) O.init n (Function.update π₀' i πᵢ) ss₂ ≠ 0 :=
  pureRun_update_obs_local_of hPSAR n i hobs_i h₁ h₂
    (fun _ _ _ _ _ hobs_p hobst _ _ ht₁ ht₂ =>
      pureStep_component_eq_of_playerRecall i hPSR_i hobs_p hobst ht₁ ht₂) πᵢ

set_option linter.unusedFintypeInType false in
open Classical in
/-- Under PSAR + `PlayerStepRecall O i`, obs-locality with different reference profiles.
Corollary of `reweightPMF_update_obs_local_of` with `hiff` from
`pureRun_update_obs_local_player`. -/
theorem reweightPMF_update_obs_local_player
    [∀ i, Fintype (O.LocalTrace i)]
    (hPSAR : PerStepActionRecall O) (i : ι) (hPSR_i : PlayerStepRecall O i)
    (n : Nat)
    (b_i : PMF (O.LocalStrategy i))
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List σ}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (O.pureStep) O.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (O.pureStep) O.init n π₀' ss₂ ≠ 0) :
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n
        (Function.update π₀ i πᵢ) ss₁) =
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n
        (Function.update π₀' i πᵢ) ss₂) :=
  reweightPMF_update_obs_local_of hPSAR n i b_i h₁ h₂
    fun πᵢ => pureRun_update_obs_local_player hPSAR i hPSR_i n hobs_i h₁ h₂ πᵢ

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

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

open Math.PMFProduct

/-- If a correlated behavioral profile factors as `pmfPi (fun i => β i (v i))`
at every observation tuple `v`, then its step distribution equals that of the
independent behavioral profile `β`. -/
theorem stepDistCorr_eq_stepDist_of_product
    (β : BehavioralProfile O) (bc : BehavioralProfileCorr O)
    (hprod : ∀ v, bc v = pmfPi (fun i => β i (v i)))
    (ss : List σ) :
    O.stepDistCorr bc ss = O.stepDist β ss := by
  simp only [ObsModel.stepDistCorr, ObsModel.stepDist, jointActionDist, hprod]
  rfl

/-- Independent behavioral realization from correlated one: if a correlated profile
always outputs products with observation-local factors, the independent profile
produces the same trace distribution. -/
theorem runDist_eq_of_corrProduct
    (β : BehavioralProfile O) (bc : BehavioralProfileCorr O)
    (hprod : ∀ v, bc v = pmfPi (fun i => β i (v i)))
    (k : Nat) :
    O.runDist k β =
      seqRun (fun _ ss => O.stepDistCorr bc ss) O.init k := by
  -- runDist D k β is definitionally seqRun (fun _ ss => O.stepDist β ss) O.init k
  change seqRun (fun _ ss => O.stepDist β ss) O.init k =
       seqRun (fun _ ss => O.stepDistCorr bc ss) O.init k
  congr 1
  funext _ ss
  exact (stepDistCorr_eq_stepDist_of_product β bc hprod ss).symm

end Decentralization

/-! ## Generalized Kuhn (M→B) under PSPR

The full mixed-to-behavioral direction of Kuhn's theorem under
`PerStepPlayerRecall`. Given a product distribution `ν = pmfPi μ` over
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

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.LocalTrace i)]

open Math.PMFProduct

set_option linter.unusedFintypeInType false in
open Classical in
/-- Non-existential version of `mediator_product_of_product`:
the mediator output equals the product of per-player factors. -/
private theorem mixedToMediator_eq_pmfPi_factor
    (hPSAR : PerStepActionRecall O) (μ : ∀ i, PMF (O.LocalStrategy i))
    (n : Nat) (ss : List σ) {π₀ : PureProfile O}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0)
    (hν₀ : (pmfPi μ) π₀ ≠ 0) :
    O.mixedToMediator (pmfPi μ) n ss = pmfPi (fun i =>
      Math.PMFProduct.pushforward
        (reweightPMF (μ i)
          (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss))
        (fun πᵢ => πᵢ (O.projectStates i ss))) := by
  set ν := pmfPi μ with hν_def
  set w := fun π => pureRun (O.pureStep) O.init n π ss
  set wᵢ := fun i (πᵢ : O.LocalStrategy i) =>
    pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss
  suffices hprod : reweightPMF ν w = pmfPi (fun i => reweightPMF (μ i) (wᵢ i)) by
    unfold mixedToMediator; rw [hprod]
    simp only [jointActionDist, pureToBehavioral]
    conv_lhs => arg 2; ext π; rw [pmfPi_pure]
    exact pmfPi_push_coordwise _ (fun i (πᵢ : O.LocalStrategy i) =>
      πᵢ (O.projectStates i ss))
  -- Non-degeneracy setup
  have hμ_ne : ∀ i, μ i (π₀ i) ≠ 0 := by
    intro i hi; apply hν₀; rw [hν_def, pmfPi_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hwi_ne : ∀ i, wᵢ i (π₀ i) ≠ 0 :=
    fun i => ((pureRun_nonzero_iff_update hPSAR n h₀ π₀).mp h₀) i
  have hCwi0 : ∀ i, ∑ a, μ i a * wᵢ i a ≠ 0 := fun i => by
    apply ne_of_gt
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero (hμ_ne i) (hwi_ne i)))
      (Finset.single_le_sum (f := fun a => μ i a * wᵢ i a)
        (fun _ _ => zero_le _) (Finset.mem_univ (π₀ i)))
  have hCwit : ∀ i, ∑ a, μ i a * wᵢ i a ≠ ⊤ := fun i =>
    sum_mul_pmf_ne_top (μ i) _ fun a => PMF.coe_le_one _ ss
  have hCw0 : ∑ π, ν π * w π ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero hν₀ h₀))
      (Finset.single_le_sum (f := fun π => ν π * w π)
        (fun _ _ => zero_le _) (Finset.mem_univ π₀))
  have hCwt : ∑ π, ν π * w π ≠ ⊤ :=
    sum_mul_pmf_ne_top ν _ fun π => PMF.coe_le_one _ ss
  have hsum_eq : ∑ π, ν π * ∏ i, wᵢ i (π i) = ∏ i, ∑ a, μ i a * wᵢ i a := by
    rw [hν_def]; conv_lhs => arg 2; ext π; rw [pmfPi_apply, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i a => μ i a * wᵢ i a)).symm
  have hCprod0 : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ 0 := by
    rw [hsum_eq]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hCwi0 i)
  have hCprodt : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ ⊤ := by
    rw [hsum_eq]; exact ne_of_lt (ENNReal.prod_lt_top (fun i _ => (hCwit i).lt_top))
  rw [reweightPMF_eq_of_cross_mul ν w (fun π => ∏ i, wᵢ i (π i))
      hCw0 hCwt hCprod0 hCprodt (pureRun_cross_mul_product hPSAR ν n h₀),
    hν_def]
  exact reweightPMF_pmfPi μ wᵢ hCwi0 hCwit

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

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- **Semantic condition**: Whether a continuation strategy `πᵢ` for player `i` is feasible
(has nonzero probability of reaching a given trace) depends only on player `i`'s observation
of that trace, not on the full state trace.

This is the semantic content of what `PlayerStepRecall O i` provides in the Kuhn proof.
Unlike `PlayerStepRecall`, this condition depends on the dynamics `D`. -/
def ObsLocalFeasibility (i : ι) : Prop :=
  ∀ (n : Nat) (π₀ π₀' : PureProfile O) (ss₁ ss₂ : List σ),
    O.projectStates i ss₁ = O.projectStates i ss₂ →
    pureRun (O.pureStep) O.init n π₀ ss₁ ≠ 0 →
    pureRun (O.pureStep) O.init n π₀' ss₂ ≠ 0 →
    ∀ (πᵢ : O.LocalStrategy i),
      pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
      pureRun (O.pureStep) O.init n (Function.update π₀' i πᵢ) ss₂ ≠ 0

/-- **Semantic condition**: At any reachable transition `(s, a, t)`, the joint action `a`
is uniquely determined by the source-target pair `(s, t)`.

This is the semantic content of what `PerStepActionRecall` provides: at reachable
transitions with the same obs-equivalence classes, the action must be the same.
Since `StepActionDeterminism` applies to the *same* states (reflexive obs-equivalence),
it is strictly weaker than PSAR. -/
def StepActionDeterminism (O : ObsModel ι σ Obs Act) : Prop :=
  ∀ (s t : σ) (a a' : O.JointActionAt s),
    (O.step s a) t ≠ 0 → (O.step s a') t ≠ 0 → a = a'

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] in
/-- PSAR implies step action determinism.
PSAR with reflexive obs-equivalence (same source, same target) gives action uniqueness. -/
theorem PerStepActionRecall.toStepActionDeterminism
    (hPSAR : PerStepActionRecall O) :
    O.StepActionDeterminism :=
  fun s t a a' h1 h2 => funext fun i =>
    (hPSAR s s t t a a' h1 h2 (fun _ => rfl) (fun _ => rfl) i)

open Classical in
/-- **Syntactic → Semantic**: PSAR + `PlayerStepRecall O i` implies `ObsLocalFeasibility D i`
for any dynamics `D`.

This is exactly `pureRun_update_obs_local_player`, restated as an implication between
named conditions. -/
theorem obsLocalFeasibility_of_playerStepRecall
    (hPSAR : PerStepActionRecall O) (i : ι) (hPSR_i : PlayerStepRecall O i)
    : O.ObsLocalFeasibility i :=
  fun n _ _ _ _ hobs h₁ h₂ πᵢ =>
    pureRun_update_obs_local_player hPSAR i hPSR_i n hobs h₁ h₂ πᵢ

/-- Under `PerStepPlayerRecall` (= ∀ i, PlayerStepRecall O i), obs-local feasibility
holds for every player and any dynamics. -/
theorem obsLocalFeasibility_of_pspr
    (hPSPR : PerStepPlayerRecall O) (i : ι) :
    O.ObsLocalFeasibility i :=
  obsLocalFeasibility_of_playerStepRecall
    hPSPR.toAction i (perStepPlayerRecall_iff_forall.mp hPSPR i)

/-- Per-player step action equality at reachable states: like
`pureStep_component_eq_of_playerRecall` but using the weaker
`ReachablePlayerStepRecall` with explicit step-reachability witnesses. -/
theorem pureStep_component_eq_of_reachablePlayerRecall
    (i : ι) (hRPSR_i : O.ReachablePlayerStepRecall i)
    {π π' : PureProfile O} {ss ss' : List σ} {t t' : σ}
    (hobs_i : O.projectStates i ss = O.projectStates i ss')
    (hobst_i : O.obsEq i t t')
    (h1 : O.pureStep π ss t ≠ 0) (h2 : O.pureStep π' ss' t' ≠ 0)
    (hreach_s : O.StepReachable (O.lastState ss))
    (hreach_s' : O.StepReachable (O.lastState ss')) :
    π i (O.projectStates i ss) = hobs_i ▸ π' i (O.projectStates i ss') := by
  rw [pureStep_eq] at h1 h2
  have hpspr := hRPSR_i _ _ _ _ _ _
    h1 h2 (O.obsEq_of_projectStates_getLast i hobs_i) hobst_i hreach_s hreach_s'
  apply eq_of_heq
  exact (fwd_subst_heq _ (π i _)).trans
    ((fwd_subst_heq _ (O.lastObs_projectStates i ss ▸ π i _)).trans
      ((heq_of_eq hpspr).trans (fwd_subst_heq _ (π' i _)).symm)) |>.trans
    (subst_heq' (P := fun v => Act i (O.lastObs i v))
      hobs_i (π' i (O.projectStates i ss'))).symm

open Classical in
/-- **Weakest syntactic → semantic**: PSAR + `ReachablePlayerStepRecall O i`
implies `ObsLocalFeasibility D i`. This uses the weakest syntactic condition
that the Kuhn proof actually needs.

The key insight: `pureRun_update_obs_local_player` only invokes
`PlayerStepRecall` at states reached via `pureRun` with nonzero probability,
which are exactly the step-reachable states. -/
theorem obsLocalFeasibility_of_reachablePlayerStepRecall
    (hPSAR : PerStepActionRecall O) (i : ι)
    (hRPSR_i : O.ReachablePlayerStepRecall i)
    : O.ObsLocalFeasibility i :=
  fun n _ _ _ _ hobs h₁ h₂ πᵢ =>
    pureRun_update_obs_local_of hPSAR n i hobs h₁ h₂
      (fun m p₁ p₂ _ _ hobs_p hobst hp₁ hp₂ ht₁ ht₂ =>
        pureStep_component_eq_of_reachablePlayerRecall i hRPSR_i
          hobs_p hobst ht₁ ht₂
          (pureRun_nonzero_last_stepReachable m _ p₁ hp₁)
          (pureRun_nonzero_last_stepReachable m _ p₂ hp₂)) πᵢ

/-- Step-level action equality under `TracePlayerStepRecall`:
at pureStep-supported transitions from traces with equal obs-projections,
the player-i action components agree. -/
theorem pureStep_component_eq_of_tracePlayerRecall
    (i : ι) (hTPSR : O.TracePlayerStepRecall i)
    {π π' : PureProfile O} {ss ss' : List σ} {t t' : σ}
    (hproj : O.projectStates i ss = O.projectStates i ss')
    (hobst : O.obsEq i t t')
    (h1 : O.pureStep π ss t ≠ 0) (h2 : O.pureStep π' ss' t' ≠ 0)
    (hreach : Nonempty (O.ReachActionTrace ss))
    (hreach' : Nonempty (O.ReachActionTrace ss')) :
    π i (O.projectStates i ss) = hproj ▸ π' i (O.projectStates i ss') := by
  rw [pureStep_eq] at h1 h2
  have rat_ne : ∀ {l : List σ}, Nonempty (O.ReachActionTrace l) → l ≠ [] := by
    intro l ⟨r⟩; cases r with
    | init => exact List.cons_ne_nil _ _
    | snoc _ _ _ _ => exact List.concat_ne_nil _ _
  have hlast_eq : ∀ {l : List σ}, l ≠ [] → l.getLast? = some (O.lastState l) := by
    intro l hl; cases hg : l.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hl
    | some s => simp [lastState, hg]
  have hpspr := hTPSR _ _ _ _ _ _ _ _ hreach hreach'
    (hlast_eq (rat_ne hreach)) (hlast_eq (rat_ne hreach')) hproj h1 h2 hobst
    (O.obsEq_of_projectStates_getLast i hproj)
  apply eq_of_heq
  exact (fwd_subst_heq _ (π i _)).trans
    ((fwd_subst_heq _ (O.lastObs_projectStates i ss ▸ π i _)).trans
      ((heq_of_eq hpspr).trans (fwd_subst_heq _ (π' i _)).symm)) |>.trans
    (subst_heq' (P := fun v => Act i (O.lastObs i v))
      hproj (π' i (O.projectStates i ss'))).symm

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
    (hTPSR : O.TracePlayerStepRecall i)
    : O.ObsLocalFeasibility i :=
  fun n _ _ _ _ hobs h₁ h₂ πᵢ =>
    pureRun_update_obs_local_of hPSAR n i hobs h₁ h₂
      (fun m p₁ p₂ _ _ hobs_p hobst hp₁ hp₂ ht₁ ht₂ =>
        pureStep_component_eq_of_tracePlayerRecall i hTPSR
          hobs_p hobst ht₁ ht₂
          (pureRun_nonzero_to_reachActionTrace m _ p₁ hp₁)
          (pureRun_nonzero_to_reachActionTrace m _ p₂ hp₂)) πᵢ

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
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (hPSAR : PerStepActionRecall O) (i : ι)
    (hTPSR : O.TracePlayerStepRecall i)
    (n : Nat)
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List σ}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (O.pureStep) O.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (O.pureStep) O.init n π₀' ss₂ ≠ 0)
    (πᵢ : O.LocalStrategy i) :
    pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
    pureRun (O.pureStep) O.init n (Function.update π₀' i πᵢ) ss₂ ≠ 0 :=
  pureRun_update_obs_local_of hPSAR n i hobs_i h₁ h₂
    (fun m p₁ p₂ _ _ hobs_p hobst hp₁ hp₂ ht₁ ht₂ =>
      pureStep_component_eq_of_tracePlayerRecall i hTPSR
        hobs_p hobst ht₁ ht₂
        (pureRun_nonzero_to_reachActionTrace m _ p₁ hp₁)
        (pureRun_nonzero_to_reachActionTrace m _ p₂ hp₂)) πᵢ

set_option linter.unusedFintypeInType false in
open Classical in
/-- Under PSAR + `TracePlayerStepRecall O i`, `reweightPMF` is obs-local for player `i`. -/
theorem reweightPMF_update_obs_local_trace
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    [∀ i, Fintype (O.LocalTrace i)]
    (hPSAR : PerStepActionRecall O) (i : ι)
    (hTPSR : O.TracePlayerStepRecall i)
    (n : Nat)
    (b_i : PMF (O.LocalStrategy i))
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List σ}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (O.pureStep) O.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (O.pureStep) O.init n π₀' ss₂ ≠ 0) :
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁) =
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀' i πᵢ) ss₂) :=
  reweightPMF_update_obs_local_of hPSAR n i b_i h₁ h₂
    fun πᵢ => pureRun_update_obs_local_trace hPSAR i hTPSR n hobs_i h₁ h₂ πᵢ

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
distribution is a product (`pmfPi μ`), conditioning on reaching any
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

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
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
theorem kuhn_mixed_to_behavioral_trace [∀ i o, Nonempty (Act i o)]
    (hPSAR : PerStepActionRecall O)
    (hTPSR : ∀ i, O.TracePlayerStepRecall i)
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (k : Nat) :
    ∃ β : BehavioralProfile O,
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) := by
  set ν := pmfPi μ with hν_def
  -- Abbreviation for the per-player factor at a specific trace
  let factorAt (i : ι) (n : Nat) (ss : List σ) (π₀ : PureProfile O) :
      PMF (Act i (O.lastObs i (O.projectStates i ss))) :=
    Math.PMFProduct.pushforward
      (reweightPMF (μ i)
        (fun πᵢ => pureRun (O.pureStep) O.init n
          (Function.update π₀ i πᵢ) ss))
      (fun πᵢ => πᵢ (O.projectStates i ss))
  -- Standalone: factorAt is obs-local under PSAR + TracePlayerStepRecall
  have factorAt_obs_local :
      ∀ (i : ι) (n₁ n₂ : Nat) (ss₁ ss₂ : List σ)
        (π₁ π₂ : PureProfile O),
      O.projectStates i ss₁ = O.projectStates i ss₂ →
      pureRun (O.pureStep) O.init n₁ π₁ ss₁ ≠ 0 →
      pureRun (O.pureStep) O.init n₂ π₂ ss₂ ≠ 0 →
      HEq (factorAt i n₁ ss₁ π₁) (factorAt i n₂ ss₂ π₂) := by
    intro i n₁ n₂ ss₁ ss₂ π₁ π₂ hobs h₁ h₂
    have hn : n₁ = n₂ := by
      have := O.projectStates_eq_length i hobs
      have := pureRun_length _ _ _ _ _ h₁
      have := pureRun_length _ _ _ _ _ h₂
      omega
    subst hn
    simp only [factorAt, Math.PMFProduct.pushforward]
    exact pmf_bind_heq'
      (congrArg (fun v => Act i (O.lastObs i v)) hobs)
      _ _
      (reweightPMF_update_obs_local_trace hPSAR i (hTPSR i) n₁ (μ i) hobs h₁ h₂)
      _ _
      (fun πᵢ => congr_arg_heq (fun v => PMF.pure (πᵢ v)) hobs)
  -- Key property: β is well-defined
  let β : BehavioralProfile O := fun i v_i =>
    if h : ∃ (n : Nat) (ss : List σ) (π₀ : PureProfile O),
        O.projectStates i ss = v_i ∧
        pureRun (O.pureStep) O.init n π₀ ss ≠ 0
    then h.choose_spec.choose_spec.choose_spec.1 ▸
      factorAt i h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose
    else PMF.pure (Classical.arbitrary _)
  have β_eq : ∀ (i : ι) (n : Nat) (ss : List σ) (π₀ : PureProfile O),
      pureRun (O.pureStep) O.init n π₀ ss ≠ 0 →
      β i (O.projectStates i ss) = factorAt i n ss π₀ := by
    intro i n ss π₀ hreach
    have hexist : ∃ (n' : Nat) (ss' : List σ) (π₀' : PureProfile O),
        O.projectStates i ss' = O.projectStates i ss ∧
        pureRun (O.pureStep) O.init n' π₀' ss' ≠ 0 :=
      ⟨n, ss, π₀, rfl, hreach⟩
    change (if h : _ then _ else _) = _
    rw [dif_pos hexist]
    have hps := hexist.choose_spec.choose_spec.choose_spec.1
    have hreach' := hexist.choose_spec.choose_spec.choose_spec.2
    exact eq_of_heq ((fwd_subst_heq (P := fun v => PMF (Act i (O.lastObs i v)))
      hps (factorAt i _ _ _)).symm.trans
      (factorAt_obs_local i _ n _ ss _ π₀ hps hreach' hreach))
  refine ⟨β, ?_⟩
  -- Main proof: runDist k β = ν.bind (runDistPure k)
  suffices hfn : ∀ (n : Nat) (ss : List σ),
      (seqRun (condStep ν (O.pureStep) O.init) O.init n) ss ≠ 0 →
      O.stepDist β ss = condStep ν (O.pureStep) O.init n ss by
    have hrun : ∀ m, O.runDist m β = seqRun (condStep ν (O.pureStep) O.init) O.init m := by
      intro m; induction m with
      | zero => simp [ObsModel.runDist, seqRun]
      | succ n ih =>
        change (O.runDist n β).bind
            (fun ss => Math.ProbabilityMassFunction.pushforward
              (O.stepDist β ss) (fun t => ss ++ [t])) =
          (seqRun (condStep ν (O.pureStep) O.init) O.init n).bind
            (fun ss => Math.ProbabilityMassFunction.pushforward
              (condStep ν (O.pureStep) O.init n ss) (fun t => ss ++ [t]))
        rw [ih]; ext y; simp only [PMF.bind_apply]
        apply tsum_congr; intro ss
        by_cases hss : (seqRun (condStep ν (O.pureStep) O.init) O.init n) ss = 0
        · simp [hss]
        · rw [hfn n ss hss]
    change O.runDist k β = ν.bind (pureRun (O.pureStep) O.init k)
    rw [hrun, condRun_eq_mixedRun]
  -- Prove the step function equality at supported traces
  intro n ss hss
  have hreach : ∑ π, ν π * pureRun (O.pureStep) O.init n π ss ≠ 0 := by
    rwa [condRun_eq_mixedRun, PMF.bind_apply, tsum_fintype] at hss
  obtain ⟨π_w, _, hπw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hreach
  have hw_ne : pureRun (O.pureStep) O.init n π_w ss ≠ 0 :=
    right_ne_zero_of_mul hπw
  have hν_ne : ν π_w ≠ 0 := left_ne_zero_of_mul hπw
  suffices haction : O.jointActionDist β ss = O.mixedToMediator ν n ss by
    change O.stepDist β ss = condStep ν (O.pureStep) O.init n ss
    unfold ObsModel.stepDist
    rw [haction, mediator_step_eq_condStep]
  rw [mixedToMediator_eq_pmfPi_factor hPSAR μ n ss hw_ne (hν_def ▸ hν_ne)]
  simp only [jointActionDist]
  congr 1; funext i
  exact β_eq i n ss π_w hw_ne

open Classical in
/-- **Generalized Kuhn (M→B) under PSPR**: For any product distribution over
pure profiles, there exists an independent behavioral profile producing the
same trace distribution.

Corollary of `kuhn_mixed_to_behavioral_trace` via
`PlayerStepRecall → ReachablePlayerStepRecall → TracePlayerStepRecall`. -/
theorem kuhn_mixed_to_behavioral_pspr [∀ i o, Nonempty (Act i o)]
    (hPSPR : PerStepPlayerRecall O) (μ : ∀ i, PMF (O.LocalStrategy i))
    (k : Nat) :
    ∃ β : BehavioralProfile O,
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) :=
  kuhn_mixed_to_behavioral_trace hPSPR.toAction
    (fun i => (perStepPlayerRecall_iff_forall.mp hPSPR i).toTrace) μ k

open Classical in
/-- **Per-player Kuhn M→B**: each player individually needs `PlayerStepRecall`.
Logically equivalent to `kuhn_mixed_to_behavioral_pspr` since
`PSPR ↔ ∀ i, PlayerStepRecall O i` (and PSPR → PSAR).

The conceptual value is that it shows the proof decomposes cleanly per player:
the global PSAR handles the reach structure (derived from the per-player
conditions), while each player's factor obs-locality uses only their own
`PlayerStepRecall`. See `reweightPMF_update_obs_local_player` for the
per-player lemma. -/
theorem kuhn_mixed_to_behavioral_decomposed [∀ i o, Nonempty (Act i o)]
    (hPSR : ∀ i, PlayerStepRecall O i)
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (k : Nat) :
    ∃ β : BehavioralProfile O,
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) :=
  kuhn_mixed_to_behavioral_pspr
    (perStepPlayerRecall_iff_forall.mpr hPSR) μ k

end Hierarchy

end ObsModel
