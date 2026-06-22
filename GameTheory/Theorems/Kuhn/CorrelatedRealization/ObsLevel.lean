/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Theorems.Kuhn.ObsModel
import GameTheory.Theorems.Kuhn.MixedToBehavioralCore

set_option autoImplicit false

namespace ObsModel

open Math.ProbabilityMassFunction Math.ParameterizedChain Math.TraceRun

attribute [local instance] Fintype.ofFinite

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
  letI : Fintype (O.toCore.PureProfile) := by
    simpa [ObsModel.toCore, ObsModelCore.PureProfile, PureProfile,
      ObsModelCore.LocalStrategy, LocalStrategy,
      ObsModelCore.InfoState, InfoState,
      ObsModelCore.currentObs, currentObs] using
      (inferInstance : Fintype (PureProfile O))
  change (O.toCore.mixedToMediator ν n ss).bind
      (fun a => O.toCore.step (O.toCore.lastState ss) (O.toCore.castJointAction ss a)) =
      condStep ν O.toCore.pureStep O.toCore.init n ss
  exact ObsModelCore.mediator_step_eq_condStep (O := O.toCore) ν n ss

/-- **Correlated realization theorem**: for any joint distribution `ν` over
pure profiles, there exists a mediator `m` — producing correlated action
recommendations from the state trace at each step — such that the run under `m`
(with actions converted to state transitions by the step function) yields the same
trace distribution as the `ν`-averaged pure runs.

No perfect recall is needed. -/
theorem correlated_realization [Finite (PureProfile O)]
    (ν : PMF (PureProfile O)) (k : Nat) :
    ∃ m : (n : Nat) → (ss : List σ) →
        PMF (∀ i, Act i (O.currentObs i (O.projectStates i ss))),
      seqRun (fun n ss =>
        (m n ss).bind (fun a =>
          O.step (O.lastState ss) (O.castJointAction ss a)))
        O.init k =
      ν.bind (pureRun O.pureStep O.init k) := by
  letI : Fintype (O.toCore.PureProfile) := by
    simpa [ObsModel.toCore, ObsModelCore.PureProfile, PureProfile,
      ObsModelCore.LocalStrategy, LocalStrategy,
      ObsModelCore.InfoState, InfoState,
      ObsModelCore.currentObs, currentObs] using
      (inferInstance : Fintype (PureProfile O))
  change ∃ m : (n : Nat) → (ss : List σ) →
        PMF (∀ i, Act i (O.toCore.currentObs i (O.toCore.projectStates i ss))),
      seqRun (fun n ss =>
        (m n ss).bind (fun a =>
          O.toCore.step (O.toCore.lastState ss) (O.toCore.castJointAction ss a)))
        O.toCore.init k =
      ν.bind (pureRun O.toCore.pureStep O.toCore.init k)
  exact ObsModelCore.correlated_realization (O := O.toCore) ν k

end

/-! ## Observation-level correlated realization

Under **per-step action recall** (the observation transition determines the
action), the state-trace mediator factors through observations, giving a
`BehavioralProfileCorr O` witness. -/

section ObsLevel

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] in
private theorem pmfPi_heq_of_eq {O : ObsModel ι σ Obs Act}
    [Fintype ι]
    {b : BehavioralProfile O} {v₁ v₂ : ∀ i, O.InfoState i} (h : v₁ = v₂) :
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
        (fun i => O.currentObs_projectStates i ss ▸ π i (O.projectStates i ss)) := by
  change O.toCore.pureStep π ss =
      O.toCore.step (O.toCore.lastState ss)
        (fun i => O.toCore.currentObs_projectStates i ss ▸
          π i (O.toCore.projectStates i ss))
  exact ObsModelCore.pureStep_eq (O := O.toCore) π ss

/-- Under PSAR, if two profiles produce nonzero transition at the same state
trace and target, their step distributions are equal. -/
theorem pureStep_eq_of_nonzero_same
    (hPSAR : PerStepActionRecall O) {π₁ π₂ : PureProfile O} {ss : List σ} {t : σ}
    (h₁ : O.pureStep π₁ ss t ≠ 0) (h₂ : O.pureStep π₂ ss t ≠ 0) :
    O.pureStep π₁ ss = O.pureStep π₂ ss := by
  have hDet : ObsModelCore.StepActionDeterminism O.toCore := by
    intro s t a a' hs hs'
    exact funext fun i => hPSAR s s t t a a' hs hs' (fun _ => rfl) (fun _ => rfl) i
  exact ObsModelCore.pureStep_eq_of_nonzero_same
    (O := O.toCore) hDet h₁ h₂

/-- Under `PerStepActionRecall`, if `pureStep` at obs-equivalent traces gives
nonzero probability to obs-equivalent next states, the cast actions are equal. -/
theorem pureStep_action_eq_of_psar
    (hPSAR : PerStepActionRecall O) {π π' : PureProfile O} {ss ss' : List σ} {t t' : σ}
    (hobs : ∀ i, O.projectStates i ss = O.projectStates i ss')
    (hobst : ∀ i, O.obsEq i t t')
    (h1 : O.pureStep π ss t ≠ 0) (h2 : O.pureStep π' ss' t' ≠ 0)
    (i : ι) :
    (O.obsEq_of_projectStates_getLast i (hobs i)) ▸
      (O.currentObs_projectStates i ss ▸ π i (O.projectStates i ss)) =
      (O.currentObs_projectStates i ss' ▸ π' i (O.projectStates i ss')) := by
  rw [pureStep_eq] at h1 h2
  exact hPSAR _ _ _ _ _ _
    h1 h2
    (fun j => O.obsEq_of_projectStates_getLast j (hobs j)) hobst i

omit [DecidableEq ι] [Fintype ι] [(i : ι) → (o : Obs i) → Fintype (Act i o)] in
/-- Compare two composed transports with the same target. -/
private theorem transport_composed {α : Type} {P : α → Type} {a₁ a₂ b₁ b₂ : α}
    (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (hb : b₁ = b₂)
    (x₁ : P a₁) (x₂ : P a₂) (hx : HEq x₁ x₂) :
    (h₁ ▸ x₁ : P b₁) = (hb ▸ (h₂ ▸ x₂ : P b₂) : P b₁) := by
  subst h₁
  subst h₂
  subst hb
  exact eq_of_heq hx

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
  have hπ : HEq (π i (O.projectStates i ss₁)) (π i (O.projectStates i ss₂)) :=
    congr_arg_heq (fun v => π i v) (hobs i)
  exact transport_composed
    (O.currentObs_projectStates i ss₁) (O.currentObs_projectStates i ss₂)
    (O.obsEq_of_projectStates_getLast i (hobs i))
    _ _ hπ

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
    have := ha_rel i
    rw [this]
    exact rec_heq_of_heq (hobss i).symm HEq.rfl
  have hb_heq : ∀ i, HEq (b₁ i) (b₂ i) := fun i => by
    have := hb_rel i
    rw [this]
    exact rec_heq_of_heq (hobss i).symm HEq.rfl
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
        (((rec_heq_of_heq (hobss i) HEq.rfl).symm).trans
          (heq_of_eq (hpsar i)) |>.trans (hb_heq i).symm))
    have hR : (O.step s₁ b₁) t₁ * (O.step s₂ a₂) t₂ = 0 := by
      by_contra h
      rw [mul_eq_zero, not_or] at h
      have hpsar := fun i => hPSAR s₁ s₂ t₁ t₂ b₁ a₂ h.1 h.2 hobss hobst i
      exact hab (funext fun i => eq_of_heq
        (((rec_heq_of_heq (hobss i) HEq.rfl).symm).trans
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
  apply Math.ProbabilityMassFunction.reweightPMF_eq_of_cross_mul ν _ _ hreach₁ hCtop₁ hreach₂ hCtop₂
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
  unfold ObsModel.mixedToMediator ObsModelCore.mixedToMediator
  exact bind_heq_of_eq
    (congrArg (fun f => ∀ i, Act i (O.currentObs i (f i))) (funext hobs))
    _ _
    (by
      simpa [ObsModel.pureStep, ObsModel.init, ObsModel.toCore] using
        (reweightPMF_pureRun_obs_invariant hPSAR ν n ss₁ ss₂ hobs hreach₁ hreach₂))
    _ _
    (fun π => jointActionDist_obs_heq (O.pureToBehavioral π) ss₁ ss₂ hobs)

end ObsLevel

section ObsCorrelatedRealization

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Finite (O.InfoState i)]

open Classical in
/-- **Observation-level correlated realization**: under `PerStepActionRecall`,
a `BehavioralProfileCorr O` (observation-level mediator) produces the same
trace distribution as any mixed strategy `ν`. -/
theorem obs_correlated_realization [Inhabited ι] [∀ i o, Nonempty (Act i o)]
    [Finite (PureProfile O)]
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
    · exact rec_heq_of_heq
        (C := fun f => PMF ((i : ι) → Act i (O.currentObs i (f i))))
        (x := O.mixedToMediator ν (ss'.length - 1) ss')
        (y := O.mixedToMediator ν (ss'.length - 1) ss')
        (funext hobs') HEq.rfl
    · exact hmed_heq
  -- 4. stepDistCorr bc ss = condStep ... n ss
  calc O.stepDistCorr bc ss
      = (bc (fun i => O.projectStates i ss)).bind
          (fun a => O.step (O.lastState ss)
            (fun i => O.currentObs_projectStates i ss ▸ a i)) := rfl
    _ = (O.mixedToMediator ν n ss).bind
          (fun a => O.step (O.lastState ss)
            (fun i => O.currentObs_projectStates i ss ▸ a i)) := by
        rw [hbc]
    _ = condStep ν (O.pureStep) O.init n ss :=
        mediator_step_eq_condStep ν n ss

end ObsCorrelatedRealization

end ObsModel
