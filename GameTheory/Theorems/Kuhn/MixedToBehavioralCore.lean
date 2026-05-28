/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Theorems.Kuhn.KuhnModel
import Math.PMFProduct

/-! # Mixed-to-behavioral realization on `KuhnModel`

Semantic core of Kuhn's mixed-to-behavioral direction.

This file contains the `ObsModelCore`/`KuhnModel` part of the development:
- correlated realization for arbitrary mixed plan distributions
- semantic step mass/support conditions
- semantic locality conditions (`ObsLocalFeasibility`, `ActionPosteriorLocal`)
- the core theorem `ObsModelCore.kuhn_mixed_to_behavioral_semantic`

The stronger `ObsModel` layer and syntactic recall corollaries live in
`CorrelatedRealization.lean`.
-/

set_option autoImplicit false

namespace ObsModelCore

open Math.PMFProduct Math.ProbabilityMassFunction Math.ParameterizedChain Math.TraceRun

attribute [local instance] Fintype.ofFinite

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}
variable {O : ObsModelCore ι σ Obs Act}

/-- Forward `▸`-transport is HEq to the original value. -/
private theorem fwd_subst_heq {α : Type} {P : α → Type} {a b : α}
    (h : a = b) (x : P a) : HEq x (h ▸ x : P b) := by
  subst h
  rfl

/-- `PMF.bind` is HEq-compatible when binding functions are pointwise HEq. -/
private theorem pmf_bind_heq {α β₁ β₂ : Type} (hβ : β₁ = β₂)
    (p : PMF α) (f₁ : α → PMF β₁) (f₂ : α → PMF β₂)
    (hf : ∀ a, HEq (f₁ a) (f₂ a)) :
    HEq (p.bind f₁) (p.bind f₂) := by
  subst hβ
  exact heq_of_eq (congrArg p.bind (funext fun a => eq_of_heq (hf a)))

/-- `PMF.bind` HEq when both base measure and binding function change. -/
private theorem pmf_bind_heq' {α β₁ β₂ : Type} (hβ : β₁ = β₂)
    (p₁ p₂ : PMF α) (hp : p₁ = p₂) (f₁ : α → PMF β₁) (f₂ : α → PMF β₂)
    (hf : ∀ a, HEq (f₁ a) (f₂ a)) :
    HEq (p₁.bind f₁) (p₂.bind f₂) := by
  subst hp
  exact pmf_bind_heq hβ p₁ f₁ f₂ hf

/-- When `d` is a PMF and `w x ≤ 1` for all `x`, the sum `∑ x, d x * w x` is
not `⊤`. -/
theorem sum_mul_pmf_ne_top {α : Type*} [Fintype α] (d : PMF α) (w : α → ENNReal)
    (hw : ∀ a, w a ≤ 1) : ∑ a, d a * w a ≠ ⊤ :=
  ne_of_lt (calc
    ∑ a, d a * w a ≤ ∑ a, d a := by
      refine Finset.sum_le_sum ?_
      intro a _
      exact mul_le_of_le_one_right zero_le (hw a)
    _ = 1 := by
      have := PMF.tsum_coe d
      rwa [tsum_fintype] at this
    _ < ⊤ := ENNReal.one_lt_top)

section

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- The mediator's action recommendations composed with step equal
the `condStep` from `ParameterizedChain` (monad associativity). -/
  theorem mediator_step_eq_condStep [Fintype (ObsModelCore.PureProfile O)]
    (ν : PMF (ObsModelCore.PureProfile O)) (n : Nat) (ss : List σ) :
    (O.mixedToMediator ν n ss).bind
      (fun a => O.step (O.lastState ss) (O.castJointAction ss a)) =
      condStep ν O.pureStep O.init n ss := by
  unfold ObsModelCore.mixedToMediator condStep ObsModelCore.pureStep
    ObsModelCore.stepDist ObsModelCore.castJointAction
  rw [PMF.bind_bind]

/-- Core correlated realization theorem, stated on the information-state core. -/
theorem correlated_realization [Finite (ObsModelCore.PureProfile O)]
    (ν : PMF (ObsModelCore.PureProfile O)) (k : Nat) :
    ∃ m : (n : Nat) → (ss : List σ) →
        PMF (∀ i, Act i (O.currentObs i (O.projectStates i ss))),
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

/-- Semantic step-mass invariance on the core model.
If two pure profiles can reach the same next state from the same trace in one
step, then that one-step mass is the same. -/
def StepMassInvariant (O : ObsModelCore ι σ Obs Act) : Prop :=
  ∀ {ss : List σ} {t : σ} (π₁ π₂ : ObsModelCore.PureProfile O),
    O.pureStep π₁ ss t ≠ 0 → O.pureStep π₂ ss t ≠ 0 →
      O.pureStep π₁ ss t = O.pureStep π₂ ss t

/-- Semantic one-step support factorization on the core model.
Fix any witness profile reaching `t` from `ss`. Another profile reaches the same
`t` iff each single-player update of the witness profile does. -/
def StepSupportFactorization (O : ObsModelCore ι σ Obs Act) : Prop :=
  ∀ {ss : List σ} {t : σ} (π₀ π : ObsModelCore.PureProfile O),
    O.pureStep π₀ ss t ≠ 0 →
      (O.pureStep π ss t ≠ 0 ↔
        ∀ i, O.pureStep (Function.update π₀ i (π i)) ss t ≠ 0)

/-- Stronger but easier-to-check action uniqueness condition.
Kept as a sufficient condition; the core theorem below uses only the weaker
mass/support properties. -/
def StepActionDeterminism (O : ObsModelCore ι σ Obs Act) : Prop :=
  ∀ (s t : σ) (a a' : O.JointActionAt s),
    (O.step s a) t ≠ 0 → (O.step s a') t ≠ 0 → a = a'

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] in
/-- PSAR implies step action determinism on the core model. -/
theorem PerStepActionRecall.toStepActionDeterminism
    (hPSAR : ObsModelCore.PerStepActionRecall O) :
    StepActionDeterminism O :=
  fun s t a a' h1 h2 => funext fun i =>
    hPSAR s s t t a a' h1 h2 (fun _ => rfl) (fun _ => rfl) i

end

section ReachFactorCore

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- Under a pure behavioral profile, `jointActionDist` is a point mass. -/
theorem jointActionDist_pureToBehavioral_m2b (O : ObsModelCore ι σ Obs Act)
    (π : ObsModelCore.PureProfile O) (ss : List σ) :
    O.jointActionDist (O.pureToBehavioral π) ss =
      PMF.pure (fun i => π i (O.projectStates i ss)) := by
  unfold ObsModelCore.jointActionDist ObsModelCore.pureToBehavioral
  exact Math.PMFProduct.pmfPi_pure (fun i => π i (O.projectStates i ss))

/-- Under a pure behavioral profile, `stepDist` is a deterministic step. -/
theorem stepDist_pureToBehavioral_m2b (O : ObsModelCore ι σ Obs Act)
    (π : ObsModelCore.PureProfile O) (ss : List σ) :
    O.stepDist (O.pureToBehavioral π) ss =
      O.step (O.lastState ss)
        (O.castJointAction ss (fun i => π i (O.projectStates i ss))) := by
  unfold ObsModelCore.stepDist
  rw [jointActionDist_pureToBehavioral_m2b, PMF.pure_bind]

/-- For pure profiles, `pureStep` is just `O.step` with the cast action. -/
theorem pureStep_eq (π : ObsModelCore.PureProfile O) (ss : List σ) :
    O.pureStep π ss =
      O.step (O.lastState ss)
        (fun i => O.currentObs_projectStates i ss ▸ π i (O.projectStates i ss)) := by
  unfold ObsModelCore.pureStep ObsModelCore.stepDist ObsModelCore.jointActionDist
    ObsModelCore.pureToBehavioral ObsModelCore.castJointAction
  simp [Math.PMFProduct.pmfPi_pure, PMF.pure_bind]

/-- Under step-action determinism, if two profiles produce nonzero transition at the same state
trace and target, their step distributions are equal. -/
theorem pureStep_eq_of_nonzero_same
    (hDet : StepActionDeterminism O)
    {π₁ π₂ : ObsModelCore.PureProfile O} {ss : List σ} {t : σ}
    (h₁ : O.pureStep π₁ ss t ≠ 0) (h₂ : O.pureStep π₂ ss t ≠ 0) :
    O.pureStep π₁ ss = O.pureStep π₂ ss := by
  simp only [pureStep_eq] at h₁ h₂ ⊢
  congr 1
  funext i
  have hEq := hDet _ _ _ _ h₁ h₂
  have := congrArg (fun a => a i) hEq
  simpa using this

/-- Under step-mass invariance, nonzero reach probabilities at the same trace are equal. -/
theorem pureRun_const_of_support
    (hMass : StepMassInvariant O) (n : Nat)
    {π π' : ObsModelCore.PureProfile O} {ss : List σ}
    (h : pureRun (O.pureStep) O.init n π ss ≠ 0)
    (h' : pureRun (O.pureStep) O.init n π' ss ≠ 0) :
    pureRun (O.pureStep) O.init n π ss =
      pureRun (O.pureStep) O.init n π' ss := by
  induction n generalizing ss π with
  | zero =>
      simp [pureRun] at h h' ⊢
  | succ k ih =>
      rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
      · exact absurd (pureRun_succ_nil _ _ _ _) h
      · simp only [List.concat_eq_append, pureRun_succ_append] at h h' ⊢
        have hp := left_ne_zero_of_mul h
        have hp' := left_ne_zero_of_mul h'
        have ht := right_ne_zero_of_mul h
        have ht' := right_ne_zero_of_mul h'
        rw [ih hp hp', hMass _ _ ht ht']

/-- Under step-action determinism, at a reachable transition, `pureStep` is nonzero iff
the profile produces the same action as any fixed witness profile. -/
theorem pureStep_nonzero_iff_action_eq
    (hDet : StepActionDeterminism O)
    {π₀ : ObsModelCore.PureProfile O} {ss : List σ} {t : σ}
    (h₀ : O.pureStep π₀ ss t ≠ 0) (π : ObsModelCore.PureProfile O) :
    O.pureStep π ss t ≠ 0 ↔
      (fun i => π i (O.projectStates i ss)) =
        (fun i => π₀ i (O.projectStates i ss)) := by
  constructor
  · intro hne
    rw [pureStep_eq] at hne h₀
    have h := hDet _ _ _ _ hne h₀
    exact funext fun i => by
      have hi : (O.currentObs_projectStates i ss ▸ π i (O.projectStates i ss)) =
          O.currentObs_projectStates i ss ▸ π₀ i (O.projectStates i ss) :=
        congrArg (fun a => a i) h
      exact eq_of_heq ((fwd_subst_heq _ _).trans
        ((heq_of_eq hi).trans (fwd_subst_heq _ _).symm))
  · intro heq
    have : O.pureStep π ss = O.pureStep π₀ ss := by
      simp only [pureStep_eq]
      congr 1
      funext i
      exact congrArg (O.currentObs_projectStates i ss ▸ ·) (congr_fun heq i)
    rwa [this]

/-- Under step-action determinism, `pureStep` factors per-player: it is nonzero iff each player
individually produces the forced action component. -/
theorem pureStep_nonzero_iff_forall_player
    (hDet : StepActionDeterminism O)
    {π₀ : ObsModelCore.PureProfile O} {ss : List σ} {t : σ}
    (h₀ : O.pureStep π₀ ss t ≠ 0) (π : ObsModelCore.PureProfile O) :
    O.pureStep π ss t ≠ 0 ↔
      ∀ i, π i (O.projectStates i ss) = π₀ i (O.projectStates i ss) := by
  rw [pureStep_nonzero_iff_action_eq hDet h₀]
  exact ⟨fun h i => congr_fun h i, funext⟩

/-- Step-action determinism implies step-mass invariance. -/
theorem StepActionDeterminism.toMassInvariant
    (hDet : StepActionDeterminism O) :
    StepMassInvariant O := by
  intro ss t π₁ π₂ h₁ h₂
  have hEq := pureStep_eq_of_nonzero_same (O := O) hDet h₁ h₂
  exact congrArg (fun d => d t) hEq

/-- Step-action determinism implies step-support factorization. -/
theorem StepActionDeterminism.toSupportFactorization
    (hDet : StepActionDeterminism O) :
    StepSupportFactorization O := by
  intro ss t π₀ π h₀
  constructor
  · intro hπ i
    apply (pureStep_nonzero_iff_forall_player (O := O) hDet h₀
      (Function.update π₀ i (π i))).mpr
    intro j
    by_cases hji : j = i
    · subst j
      simpa using
        (pureStep_nonzero_iff_forall_player (O := O) hDet h₀ π).mp hπ i
    · simp [Function.update_of_ne hji]
  · intro hall
    apply (pureStep_nonzero_iff_forall_player (O := O) hDet h₀ π).mpr
    intro i
    have hi :=
      (pureStep_nonzero_iff_forall_player (O := O) hDet h₀
        (Function.update π₀ i (π i))).mp (hall i) i
    simpa [Function.update_self] using hi

/-- Under step-action determinism, `pureRun` nonzero is equivalent to matching the witness action
at each prefix. -/
theorem pureRun_succ_nonzero_iff
    (hDet : StepActionDeterminism O) (m : Nat)
    {π₀ : ObsModelCore.PureProfile O} {p : List σ} {t : σ}
    (h₀ : pureRun (O.pureStep) O.init (m + 1) π₀ (p ++ [t]) ≠ 0)
    (π : ObsModelCore.PureProfile O) :
    pureRun (O.pureStep) O.init (m + 1) π (p ++ [t]) ≠ 0 ↔
      pureRun (O.pureStep) O.init m π p ≠ 0 ∧
        ∀ i, π i (O.projectStates i p) = π₀ i (O.projectStates i p) := by
  simp only [pureRun_succ_append] at h₀ ⊢
  have hp₀ := left_ne_zero_of_mul h₀
  have ht₀ := right_ne_zero_of_mul h₀
  constructor
  · intro hne
    exact ⟨left_ne_zero_of_mul hne,
      (pureStep_nonzero_iff_forall_player hDet ht₀ π).mp
        (right_ne_zero_of_mul hne)⟩
  · intro ⟨hp, hall⟩
    exact mul_ne_zero hp
      ((pureStep_nonzero_iff_forall_player hDet ht₀ π).mpr hall)

/-- Under one-step support factorization, reach factors per-player via `Function.update`. -/
theorem pureRun_nonzero_iff_update
    (hFactor : StepSupportFactorization O) (n : Nat)
    {π₀ : ObsModelCore.PureProfile O} {ss : List σ}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0)
    (π : ObsModelCore.PureProfile O) :
    pureRun (O.pureStep) O.init n π ss ≠ 0 ↔
      ∀ i, pureRun (O.pureStep) O.init n
        (Function.update π₀ i (π i)) ss ≠ 0 := by
  revert π
  induction n generalizing ss with
  | zero =>
      intro π
      simp only [pureRun, ne_eq] at h₀ ⊢
      exact ⟨fun _ _ => h₀, fun _ => h₀⟩
  | succ m ih =>
      intro π
      rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
      · exact absurd (pureRun_succ_nil _ _ _ _) h₀
      · simp only [List.concat_eq_append]
        have h₀_step : pureRun (O.pureStep) O.init (m + 1) π₀ (p ++ [t]) ≠ 0 := by
          simpa [List.concat_eq_append] using h₀
        have hp₀ : pureRun (O.pureStep) O.init m π₀ p ≠ 0 := by
          rw [pureRun_succ_append] at h₀_step
          exact left_ne_zero_of_mul h₀_step
        have ht₀ : O.pureStep π₀ p t ≠ 0 := by
          rw [pureRun_succ_append] at h₀_step
          exact right_ne_zero_of_mul h₀_step
        constructor
        · intro hπ
          have hp : pureRun (O.pureStep) O.init m π p ≠ 0 := by
            rw [pureRun_succ_append] at hπ
            exact left_ne_zero_of_mul hπ
          have ht : O.pureStep π p t ≠ 0 := by
            rw [pureRun_succ_append] at hπ
            exact right_ne_zero_of_mul hπ
          intro i
          have hp_i : pureRun (O.pureStep) O.init m (Function.update π₀ i (π i)) p ≠ 0 := by
            exact (ih hp₀ π).mp hp i
          have ht_i : O.pureStep (Function.update π₀ i (π i)) p t ≠ 0 := by
            exact (hFactor π₀ π ht₀).mp ht i
          rw [pureRun_succ_append]
          exact mul_ne_zero hp_i ht_i
        · intro hall
          have hp : pureRun (O.pureStep) O.init m π p ≠ 0 := by
            exact (ih hp₀ π).mpr fun i => by
              have hi := hall i
              rw [pureRun_succ_append] at hi
              exact left_ne_zero_of_mul hi
          have hall_step : ∀ i, O.pureStep (Function.update π₀ i (π i)) p t ≠ 0 := by
            intro i
            have hi := hall i
            rw [pureRun_succ_append] at hi
            exact right_ne_zero_of_mul hi
          have ht : O.pureStep π p t ≠ 0 := by
            exact (hFactor π₀ π ht₀).mpr hall_step
          rw [pureRun_succ_append]
          exact mul_ne_zero hp ht

/-- Cross-multiplication identity for the reach weight. -/
theorem pureRun_cross_mul_product
    (hMass : StepMassInvariant O)
    (hFactor : StepSupportFactorization O)
    [Fintype (ObsModelCore.PureProfile O)]
    (ν : PMF (ObsModelCore.PureProfile O))
    (n : Nat) {π₀ : ObsModelCore.PureProfile O} {ss : List σ}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0) (π : ObsModelCore.PureProfile O) :
    pureRun (O.pureStep) O.init n π ss *
      (∑ π' : ObsModelCore.PureProfile O, ν π' *
        ∏ i, pureRun (O.pureStep) O.init n (Function.update π₀ i (π' i)) ss) =
    (∏ i, pureRun (O.pureStep) O.init n (Function.update π₀ i (π i)) ss) *
      (∑ π' : ObsModelCore.PureProfile O, ν π' *
        pureRun (O.pureStep) O.init n π' ss) := by
  set C₀ := pureRun (O.pureStep) O.init n π₀ ss with hC₀_def
  have hconst : ∀ π', pureRun (O.pureStep) O.init n π' ss ≠ 0 →
      pureRun (O.pureStep) O.init n π' ss = C₀ :=
    fun π' h => pureRun_const_of_support hMass n h h₀
  have hconst_upd : ∀ (π' : ObsModelCore.PureProfile O) (i : ι),
      pureRun (O.pureStep) O.init n (Function.update π₀ i (π' i)) ss ≠ 0 →
      pureRun (O.pureStep) O.init n (Function.update π₀ i (π' i)) ss = C₀ :=
    fun π' i h => pureRun_const_of_support hMass n h h₀
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π' _
  by_cases hπ : pureRun (O.pureStep) O.init n π ss = 0
  · rw [hπ, zero_mul]
    have hnotall : ¬ ∀ i,
        pureRun (O.pureStep) O.init n (Function.update π₀ i (π i)) ss ≠ 0 := by
      intro hall
      exact ((pureRun_nonzero_iff_update hFactor n h₀ π).mpr hall) hπ
    push Not at hnotall
    obtain ⟨i, hi⟩ := hnotall
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
  · by_cases hπ' : pureRun (O.pureStep) O.init n π' ss = 0
    · rw [hπ', mul_zero, mul_zero]
      have := mt (pureRun_nonzero_iff_update hFactor n h₀ π').mpr (not_not.mpr hπ')
      push Not at this
      obtain ⟨j, hj⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, mul_zero, mul_zero]
    · have hw := hconst π hπ
      have hw' := hconst π' hπ'
      have hwi : ∀ i, pureRun (O.pureStep) O.init n
          (Function.update π₀ i (π i)) ss = C₀ :=
        fun i => hconst_upd π i ((pureRun_nonzero_iff_update hFactor n h₀ π).mp hπ i)
      have hwi' : ∀ i, pureRun (O.pureStep) O.init n
          (Function.update π₀ i (π' i)) ss = C₀ :=
        fun i => hconst_upd π' i ((pureRun_nonzero_iff_update hFactor n h₀ π').mp hπ' i)
      rw [hw, hw']
      simp_rw [hwi, hwi']
      ac_rfl

/-- Run-level support factorization: the run-level analogue of
`StepSupportFactorization`. A profile reaches a trace iff each single-player
update of the witness does. This is strictly weaker than `StepSupportFactorization`
because it only constrains reachable traces, not unreachable states. -/
def RunSupportFactorization (O : ObsModelCore ι σ Obs Act) : Prop :=
  ∀ (n : Nat) {ss : List σ} (π₀ π : ObsModelCore.PureProfile O),
    pureRun (O.pureStep) O.init n π₀ ss ≠ 0 →
      (pureRun (O.pureStep) O.init n π ss ≠ 0 ↔
        ∀ i, pureRun (O.pureStep) O.init n
          (Function.update π₀ i (π i)) ss ≠ 0)

/-- Step-level support factorization implies run-level. -/
theorem StepSupportFactorization.toRunSupportFactorization
    (hFactor : StepSupportFactorization O) :
    RunSupportFactorization O := by
  intro n ss π₀ π h₀
  exact pureRun_nonzero_iff_update (ss := ss) hFactor n h₀ π

/-- Cross-multiplication identity using run-level support factorization. -/
theorem pureRun_cross_mul_product_of_run
    (hMass : StepMassInvariant O)
    (hRun : RunSupportFactorization O)
    [Fintype (ObsModelCore.PureProfile O)]
    (ν : PMF (ObsModelCore.PureProfile O))
    (n : Nat) {π₀ : ObsModelCore.PureProfile O} {ss : List σ}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0)
    (π : ObsModelCore.PureProfile O) :
    pureRun (O.pureStep) O.init n π ss *
      (∑ π' : ObsModelCore.PureProfile O, ν π' *
        ∏ i, pureRun (O.pureStep) O.init n (Function.update π₀ i (π' i)) ss) =
    (∏ i, pureRun (O.pureStep) O.init n (Function.update π₀ i (π i)) ss) *
      (∑ π' : ObsModelCore.PureProfile O, ν π' *
        pureRun (O.pureStep) O.init n π' ss) := by
  set C₀ := pureRun (O.pureStep) O.init n π₀ ss with hC₀_def
  have hconst : ∀ π', pureRun (O.pureStep) O.init n π' ss ≠ 0 →
      pureRun (O.pureStep) O.init n π' ss = C₀ :=
    fun π' h => pureRun_const_of_support hMass n h h₀
  have hconst_upd : ∀ (π' : ObsModelCore.PureProfile O) (i : ι),
      pureRun (O.pureStep) O.init n (Function.update π₀ i (π' i)) ss ≠ 0 →
      pureRun (O.pureStep) O.init n (Function.update π₀ i (π' i)) ss = C₀ :=
    fun π' i h => pureRun_const_of_support hMass n h h₀
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π' _
  by_cases hπ : pureRun (O.pureStep) O.init n π ss = 0
  · rw [hπ, zero_mul]
    have hnotall : ¬ ∀ i,
        pureRun (O.pureStep) O.init n (Function.update π₀ i (π i)) ss ≠ 0 := by
      intro hall
      exact ((hRun n π₀ π h₀).mpr hall) hπ
    push Not at hnotall
    obtain ⟨i, hi⟩ := hnotall
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
  · by_cases hπ' : pureRun (O.pureStep) O.init n π' ss = 0
    · rw [hπ', mul_zero, mul_zero]
      have := mt (hRun n π₀ π' h₀).mpr (not_not.mpr hπ')
      push Not at this
      obtain ⟨j, hj⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, mul_zero, mul_zero]
    · have hw := hconst π hπ
      have hw' := hconst π' hπ'
      have hwi : ∀ i, pureRun (O.pureStep) O.init n
          (Function.update π₀ i (π i)) ss = C₀ :=
        fun i => hconst_upd π i ((hRun n π₀ π h₀).mp hπ i)
      have hwi' : ∀ i, pureRun (O.pureStep) O.init n
          (Function.update π₀ i (π' i)) ss = C₀ :=
        fun i => hconst_upd π' i ((hRun n π₀ π' h₀).mp hπ' i)
      rw [hw, hw']
      simp_rw [hwi, hwi']
      ac_rfl

end ReachFactorCore

section ObsLocalKuhn

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- Full obs-local feasibility: like `ObsLocalFeasibility` but without the
`Subsingleton` guard. This is the condition needed for the chaining argument
that derives run-level support factorization.

`ObsLocalFeasibility` guards by `¬ Subsingleton (Act i ...)` because it was
designed for `ActionPosteriorLocal` (where subsingleton types are trivially
handled). For run-level support factorization, we need the iff at ALL info
states including those with subsingleton actions, because updating player `i`'s
full local strategy can affect earlier steps even when the current action type
is trivial. -/
def ObsLocalFeasibilityFull (O : ObsModelCore ι σ Obs Act) (i : ι) : Prop :=
  ∀ (n₁ n₂ : Nat) (π₀ π₀' : ObsModelCore.PureProfile O) (ss₁ ss₂ : List σ),
    O.projectStates i ss₁ = O.projectStates i ss₂ →
    pureRun (O.pureStep) O.init n₁ π₀ ss₁ ≠ 0 →
    pureRun (O.pureStep) O.init n₂ π₀' ss₂ ≠ 0 →
    ∀ (πᵢ : O.LocalStrategy i),
      pureRun (O.pureStep) O.init n₁ (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
      pureRun (O.pureStep) O.init n₂ (Function.update π₀' i πᵢ) ss₂ ≠ 0

/-- A **local-support signature** (unguarded): the support of a one-player
replacement at any reachable trace is characterized by a predicate
`Req : InfoState i → LocalStrategy i → Prop` of the player's endpoint
information state.

This is the natural proof target for models where the player's information
state is a sufficient statistic for the support constraints on a replacement
strategy. Once available, `ObsLocalFeasibilityFull` follows immediately by
`rw [hobs]`. -/
structure LocalSupportSignatureFull
    (O : ObsModelCore ι σ Obs Act) (i : ι) where
  Req : O.InfoState i → O.LocalStrategy i → Prop
  support_iff :
    ∀ (n : Nat) (π₀ : ObsModelCore.PureProfile O) (ss : List σ),
      pureRun (O.pureStep) O.init n π₀ ss ≠ 0 →
      ∀ (πᵢ : O.LocalStrategy i),
        pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss ≠ 0 ↔
          Req (O.projectStates i ss) πᵢ

/-- A `LocalSupportSignatureFull` implies `ObsLocalFeasibilityFull`. -/
theorem obsLocalFeasibilityFull_of_localSupportSignatureFull
    (i : ι) (S : O.LocalSupportSignatureFull i) :
    ObsLocalFeasibilityFull O i := by
  intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ πᵢ
  rw [S.support_iff n₁ π₀ ss₁ h₁ πᵢ, S.support_iff n₂ π₀' ss₂ h₂ πᵢ, hobs]

/-- Profile that agrees with `π` on players in `S` and with `π₀` elsewhere. -/
private noncomputable def multiUpdate [DecidableEq ι]
    (π₀ π : ObsModelCore.PureProfile O) (S : Finset ι) :
    ObsModelCore.PureProfile O :=
  fun i => if i ∈ S then π i else π₀ i

omit [Fintype ι] [∀ i o, Fintype (Act i o)] in
private theorem multiUpdate_empty (π₀ π : ObsModelCore.PureProfile O) :
    multiUpdate π₀ π ∅ = π₀ := by
  ext i; simp [multiUpdate]

omit [∀ i o, Fintype (Act i o)] in
private theorem multiUpdate_univ (π₀ π : ObsModelCore.PureProfile O) :
    multiUpdate π₀ π Finset.univ = π := by
  ext i; simp [multiUpdate]

omit [Fintype ι] [∀ i o, Fintype (Act i o)] in
private theorem multiUpdate_insert {j : ι} {S : Finset ι} (hj : j ∉ S)
    (π₀ π : ObsModelCore.PureProfile O) :
    multiUpdate π₀ π (insert j S) =
      Function.update (multiUpdate π₀ π S) j (π j) := by
  ext i
  simp only [multiUpdate, Finset.mem_insert, Function.update]
  split
  next h =>
    rcases h with rfl | h
    · simp
    · simp [h, show i ≠ j from fun he => hj (he ▸ h)]
  next h =>
    push Not at h
    simp [h.1, h.2]

omit [Fintype ι] [∀ i o, Fintype (Act i o)] in
private theorem multiUpdate_singleton (π₀ π : ObsModelCore.PureProfile O) (i : ι) :
    multiUpdate π₀ π {i} = Function.update π₀ i (π i) := by
  ext j
  simp only [multiUpdate, Finset.mem_singleton, Function.update]
  split
  · next h => subst h; simp
  · next h => simp

/-- **Chaining lemma**: If `ObsLocalFeasibilityFull` holds for all players and
all single-player updates of the witness reach `ss`, then any multi-player
update also reaches `ss`. -/
private theorem multiUpdate_reach_of_obsLocal
    (hOLF : ∀ i, ObsLocalFeasibilityFull O i)
    {n : Nat} {ss : List σ} {π₀ π : ObsModelCore.PureProfile O}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0)
    (hall : ∀ i, pureRun (O.pureStep) O.init n
      (Function.update π₀ i (π i)) ss ≠ 0)
    (S : Finset ι) :
    pureRun (O.pureStep) O.init n (multiUpdate π₀ π S) ss ≠ 0 := by
  induction S using Finset.induction with
  | empty => rwa [multiUpdate_empty]
  | insert j S hj ih =>
      rw [multiUpdate_insert hj]
      exact (hOLF j n n π₀ (multiUpdate π₀ π S) ss ss rfl h₀ ih (π j)).mp (hall j)

/-- `ObsLocalFeasibilityFull` for all players implies `RunSupportFactorization`. -/
theorem obsLocalFeasibilityFull_toRunSupportFactorization
    (hOLF : ∀ i, ObsLocalFeasibilityFull O i) :
    RunSupportFactorization O := by
  intro n ss π₀ π h₀
  constructor
  · -- Forward: π reaches ⟹ all single-player updates reach
    intro hπ i
    -- Use OLF with witness π (reaches) and π₀ (reaches), same trace
    exact (hOLF i n n π π₀ ss ss rfl hπ h₀ (π i)).mp
      (by rwa [Function.update_eq_self])
  · -- Backward: all single-player updates reach ⟹ π reaches
    intro hall
    -- Chain updates: multiUpdate π₀ π univ = π
    have := multiUpdate_reach_of_obsLocal hOLF h₀ hall Finset.univ
    rwa [multiUpdate_univ] at this

end ObsLocalKuhn

section CoreKuhnSemantic

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.InfoState i)]

/-- Semantic locality on the core model. -/
def ObsLocalFeasibility (O : ObsModelCore ι σ Obs Act) (i : ι) : Prop :=
  ∀ (n₁ n₂ : Nat) (π₀ π₀' : ObsModelCore.PureProfile O) (ss₁ ss₂ : List σ),
    O.projectStates i ss₁ = O.projectStates i ss₂ →
    pureRun (O.pureStep) O.init n₁ π₀ ss₁ ≠ 0 →
    pureRun (O.pureStep) O.init n₂ π₀' ss₂ ≠ 0 →
    ¬ Subsingleton (Act i (O.currentObs i (O.projectStates i ss₁))) →
    ∀ (πᵢ : O.LocalStrategy i),
      pureRun (O.pureStep) O.init n₁ (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
      pureRun (O.pureStep) O.init n₂ (Function.update π₀' i πᵢ) ss₂ ≠ 0

/-- Guarded variant of `LocalSupportSignatureFull`: the support iff is only
required when the current action type is non-trivial, matching the guard on
`ObsLocalFeasibility`. -/
structure LocalSupportSignature
    (O : ObsModelCore ι σ Obs Act) (i : ι) where
  Req : O.InfoState i → O.LocalStrategy i → Prop
  support_iff :
    ∀ (n : Nat) (π₀ : ObsModelCore.PureProfile O) (ss : List σ),
      pureRun (O.pureStep) O.init n π₀ ss ≠ 0 →
      ¬ Subsingleton (Act i (O.currentObs i (O.projectStates i ss))) →
      ∀ (πᵢ : O.LocalStrategy i),
        pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss ≠ 0 ↔
          Req (O.projectStates i ss) πᵢ

omit [∀ i, Fintype (O.InfoState i)] in
/-- A `LocalSupportSignature` implies `ObsLocalFeasibility`. -/
theorem obsLocalFeasibility_of_localSupportSignature
    (i : ι) (S : O.LocalSupportSignature i) :
    ObsLocalFeasibility O i := by
  intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ hsub πᵢ
  have hsub₂ : ¬ Subsingleton (Act i (O.currentObs i (O.projectStates i ss₂))) := by
    rw [← hobs]; exact hsub
  rw [S.support_iff n₁ π₀ ss₁ h₁ hsub πᵢ, S.support_iff n₂ π₀' ss₂ h₂ hsub₂ πᵢ, hobs]

/-- Minimal semantic locality on the core model: the posterior distribution of
player `i`'s recommended action, after conditioning on reaching the current
trace, depends only on player `i`'s information state. -/
def ActionPosteriorLocal (O : ObsModelCore ι σ Obs Act) (i : ι)
    [∀ i, Fintype (O.InfoState i)] [∀ i o, Fintype (Act i o)] : Prop :=
  ∀ (n₁ n₂ : Nat) (π₀ π₀' : ObsModelCore.PureProfile O) (ss₁ ss₂ : List σ),
    O.projectStates i ss₁ = O.projectStates i ss₂ →
    pureRun (O.pureStep) O.init n₁ π₀ ss₁ ≠ 0 →
    pureRun (O.pureStep) O.init n₂ π₀' ss₂ ≠ 0 →
    ∀ (b_i : PMF (O.LocalStrategy i)),
      HEq
        (Math.ProbabilityMassFunction.pushforward
          (reweightPMF b_i
            (fun πᵢ => pureRun (O.pureStep) O.init n₁
              (Function.update π₀ i πᵢ) ss₁))
          (fun πᵢ => πᵢ (O.projectStates i ss₁)))
        (Math.ProbabilityMassFunction.pushforward
          (reweightPMF b_i
            (fun πᵢ => pureRun (O.pureStep) O.init n₂
              (Function.update π₀' i πᵢ) ss₂))
          (fun πᵢ => πᵢ (O.projectStates i ss₂)))

private theorem pmf_eq_of_subsingleton
    {α : Type} [Subsingleton α] (p q : PMF α) : p = q := by
  classical
  rcases p.support_nonempty with ⟨a, ha⟩
  have hp_support : p.support = ({a} : Set α) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      simpa using (Subsingleton.elim x a)
    · intro x hx
      have hx' : x = a := by simpa using hx
      exact hx' ▸ ha
  have hq_support : q.support = ({a} : Set α) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      simpa using (Subsingleton.elim x a)
    · intro x hx
      have hx' : x = a := by simpa using hx
      rcases q.support_nonempty with ⟨b, hb⟩
      have hba : b = a := Subsingleton.elim b a
      exact hx' ▸ (hba.symm ▸ hb)
  have hp : p a = 1 := (p.apply_eq_one_iff a).2 hp_support
  have hq : q a = 1 := (q.apply_eq_one_iff a).2 hq_support
  refine PMF.ext ?_
  intro x
  have hx : x = a := Subsingleton.elim x a
  subst hx
  exact hp.trans hq.symm

/-- Core obs-locality of `reweightPMF`. -/
theorem reweightPMF_update_obs_local_of
    (hMass : StepMassInvariant O) (n₁ n₂ : Nat)
    (i : ι) (b_i : PMF (O.LocalStrategy i))
    {π₀ π₀' : ObsModelCore.PureProfile O} {ss₁ ss₂ : List σ}
    (h₁ : pureRun (O.pureStep) O.init n₁ π₀ ss₁ ≠ 0)
    (h₂ : pureRun (O.pureStep) O.init n₂ π₀' ss₂ ≠ 0)
    (hiff : ∀ πᵢ,
      pureRun (O.pureStep) O.init n₁ (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
      pureRun (O.pureStep) O.init n₂ (Function.update π₀' i πᵢ) ss₂ ≠ 0) :
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n₁ (Function.update π₀ i πᵢ) ss₁) =
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n₂ (Function.update π₀' i πᵢ) ss₂) := by
  set w₁ := fun πᵢ => pureRun (O.pureStep) O.init n₁ (Function.update π₀ i πᵢ) ss₁
  set w₂ := fun πᵢ => pureRun (O.pureStep) O.init n₂ (Function.update π₀' i πᵢ) ss₂
  have hsum_zero_iff : (∑ πᵢ, b_i πᵢ * w₁ πᵢ) = 0 ↔ (∑ πᵢ, b_i πᵢ * w₂ πᵢ) = 0 := by
    simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies, mul_eq_zero]
    constructor
    · intro h πᵢ; rcases h πᵢ with h | h
      · exact Or.inl h
      · exact Or.inr (of_not_not (mt (hiff πᵢ).mpr (not_not.mpr h)))
    · intro h πᵢ; rcases h πᵢ with h | h
      · exact Or.inl h
      · exact Or.inr (of_not_not (mt (hiff πᵢ).mp (not_not.mpr h)))
  have htop₁ : (∑ πᵢ, b_i πᵢ * w₁ πᵢ) ≠ ⊤ := sum_mul_pmf_ne_top b_i _ fun πᵢ => PMF.coe_le_one _ ss₁
  have htop₂ : (∑ πᵢ, b_i πᵢ * w₂ πᵢ) ≠ ⊤ := sum_mul_pmf_ne_top b_i _ fun πᵢ => PMF.coe_le_one _ ss₂
  by_cases hC₁ : (∑ πᵢ, b_i πᵢ * w₁ πᵢ) = 0
  · rw [reweightPMF_fallback _ _ hC₁, reweightPMF_fallback _ _ (hsum_zero_iff.mp hC₁)]
  · have hC₂ : (∑ πᵢ, b_i πᵢ * w₂ πᵢ) ≠ 0 := mt hsum_zero_iff.mpr hC₁
    exact reweightPMF_eq_of_cross_mul b_i w₁ w₂ hC₁ htop₁ hC₂ htop₂ (fun πᵢ => by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro πᵢ' _
      by_cases hw : w₁ πᵢ = 0
      · have hw2 : w₂ πᵢ = 0 := of_not_not (mt (hiff πᵢ).mpr (not_not.mpr hw))
        simp [hw, hw2]
      · by_cases hw' : w₁ πᵢ' = 0
        · have hw2' : w₂ πᵢ' = 0 := of_not_not (mt (hiff πᵢ').mpr (not_not.mpr hw'))
          simp [hw', hw2']
        · have eq1 : w₁ πᵢ = pureRun (O.pureStep) O.init n₁ π₀ ss₁ :=
            pureRun_const_of_support hMass n₁ hw h₁
          have eq2 : w₂ πᵢ = pureRun (O.pureStep) O.init n₂ π₀' ss₂ :=
            pureRun_const_of_support hMass n₂ ((hiff πᵢ).mp hw) h₂
          have eq3 : w₁ πᵢ' = pureRun (O.pureStep) O.init n₁ π₀ ss₁ :=
            pureRun_const_of_support hMass n₁ hw' h₁
          have eq4 : w₂ πᵢ' = pureRun (O.pureStep) O.init n₂ π₀' ss₂ :=
            pureRun_const_of_support hMass n₂ ((hiff πᵢ').mp hw') h₂
          rw [eq1, eq2, eq3, eq4]
          ring)

/-- The stronger feasibility-style locality condition implies the minimal
posterior-locality condition used by the core Kuhn theorem. -/
theorem actionPosteriorLocal_of_obsLocalFeasibility
    (hMass : StepMassInvariant O)
    (i : ι) (hLocal : ObsLocalFeasibility O i) :
    ActionPosteriorLocal O i := by
  intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ b_i
  by_cases hsub : Subsingleton (Act i (O.currentObs i (O.projectStates i ss₁)))
  · let hAct := congrArg (fun v => Act i (O.currentObs i v)) hobs
    have hsub' : Subsingleton (Act i (O.currentObs i (O.projectStates i ss₂))) := by
      simpa [hAct] using hsub
    letI := hsub'
    let hPMF :
        PMF (Act i (O.currentObs i (O.projectStates i ss₁))) =
          PMF (Act i (O.currentObs i (O.projectStates i ss₂))) :=
      congrArg PMF hAct
    have hEq :
        cast hPMF
          (Math.ProbabilityMassFunction.pushforward
            (reweightPMF b_i
              (fun πᵢ => pureRun (O.pureStep) O.init n₁
                (Function.update π₀ i πᵢ) ss₁))
            (fun πᵢ => πᵢ (O.projectStates i ss₁))) =
        Math.ProbabilityMassFunction.pushforward
          (reweightPMF b_i
            (fun πᵢ => pureRun (O.pureStep) O.init n₂
              (Function.update π₀' i πᵢ) ss₂))
          (fun πᵢ => πᵢ (O.projectStates i ss₂)) := by
      exact pmf_eq_of_subsingleton _ _
    exact (cast_heq hPMF _).symm.trans (heq_of_eq hEq)
  · exact pmf_bind_heq'
      (congrArg (fun v => Act i (O.currentObs i v)) hobs)
      _ _
      (reweightPMF_update_obs_local_of hMass n₁ n₂ i b_i h₁ h₂
        (hLocal n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ hsub))
      _ _
      (fun πᵢ => congr_arg_heq (fun v => PMF.pure (πᵢ v)) hobs)

/-- Product mixed plans induce product mediator outputs at each reachable trace. -/
theorem mixedToMediator_eq_pmfPi_factor
    (hMass : StepMassInvariant O)
    (hFactor : StepSupportFactorization O)
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (n : Nat) (ss : List σ) {π₀ : ObsModelCore.PureProfile O}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0)
    (hν₀ : (pmfPi μ) π₀ ≠ 0) :
    O.mixedToMediator (pmfPi μ) n ss = pmfPi (fun i =>
      Math.ProbabilityMassFunction.pushforward
        (reweightPMF (μ i)
          (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss))
        (fun πᵢ => πᵢ (O.projectStates i ss))) := by
  set ν := pmfPi μ with hν_def
  set w := fun π => pureRun (O.pureStep) O.init n π ss
  set wᵢ := fun i (πᵢ : O.LocalStrategy i) =>
    pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss
  suffices hprod : reweightPMF ν w = pmfPi (fun i => reweightPMF (μ i) (wᵢ i)) by
    unfold ObsModelCore.mixedToMediator
    rw [hprod]
    simp only [ObsModelCore.jointActionDist, ObsModelCore.pureToBehavioral]
    conv_lhs => arg 2; ext π; rw [pmfPi_pure]
    exact pmfPi_push_coordwise _ (fun i (πᵢ : O.LocalStrategy i) =>
      πᵢ (O.projectStates i ss))
  have hμ_ne : ∀ i, μ i (π₀ i) ≠ 0 := by
    intro i hi; apply hν₀; rw [hν_def, pmfPi_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hwi_ne : ∀ i, wᵢ i (π₀ i) ≠ 0 :=
    fun i => ((pureRun_nonzero_iff_update hFactor n h₀ π₀).mp h₀) i
  have hCwi0 : ∀ i, ∑ a, μ i a * wᵢ i a ≠ 0 := fun i => by
    apply ne_of_gt
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero (hμ_ne i) (hwi_ne i)))
      (Finset.single_le_sum (f := fun a => μ i a * wᵢ i a)
        (fun _ _ => zero_le) (Finset.mem_univ (π₀ i)))
  have hCwit : ∀ i, ∑ a, μ i a * wᵢ i a ≠ ⊤ := fun i =>
    sum_mul_pmf_ne_top (μ i) _ fun a => PMF.coe_le_one _ ss
  have hCw0 : ∑ π, ν π * w π ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero hν₀ h₀))
      (Finset.single_le_sum (f := fun π => ν π * w π)
        (fun _ _ => zero_le) (Finset.mem_univ π₀))
  have hCwt : ∑ π, ν π * w π ≠ ⊤ := sum_mul_pmf_ne_top ν _ fun π => PMF.coe_le_one _ ss
  have hsum_eq : ∑ π, ν π * ∏ i, wᵢ i (π i) = ∏ i, ∑ a, μ i a * wᵢ i a := by
    rw [hν_def]
    conv_lhs => arg 2; ext π; rw [pmfPi_apply, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i a => μ i a * wᵢ i a)).symm
  have hCprod0 : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ 0 := by
    rw [hsum_eq]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hCwi0 i)
  have hCprodt : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ ⊤ := by
    rw [hsum_eq]
    exact ne_of_lt (ENNReal.prod_lt_top (fun i _ => (hCwit i).lt_top))
  rw [reweightPMF_eq_of_cross_mul ν w (fun π => ∏ i, wᵢ i (π i))
      hCw0 hCwt hCprod0 hCprodt (pureRun_cross_mul_product hMass hFactor ν n h₀),
    hν_def]
  exact reweightPMF_pmfPi μ wᵢ hCwi0 hCwit

/-- Player `i`'s posterior action factor at a reachable trace in the core
mixed-to-behavioral construction. -/
noncomputable def mixedToBehavioralFactorAt
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (i : ι) (n : Nat) (ss : List σ) (π₀ : ObsModelCore.PureProfile O) :
    PMF (Act i (O.currentObs i (O.projectStates i ss))) :=
  Math.ProbabilityMassFunction.pushforward
    (reweightPMF (μ i)
      (fun πᵢ => pureRun (O.pureStep) O.init n
        (Function.update π₀ i πᵢ) ss))
    (fun πᵢ => πᵢ (O.projectStates i ss))

open Classical in
/-- Core mixed-to-behavioral witness with an explicit fallback at information
states not reached by any pure profile. The run-equality proof only uses the
reachable branch; language frontends can choose a fallback satisfying their
own legality predicates. -/
noncomputable def mixedToBehavioralProfileWithFallback
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (fallback : ObsModelCore.BehavioralProfile O) :
    ObsModelCore.BehavioralProfile O := fun i v_i =>
  if h : ∃ (n : Nat) (ss : List σ) (π₀ : ObsModelCore.PureProfile O),
      O.projectStates i ss = v_i ∧
      pureRun (O.pureStep) O.init n π₀ ss ≠ 0
  then h.choose_spec.choose_spec.choose_spec.1 ▸
    mixedToBehavioralFactorAt (O := O) μ i h.choose h.choose_spec.choose
      h.choose_spec.choose_spec.choose
  else fallback i v_i

/-- A player update to the mixed profile does not change any other player's
posterior action factor in the mixed-to-behavioral construction. -/
theorem mixedToBehavioralFactorAt_update_ne
    (μ : ∀ i, PMF (O.LocalStrategy i))
    {who i : ι} (hne : i ≠ who)
    (τ : PMF (O.LocalStrategy who))
    (n : Nat) (ss : List σ) (π₀ : ObsModelCore.PureProfile O) :
    mixedToBehavioralFactorAt (O := O)
        (Function.update μ who τ) i n ss π₀ =
      mixedToBehavioralFactorAt (O := O) μ i n ss π₀ := by
  simp [mixedToBehavioralFactorAt, Function.update_of_ne hne]

/-- A player update to the mixed profile does not change another player's
behavioral strategy produced by the mixed-to-behavioral construction, provided
the fallback profile is unchanged. -/
theorem mixedToBehavioralProfileWithFallback_update_ne
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (fallback : ObsModelCore.BehavioralProfile O)
    {who i : ι} (hne : i ≠ who)
    (τ : PMF (O.LocalStrategy who))
    (v : O.InfoState i) :
    mixedToBehavioralProfileWithFallback (O := O)
        (Function.update μ who τ) fallback i v =
      mixedToBehavioralProfileWithFallback (O := O) μ fallback i v := by
  classical
  unfold mixedToBehavioralProfileWithFallback
  by_cases h :
      ∃ (n : Nat) (ss : List σ) (π₀ : ObsModelCore.PureProfile O),
        O.projectStates i ss = v ∧
        pureRun (O.pureStep) O.init n π₀ ss ≠ 0
  · rw [dif_pos h, dif_pos h]
    simp [mixedToBehavioralFactorAt_update_ne (O := O) μ hne τ]
  · rw [dif_neg h, dif_neg h]

theorem mixedToBehavioralProfileWithFallback_eq_factorAt
    (hLocal : ∀ i, ActionPosteriorLocal O i)
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (fallback : ObsModelCore.BehavioralProfile O)
    (i : ι) (n : Nat) (ss : List σ) (π₀ : ObsModelCore.PureProfile O)
    (hreach : pureRun (O.pureStep) O.init n π₀ ss ≠ 0) :
    mixedToBehavioralProfileWithFallback (O := O) μ fallback i (O.projectStates i ss) =
      mixedToBehavioralFactorAt (O := O) μ i n ss π₀ := by
  classical
  have factorAt_obs_local :
      ∀ (i : ι) (n₁ n₂ : Nat) (ss₁ ss₂ : List σ)
        (π₁ π₂ : ObsModelCore.PureProfile O),
      O.projectStates i ss₁ = O.projectStates i ss₂ →
      pureRun (O.pureStep) O.init n₁ π₁ ss₁ ≠ 0 →
      pureRun (O.pureStep) O.init n₂ π₂ ss₂ ≠ 0 →
      HEq (mixedToBehavioralFactorAt (O := O) μ i n₁ ss₁ π₁)
        (mixedToBehavioralFactorAt (O := O) μ i n₂ ss₂ π₂) := by
    intro i n₁ n₂ ss₁ ss₂ π₁ π₂ hobs h₁ h₂
    simpa [mixedToBehavioralFactorAt] using hLocal i n₁ n₂ π₁ π₂ ss₁ ss₂ hobs h₁ h₂ (μ i)
  have hexist : ∃ (n' : Nat) (ss' : List σ) (π₀' : ObsModelCore.PureProfile O),
      O.projectStates i ss' = O.projectStates i ss ∧
      pureRun (O.pureStep) O.init n' π₀' ss' ≠ 0 := ⟨n, ss, π₀, rfl, hreach⟩
  change (if h : _ then _ else _) = _
  rw [dif_pos hexist]
  have hps := hexist.choose_spec.choose_spec.choose_spec.1
  have hreach' := hexist.choose_spec.choose_spec.choose_spec.2
  exact eq_of_heq ((fwd_subst_heq (P := fun v => PMF (Act i (O.currentObs i v)))
    hps (mixedToBehavioralFactorAt (O := O) μ i _ _ _)).symm.trans
    (factorAt_obs_local i _ n _ ss _ π₀ hps hreach' hreach))

/-- Core semantic mixed-to-behavioral theorem with an explicit fallback for
unreached information states. -/
theorem mixedToBehavioralProfileWithFallback_runDist [∀ i o, Nonempty (Act i o)]
    (hMass : StepMassInvariant O)
    (hFactor : StepSupportFactorization O)
    (hLocal : ∀ i, ActionPosteriorLocal O i)
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (fallback : ObsModelCore.BehavioralProfile O)
    (k : Nat) :
    O.runDist k (mixedToBehavioralProfileWithFallback (O := O) μ fallback) =
      (pmfPi μ).bind (O.runDistPure k) := by
  classical
  set ν := pmfPi μ with hν_def
  let β := mixedToBehavioralProfileWithFallback (O := O) μ fallback
  suffices hfn : ∀ (n : Nat) (ss : List σ),
      (seqRun (condStep ν (O.pureStep) O.init) O.init n) ss ≠ 0 →
      O.stepDist β ss = condStep ν (O.pureStep) O.init n ss by
    have hrun : ∀ m, O.runDist m β = seqRun (condStep ν (O.pureStep) O.init) O.init m := by
      intro m
      induction m with
      | zero => simp [ObsModelCore.runDist, seqRun]
      | succ n ih =>
          change (O.runDist n β).bind
              (fun ss => Math.ProbabilityMassFunction.pushforward
                (O.stepDist β ss) (fun t => ss ++ [t])) =
            (seqRun (condStep ν (O.pureStep) O.init) O.init n).bind
              (fun ss => Math.ProbabilityMassFunction.pushforward
                (condStep ν (O.pureStep) O.init n ss) (fun t => ss ++ [t]))
          rw [ih]
          ext y
          simp only [PMF.bind_apply]
          apply tsum_congr
          intro ss
          by_cases hss : (seqRun (condStep ν (O.pureStep) O.init) O.init n) ss = 0
          · simp [hss]
          · rw [hfn n ss hss]
    rw [show O.runDistPure k = pureRun (O.pureStep) O.init k from
      funext (O.runDistPure_eq_pureRun k)]
    change O.runDist k β = ν.bind (pureRun (O.pureStep) O.init k)
    rw [hrun, condRun_eq_mixedRun]
  intro n ss hss
  have hreach : ∑ π, ν π * pureRun (O.pureStep) O.init n π ss ≠ 0 := by
    rwa [condRun_eq_mixedRun, PMF.bind_apply, tsum_fintype] at hss
  obtain ⟨π_w, _, hπw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hreach
  have hw_ne : pureRun (O.pureStep) O.init n π_w ss ≠ 0 := right_ne_zero_of_mul hπw
  have hν_ne : ν π_w ≠ 0 := left_ne_zero_of_mul hπw
  suffices haction : O.jointActionDist β ss = O.mixedToMediator ν n ss by
    change O.stepDist β ss = condStep ν (O.pureStep) O.init n ss
    unfold ObsModelCore.stepDist
    rw [haction, mediator_step_eq_condStep]
  rw [mixedToMediator_eq_pmfPi_factor hMass hFactor μ n ss hw_ne (hν_def ▸ hν_ne)]
  simp only [ObsModelCore.jointActionDist]
  congr 1
  funext i
  exact mixedToBehavioralProfileWithFallback_eq_factorAt (O := O) hLocal μ fallback i n ss π_w hw_ne

/-- Core semantic mixed-to-behavioral theorem on `ObsModelCore`. -/
theorem kuhn_mixed_to_behavioral_semantic [∀ i o, Nonempty (Act i o)]
    (hMass : StepMassInvariant O)
    (hFactor : StepSupportFactorization O)
    (hLocal : ∀ i, ActionPosteriorLocal O i)
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (k : Nat) :
    ∃ β : ObsModelCore.BehavioralProfile O,
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) := by
  classical
  refine ⟨mixedToBehavioralProfileWithFallback (O := O) μ
    (fun i v => PMF.pure (Classical.arbitrary _)), ?_⟩
  exact mixedToBehavioralProfileWithFallback_runDist
    (O := O) hMass hFactor hLocal μ _ k

/-- Variant of `mixedToMediator_eq_pmfPi_factor` using run-level support
factorization instead of step-level. -/
theorem mixedToMediator_eq_pmfPi_factor_of_run
    (hMass : StepMassInvariant O)
    (hRun : RunSupportFactorization O)
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (n : Nat) (ss : List σ) {π₀ : ObsModelCore.PureProfile O}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0)
    (hν₀ : (pmfPi μ) π₀ ≠ 0) :
    O.mixedToMediator (pmfPi μ) n ss = pmfPi (fun i =>
      Math.ProbabilityMassFunction.pushforward
        (reweightPMF (μ i)
          (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss))
        (fun πᵢ => πᵢ (O.projectStates i ss))) := by
  set ν := pmfPi μ with hν_def
  set w := fun π => pureRun (O.pureStep) O.init n π ss
  set wᵢ := fun i (πᵢ : O.LocalStrategy i) =>
    pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss
  suffices hprod : reweightPMF ν w = pmfPi (fun i => reweightPMF (μ i) (wᵢ i)) by
    unfold ObsModelCore.mixedToMediator
    rw [hprod]
    simp only [ObsModelCore.jointActionDist, ObsModelCore.pureToBehavioral]
    conv_lhs => arg 2; ext π; rw [pmfPi_pure]
    exact pmfPi_push_coordwise _ (fun i (πᵢ : O.LocalStrategy i) =>
      πᵢ (O.projectStates i ss))
  have hμ_ne : ∀ i, μ i (π₀ i) ≠ 0 := by
    intro i hi; apply hν₀; rw [hν_def, pmfPi_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hwi_ne : ∀ i, wᵢ i (π₀ i) ≠ 0 := by
    intro i
    exact ((hRun n π₀ π₀ h₀).mp h₀) i
  have hCwi0 : ∀ i, ∑ a, μ i a * wᵢ i a ≠ 0 := fun i => by
    apply ne_of_gt
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero (hμ_ne i) (hwi_ne i)))
      (Finset.single_le_sum (f := fun a => μ i a * wᵢ i a)
        (fun _ _ => zero_le) (Finset.mem_univ (π₀ i)))
  have hCwit : ∀ i, ∑ a, μ i a * wᵢ i a ≠ ⊤ := fun i =>
    sum_mul_pmf_ne_top (μ i) _ fun a => PMF.coe_le_one _ ss
  have hCw0 : ∑ π, ν π * w π ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero hν₀ h₀))
      (Finset.single_le_sum (f := fun π => ν π * w π)
        (fun _ _ => zero_le) (Finset.mem_univ π₀))
  have hCwt : ∑ π, ν π * w π ≠ ⊤ := sum_mul_pmf_ne_top ν _ fun π => PMF.coe_le_one _ ss
  have hsum_eq : ∑ π, ν π * ∏ i, wᵢ i (π i) = ∏ i, ∑ a, μ i a * wᵢ i a := by
    rw [hν_def]
    conv_lhs => arg 2; ext π; rw [pmfPi_apply, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i a => μ i a * wᵢ i a)).symm
  have hCprod0 : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ 0 := by
    rw [hsum_eq]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hCwi0 i)
  have hCprodt : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ ⊤ := by
    rw [hsum_eq]
    exact ne_of_lt (ENNReal.prod_lt_top (fun i _ => (hCwit i).lt_top))
  rw [reweightPMF_eq_of_cross_mul ν w (fun π => ∏ i, wᵢ i (π i))
      hCw0 hCwt hCprod0 hCprodt (pureRun_cross_mul_product_of_run hMass hRun ν n h₀),
    hν_def]
  exact reweightPMF_pmfPi μ wᵢ hCwi0 hCwit

/-- Core M→B theorem using the exact run-level semantic hypotheses.

`RunSupportFactorization` is the trace-level support condition actually used
by the cross-multiplication argument. `ActionPosteriorLocal` is the locality
condition that makes the behavioral profile independent of the chosen reaching
witness. -/
theorem kuhn_mixed_to_behavioral_of_runSupport [∀ i o, Nonempty (Act i o)]
    (hMass : StepMassInvariant O)
    (hRun : RunSupportFactorization O)
    (hAPL : ∀ i, ActionPosteriorLocal O i)
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (k : Nat) :
    ∃ β : ObsModelCore.BehavioralProfile O,
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) := by
  classical
  set ν := pmfPi μ with hν_def
  let factorAt (i : ι) (n : Nat) (ss : List σ) (π₀ : ObsModelCore.PureProfile O) :
      PMF (Act i (O.currentObs i (O.projectStates i ss))) :=
    Math.ProbabilityMassFunction.pushforward
      (reweightPMF (μ i)
        (fun πᵢ => pureRun (O.pureStep) O.init n
          (Function.update π₀ i πᵢ) ss))
      (fun πᵢ => πᵢ (O.projectStates i ss))
  have factorAt_obs_local :
      ∀ (i : ι) (n₁ n₂ : Nat) (ss₁ ss₂ : List σ)
        (π₁ π₂ : ObsModelCore.PureProfile O),
      O.projectStates i ss₁ = O.projectStates i ss₂ →
      pureRun (O.pureStep) O.init n₁ π₁ ss₁ ≠ 0 →
      pureRun (O.pureStep) O.init n₂ π₂ ss₂ ≠ 0 →
      HEq (factorAt i n₁ ss₁ π₁) (factorAt i n₂ ss₂ π₂) := by
    intro i n₁ n₂ ss₁ ss₂ π₁ π₂ hobs h₁ h₂
    simpa [factorAt] using hAPL i n₁ n₂ π₁ π₂ ss₁ ss₂ hobs h₁ h₂ (μ i)
  let β : ObsModelCore.BehavioralProfile O := fun i v_i =>
    if h : ∃ (n : Nat) (ss : List σ) (π₀ : ObsModelCore.PureProfile O),
        O.projectStates i ss = v_i ∧
        pureRun (O.pureStep) O.init n π₀ ss ≠ 0
    then h.choose_spec.choose_spec.choose_spec.1 ▸
      factorAt i h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose
    else PMF.pure (Classical.arbitrary _)
  have β_eq : ∀ (i : ι) (n : Nat) (ss : List σ) (π₀ : ObsModelCore.PureProfile O),
      pureRun (O.pureStep) O.init n π₀ ss ≠ 0 →
      β i (O.projectStates i ss) = factorAt i n ss π₀ := by
    intro i n ss π₀ hreach
    have hexist : ∃ (n' : Nat) (ss' : List σ) (π₀' : ObsModelCore.PureProfile O),
        O.projectStates i ss' = O.projectStates i ss ∧
        pureRun (O.pureStep) O.init n' π₀' ss' ≠ 0 := ⟨n, ss, π₀, rfl, hreach⟩
    change (if h : _ then _ else _) = _
    rw [dif_pos hexist]
    have hps := hexist.choose_spec.choose_spec.choose_spec.1
    have hreach' := hexist.choose_spec.choose_spec.choose_spec.2
    exact eq_of_heq ((fwd_subst_heq (P := fun v => PMF (Act i (O.currentObs i v)))
      hps (factorAt i _ _ _)).symm.trans
      (factorAt_obs_local i _ n _ ss _ π₀ hps hreach' hreach))
  refine ⟨β, ?_⟩
  suffices hfn : ∀ (n : Nat) (ss : List σ),
      (seqRun (condStep ν (O.pureStep) O.init) O.init n) ss ≠ 0 →
      O.stepDist β ss = condStep ν (O.pureStep) O.init n ss by
    have hrun : ∀ m, O.runDist m β = seqRun (condStep ν (O.pureStep) O.init) O.init m := by
      intro m
      induction m with
      | zero => simp [ObsModelCore.runDist, seqRun]
      | succ n ih =>
          change (O.runDist n β).bind
              (fun ss => Math.ProbabilityMassFunction.pushforward
                (O.stepDist β ss) (fun t => ss ++ [t])) =
            (seqRun (condStep ν (O.pureStep) O.init) O.init n).bind
              (fun ss => Math.ProbabilityMassFunction.pushforward
                (condStep ν (O.pureStep) O.init n ss) (fun t => ss ++ [t]))
          rw [ih]
          ext y
          simp only [PMF.bind_apply]
          apply tsum_congr
          intro ss
          by_cases hss : (seqRun (condStep ν (O.pureStep) O.init) O.init n) ss = 0
          · simp [hss]
          · rw [hfn n ss hss]
    rw [show O.runDistPure k = pureRun (O.pureStep) O.init k from
      funext (O.runDistPure_eq_pureRun k)]
    change O.runDist k β = ν.bind (pureRun (O.pureStep) O.init k)
    rw [hrun, condRun_eq_mixedRun]
  intro n ss hss
  have hreach : ∑ π, ν π * pureRun (O.pureStep) O.init n π ss ≠ 0 := by
    rwa [condRun_eq_mixedRun, PMF.bind_apply, tsum_fintype] at hss
  obtain ⟨π_w, _, hπw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hreach
  have hw_ne : pureRun (O.pureStep) O.init n π_w ss ≠ 0 := right_ne_zero_of_mul hπw
  have hν_ne : ν π_w ≠ 0 := left_ne_zero_of_mul hπw
  suffices haction : O.jointActionDist β ss = O.mixedToMediator ν n ss by
    change O.stepDist β ss = condStep ν (O.pureStep) O.init n ss
    unfold ObsModelCore.stepDist
    rw [haction, mediator_step_eq_condStep]
  rw [mixedToMediator_eq_pmfPi_factor_of_run hMass hRun μ n ss hw_ne (hν_def ▸ hν_ne)]
  simp only [ObsModelCore.jointActionDist]
  congr 1
  funext i
  exact β_eq i n ss π_w hw_ne

omit [∀ i, Fintype (O.InfoState i)] in
/-- **Unified core M→B theorem**: requires only `StepMassInvariant` and
`ObsLocalFeasibilityFull` for all players. This subsumes the three-condition
`kuhn_mixed_to_behavioral_semantic` because `ObsLocalFeasibilityFull` implies
both `RunSupportFactorization` (for the cross-multiplication identity) and
`ActionPosteriorLocal` (for the behavioral profile well-definedness). -/
theorem kuhn_mixed_to_behavioral_of_obsLocal
    [∀ i, Finite (O.InfoState i)] [∀ i o, Nonempty (Act i o)]
    (hMass : StepMassInvariant O)
    (hOLF : ∀ i, ObsLocalFeasibilityFull O i)
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (k : Nat) :
    ∃ β : ObsModelCore.BehavioralProfile O,
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) := by
  letI : ∀ i, Fintype (O.InfoState i) := fun i => Fintype.ofFinite (O.InfoState i)
  exact kuhn_mixed_to_behavioral_of_runSupport hMass
    (obsLocalFeasibilityFull_toRunSupportFactorization hOLF)
    (fun i =>
      actionPosteriorLocal_of_obsLocalFeasibility hMass i
        (fun n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ _ =>
          hOLF i n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂))
    μ k

end CoreKuhnSemantic

section

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

open Math.PMFProduct

/-- Generic step-independence implies trace-distribution equality on the core model. -/
theorem runDist_eq_of_correlatedStepIndependence
    (O : ObsModelCore ι σ Obs Act)
    (ν : PMF (ObsModelCore.PureProfile O))
    (b : ObsModelCore.BehavioralProfile O)
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
  | zero =>
      simp [ObsModelCore.runDist, ObsModelCore.runDistPure]
  | succ n ih =>
      calc O.runDist (n + 1) b
          = (O.runDist n b).bind (fun ss =>
              pushforward (O.stepDist b ss) (fun t => ss ++ [t])) := by
            simp [ObsModelCore.runDist, Math.TraceRun.traceRun]
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
            simp [ObsModelCore.runDist, ObsModelCore.runDistPure,
              Math.TraceRun.traceRun]

/-- Product correlated steps coincide with independent steps on the core model. -/
theorem stepDistCorr_eq_stepDist_of_product
    (O : ObsModelCore ι σ Obs Act)
    (β : ObsModelCore.BehavioralProfile O) (bc : ObsModelCore.BehavioralProfileCorr O)
    (hprod : ∀ v, bc v = pmfPi (fun i => β i (v i)))
    (ss : List σ) :
    O.stepDistCorr bc ss = O.stepDist β ss := by
  simp only [ObsModelCore.stepDistCorr, ObsModelCore.stepDist, hprod]
  rfl

end

end ObsModelCore
