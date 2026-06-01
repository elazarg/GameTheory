/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Theorems.Kuhn.KuhnModel
import Math.PMFProduct

set_option autoImplicit false

namespace ObsModelCore

open Math.PMFProduct Math.ProbabilityMassFunction
open Math.ParameterizedChain Math.TraceRun

attribute [local instance] Fintype.ofFinite

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}
variable {O : ObsModelCore ι σ Obs Act}

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
      exact eq_of_heq ((rec_heq_of_heq _ HEq.rfl).symm.trans
        ((heq_of_eq hi).trans (rec_heq_of_heq _ HEq.rfl)))
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

/-- **Chaining lemma**: If `ObsLocalFeasibilityFull` holds for all players and
all single-player updates of the witness reach `ss`, then any multi-player
update also reaches `ss`. -/
private theorem replaceOn_reach_of_obsLocal
    (hOLF : ∀ i, ObsLocalFeasibilityFull O i)
    {n : Nat} {ss : List σ} {π₀ π : ObsModelCore.PureProfile O}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0)
    (hall : ∀ i, pureRun (O.pureStep) O.init n
      (Function.update π₀ i (π i)) ss ≠ 0)
    (S : Finset ι) :
    pureRun (O.pureStep) O.init n (replaceOn (A := O.LocalStrategy) S π₀ π) ss ≠ 0 := by
  induction S using Finset.induction with
  | empty => rwa [replaceOn_empty]
  | insert j S hj ih =>
      rw [replaceOn_insert (A := O.LocalStrategy) S j hj π₀ π]
      exact (hOLF j n n π₀ (replaceOn (A := O.LocalStrategy) S π₀ π)
        ss ss rfl h₀ ih (π j)).mp (hall j)

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
    have := replaceOn_reach_of_obsLocal hOLF h₀ hall Finset.univ
    rwa [replaceOn_univ_snd] at this

end ObsLocalKuhn

end ObsModelCore
