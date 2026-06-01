/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Theorems.Kuhn.KuhnModel
import Math.PMFProduct
import GameTheory.Theorems.Kuhn.MixedToBehavioralCore.ReachFactor

set_option autoImplicit false

namespace ObsModelCore

open Math.PMFProduct Math.ProbabilityMassFunction
open Math.ParameterizedChain Math.TraceRun

attribute [local instance] Fintype.ofFinite

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}
variable {O : ObsModelCore ι σ Obs Act}


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
  have hsum_zero_iff :
      (∑ πᵢ, b_i πᵢ * w₁ πᵢ) = 0 ↔ (∑ πᵢ, b_i πᵢ * w₂ πᵢ) = 0 :=
    sum_mul_pmf_eq_zero_iff_of_weight_ne_zero_iff b_i hiff
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
  · exact bind_heq_of_eq
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
  have hCwi0 : ∀ i, ∑ a, μ i a * wᵢ i a ≠ 0 := fun i =>
    sum_mul_pmf_ne_zero_of_ne_zero (μ i) (wᵢ i) (hμ_ne i) (hwi_ne i)
  have hCwit : ∀ i, ∑ a, μ i a * wᵢ i a ≠ ⊤ := fun i =>
    sum_mul_pmf_ne_top (μ i) _ fun a => PMF.coe_le_one _ ss
  have hCw0 : ∑ π, ν π * w π ≠ 0 :=
    sum_mul_pmf_ne_zero_of_ne_zero ν w hν₀ h₀
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

/-- The posterior action factor in the mixed-to-behavioral construction depends
only on the mixed strategy of the queried player. -/
theorem mixedToBehavioralFactorAt_congr_coord
    {μ μ' : ∀ i, PMF (O.LocalStrategy i)}
    {i : ι} (hμ : μ i = μ' i)
    (n : Nat) (ss : List σ) (π₀ : ObsModelCore.PureProfile O) :
    mixedToBehavioralFactorAt (O := O) μ i n ss π₀ =
      mixedToBehavioralFactorAt (O := O) μ' i n ss π₀ := by
  simp [mixedToBehavioralFactorAt, hμ]

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
  exact (mixedToBehavioralFactorAt_congr_coord (O := O)
    (μ := μ) (μ' := Function.update μ who τ)
    (i := i) (by simp [Function.update_of_ne hne]) n ss π₀).symm

/-- The mixed-to-behavioral profile with fixed fallback depends on a player's
own mixed strategy only at that player's behavioral strategy. -/
theorem mixedToBehavioralProfileWithFallback_congr_coord
    {μ μ' : ∀ i, PMF (O.LocalStrategy i)}
    (fallback : ObsModelCore.BehavioralProfile O)
    {i : ι} (hμ : μ i = μ' i)
    (v : O.InfoState i) :
    mixedToBehavioralProfileWithFallback (O := O) μ fallback i v =
      mixedToBehavioralProfileWithFallback (O := O) μ' fallback i v := by
  classical
  unfold mixedToBehavioralProfileWithFallback
  by_cases h : ∃ (n : Nat) (ss : List σ) (π₀ : ObsModelCore.PureProfile O),
      O.projectStates i ss = v ∧
      pureRun (O.pureStep) O.init n π₀ ss ≠ 0
  · rw [dif_pos h, dif_pos h]
    exact congrArg (fun x => h.choose_spec.choose_spec.choose_spec.1 ▸ x)
      (mixedToBehavioralFactorAt_congr_coord (O := O) (μ := μ) (μ' := μ')
        hμ h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose)
  · rw [dif_neg h, dif_neg h]

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
  exact (mixedToBehavioralProfileWithFallback_congr_coord (O := O)
    (μ := μ) (μ' := Function.update μ who τ) fallback
    (i := i) (by simp [Function.update_of_ne hne]) v).symm

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
  have htransport :
      HEq (hps ▸ mixedToBehavioralFactorAt (O := O) μ i
          hexist.choose hexist.choose_spec.choose
          hexist.choose_spec.choose_spec.choose)
        (mixedToBehavioralFactorAt (O := O) μ i
          hexist.choose hexist.choose_spec.choose
          hexist.choose_spec.choose_spec.choose) := by
    exact eqRec_heq_iff_heq.mpr HEq.rfl
  exact eq_of_heq (htransport.trans
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
  have hCwi0 : ∀ i, ∑ a, μ i a * wᵢ i a ≠ 0 := fun i =>
    sum_mul_pmf_ne_zero_of_ne_zero (μ i) (wᵢ i) (hμ_ne i) (hwi_ne i)
  have hCwit : ∀ i, ∑ a, μ i a * wᵢ i a ≠ ⊤ := fun i =>
    sum_mul_pmf_ne_top (μ i) _ fun a => PMF.coe_le_one _ ss
  have hCw0 : ∑ π, ν π * w π ≠ 0 :=
    sum_mul_pmf_ne_zero_of_ne_zero ν w hν₀ h₀
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
    have htransport :
        HEq (hps ▸ factorAt i hexist.choose hexist.choose_spec.choose
            hexist.choose_spec.choose_spec.choose)
          (factorAt i hexist.choose hexist.choose_spec.choose
            hexist.choose_spec.choose_spec.choose) := by
      exact eqRec_heq_iff_heq.mpr HEq.rfl
    exact eq_of_heq (htransport.trans
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
