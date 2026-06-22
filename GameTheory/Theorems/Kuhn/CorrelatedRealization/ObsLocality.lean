/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Theorems.Kuhn.ObsModel
import GameTheory.Theorems.Kuhn.MixedToBehavioralCore
import GameTheory.Theorems.Kuhn.CorrelatedRealization.ProductPreservation

set_option autoImplicit false

namespace ObsModel

open Math.ProbabilityMassFunction Math.ParameterizedChain Math.TraceRun

attribute [local instance] Fintype.ofFinite

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}
variable {O : ObsModel ι σ Obs Act}


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
              (rec_heq_of_heq
                (C := fun v => Act i (O.currentObs i v))
                (x := π₀' i (O.projectStates i p₂))
                (y := π₀' i (O.projectStates i p₂))
                hobs_p.symm HEq.rfl))))
        · rw [Function.update_of_ne hij]
      · intro j; by_cases hij : j = i
        · rw [hij, Function.update_self]
          have h_i := h i; rw [Function.update_self] at h_i
          -- h_i : πᵢ(p₂) = π₀'(p₂). Want: πᵢ(p₁) = π₀(p₁)
          -- Chain: πᵢ(p₁) ≅ πᵢ(p₂) = π₀'(p₂) ≅ hobs_p▸π₀'(p₂) = π₀(p₁)
          exact eq_of_heq ((congr_arg_heq πᵢ hobs_p).trans
            (heq_of_eq h_i |>.trans
              ((rec_heq_of_heq
                (C := fun v => Act i (O.currentObs i v))
                (x := π₀' i (O.projectStates i p₂))
                (y := π₀' i (O.projectStates i p₂))
                hobs_p.symm HEq.rfl).symm |>.trans
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
      (fun _ _ p₂ _ _ hobs_p _ _ _ _ _ => by
        apply eq_of_heq
        exact (congr_arg_heq (π₀ i) hobs_p).trans
          ((rec_heq_of_heq
            (C := fun v => Act i (O.currentObs i v))
            (x := π₀ i (O.projectStates i p₂))
            (y := π₀ i (O.projectStates i p₂))
            hobs_p.symm HEq.rfl).symm)) πᵢ

open Classical in
/-- Generic obs-locality of `reweightPMF`, parameterized by a support-equivalence
hypothesis `hiff` between two weight functions `w₁` and `w₂`. Under PSAR,
nonzero weights are constant (`pureRun_const_of_psar`), so the cross-multiplication
identity holds and `reweightPMF_eq_of_cross_mul` closes the goal.

All concrete variants (`reweightPMF_update_obs_local`, `_pspr`, `_player`) are
one-line corollaries that supply the appropriate `hiff`. -/
theorem reweightPMF_update_obs_local_of
    [∀ i, Fintype (O.InfoState i)]
    (hPSAR : PerStepActionRecall O) (n₁ n₂ : Nat)
    (i : ι) (b_i : PMF (O.LocalStrategy i))
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List σ}
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
        · have eq1 : w₁ πᵢ = pureRun (O.pureStep) O.init n₁ π₀ ss₁ :=
            pureRun_const_of_psar hPSAR n₁ hw h₁
          have eq2 : w₂ πᵢ = pureRun (O.pureStep) O.init n₂ π₀' ss₂ :=
            pureRun_const_of_psar hPSAR n₂ ((hiff πᵢ).mp hw) h₂
          have eq3 : w₁ πᵢ' = pureRun (O.pureStep) O.init n₁ π₀ ss₁ :=
            pureRun_const_of_psar hPSAR n₁ hw' h₁
          have eq4 : w₂ πᵢ' = pureRun (O.pureStep) O.init n₂ π₀' ss₂ :=
            pureRun_const_of_psar hPSAR n₂ ((hiff πᵢ').mp hw') h₂
          rw [eq1, eq2, eq3, eq4]; ring)

open Classical in
/-- Under PSAR, the per-player reweighted PMF depends on `ss` only through
`projectStates i ss`. Corollary of `reweightPMF_update_obs_local_of`. -/
theorem reweightPMF_update_obs_local
    [∀ i, Fintype (O.InfoState i)]
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
  reweightPMF_update_obs_local_of hPSAR n n i b_i h₁ h₂
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

open Classical in
/-- Under PSPR, obs-locality with **different** reference profiles.
Corollary of `reweightPMF_update_obs_local_of` with `hiff` from
`pureRun_update_obs_local_pspr`. -/
theorem reweightPMF_update_obs_local_pspr
    [∀ i, Fintype (O.InfoState i)]
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
  reweightPMF_update_obs_local_of (hPSPR.toAction) n n i b_i h₁ h₂
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

open Classical in
/-- Under PSAR + `PlayerStepRecall O i`, obs-locality with different reference profiles.
Corollary of `reweightPMF_update_obs_local_of` with `hiff` from
`pureRun_update_obs_local_player`. -/
theorem reweightPMF_update_obs_local_player
    [∀ i, Fintype (O.InfoState i)]
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
  reweightPMF_update_obs_local_of hPSAR n n i b_i h₁ h₂
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
  simpa [ObsModel.stepDistCorr, ObsModel.stepDist, ObsModel.toCore] using
    (ObsModelCore.stepDistCorr_eq_stepDist_of_product (O := O.toCore) β bc hprod ss)

/-- Independent behavioral realization from correlated one: if a correlated profile
always outputs products with observation-local factors, the independent profile
produces the same trace distribution. -/
theorem runDist_eq_of_corrProduct
    (β : BehavioralProfile O) (bc : BehavioralProfileCorr O)
    (hprod : ∀ v, bc v = pmfPi (fun i => β i (v i)))
    (k : Nat) :
    O.runDist k β =
      seqRun (fun _ ss => O.stepDistCorr bc ss) O.init k := by
  -- runDist k β = traceRun (stepDist β) O.init k (by definition);
  -- seqRun on a step-index-independent step matches traceRun shape.
  have hmatch : O.runDist k β =
      seqRun (fun _ ss => O.stepDist β ss) O.init k := by
    induction k with
    | zero => rfl
    | succ n ih =>
      change (O.runDist n β).bind _ = _
      rw [ih]
      rfl
  rw [hmatch]
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
variable [∀ i, Fintype (O.InfoState i)]

open Math.PMFProduct

open Classical in
/-- Non-existential version of `mediator_product_of_product`:
the mediator output equals the product of per-player factors. -/
private theorem mixedToMediator_eq_pmfPi_factor
    (hPSAR : PerStepActionRecall O) (μ : ∀ i, PMF (O.LocalStrategy i))
    (n : Nat) (ss : List σ) {π₀ : PureProfile O}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0)
    (hν₀ : (pmfPi μ) π₀ ≠ 0) :
    O.mixedToMediator (pmfPi μ) n ss = pmfPi (fun i =>
      Math.ProbabilityMassFunction.pushforward
        (reweightPMF (μ i)
          (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss))
        (fun πᵢ => πᵢ (O.projectStates i ss))) := by
  letI : ∀ i, Fintype (O.toCore.InfoState i) := by
    intro i
    simpa [ObsModel.toCore, ObsModelCore.InfoState] using
      (inferInstance : Fintype (O.InfoState i))
  have hDet : ObsModelCore.StepActionDeterminism O.toCore := by
    intro s t a a' hs hs'
    exact funext fun i => hPSAR s s t t a a' hs hs' (fun _ => rfl) (fun _ => rfl) i
  change O.toCore.mixedToMediator (pmfPi μ) n ss = pmfPi (fun i =>
    Math.ProbabilityMassFunction.pushforward
      (reweightPMF (μ i)
        (fun πᵢ => pureRun O.toCore.pureStep O.toCore.init n
          (Function.update π₀ i πᵢ) ss))
      (fun πᵢ => πᵢ (O.toCore.projectStates i ss)))
  exact ObsModelCore.mixedToMediator_eq_pmfPi_factor
    (O := O.toCore) hDet.toMassInvariant hDet.toSupportFactorization μ n ss h₀ hν₀

end KuhnMtoB

end ObsModel
