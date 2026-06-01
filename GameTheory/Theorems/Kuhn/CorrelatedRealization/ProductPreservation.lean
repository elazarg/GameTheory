/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Theorems.Kuhn.ObsModel
import GameTheory.Theorems.Kuhn.MixedToBehavioralCore
import GameTheory.Theorems.Kuhn.CorrelatedRealization.ReachFactor

set_option autoImplicit false

namespace ObsModel

open Math.ProbabilityMassFunction Math.ParameterizedChain Math.TraceRun

attribute [local instance] Fintype.ofFinite

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}
variable {O : ObsModel ι σ Obs Act}


section ProductPreservation

open Math.PMFProduct

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.InfoState i)]

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
    push Not at this; obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
  · by_cases hπ' : pureRun (O.pureStep) O.init n π' ss = 0
    · -- π' not consistent: w(π') = 0 and ∏ wᵢ(π'ᵢ) = 0
      rw [hπ', mul_zero, mul_zero]
      have := mt (pureRun_nonzero_iff_update hPSAR n h₀ π').mpr
        (not_not.mpr hπ')
      push Not at this; obtain ⟨j, hj⟩ := this
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
    ∃ τ : ∀ i, PMF (Act i (O.currentObs i (O.projectStates i ss))),
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
    exact ⟨fun i =>
      Math.ProbabilityMassFunction.pushforward (ρ i)
        (fun πᵢ => πᵢ (O.projectStates i ss)), by
      unfold ObsModel.mixedToMediator ObsModelCore.mixedToMediator
      have hρ' :
          reweightPMF ν (fun π => pureRun O.toCore.pureStep O.toCore.init n π ss) =
            pmfPi ρ := by
        simpa [w, ObsModel.pureStep, ObsModel.init, ObsModel.toCore] using hρ
      have hbind := congrArg (fun q =>
        q.bind (fun π => O.toCore.jointActionDist (O.toCore.pureToBehavioral π) ss)) hρ'
      calc
        ((reweightPMF ν (fun π => pureRun O.toCore.pureStep O.toCore.init n π ss)).bind
            fun π => O.toCore.jointActionDist (O.toCore.pureToBehavioral π) ss)
            =
              (pmfPi ρ).bind
                (fun π => O.toCore.jointActionDist (O.toCore.pureToBehavioral π) ss) := hbind
        _ =
            pmfPi
              (fun i =>
                Math.ProbabilityMassFunction.pushforward (ρ i) fun πᵢ =>
                  πᵢ (O.projectStates i ss)) := by
          simp only [ObsModelCore.jointActionDist, ObsModelCore.pureToBehavioral]
          conv_lhs => arg 2; ext π; rw [pmfPi_pure]
          exact pmfPi_push_coordwise ρ (fun i πᵢ => πᵢ (O.projectStates i ss))⟩
  -- Case split on mass condition for reweightPMF
  by_cases hmass : (∑ π, ν π * w π) = 0 ∨ (∑ π, ν π * w π) = ⊤
  · -- Degenerate: reweightPMF falls back to ν = pmfPi μ
    exact ⟨μ, by rw [reweightPMF_degenerate _ _ hmass, hν_def]⟩
  · -- Non-degenerate: use cross-multiplication to factor the reweighted PMF
    push Not at hmass; obtain ⟨hCw0, hCwt⟩ := hmass
    -- Extract a witness with nonzero mass
    have ⟨π_w, hπw⟩ : ∃ π, ν π * w π ≠ 0 := by
      by_contra hall; push Not at hall
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
    have hCwi0 : ∀ i, ∑ a, μ i a * wᵢ i a ≠ 0 := fun i =>
      sum_mul_pmf_ne_zero_of_ne_zero (μ i) (wᵢ i) (hμ_ne i) (hwi_ne i)
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
variable [∀ i, Fintype (O.InfoState i)]

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
  · push Not at hmass; obtain ⟨hCw0, hCwt⟩ := hmass
    -- Witness with nonzero mass
    have ⟨π_w, hπw⟩ : ∃ π, ν π * w π ≠ 0 := by
      by_contra hall; push Not at hall
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
    have hCwi0 : ∀ i, ∑ a, μ i a * wᵢ i a ≠ 0 := fun i =>
      sum_mul_pmf_ne_zero_of_ne_zero (μ i) (wᵢ i) (hμ_ne i) (hwi_ne i)
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

end ObsModel
