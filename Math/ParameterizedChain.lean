/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ProbabilityMassFunction
import Math.PMFProduct
import Math.TraceRun

/-! # Tower property for parameterized Markov chains

Given a distribution `ν` over parameters `P` and a parameterized step function
`step : P → List S → PMF S`, we show that the averaged ("mixed") run can be
realized by a single non-parameterized chain whose transitions condition `ν`
on the observed trace at each step.

This is the abstract core of Kuhn's theorem: conditioning distributes over
sequential Kleisli composition.
-/

set_option autoImplicit false

namespace Math.ParameterizedChain

open Math.ProbabilityMassFunction

attribute [local instance] Fintype.ofFinite

variable {P S : Type*}

/-- Run a parameterized Markov chain for `k` steps from initial state `s₀`,
recording the full state trace. Defined as a parameterized wrapper around
`Math.TraceRun.traceRun`. -/
noncomputable def pureRun (step : P → List S → PMF S) (s₀ : S)
    (k : Nat) (π : P) : PMF (List S) :=
  Math.TraceRun.traceRun (step π) s₀ k

theorem append_singleton_inj {α : Type*} {as bs : List α} {a b : α}
    (h : as ++ [a] = bs ++ [b]) : as = bs ∧ a = b :=
  Math.TraceRun.append_singleton_inj h

/-- At successor step, `pureRun` decomposes as prefix reach times one-step transition. -/
theorem pureRun_succ_append (step : P → List S → PMF S) (s₀ : S)
    (k : Nat) (π : P) (ss : List S) (t : S) :
    pureRun step s₀ (k + 1) π (ss ++ [t]) =
      pureRun step s₀ k π ss * step π ss t :=
  Math.TraceRun.traceRun_succ_append (step π) s₀ k ss t

/-- `pureRun` at successor step assigns zero probability to the empty trace. -/
theorem pureRun_succ_nil (step : P → List S → PMF S) (s₀ : S) (k : Nat) (π : P) :
    pureRun step s₀ (k + 1) π [] = 0 :=
  Math.TraceRun.traceRun_succ_nil (step π) s₀ k

/-- Traces with nonzero `pureRun` probability have length exactly `n + 1`. -/
theorem pureRun_length (step : P → List S → PMF S) (s₀ : S)
    (n : Nat) (π : P) (ss : List S)
    (h : pureRun step s₀ n π ss ≠ 0) : ss.length = n + 1 :=
  Math.TraceRun.traceRun_length (step π) s₀ n ss h

/-- On a nonzero-probability trace, each per-step transition has nonzero probability. -/
theorem pureRun_step_nonzero (step : P → List S → PMF S) (s₀ : S)
    (k : Nat) (π : P) (ss : List S)
    (h : pureRun step s₀ k π ss ≠ 0)
    (j : Nat) (hj : j + 1 < ss.length) :
    step π (ss.take (j + 1)) ss[j + 1] ≠ 0 :=
  Math.TraceRun.traceRun_step_nonzero (step π) s₀ k ss h j hj

/-- Every time-prefix of a supported parameterized trace is itself supported at
the corresponding shorter horizon. -/
theorem pureRun_take_nonzero (step : P → List S → PMF S) (s₀ : S)
    (k : Nat) (π : P) (ss : List S)
    (h : pureRun step s₀ k π ss ≠ 0)
    (m : Nat) (hm : m ≤ k) :
    pureRun step s₀ m π (ss.take (m + 1)) ≠ 0 := by
  induction k generalizing ss m with
  | zero =>
      have hm0 : m = 0 := by omega
      subst hm0
      have hss : ss = [s₀] := by
        by_contra hne
        exact h (by simp [pureRun, Math.TraceRun.traceRun, PMF.pure_apply, hne])
      simp [hss, pureRun, Math.TraceRun.traceRun]
  | succ k ih =>
      rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
      · exact absurd (pureRun_succ_nil step s₀ k π) h
      rw [List.concat_eq_append] at h ⊢
      by_cases hm_last : m = k + 1
      · subst hm_last
        have hlen := pureRun_length step s₀ (k + 1) π (p ++ [t]) h
        have htake : (p ++ [t]).take (k + 1 + 1) = p ++ [t] := by
          rw [show k + 1 + 1 = (p ++ [t]).length by omega]
          exact List.take_length
        simpa [htake] using h
      · have hmle : m ≤ k := by omega
        have hp : pureRun step s₀ k π p ≠ 0 := by
          exact left_ne_zero_of_mul (pureRun_succ_append step s₀ k π p t ▸ h)
        have hplen : p.length = k + 1 :=
          pureRun_length step s₀ k π p hp
        have htake : (p ++ [t]).take (m + 1) = p.take (m + 1) := by
          rw [List.take_append_of_le_length]
          omega
        simpa [htake] using ih p hp m hmle

/-- Run a Markov chain with step-index-dependent transition functions. -/
noncomputable def seqRun (steps : Nat → List S → PMF S) (s₀ : S)
    (k : Nat) : PMF (List S) :=
  Nat.rec (PMF.pure [s₀])
    (fun n rec =>
      rec.bind (fun ss =>
        pushforward (steps n ss) (fun t => ss ++ [t])))
    k

section ReweightPMF

variable [Fintype P]

open Classical in
/-- Reweight a finitely-supported PMF by an `ENNReal` weight function.
Falls back to `ν` when the total weight is zero or infinite. -/
noncomputable def reweightPMF (ν : PMF P) (w : P → ENNReal) : PMF P :=
  let C := ∑ π : P, ν π * w π
  if h : C = 0 ∨ C = ⊤ then ν
  else
    have hne0 : C ≠ 0 := fun h0 => h (Or.inl h0)
    have hneTop : C ≠ ⊤ := fun ht => h (Or.inr ht)
    PMF.ofFintype (fun π => ν π * w π / C) (by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      exact ENNReal.mul_inv_cancel hne0 hneTop)

open Classical in
theorem reweightPMF_apply (ν : PMF P) (w : P → ENNReal) (π : P)
    (hC : ∑ π' : P, ν π' * w π' ≠ 0)
    (hCtop : ∑ π' : P, ν π' * w π' ≠ ⊤) :
    reweightPMF ν w π = ν π * w π / (∑ π' : P, ν π' * w π') := by
  unfold reweightPMF
  dsimp only
  split_ifs with h
  · exact absurd h (not_or.mpr ⟨hC, hCtop⟩)
  · exact PMF.ofFintype_apply _ π

open Classical in
theorem reweightPMF_support_subset (ν : PMF P) (w : P → ENNReal) :
    (reweightPMF ν w).support ⊆ ν.support := by
  intro π hπ
  rw [PMF.mem_support_iff] at hπ ⊢
  intro hν
  unfold reweightPMF at hπ
  dsimp only at hπ
  split_ifs at hπ with hdeg
  · exact hπ hν
  · apply hπ
    rw [PMF.ofFintype_apply, hν]
    simp

theorem reweightPMF_fallback (ν : PMF P) (w : P → ENNReal)
    (hC : ∑ π : P, ν π * w π = 0) :
    reweightPMF ν w = ν := by
  unfold reweightPMF
  dsimp only
  split_ifs with h
  · rfl
  · exact absurd (Or.inl hC) h

theorem reweightPMF_degenerate (ν : PMF P) (w : P → ENNReal)
    (hC : (∑ π : P, ν π * w π) = 0 ∨ (∑ π : P, ν π * w π) = ⊤) :
    reweightPMF ν w = ν := by
  unfold reweightPMF
  exact dif_pos hC

open Classical in
/-- Scaling the weight function by a finite nonzero constant doesn't change
the reweighted PMF (the constant cancels in the normalization). -/
theorem reweightPMF_scale (ν : PMF P) (w : P → ENNReal) (c : ENNReal)
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    reweightPMF ν (fun π => c * w π) = reweightPMF ν w := by
  have hfact : ∀ π', ν π' * (c * w π') = c * (ν π' * w π') := fun π' => by ring
  have hCeq : ∑ π' : P, ν π' * (c * w π') = c * ∑ π' : P, ν π' * w π' := by
    simp_rw [hfact, ← Finset.mul_sum]
  by_cases hC0 : ∑ π' : P, ν π' * w π' = 0
  · exact (reweightPMF_degenerate ν _ (Or.inl (by rw [hCeq, hC0, mul_zero]))).trans
      (reweightPMF_degenerate ν _ (Or.inl hC0)).symm
  by_cases hCtop : ∑ π' : P, ν π' * w π' = ⊤
  · exact (reweightPMF_degenerate ν _ (Or.inr (by rw [hCeq, hCtop, ENNReal.mul_top hc0]))).trans
      (reweightPMF_degenerate ν _ (Or.inr hCtop)).symm
  · -- Non-degenerate case: both sums are finite and positive
    have hC0' : ∑ π' : P, ν π' * (c * w π') ≠ 0 := by
      rw [hCeq]; exact mul_ne_zero hc0 hC0
    have hCtop' : ∑ π' : P, ν π' * (c * w π') ≠ ⊤ := by
      rw [hCeq]; exact ENNReal.mul_ne_top hctop.lt_top.ne hCtop
    ext π
    rw [reweightPMF_apply ν _ π hC0' hCtop', reweightPMF_apply ν _ π hC0 hCtop]
    rw [show ν π * (c * w π) = c * (ν π * w π) from by ring, hCeq]
    exact ENNReal.mul_div_mul_left _ _ hc0 hctop

open Classical in
/-- If weights satisfy a cross-multiplication identity
`∀ π, w₁ π * C₂ = w₂ π * C₁`, the reweighted PMFs are equal. -/
theorem reweightPMF_eq_of_cross_mul (ν : PMF P) (w₁ w₂ : P → ENNReal)
    (hC₁ : ∑ π' : P, ν π' * w₁ π' ≠ 0)
    (hC₁top : ∑ π' : P, ν π' * w₁ π' ≠ ⊤)
    (hC₂ : ∑ π' : P, ν π' * w₂ π' ≠ 0)
    (hC₂top : ∑ π' : P, ν π' * w₂ π' ≠ ⊤)
    (hcross : ∀ π, w₁ π * (∑ π' : P, ν π' * w₂ π') =
                    w₂ π * (∑ π' : P, ν π' * w₁ π')) :
    reweightPMF ν w₁ = reweightPMF ν w₂ := by
  ext π
  rw [reweightPMF_apply ν w₁ π hC₁ hC₁top, reweightPMF_apply ν w₂ π hC₂ hC₂top]
  rw [ENNReal.div_eq_div_iff hC₂ hC₂top hC₁ hC₁top]
  calc (∑ π', ν π' * w₂ π') * (ν π * w₁ π)
      = ν π * (w₁ π * (∑ π', ν π' * w₂ π')) := by ac_rfl
    _ = ν π * (w₂ π * (∑ π', ν π' * w₁ π')) := by rw [hcross π]
    _ = (∑ π', ν π' * w₁ π') * (ν π * w₂ π) := by ac_rfl

end ReweightPMF

section ReweightProduct

open Math.PMFProduct

variable {ι : Type*} {A : ι → Type*}
  [Fintype ι] [DecidableEq ι] [∀ i, Fintype (A i)]

open Classical in
/-- Reweighting a product PMF by product weights gives a product of reweighted
marginals. This is the multiplicative Fubini identity for `reweightPMF`. -/
theorem reweightPMF_pmfPi
    (σ : ∀ i, PMF (A i)) (w : ∀ i, A i → ENNReal)
    (hC : ∀ i, ∑ a, σ i a * w i a ≠ 0)
    (hCt : ∀ i, ∑ a, σ i a * w i a ≠ ⊤) :
    reweightPMF (pmfPi σ) (fun f => ∏ i, w i (f i)) =
      pmfPi (fun i => reweightPMF (σ i) (w i)) := by
  -- Total weight factorization via Fubini
  have hfub : ∑ f : ∀ i, A i, (pmfPi σ) f * ∏ i, w i (f i) =
      ∏ i, ∑ a, σ i a * w i a := by
    simp only [pmfPi_apply, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i a => σ i a * w i a)).symm
  have hCL : ∑ f, (pmfPi σ) f * ∏ i, w i (f i) ≠ 0 := by
    rw [hfub]; exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hC i))
  have hCLt : ∑ f, (pmfPi σ) f * ∏ i, w i (f i) ≠ ⊤ := by
    rw [hfub]; exact ne_of_lt (ENNReal.prod_lt_top (fun i _ => (hCt i).lt_top))
  ext f
  rw [reweightPMF_apply _ _ _ hCL hCLt, pmfPi_apply, pmfPi_apply, hfub]
  simp_rw [reweightPMF_apply _ _ _ (hC _) (hCt _)]
  -- Goal: (∏ σ * ∏ w) / ∏ C = ∏ (σ * w / C)
  rw [← Finset.prod_mul_distrib]
  -- Goal: ∏ (σ * w) / ∏ C = ∏ (σ * w / C)
  simp only [ENNReal.div_eq_inv_mul]
  -- Goal: (∏ C)⁻¹ * ∏ (σ * w) = ∏ (C⁻¹ * (σ * w))
  conv_lhs =>
    rw [ENNReal.prod_inv_distrib (by
      intro i _ j _ _; exact Or.inl (hC i))]
  rw [← Finset.prod_mul_distrib]

open Classical in
/-- Reweighting a product distribution by a scalar weight that ignores
coordinate `j` preserves the `j`-marginal.

This is the product-measure independence calculation used when a reach event
depends only on the other coordinates: conditioning/reweighting on that event
does not change the unused coordinate's law. -/
theorem reweightPMF_pmfPi_push_coord_of_ignores
    (σ : ∀ i, PMF (A i)) (j : ι)
    (w : (∀ i, A i) → ENNReal)
    (hign : Math.PMFProduct.Ignores (A := A) j w)
    (hC0 : ∑ s, pmfPi (A := A) σ s * w s ≠ 0)
    (hCtop : ∑ s, pmfPi (A := A) σ s * w s ≠ ⊤) :
    Math.ProbabilityMassFunction.pushforward
        (reweightPMF (pmfPi (A := A) σ) w) (fun s => s j) =
      σ j := by
  classical
  ext a
  set C : ENNReal := ∑ s, pmfPi (A := A) σ s * w s
  have hC0' : C ≠ 0 := by simpa [C] using hC0
  have hCtop' : C ≠ ⊤ := by simpa [C] using hCtop
  have hf :
      ∀ q, q ∉ ({j} : Finset ι) →
        Math.PMFProduct.Ignores (A := A) q
          (fun s : (∀ i, A i) => if s j = a then (1 : ENNReal) else 0) := by
    intro q hq s b
    have hqj : q ≠ j := by
      intro h
      exact hq (by simp [h])
    have hneq : j ≠ q := Ne.symm hqj
    simp [Function.update, hneq]
  have hg :
      ∀ q, q ∈ ({j} : Finset ι) →
        Math.PMFProduct.Ignores (A := A) q w := by
    intro q hq
    have hqj : q = j := by simpa using hq
    subst q
    exact hign
  have hindep :
      (∑ s : (∀ i, A i),
        pmfPi (A := A) σ s *
          (((if s j = a then (1 : ENNReal) else 0) * w s))) =
        (∑ s : (∀ i, A i),
          pmfPi (A := A) σ s *
            (if s j = a then (1 : ENNReal) else 0)) * C := by
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using
      Math.PMFProduct.pmfPi_expect_indep
        (A := A) σ
        (fun s : (∀ i, A i) => if s j = a then (1 : ENNReal) else 0)
        w ({j} : Finset ι) hf hg
  have hcoord :
      (∑ s : (∀ i, A i),
        pmfPi (A := A) σ s *
          (if s j = a then (1 : ENNReal) else 0)) = σ j a := by
    simpa [mul_ite, mul_one, mul_zero] using
      Math.PMFProduct.pmfPi_coord_mass (A := A) σ j a
  rw [Math.ProbabilityMassFunction.pushforward, PMF.map_apply]
  simp only [tsum_fintype]
  simp_rw [@eq_comm _ a]
  calc
    (∑ s : (∀ i, A i),
        if s j = a then reweightPMF (pmfPi (A := A) σ) w s else 0)
        =
      (∑ s : (∀ i, A i),
        pmfPi (A := A) σ s *
          (((if s j = a then (1 : ENNReal) else 0) * w s))) * C⁻¹ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro s _
        rw [reweightPMF_apply (pmfPi (A := A) σ) w s hC0 hCtop]
        by_cases hs : s j = a
        · simp [hs, C, div_eq_mul_inv, mul_assoc, mul_comm]
        · simp [hs]
    _ = (σ j a * C) * C⁻¹ := by rw [hindep, hcoord]
    _ = σ j a := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hC0' hCtop', mul_one]

open Classical in
/-- Reweighting a product distribution by a scalar weight that ignores
coordinate `j` preserves the `j`-marginal, including the zero-total-weight
fallback case of `reweightPMF`. -/
theorem reweightPMF_pmfPi_push_coord_of_ignores'
    (σ : ∀ i, PMF (A i)) (j : ι)
    (w : (∀ i, A i) → ENNReal)
    (hign : Math.PMFProduct.Ignores (A := A) j w)
    (hCtop : ∑ s, pmfPi (A := A) σ s * w s ≠ ⊤) :
    Math.ProbabilityMassFunction.pushforward
        (reweightPMF (pmfPi (A := A) σ) w) (fun s => s j) =
      σ j := by
  classical
  by_cases hC0 : ∑ s, pmfPi (A := A) σ s * w s = 0
  · rw [reweightPMF_degenerate _ _ (Or.inl hC0)]
    exact Math.PMFProduct.pmfPi_push_coord (A := A) σ j
  · exact reweightPMF_pmfPi_push_coord_of_ignores
      (A := A) σ j w hign hC0 hCtop

end ReweightProduct

/-- Conditioned step at depth `n`: reweight `ν` by the probability of each
parameter reaching state trace `ss` after `n` steps, then average the
parameterized step function. -/
noncomputable def condStep [Fintype P] (ν : PMF P)
    (step : P → List S → PMF S) (s₀ : S) (n : Nat) (ss : List S) : PMF S :=
  (reweightPMF ν (fun π => (pureRun step s₀ n π) ss)).bind (fun π => step π ss)

section Tower

variable [Fintype P]

open Classical in
/-- Core weighted identity: the total weight times the conditioned step
equals the parameter-weighted sum of pure steps. -/
theorem condStep_weighted_eq (ν : PMF P) (step : P → List S → PMF S)
    (s₀ : S) (n : Nat) (ss : List S) (y : List S) :
    let C := ∑ π : P, ν π * (pureRun step s₀ n π) ss
    C * (pushforward (condStep ν step s₀ n ss) (fun t => ss ++ [t])) y =
      ∑ π : P, ν π * ((pureRun step s₀ n π) ss *
        (pushforward (step π ss) (fun t => ss ++ [t])) y) := by
  classical
  simp only
  by_cases hC0 : (∑ π : P, ν π * (pureRun step s₀ n π) ss) = 0
  · -- All weights are zero ⟹ both sides zero
    have hterm : ∀ π, ν π * (pureRun step s₀ n π) ss = 0 :=
      fun π => (ENNReal.tsum_eq_zero.mp (by rwa [tsum_fintype])) π
    rw [hC0, zero_mul]
    symm; apply Finset.sum_eq_zero
    intro π _
    rw [← mul_assoc, hterm π, zero_mul]
  by_cases hCtop : (∑ π : P, ν π * (pureRun step s₀ n π) ss) = ⊤
  · -- C cannot be ⊤ when weights come from PMF values (each ≤ 1)
    exfalso
    have hle : (∑ π : P, ν π * (pureRun step s₀ n π) ss) ≤ ∑ π : P, ν π :=
      Finset.sum_le_sum fun π _ => by
        calc ν π * (pureRun step s₀ n π) ss
            ≤ ν π * 1 := by gcongr; exact PMF.coe_le_one _ _
          _ = ν π := mul_one _
    rw [hCtop] at hle
    have hone : (∑ π : P, (ν π : ENNReal)) = 1 := by
      have := PMF.tsum_coe ν; rwa [tsum_fintype] at this
    rw [hone] at hle
    exact absurd hle (by simp)
  · -- C > 0 and C < ⊤: the interesting case
    unfold condStep
    rw [pushforward_bind
      (reweightPMF ν (fun π => (pureRun step s₀ n π) ss))
      (fun π => step π ss) (fun t => ss ++ [t])]
    simp only [PMF.bind_apply, tsum_fintype]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro π _
    rw [reweightPMF_apply ν _ π hC0 hCtop, div_eq_mul_inv]
    -- Goal: C * (a * C⁻¹ * F) = ν π * (R * F)
    -- Fully left-associate, commute C next to C⁻¹, cancel
    rw [← mul_assoc, ← mul_assoc (∑ _, _)]
    rw [mul_comm (∑ _, _) (ν π * _)]
    rw [mul_assoc (ν π * _) (∑ _, _)]
    rw [ENNReal.mul_inv_cancel hC0 hCtop, mul_one, mul_assoc]

/-- One-step equality: under `ν`-weighted averaging, the conditioned step
at depth `n` produces the same continuation as the pure step. -/
theorem condStep_step_eq (ν : PMF P) (step : P → List S → PMF S)
    (s₀ : S) (n : Nat) :
    ν.bind (fun π =>
      (pureRun step s₀ n π).bind (fun ss =>
        pushforward (condStep ν step s₀ n ss) (fun t => ss ++ [t]))) =
    ν.bind (fun π =>
      (pureRun step s₀ n π).bind (fun ss =>
        pushforward (step π ss) (fun t => ss ++ [t]))) := by
  classical
  ext y
  simp only [PMF.bind_apply]
  -- Absorb ν π into inner tsum
  simp_rw [← ENNReal.tsum_mul_left]
  -- Swap order of summation
  rw [ENNReal.tsum_comm
    (f := fun π ss => ν π * ((pureRun step s₀ n π) ss *
      (pushforward (condStep ν step s₀ n ss) (fun t => ss ++ [t])) y))]
  rw [ENNReal.tsum_comm
    (f := fun π ss => ν π * ((pureRun step s₀ n π) ss *
      (pushforward (step π ss) (fun t => ss ++ [t])) y))]
  -- Per-ss equality
  congr 1; funext ss
  -- LHS: ∑' π, ν π * (R(π)(ss) * Gc(ss)(y))
  -- RHS: ∑' π, ν π * (R(π)(ss) * Gp(π)(ss)(y))
  -- Factor LHS: condStep term doesn't depend on π
  simp_rw [← mul_assoc]
  rw [ENNReal.tsum_mul_right]
  have htf : ∑' π : P, ν π * (pureRun step s₀ n π) ss =
      ∑ π : P, ν π * (pureRun step s₀ n π) ss := tsum_fintype _
  rw [htf]
  -- LHS: (∑ π, ν π * R(π)(ss)) * Gc(ss)(y) = C * Gc
  -- Apply core identity
  rw [condStep_weighted_eq ν step s₀ n ss y]
  -- Goal: ∑ π, ν π * (R * Gp) = ∑' π, (ν π * R) * Gp
  rw [show ∑ π : P, ν π * ((pureRun step s₀ n π) ss *
      (pushforward (step π ss) (fun t => ss ++ [t])) y) =
    ∑' π : P, ν π * ((pureRun step s₀ n π) ss *
      (pushforward (step π ss) (fun t => ss ++ [t])) y) from
    (tsum_fintype _).symm]
  congr 1; funext π
  rw [mul_assoc]

/-- **Tower property**: running under conditioned steps produces the same
trace distribution as averaging the parameterized runs over `ν`.

This is the abstract content of Kuhn's theorem: conditioning distributes
over sequential Kleisli composition. -/
theorem condRun_eq_mixedRun (ν : PMF P) (step : P → List S → PMF S)
    (s₀ : S) (k : Nat) :
    seqRun (condStep ν step s₀) s₀ k = ν.bind (pureRun step s₀ k) := by
  induction k with
  | zero =>
    ext x
    change (PMF.pure [s₀]) x = (ν.bind (fun π => PMF.pure [s₀])) x
    simp only [PMF.bind_apply, PMF.pure_apply]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | succ n ih =>
    calc
      seqRun (condStep ν step s₀) s₀ (n + 1)
          = (seqRun (condStep ν step s₀) s₀ n).bind (fun ss =>
              pushforward (condStep ν step s₀ n ss)
                (fun t => ss ++ [t])) := by
            simp [seqRun]
      _ = (ν.bind (pureRun step s₀ n)).bind (fun ss =>
              pushforward (condStep ν step s₀ n ss)
                (fun t => ss ++ [t])) := by
            rw [ih]
      _ = ν.bind (fun π =>
            (pureRun step s₀ n π).bind (fun ss =>
              pushforward (condStep ν step s₀ n ss)
                (fun t => ss ++ [t]))) := by
            rw [PMF.bind_bind]
      _ = ν.bind (fun π =>
            (pureRun step s₀ n π).bind (fun ss =>
              pushforward (step π ss) (fun t => ss ++ [t]))) :=
            condStep_step_eq ν step s₀ n

end Tower

/-- Corollary: for any `ν` there exists a step sequence realizing
the mixed run. -/
theorem exists_realizing_steps [Finite P] (ν : PMF P) (step : P → List S → PMF S)
    (s₀ : S) (k : Nat) :
    ∃ g : Nat → List S → PMF S,
      seqRun g s₀ k = ν.bind (pureRun step s₀ k) :=
  letI : Fintype P := Fintype.ofFinite P
  ⟨condStep ν step s₀, condRun_eq_mixedRun ν step s₀ k⟩

/-- Outcome-level corollary: applying any outcome function preserves
the realization. -/
theorem exists_realizing_steps_outcome [Finite P] {β : Type*} (ν : PMF P)
    (step : P → List S → PMF S) (s₀ : S) (k : Nat)
    (outcome : List S → β) :
    ∃ g : Nat → List S → PMF S,
      pushforward (seqRun g s₀ k) outcome =
        ν.bind (fun π => pushforward (pureRun step s₀ k π) outcome) := by
  letI : Fintype P := Fintype.ofFinite P
  refine ⟨condStep ν step s₀, ?_⟩
  rw [condRun_eq_mixedRun]
  exact pushforward_bind ν (pureRun step s₀ k) outcome
end Math.ParameterizedChain
