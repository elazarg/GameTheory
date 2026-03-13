import Math.ProbabilityMassFunction
import Math.PMFProduct

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

variable {P S : Type*}

/-- Run a parameterized Markov chain for `k` steps from initial state `s₀`,
recording the full state trace. -/
noncomputable def pureRun (step : P → List S → PMF S) (s₀ : S)
    (k : Nat) (π : P) : PMF (List S) :=
  Nat.rec (PMF.pure [s₀])
    (fun _ rec =>
      rec.bind (fun ss =>
        pushforward (step π ss) (fun t => ss ++ [t])))
    k

theorem append_singleton_inj {α : Type*} {as bs : List α} {a b : α}
    (h : as ++ [a] = bs ++ [b]) : as = bs ∧ a = b :=
  ⟨List.append_inj_left' h (by simp),
   by have := List.append_inj_right' h (by simp); simpa using this⟩

open Classical in
/-- At successor step, `pureRun` decomposes as prefix reach times one-step transition. -/
theorem pureRun_succ_append (step : P → List S → PMF S) (s₀ : S)
    (k : Nat) (π : P) (ss : List S) (t : S) :
    pureRun step s₀ (k + 1) π (ss ++ [t]) =
      pureRun step s₀ k π ss * step π ss t := by
  change (pureRun step s₀ k π).bind
    (fun ss' => pushforward (step π ss') (fun t' => ss' ++ [t'])) (ss ++ [t]) = _
  rw [PMF.bind_apply]
  have hterm : ∀ ss' : List S, ss' ≠ ss →
      pureRun step s₀ k π ss' *
        (pushforward (step π ss') (fun t' => ss' ++ [t'])) (ss ++ [t]) = 0 := by
    intro ss' hne
    suffices (pushforward (step π ss') (fun t' => ss' ++ [t'])) (ss ++ [t]) = 0 by
      rw [this, mul_zero]
    simp only [pushforward, PMF.bind_apply, PMF.pure_apply]
    rw [ENNReal.tsum_eq_zero]
    intro t'
    rw [if_neg (fun h => hne (append_singleton_inj h).1.symm), mul_zero]
  rw [tsum_eq_single ss (fun ss' hne => hterm ss' hne)]
  congr 1
  simp only [pushforward, PMF.bind_apply, PMF.pure_apply]
  rw [tsum_eq_single t (fun t' ht' => by
    rw [if_neg (fun h => ht' (append_singleton_inj h).2.symm), mul_zero])]
  simp

open Classical in
/-- `pureRun` at successor step assigns zero probability to the empty trace. -/
theorem pureRun_succ_nil (step : P → List S → PMF S) (s₀ : S) (k : Nat) (π : P) :
    pureRun step s₀ (k + 1) π [] = 0 := by
  change (pureRun step s₀ k π).bind
    (fun ss => pushforward (step π ss) (fun t => ss ++ [t])) [] = 0
  simp only [PMF.bind_apply]
  rw [ENNReal.tsum_eq_zero]
  intro ss
  suffices (pushforward (step π ss) (fun t => ss ++ [t])) [] = 0 by rw [this, mul_zero]
  simp only [pushforward, PMF.bind_apply, PMF.pure_apply]
  rw [ENNReal.tsum_eq_zero]
  intro t
  simp [show ([] : List S) ≠ ss ++ [t] from List.ne_nil_of_length_pos (by simp)]

open Classical in
/-- Traces with nonzero `pureRun` probability have length exactly `n + 1`. -/
theorem pureRun_length (step : P → List S → PMF S) (s₀ : S)
    (n : Nat) (π : P) (ss : List S)
    (h : pureRun step s₀ n π ss ≠ 0) : ss.length = n + 1 := by
  induction n generalizing ss with
  | zero =>
    have hss : ss = [s₀] := by
      by_contra hne
      exact h (by simp [pureRun, PMF.pure_apply, hne])
    simp [hss]
  | succ k ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
    · exact absurd (pureRun_succ_nil step s₀ k π) h
    · simp only [List.concat_eq_append, pureRun_succ_append] at h
      have hp : pureRun step s₀ k π p ≠ 0 :=
        left_ne_zero_of_mul h
      simp [List.length_append, ih p hp]

open Classical in
/-- On a nonzero-probability trace, each per-step transition has nonzero probability.
If `pureRun step s₀ k π ss ≠ 0` and `j + 1 < ss.length`, then
`step π (ss.take (j + 1)) ss[j + 1] ≠ 0`. -/
theorem pureRun_step_nonzero (step : P → List S → PMF S) (s₀ : S)
    (k : Nat) (π : P) (ss : List S)
    (h : pureRun step s₀ k π ss ≠ 0)
    (j : Nat) (hj : j + 1 < ss.length) :
    step π (ss.take (j + 1)) ss[j + 1] ≠ 0 := by
  have hlen := pureRun_length step s₀ k π ss h
  -- Induction on k from the end of the trace
  induction k generalizing ss j with
  | zero => omega
  | succ m ih =>
    have hne : ss ≠ [] := by intro he; simp [he] at hlen
    -- Decompose ss = pre ++ [t]
    obtain ⟨pre, t, hss_eq⟩ : ∃ pre t, ss = pre ++ [t] := by
      exact ⟨ss.dropLast, ss.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    subst hss_eq
    have hplen : pre.length = m + 1 := by simp at hlen; omega
    rw [pureRun_succ_append] at h
    have hpre : pureRun step s₀ m π pre ≠ 0 := left_ne_zero_of_mul h
    have hstep_last : step π pre t ≠ 0 := right_ne_zero_of_mul h
    by_cases hjlast : j + 1 = pre.length
    · -- The last step: step π pre t ≠ 0
      suffices step π (List.take (j + 1) (pre ++ [t])) (pre ++ [t])[j + 1] ≠ 0 from this
      rw [List.take_append_of_le_length (by omega)]
      rw [List.getElem_append_right (by omega)]
      simp only [List.getElem_singleton, ne_eq]
      have : List.take pre.length pre = pre := List.take_length
      rw [hjlast, this]
      exact hstep_last
    · -- An earlier step: delegate to IH on pre
      have hjpre : j + 1 < pre.length := by simp at hj; omega
      suffices step π (List.take (j + 1) (pre ++ [t]))
          (pre ++ [t])[j + 1] ≠ 0 from this
      rw [List.take_append_of_le_length (by omega)]
      rw [List.getElem_append_left hjpre]
      exact ih pre hpre j hjpre hplen

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

set_option linter.unusedFintypeInType false in
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

set_option linter.unusedFintypeInType false in
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

set_option linter.unusedFintypeInType false in
theorem reweightPMF_fallback (ν : PMF P) (w : P → ENNReal)
    (hC : ∑ π : P, ν π * w π = 0) :
    reweightPMF ν w = ν := by
  unfold reweightPMF
  dsimp only
  split_ifs with h
  · rfl
  · exact absurd (Or.inl hC) h

set_option linter.unusedFintypeInType false in
theorem reweightPMF_degenerate (ν : PMF P) (w : P → ENNReal)
    (hC : (∑ π : P, ν π * w π) = 0 ∨ (∑ π : P, ν π * w π) = ⊤) :
    reweightPMF ν w = ν := by
  unfold reweightPMF
  exact dif_pos hC

set_option linter.unusedFintypeInType false in
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

set_option linter.unusedFintypeInType false in
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

set_option linter.unusedFintypeInType false in
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

end ReweightProduct

set_option linter.unusedFintypeInType false in
/-- Conditioned step at depth `n`: reweight `ν` by the probability of each
parameter reaching state trace `ss` after `n` steps, then average the
parameterized step function. -/
noncomputable def condStep [Fintype P] (ν : PMF P)
    (step : P → List S → PMF S) (s₀ : S) (n : Nat) (ss : List S) : PMF S :=
  (reweightPMF ν (fun π => (pureRun step s₀ n π) ss)).bind (fun π => step π ss)

section Tower

variable [Fintype P]

set_option linter.unusedFintypeInType false in
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

set_option linter.unusedFintypeInType false in
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

set_option linter.unusedFintypeInType false in
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

set_option linter.unusedFintypeInType false in
/-- Corollary: for any `ν` there exists a step sequence realizing
the mixed run. -/
theorem exists_realizing_steps (ν : PMF P) (step : P → List S → PMF S)
    (s₀ : S) (k : Nat) :
    ∃ g : Nat → List S → PMF S,
      seqRun g s₀ k = ν.bind (pureRun step s₀ k) :=
  ⟨condStep ν step s₀, condRun_eq_mixedRun ν step s₀ k⟩

set_option linter.unusedFintypeInType false in
/-- Outcome-level corollary: applying any outcome function preserves
the realization. -/
theorem exists_realizing_steps_outcome {β : Type*} (ν : PMF P)
    (step : P → List S → PMF S) (s₀ : S) (k : Nat)
    (outcome : List S → β) :
    ∃ g : Nat → List S → PMF S,
      pushforward (seqRun g s₀ k) outcome =
        ν.bind (fun π => pushforward (pureRun step s₀ k π) outcome) := by
  refine ⟨condStep ν step s₀, ?_⟩
  rw [condRun_eq_mixedRun]
  exact pushforward_bind ν (pureRun step s₀ k) outcome

end Tower

end Math.ParameterizedChain
