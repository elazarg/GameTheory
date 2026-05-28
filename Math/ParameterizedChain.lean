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

theorem append_singleton_inj_iff {α : Type*} {as bs : List α} {a b : α} :
    as ++ [a] = bs ++ [b] ↔ as = bs ∧ a = b :=
  Math.TraceRun.append_singleton_inj_iff

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
    pureRun step s₀ m π (ss.take (m + 1)) ≠ 0 :=
  Math.TraceRun.traceRun_take_nonzero (step π) s₀ k ss h m hm

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
      exact sum_coe_fintype ν
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
    Math.TraceRun.seqRun (condStep ν step s₀) s₀ k = ν.bind (pureRun step s₀ k) := by
  induction k with
  | zero =>
    ext x
    change (PMF.pure [s₀]) x = (ν.bind (fun π => PMF.pure [s₀])) x
    simp only [PMF.bind_apply, PMF.pure_apply]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | succ n ih =>
    calc
      Math.TraceRun.seqRun (condStep ν step s₀) s₀ (n + 1)
          = (Math.TraceRun.seqRun (condStep ν step s₀) s₀ n).bind (fun ss =>
              pushforward (condStep ν step s₀ n ss)
                (fun t => ss ++ [t])) := by
            rw [Math.TraceRun.seqRun_succ]
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
      Math.TraceRun.seqRun g s₀ k = ν.bind (pureRun step s₀ k) :=
  letI : Fintype P := Fintype.ofFinite P
  ⟨condStep ν step s₀, condRun_eq_mixedRun ν step s₀ k⟩

/-- Outcome-level corollary: applying any outcome function preserves
the realization. -/
theorem exists_realizing_steps_outcome [Finite P] {β : Type*} (ν : PMF P)
    (step : P → List S → PMF S) (s₀ : S) (k : Nat)
    (outcome : List S → β) :
    ∃ g : Nat → List S → PMF S,
      pushforward (Math.TraceRun.seqRun g s₀ k) outcome =
        ν.bind (fun π => pushforward (pureRun step s₀ k π) outcome) := by
  letI : Fintype P := Fintype.ofFinite P
  refine ⟨condStep ν step s₀, ?_⟩
  rw [condRun_eq_mixedRun]
  exact pushforward_bind ν (pureRun step s₀ k) outcome
end Math.ParameterizedChain
