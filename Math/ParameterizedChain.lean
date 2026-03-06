import Math.ProbabilityMassFunction

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

end ReweightPMF

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
