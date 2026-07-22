/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Uniform

/-!
# Discounted Payoffs in Stochastic Games

Per-stage expected payoffs and the `β`-discounted payoff aggregation for
behavior strategies in stochastic games.  The discounted evaluation is the
second classical payoff aggregation of the uniform-equilibrium literature
(Shapley 1953): uniform notions can equivalently be phrased over all
discount factors close to `1`, and the discounted track — Shapley's
discounted values, Fink's discounted stationary equilibria — feeds the
vanishing-discount analysis behind uniform values
(see `GameTheory.Concepts.Stochastic.Uniform`).

## Main definitions

* `StochasticGame.expectedStagePayoff` — expected payoff of stage `t`
* `StochasticGame.discountedPayoff` — normalized `β`-discounted payoff
* `StochasticGame.IsDiscountedεNash` — ε-Nash under discounted payoffs

## Main results

* `StochasticGame.expect_totalPayoff_eq_sum_expectedStagePayoff` — the
  finite-horizon total payoff is the sum of the per-stage payoffs
* `StochasticGame.abs_expectedStagePayoff_le` — stage payoff bounds
* `StochasticGame.summable_discounted_expectedStagePayoff` — the discounted
  series converges for `|β| < 1`
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace StochasticGame

open Math.Probability

variable {ι : Type}

/-- Expected payoff of stage `t` (the `t+1`-st stage played) from initial
state `s₀` under behavior profile `σ`: the expectation, over histories at
decision epoch `t`, of the expected payoff of the stage played there. -/
def expectedStagePayoff (G : StochasticGame ι) [Fintype ι]
    (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) (who : ι) : ℝ :=
  expect (G.histDist σ s₀ t) (fun h => G.stageEUAt σ h who)

/-- The finite-horizon expected total payoff is the sum of the per-stage
expected payoffs. -/
theorem expect_totalPayoff_eq_sum_expectedStagePayoff
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι) (T : ℕ) :
    expect (G.histDist σ s₀ T) (fun h => G.totalPayoff who h) =
      ∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [G.expect_totalPayoff_succ, ih, Finset.sum_range_succ]
    rfl

/-- The finite-horizon average payoff is the average of the per-stage
expected payoffs. -/
theorem finiteAveragePayoff_eq_sum_expectedStagePayoff
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι) (T : ℕ) :
    G.finiteAveragePayoff s₀ T σ who =
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who := by
  rw [finiteAveragePayoff,
    G.expect_totalPayoff_eq_sum_expectedStagePayoff σ s₀ who T]

/-- A uniform stage payoff bound bounds every per-stage expected payoff. -/
theorem abs_expectedStagePayoff_le (G : StochasticGame ι) [Fintype ι]
    {who : ι} {C : ℝ} (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) :
    |G.expectedStagePayoff σ s₀ t who| ≤ C := by
  refine abs_expect_le_of_abs_le _ _ fun h => ?_
  exact abs_expect_le_of_abs_le _ _ fun a => hC h.2 a

/-- The discounted payoff series converges for `|β| < 1` and bounded stage
payoffs. -/
theorem summable_discounted_expectedStagePayoff
    (G : StochasticGame ι) [Fintype ι] {who : ι} {C : ℝ}
    (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    (σ : G.BehaviorProfile) (s₀ : G.State) {β : ℝ} (hβ : |β| < 1) :
    Summable (fun t : ℕ => β ^ t * G.expectedStagePayoff σ s₀ t who) := by
  refine (summable_geometric_of_lt_one (abs_nonneg β) hβ).mul_right C
    |>.of_norm_bounded ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left
    (G.abs_expectedStagePayoff_le hC σ s₀ t)
    (pow_nonneg (abs_nonneg β) t)

/-- Normalized `β`-discounted expected payoff: the factor `1 - β` scales the
aggregation to the same units as stage payoffs. -/
def discountedPayoff (G : StochasticGame ι) [Fintype ι] (β : ℝ)
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι) : ℝ :=
  (1 - β) * ∑' t : ℕ, β ^ t * G.expectedStagePayoff σ s₀ t who

/-- Constant per-stage expected payoffs make the normalized discounted
payoff that constant. -/
theorem discountedPayoff_of_forall_expectedStagePayoff_eq
    (G : StochasticGame ι) [Fintype ι] {σ : G.BehaviorProfile}
    {s₀ : G.State} {who : ι} {v : ℝ}
    (hconst : ∀ t, G.expectedStagePayoff σ s₀ t who = v)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    G.discountedPayoff β σ s₀ who = v := by
  have h1β : (0 : ℝ) < 1 - β := by linarith
  unfold discountedPayoff
  have hfun : (fun t : ℕ => β ^ t * G.expectedStagePayoff σ s₀ t who) =
      fun t : ℕ => β ^ t * v := by
    funext t
    rw [hconst]
  rw [hfun, tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1,
    ← mul_assoc, mul_inv_cancel₀ h1β.ne', one_mul]

/-- Dominated per-stage expected payoffs dominate the normalized discounted
payoff. -/
theorem discountedPayoff_le_of_forall_expectedStagePayoff_le
    (G : StochasticGame ι) [Fintype ι] {σ : G.BehaviorProfile}
    {s₀ : G.State} {who : ι} {v C : ℝ}
    (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    (hle : ∀ t, G.expectedStagePayoff σ s₀ t who ≤ v)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    G.discountedPayoff β σ s₀ who ≤ v := by
  have h1β : (0 : ℝ) < 1 - β := by linarith
  have hsum := G.summable_discounted_expectedStagePayoff hC σ s₀
    (β := β) (by rwa [abs_of_nonneg hβ0])
  have hgeom : Summable (fun t : ℕ => β ^ t * v) :=
    (summable_geometric_of_lt_one hβ0 hβ1).mul_right v
  have hts : (∑' t : ℕ, β ^ t * G.expectedStagePayoff σ s₀ t who) ≤
      ∑' t : ℕ, β ^ t * v :=
    hsum.tsum_le_tsum
      (fun t => mul_le_mul_of_nonneg_left (hle t) (pow_nonneg hβ0 t))
      hgeom
  calc G.discountedPayoff β σ s₀ who
      ≤ (1 - β) * ∑' t : ℕ, β ^ t * v :=
        mul_le_mul_of_nonneg_left hts h1β.le
    _ = v := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1,
          ← mul_assoc, mul_inv_cancel₀ h1β.ne', one_mul]

/-- ε-Nash equilibrium of the `β`-discounted game from `s₀`: no unilateral
replacement of a whole behavior strategy gains more than `ε` in discounted
payoff. -/
def IsDiscountedεNash (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (β : ℝ) (s₀ : G.State) (ε : ℝ) (σ : G.BehaviorProfile) : Prop :=
  ∀ who (dev : G.BehaviorStrategy who),
    G.discountedPayoff β σ s₀ who + ε ≥
      G.discountedPayoff β (Function.update σ who dev) s₀ who

/-- Discounted approximate Nash is monotone in the error allowance. -/
theorem IsDiscountedεNash.mono {G : StochasticGame ι} [Fintype ι]
    [DecidableEq ι] {β : ℝ} {s₀ : G.State} {ε ε' : ℝ}
    {σ : G.BehaviorProfile}
    (h : G.IsDiscountedεNash β s₀ ε σ) (hε : ε ≤ ε') :
    G.IsDiscountedεNash β s₀ ε' σ := by
  intro who dev
  have := h who dev
  linarith

end StochasticGame

end GameTheory
