/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Equilibrium.Uniform

/-!
# Discounted Payoffs in Stochastic Games

Per-stage expected payoffs and the `β`-discounted payoff aggregation for
behavior strategies in stochastic games.  The discounted evaluation is the
second classical payoff aggregation of the uniform-equilibrium literature
(Shapley 1953): uniform notions can equivalently be phrased over all
discount factors close to `1`, and the discounted track — Shapley's
discounted values, Fink's discounted stationary equilibria — feeds the
vanishing-discount analysis behind uniform values
(see `GameTheory.Concepts.Stochastic.Equilibrium.Uniform`).

## Main definitions

* `StochasticGame.expectedStagePayoff` — expected payoff of stage `t`
* `StochasticGame.expectedStateValue` — expected value of the state at epoch `t`
* `StochasticGame.discountedPayoff` — normalized `β`-discounted payoff
* `StochasticGame.IsDiscountedεNash` — ε-Nash under discounted payoffs

## Main results

* `StochasticGame.expect_totalPayoff_eq_sum_expectedStagePayoff` — the
  finite-horizon total payoff is the sum of the per-stage payoffs
* `StochasticGame.abs_expectedStagePayoff_le` — stage payoff bounds
* `StochasticGame.summable_discounted_expectedStagePayoff` — the discounted
  series converges for `|β| < 1`
* `StochasticGame.le_discountedPayoff_of_bellman_le` — an excessive-function
  inequality at every history guarantees the corresponding discounted value
* `StochasticGame.discountedPayoff_le_of_bellman_ge` — the dual: a
  subexcessive-function inequality at every history caps the discounted value
* `StochasticGame.finiteAveragePayoff_ge_of_averageReward_bellman_le` — a
  time-varying average-reward Bellman certificate gives a quantitative
  finite-horizon guarantee
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

open Math.Probability in
/-- Geometric domination: a uniformly bounded sequence has a summable
`β`-discounted series for `|β| < 1`. -/
theorem summable_pow_mul_of_abs_le {β C : ℝ} (hβ : |β| < 1) {g : ℕ → ℝ}
    (hg : ∀ t, |g t| ≤ C) :
    Summable fun t : ℕ => β ^ t * g t := by
  refine (summable_geometric_of_lt_one (abs_nonneg β) hβ).mul_right C
    |>.of_norm_bounded ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hg t) (pow_nonneg (abs_nonneg β) t)

namespace StochasticGame

open Math.Probability

variable {ι : Type}

/-- Expected payoff of stage `t` (the `t+1`-st stage played) from initial
state `s₀` under behavior profile `σ`: the expectation, over histories at
decision epoch `t`, of the expected payoff of the stage played there. -/
def expectedStagePayoff (G : StochasticGame ι) [Fintype ι]
    (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) (who : ι) : ℝ :=
  expect (G.histDist σ s₀ t) (fun h => G.stageEUAt σ h who)

/-- Expected value of the current state after `t` completed stages.  This is
the process used to telescope one-step Bellman inequalities. -/
def expectedStateValue (G : StochasticGame ι) [Fintype ι]
    (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) (v : G.State → ℝ) : ℝ :=
  expect (G.histDist σ s₀ t) (fun h => v h.2)

@[simp] theorem expectedStateValue_zero (G : StochasticGame ι) [Fintype ι]
    (σ : G.BehaviorProfile) (s₀ : G.State) (v : G.State → ℝ) :
    G.expectedStateValue σ s₀ 0 v = v s₀ := by
  simp [expectedStateValue, emptyHist]

/-- The expected next-state value is obtained by averaging the transition
continuation over the current history and joint action. -/
theorem expectedStateValue_succ (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) (v : G.State → ℝ) :
    G.expectedStateValue σ s₀ (t + 1) v =
      expect (G.histDist σ s₀ t) fun h =>
        expect (G.stageActionDist σ h) fun a =>
          expect (G.transition h.2 a) v := by
  unfold expectedStateValue
  rw [histDist_succ, expect_bind]
  congr 1
  funext h
  rw [expect_bind]
  congr 1
  funext a
  rw [expect_bind]
  simp

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
    Summable (fun t : ℕ => β ^ t * G.expectedStagePayoff σ s₀ t who) :=
  summable_pow_mul_of_abs_le hβ fun t =>
    G.abs_expectedStagePayoff_le hC σ s₀ t

@[simp] theorem expectedStagePayoff_zero (G : StochasticGame ι) [Fintype ι]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι) :
    G.expectedStagePayoff σ s₀ 0 who =
      G.stageEUAt σ (G.emptyHist s₀) who := by
  unfold expectedStagePayoff
  rw [histDist_zero, expect_pure]

/-- One-step recursion for per-stage expected payoffs: stage `t + 1` from
`s₀` is stage `t` of the shifted profile from the successor state. -/
theorem expectedStagePayoff_succ_shift (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) (who : ι) :
    G.expectedStagePayoff σ s₀ (t + 1) who =
      expect (G.stageActionDist σ (G.emptyHist s₀)) fun a =>
        expect (G.transition s₀ a) fun s₁ =>
          G.expectedStagePayoff (G.shiftProfile σ (s₀, a)) s₁ t who := by
  unfold expectedStagePayoff
  rw [G.histDist_succ_shift, expect_bind]
  congr 1
  funext a
  rw [expect_bind]
  congr 1
  funext s₁
  rw [Math.Probability.expect_map_fintype_target]
  rfl

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

/-- **Bellman unrolling of the discounted payoff**: the normalized
discounted payoff is the convex combination of the first stage's expected
payoff and the expected discounted payoff of the shifted profile from the
successor state. -/
theorem discountedPayoff_shift (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : ι} {C : ℝ} (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    (σ : G.BehaviorProfile) (s₀ : G.State) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    G.discountedPayoff β σ s₀ who =
      (1 - β) * G.stageEUAt σ (G.emptyHist s₀) who +
        β * expect (G.stageActionDist σ (G.emptyHist s₀)) fun a =>
          expect (G.transition s₀ a) fun s₁ =>
            G.discountedPayoff β (G.shiftProfile σ (s₀, a)) s₁ who := by
  have hβabs : |β| < 1 := by rwa [abs_of_nonneg hβ0]
  have hsum := G.summable_discounted_expectedStagePayoff hC σ s₀ hβabs
  have h1 : (∑' t : ℕ, β ^ t * G.expectedStagePayoff σ s₀ t who) =
      G.stageEUAt σ (G.emptyHist s₀) who +
        ∑' t : ℕ, β ^ (t + 1) * G.expectedStagePayoff σ s₀ (t + 1) who := by
    rw [hsum.tsum_eq_zero_add, pow_zero, one_mul, expectedStagePayoff_zero]
  have h2 : ∀ t : ℕ,
      β ^ (t + 1) * G.expectedStagePayoff σ s₀ (t + 1) who =
        β * expect (G.stageActionDist σ (G.emptyHist s₀)) fun a =>
          β ^ t * expect (G.transition s₀ a) fun s₁ =>
            G.expectedStagePayoff (G.shiftProfile σ (s₀, a)) s₁ t who := by
    intro t
    rw [G.expectedStagePayoff_succ_shift, pow_succ', mul_assoc,
      ← expect_const_mul]
  have h3 : (∑' t : ℕ, β ^ (t + 1) *
        G.expectedStagePayoff σ s₀ (t + 1) who) =
      β * expect (G.stageActionDist σ (G.emptyHist s₀)) fun a =>
        ∑' t : ℕ, β ^ t * expect (G.transition s₀ a) fun s₁ =>
          G.expectedStagePayoff (G.shiftProfile σ (s₀, a)) s₁ t who := by
    rw [tsum_congr h2, tsum_mul_left]
    congr 1
    exact tsum_expect_comm _ _ fun a =>
      summable_pow_mul_of_abs_le hβabs fun t =>
        abs_expect_le_of_abs_le _ _ fun s₁ =>
          G.abs_expectedStagePayoff_le hC _ _ t
  have h4 : ∀ a : G.JointAct,
      (∑' t : ℕ, β ^ t * expect (G.transition s₀ a) fun s₁ =>
          G.expectedStagePayoff (G.shiftProfile σ (s₀, a)) s₁ t who) =
        expect (G.transition s₀ a) fun s₁ =>
          ∑' t : ℕ, β ^ t *
            G.expectedStagePayoff (G.shiftProfile σ (s₀, a)) s₁ t who := by
    intro a
    rw [tsum_congr fun t => (expect_const_mul _ _ _).symm]
    exact tsum_expect_comm _ _ fun s₁ =>
      summable_pow_mul_of_abs_le hβabs fun t =>
        G.abs_expectedStagePayoff_le hC _ _ t
  calc G.discountedPayoff β σ s₀ who
      = (1 - β) * ∑' t : ℕ, β ^ t * G.expectedStagePayoff σ s₀ t who := rfl
    _ = (1 - β) * G.stageEUAt σ (G.emptyHist s₀) who +
        (1 - β) * ∑' t : ℕ, β ^ (t + 1) *
          G.expectedStagePayoff σ s₀ (t + 1) who := by
        rw [h1, mul_add]
    _ = (1 - β) * G.stageEUAt σ (G.emptyHist s₀) who +
        β * expect (G.stageActionDist σ (G.emptyHist s₀)) fun a =>
          expect (G.transition s₀ a) fun s₁ =>
            G.discountedPayoff β (G.shiftProfile σ (s₀, a)) s₁ who := by
        rw [h3, ← mul_assoc, mul_comm (1 - β) β, mul_assoc]
        congr 1
        rw [← expect_const_mul]
        congr 1
        refine congrArg (expect (G.stageActionDist σ (G.emptyHist s₀)))
          (funext fun a => ?_)
        rw [h4 a, ← expect_const_mul]
        rfl

/-- **Excessive-function discounted guarantee.**  Suppose `v` satisfies the
one-step Bellman lower inequality at every finite history under `σ`: current
value is at most normalized current payoff plus discounted expected successor
value.  Then `σ` guarantees at least `v` from the initial state.

The hypothesis is historywise, so the theorem applies directly when one
player uses a stationary Shapley action while the opponent uses an arbitrary
history-dependent behavior strategy. -/
theorem le_discountedPayoff_of_bellman_le
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] {who : ι} {C : ℝ}
    (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    (σ : G.BehaviorProfile) (s₀ : G.State) (v : G.State → ℝ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      v h.2 ≤ (1 - β) * G.stageEUAt σ h who +
        β * expect (G.stageActionDist σ h) (fun a =>
          expect (G.transition h.2 a) v)) :
    v s₀ ≤ G.discountedPayoff β σ s₀ who := by
  let V : ℕ → ℝ := fun t => G.expectedStateValue σ s₀ t v
  let r : ℕ → ℝ := fun t => G.expectedStagePayoff σ s₀ t who
  have hstep : ∀ t, V t ≤ (1 - β) * r t + β * V (t + 1) := by
    intro t
    calc V t
        ≤ expect (G.histDist σ s₀ t) (fun h =>
            (1 - β) * G.stageEUAt σ h who +
              β * expect (G.stageActionDist σ h) (fun a =>
                expect (G.transition h.2 a) v)) :=
          expect_mono _ _ _ (hbellman t)
      _ = (1 - β) * r t + β * V (t + 1) := by
          rw [expect_add, expect_const_mul, expect_const_mul,
            ← G.expectedStateValue_succ]
          rfl
  obtain ⟨Cv, hCv⟩ := exists_abs_bound_of_finite v
  have hV : ∀ t, |V t| ≤ Cv := by
    intro t
    exact abs_expect_le_of_abs_le _ _ fun h => hCv h.2
  have hβabs : |β| < 1 := by rwa [abs_of_nonneg hβ0]
  have hsumV : Summable (fun t : ℕ => β ^ t * V t) :=
    summable_pow_mul_of_abs_le hβabs hV
  have hsumVsucc : Summable (fun t : ℕ => β ^ t * V (t + 1)) :=
    summable_pow_mul_of_abs_le hβabs fun t => hV (t + 1)
  have hsumR : Summable (fun t : ℕ => β ^ t * r t) :=
    G.summable_discounted_expectedStagePayoff hC σ s₀ hβabs
  let A : ℕ → ℝ := fun t => β ^ t * ((1 - β) * r t)
  let B : ℕ → ℝ := fun t => β ^ t * (β * V (t + 1))
  let D : ℕ → ℝ := fun t => A t + B t - β ^ t * V t
  have hsumA : Summable A := by
    exact (hsumR.mul_right (1 - β)).congr fun t => by simp [A]; ring
  have hsumB : Summable B := by
    exact (hsumVsucc.mul_left β).congr fun t => by simp [B]; ring
  have hD0 : ∀ t, 0 ≤ D t := by
    intro t
    unfold D A B
    rw [← mul_add, ← mul_sub]
    exact mul_nonneg (pow_nonneg hβ0 t) (sub_nonneg.mpr (hstep t))
  have htsumD0 : 0 ≤ ∑' t : ℕ, D t := tsum_nonneg hD0
  have htsumA : (∑' t : ℕ, A t) = G.discountedPayoff β σ s₀ who := by
    unfold A discountedPayoff r
    rw [← tsum_mul_left]
    congr 1
    funext t
    ring
  have htsumB : (∑' t : ℕ, B t) =
      (∑' t : ℕ, β ^ t * V t) - V 0 := by
    have hshift := hsumV.tsum_eq_zero_add
    have htail : (∑' t : ℕ, β ^ (t + 1) * V (t + 1)) =
        (∑' t : ℕ, β ^ t * V t) - V 0 := by
      rw [hshift]
      simp
    rw [← htail]
    apply tsum_congr
    intro t
    simp [B, pow_succ']
    ring
  change 0 ≤ (∑' (t : ℕ), ((A t + B t) - β ^ t * V t)) at htsumD0
  rw [(hsumA.add hsumB).tsum_sub hsumV, hsumA.tsum_add hsumB,
    htsumA, htsumB] at htsumD0
  have hV0 : V 0 = v s₀ := by simp [V]
  linarith

/-- **Subexcessive-function discounted cap.**  Dual of
`le_discountedPayoff_of_bellman_le`: suppose `v` satisfies the one-step
Bellman upper inequality at every finite history under `σ`: current value is
at least normalized current payoff plus discounted expected successor value.
Then `σ` cannot guarantee more than `v` from the initial state.

The hypothesis is historywise, so the theorem applies directly to a
unilateral behavior-strategy deviation once the non-deviating history-value
map is fixed. -/
theorem discountedPayoff_le_of_bellman_ge
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] {who : ι} {C : ℝ}
    (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    (σ : G.BehaviorProfile) (s₀ : G.State) (v : G.State → ℝ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      (1 - β) * G.stageEUAt σ h who +
        β * expect (G.stageActionDist σ h) (fun a =>
          expect (G.transition h.2 a) v) ≤ v h.2) :
    G.discountedPayoff β σ s₀ who ≤ v s₀ := by
  let V : ℕ → ℝ := fun t => G.expectedStateValue σ s₀ t v
  let r : ℕ → ℝ := fun t => G.expectedStagePayoff σ s₀ t who
  have hstep : ∀ t, (1 - β) * r t + β * V (t + 1) ≤ V t := by
    intro t
    calc (1 - β) * r t + β * V (t + 1)
        = expect (G.histDist σ s₀ t) (fun h =>
            (1 - β) * G.stageEUAt σ h who +
              β * expect (G.stageActionDist σ h) (fun a =>
                expect (G.transition h.2 a) v)) := by
          rw [expect_add, expect_const_mul, expect_const_mul,
            ← G.expectedStateValue_succ]
          rfl
      _ ≤ V t := expect_mono _ _ _ (hbellman t)
  obtain ⟨Cv, hCv⟩ := exists_abs_bound_of_finite v
  have hV : ∀ t, |V t| ≤ Cv := by
    intro t
    exact abs_expect_le_of_abs_le _ _ fun h => hCv h.2
  have hβabs : |β| < 1 := by rwa [abs_of_nonneg hβ0]
  have hsumV : Summable (fun t : ℕ => β ^ t * V t) :=
    summable_pow_mul_of_abs_le hβabs hV
  have hsumVsucc : Summable (fun t : ℕ => β ^ t * V (t + 1)) :=
    summable_pow_mul_of_abs_le hβabs fun t => hV (t + 1)
  have hsumR : Summable (fun t : ℕ => β ^ t * r t) :=
    G.summable_discounted_expectedStagePayoff hC σ s₀ hβabs
  let A : ℕ → ℝ := fun t => β ^ t * ((1 - β) * r t)
  let B : ℕ → ℝ := fun t => β ^ t * (β * V (t + 1))
  let D : ℕ → ℝ := fun t => β ^ t * V t - (A t + B t)
  have hsumA : Summable A := by
    exact (hsumR.mul_right (1 - β)).congr fun t => by simp [A]; ring
  have hsumB : Summable B := by
    exact (hsumVsucc.mul_left β).congr fun t => by simp [B]; ring
  have hD0 : ∀ t, 0 ≤ D t := by
    intro t
    unfold D A B
    rw [← mul_add, ← mul_sub]
    exact mul_nonneg (pow_nonneg hβ0 t) (sub_nonneg.mpr (hstep t))
  have htsumD0 : 0 ≤ ∑' t : ℕ, D t := tsum_nonneg hD0
  have htsumA : (∑' t : ℕ, A t) = G.discountedPayoff β σ s₀ who := by
    unfold A discountedPayoff r
    rw [← tsum_mul_left]
    congr 1
    funext t
    ring
  have htsumB : (∑' t : ℕ, B t) =
      (∑' t : ℕ, β ^ t * V t) - V 0 := by
    have hshift := hsumV.tsum_eq_zero_add
    have htail : (∑' t : ℕ, β ^ (t + 1) * V (t + 1)) =
        (∑' t : ℕ, β ^ t * V t) - V 0 := by
      rw [hshift]
      simp
    rw [← htail]
    apply tsum_congr
    intro t
    simp [B, pow_succ']
    ring
  change 0 ≤ (∑' (t : ℕ), (β ^ t * V t - (A t + B t))) at htsumD0
  rw [hsumV.tsum_sub (hsumA.add hsumB), hsumA.tsum_add hsumB,
    htsumA, htsumB] at htsumD0
  have hV0 : V 0 = v s₀ := by simp [V]
  linarith

-- ============================================================================
-- Time-varying average-reward verification
-- ============================================================================

/-- Convert a normalized discounted Bellman lower inequality into an
average-reward Bellman inequality.  The discounted continuation value `v`
becomes the target reward, while `β / (1 - β) • v` is the bias.  An additive
discounted residual `δ` is amplified to `δ / (1 - β)`.

This algebraic conversion is the direct bridge from discounted Shapley/Fink
certificates to finite-horizon uniform-payoff estimates. -/
theorem averageReward_bellman_le_of_discounted_bellman_le
    (G : StochasticGame ι) [Fintype ι] (σ : G.BehaviorProfile)
    (who : ι) (v : G.State → ℝ) {β δ : ℝ} (hβ1 : β < 1)
    (hdisc : ∀ (t : ℕ) (h : G.Hist t),
      v h.2 ≤ (1 - β) * G.stageEUAt σ h who +
        β * expect (G.stageActionDist σ h) (fun a =>
          expect (G.transition h.2 a) v) + δ) :
    ∀ (t : ℕ) (h : G.Hist t),
      v h.2 + (β / (1 - β)) * v h.2 ≤
        G.stageEUAt σ h who +
          expect (G.stageActionDist σ h) (fun a =>
            expect (G.transition h.2 a)
              (fun s => (β / (1 - β)) * v s)) +
            δ / (1 - β) := by
  intro t h
  have hden : 0 < 1 - β := by linarith
  let E : ℝ := expect (G.stageActionDist σ h) (fun a =>
    expect (G.transition h.2 a) v)
  have hcont :
      expect (G.stageActionDist σ h) (fun a =>
          expect (G.transition h.2 a)
            (fun s => (β / (1 - β)) * v s)) =
        (β / (1 - β)) * E := by
    simp_rw [expect_const_mul]
    rfl
  rw [hcont]
  have hd := hdisc t h
  change v h.2 ≤ (1 - β) * G.stageEUAt σ h who + β * E + δ at hd
  rw [show v h.2 + (β / (1 - β)) * v h.2 =
      v h.2 / (1 - β) by
    field_simp
    ring]
  rw [show G.stageEUAt σ h who + (β / (1 - β)) * E + δ / (1 - β) =
      ((1 - β) * G.stageEUAt σ h who + β * E + δ) / (1 - β) by
    field_simp]
  exact (div_le_div_iff_of_pos_right hden).2 hd

/-- Dual conversion of a discounted Bellman upper inequality into an
average-reward upper certificate. -/
theorem averageReward_bellman_ge_of_discounted_bellman_ge
    (G : StochasticGame ι) [Fintype ι] (σ : G.BehaviorProfile)
    (who : ι) (v : G.State → ℝ) {β δ : ℝ} (hβ1 : β < 1)
    (hdisc : ∀ (t : ℕ) (h : G.Hist t),
      (1 - β) * G.stageEUAt σ h who +
          β * expect (G.stageActionDist σ h) (fun a =>
            expect (G.transition h.2 a) v) ≤ v h.2 + δ) :
    ∀ (t : ℕ) (h : G.Hist t),
      G.stageEUAt σ h who +
          expect (G.stageActionDist σ h) (fun a =>
            expect (G.transition h.2 a)
              (fun s => (β / (1 - β)) * v s)) ≤
        v h.2 + (β / (1 - β)) * v h.2 + δ / (1 - β) := by
  intro t h
  have hden : 0 < 1 - β := by linarith
  let E : ℝ := expect (G.stageActionDist σ h) (fun a =>
    expect (G.transition h.2 a) v)
  have hcont :
      expect (G.stageActionDist σ h) (fun a =>
          expect (G.transition h.2 a)
            (fun s => (β / (1 - β)) * v s)) =
        (β / (1 - β)) * E := by
    simp_rw [expect_const_mul]
    rfl
  rw [hcont]
  have hd := hdisc t h
  change (1 - β) * G.stageEUAt σ h who + β * E ≤ v h.2 + δ at hd
  rw [show G.stageEUAt σ h who + (β / (1 - β)) * E =
      ((1 - β) * G.stageEUAt σ h who + β * E) / (1 - β) by
    field_simp]
  rw [show v h.2 + (β / (1 - β)) * v h.2 + δ / (1 - β) =
      (v h.2 + δ) / (1 - β) by
    field_simp
    ring]
  exact (div_le_div_iff_of_pos_right hden).2 hd

/-- **Finite-horizon Bellman telescoping.**  Let `z t s` be a target reward,
`v t s` a time-varying bias (or continuation potential), and `e t` an
additive error.  If after every history

`zₜ(s) + vₜ(s) ≤ current payoff + 𝔼[vₜ₊₁(s')] + eₜ`,

then the expected targets plus the initial bias are bounded by the expected
stage payoffs plus the terminal bias and accumulated errors.  This is the
quantitative verification form needed for adaptive, history-dependent
continuation certificates in uniform-equilibrium arguments. -/
theorem finitePayoff_telescope_of_averageReward_bellman_le
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State)
    (who : ι) (z v : ℕ → G.State → ℝ) (e : ℕ → ℝ)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      z t h.2 + v t h.2 ≤ G.stageEUAt σ h who +
        expect (G.stageActionDist σ h) (fun a =>
          expect (G.transition h.2 a) (v (t + 1))) + e t)
    (T : ℕ) :
    (∑ t ∈ Finset.range T, G.expectedStateValue σ s₀ t (z t)) +
        G.expectedStateValue σ s₀ 0 (v 0) ≤
      (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who) +
        G.expectedStateValue σ s₀ T (v T) +
          ∑ t ∈ Finset.range T, e t := by
  let Z : ℕ → ℝ := fun t => G.expectedStateValue σ s₀ t (z t)
  let V : ℕ → ℝ := fun t => G.expectedStateValue σ s₀ t (v t)
  let r : ℕ → ℝ := fun t => G.expectedStagePayoff σ s₀ t who
  have hstep : ∀ t, Z t + V t ≤ r t + V (t + 1) + e t := by
    intro t
    calc
      Z t + V t = expect (G.histDist σ s₀ t) (fun h =>
          z t h.2 + v t h.2) := by
        rw [expect_add]
        rfl
      _ ≤ expect (G.histDist σ s₀ t) (fun h =>
          G.stageEUAt σ h who +
            expect (G.stageActionDist σ h) (fun a =>
              expect (G.transition h.2 a) (v (t + 1))) + e t) :=
        expect_mono _ _ _ (hbellman t)
      _ = r t + V (t + 1) + e t := by
        rw [expect_add, expect_add, expect_const,
          ← G.expectedStateValue_succ]
        rfl
  change (∑ t ∈ Finset.range T, Z t) + V 0 ≤
    (∑ t ∈ Finset.range T, r t) + V T +
      ∑ t ∈ Finset.range T, e t
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      linarith [hstep T]

/-- Finite-average lower verification that retains the actual average of the
state-dependent target.  This is the form needed when discounted values
converge to a harmonic function rather than to one constant across states. -/
theorem finiteAveragePayoff_ge_targetAverage_of_averageReward_bellman_le
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State)
    (who : ι) (z v : ℕ → G.State → ℝ) (e : ℕ → ℝ) {T : ℕ}
    {C0 CT : ℝ} (hv0 : ∀ s, |v 0 s| ≤ C0)
    (hvT : ∀ s, |v T s| ≤ CT)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      z t h.2 + v t h.2 ≤ G.stageEUAt σ h who +
        expect (G.stageActionDist σ h) (fun a =>
          expect (G.transition h.2 a) (v (t + 1))) + e t)
    (hT : 0 < T) :
    (T : ℝ)⁻¹ *
          ∑ t ∈ Finset.range T, G.expectedStateValue σ s₀ t (z t) -
        (C0 + CT) / (T : ℝ) -
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t ≤
      G.finiteAveragePayoff s₀ T σ who := by
  have htel := G.finitePayoff_telescope_of_averageReward_bellman_le
    σ s₀ who z v e hbellman T
  have hV0 : -C0 ≤ G.expectedStateValue σ s₀ 0 (v 0) := by
    have habs := abs_expect_le_of_abs_le
      (G.histDist σ s₀ 0) (fun h => v 0 h.2) fun h => hv0 h.2
    exact neg_le_of_abs_le habs
  have hVT : G.expectedStateValue σ s₀ T (v T) ≤ CT := by
    have habs := abs_expect_le_of_abs_le
      (G.histDist σ s₀ T) (fun h => v T h.2) fun h => hvT h.2
    exact le_of_abs_le habs
  have hraw :
      (∑ t ∈ Finset.range T, G.expectedStateValue σ s₀ t (z t)) -
          C0 - CT - ∑ t ∈ Finset.range T, e t ≤
        ∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who := by
    linarith
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  calc
    (T : ℝ)⁻¹ *
            ∑ t ∈ Finset.range T, G.expectedStateValue σ s₀ t (z t) -
          (C0 + CT) / (T : ℝ) -
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t =
        ((∑ t ∈ Finset.range T,
              G.expectedStateValue σ s₀ t (z t)) - C0 - CT -
            ∑ t ∈ Finset.range T, e t) / (T : ℝ) := by
      field_simp [ne_of_gt hTreal]
      ring
    _ ≤ (∑ t ∈ Finset.range T,
          G.expectedStagePayoff σ s₀ t who) / (T : ℝ) :=
      (div_le_div_iff_of_pos_right hTreal).2 hraw
    _ = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          G.expectedStagePayoff σ s₀ t who := by
      rw [div_eq_inv_mul]

/-- Finite-average lower verification with separate bounds on the initial
and terminal time-varying biases.  Unlike the uniform-bias wrapper below,
this form permits a bias schedule that grows with the horizon, provided its
terminal growth is sublinear. -/
theorem finiteAveragePayoff_ge_of_averageReward_bellman_le_endpoints
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State)
    (who : ι) (z v : ℕ → G.State → ℝ) (e : ℕ → ℝ) {T : ℕ}
    {c C0 CT : ℝ} (hz : ∀ t s, c ≤ z t s)
    (hv0 : ∀ s, |v 0 s| ≤ C0) (hvT : ∀ s, |v T s| ≤ CT)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      z t h.2 + v t h.2 ≤ G.stageEUAt σ h who +
        expect (G.stageActionDist σ h) (fun a =>
          expect (G.transition h.2 a) (v (t + 1))) + e t)
    (hT : 0 < T) :
    c - (C0 + CT) / (T : ℝ) -
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t ≤
      G.finiteAveragePayoff s₀ T σ who := by
  have htel := G.finitePayoff_telescope_of_averageReward_bellman_le
    σ s₀ who z v e hbellman T
  have hZ : ∀ t, c ≤ G.expectedStateValue σ s₀ t (z t) := by
    intro t
    calc
      c = expect (G.histDist σ s₀ t) (fun _ => c) :=
        (expect_const _ _).symm
      _ ≤ expect (G.histDist σ s₀ t) (fun h => z t h.2) :=
        expect_mono _ _ _ fun h => hz t h.2
  have hsumZ : (T : ℝ) * c ≤
      ∑ t ∈ Finset.range T, G.expectedStateValue σ s₀ t (z t) := by
    calc
      (T : ℝ) * c = ∑ _t ∈ Finset.range T, c := by simp
      _ ≤ ∑ t ∈ Finset.range T,
          G.expectedStateValue σ s₀ t (z t) :=
        Finset.sum_le_sum fun t _ => hZ t
  have hV0 : -C0 ≤ G.expectedStateValue σ s₀ 0 (v 0) := by
    have habs := abs_expect_le_of_abs_le
      (G.histDist σ s₀ 0) (fun h => v 0 h.2) fun h => hv0 h.2
    exact neg_le_of_abs_le habs
  have hVT : G.expectedStateValue σ s₀ T (v T) ≤ CT := by
    have habs := abs_expect_le_of_abs_le
      (G.histDist σ s₀ T) (fun h => v T h.2) fun h => hvT h.2
    exact le_of_abs_le habs
  have hraw : (T : ℝ) * c - C0 - CT -
      (∑ t ∈ Finset.range T, e t) ≤
        ∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who := by
    linarith
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hsumPayoff :
      (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who) =
        (T : ℝ) * G.finiteAveragePayoff s₀ T σ who := by
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    field_simp
  rw [hsumPayoff] at hraw
  rw [show c - (C0 + CT) / (T : ℝ) -
      (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, e t) =
      ((T : ℝ) * c - C0 - CT - (∑ t ∈ Finset.range T, e t)) /
        (T : ℝ) by
    field_simp
    ring]
  exact (div_le_iff₀ hTreal).2 (by simpa [mul_comm] using hraw)

/-- A uniformly lower-bounded target and bounded time-varying bias turn the
historywise average-reward Bellman inequality into a finite-horizon payoff
guarantee.  The only losses are the two boundary biases (`2C / T`) and the
average accumulated Bellman error. -/
theorem finiteAveragePayoff_ge_of_averageReward_bellman_le
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State)
    (who : ι) (z v : ℕ → G.State → ℝ) (e : ℕ → ℝ)
    {c C : ℝ} (hz : ∀ t s, c ≤ z t s) (hv : ∀ t s, |v t s| ≤ C)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      z t h.2 + v t h.2 ≤ G.stageEUAt σ h who +
        expect (G.stageActionDist σ h) (fun a =>
          expect (G.transition h.2 a) (v (t + 1))) + e t)
    {T : ℕ} (hT : 0 < T) :
    c - 2 * C / (T : ℝ) -
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t ≤
      G.finiteAveragePayoff s₀ T σ who := by
  have htel := G.finitePayoff_telescope_of_averageReward_bellman_le
    σ s₀ who z v e hbellman T
  have hZ : ∀ t, c ≤ G.expectedStateValue σ s₀ t (z t) := by
    intro t
    calc
      c = expect (G.histDist σ s₀ t) (fun _ => c) :=
        (expect_const _ _).symm
      _ ≤ expect (G.histDist σ s₀ t) (fun h => z t h.2) :=
        expect_mono _ _ _ fun h => hz t h.2
  have hsumZ : (T : ℝ) * c ≤
      ∑ t ∈ Finset.range T, G.expectedStateValue σ s₀ t (z t) := by
    calc
      (T : ℝ) * c = ∑ _t ∈ Finset.range T, c := by simp
      _ ≤ ∑ t ∈ Finset.range T,
          G.expectedStateValue σ s₀ t (z t) :=
        Finset.sum_le_sum fun t _ => hZ t
  have hV0 : -C ≤ G.expectedStateValue σ s₀ 0 (v 0) := by
    have habs := abs_expect_le_of_abs_le
      (G.histDist σ s₀ 0) (fun h => v 0 h.2) fun h => hv 0 h.2
    exact neg_le_of_abs_le habs
  have hVT : G.expectedStateValue σ s₀ T (v T) ≤ C := by
    have habs := abs_expect_le_of_abs_le
      (G.histDist σ s₀ T) (fun h => v T h.2) fun h => hv T h.2
    exact le_of_abs_le habs
  have hraw : (T : ℝ) * c - 2 * C -
      (∑ t ∈ Finset.range T, e t) ≤
        ∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who := by
    linarith
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hsumPayoff :
      (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who) =
        (T : ℝ) * G.finiteAveragePayoff s₀ T σ who := by
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    field_simp
  rw [hsumPayoff] at hraw
  rw [show c - 2 * C / (T : ℝ) -
      (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, e t) =
      ((T : ℝ) * c - 2 * C - (∑ t ∈ Finset.range T, e t)) /
        (T : ℝ) by
    field_simp]
  exact (div_le_iff₀ hTreal).2 (by simpa [mul_comm] using hraw)

/-- Dual finite-horizon telescoping for an upper average-reward Bellman
certificate. -/
theorem finitePayoff_telescope_of_averageReward_bellman_ge
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State)
    (who : ι) (z v : ℕ → G.State → ℝ) (e : ℕ → ℝ)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      G.stageEUAt σ h who +
          expect (G.stageActionDist σ h) (fun a =>
            expect (G.transition h.2 a) (v (t + 1))) ≤
        z t h.2 + v t h.2 + e t)
    (T : ℕ) :
    (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who) +
        G.expectedStateValue σ s₀ T (v T) ≤
      (∑ t ∈ Finset.range T, G.expectedStateValue σ s₀ t (z t)) +
        G.expectedStateValue σ s₀ 0 (v 0) +
          ∑ t ∈ Finset.range T, e t := by
  let Z : ℕ → ℝ := fun t => G.expectedStateValue σ s₀ t (z t)
  let V : ℕ → ℝ := fun t => G.expectedStateValue σ s₀ t (v t)
  let r : ℕ → ℝ := fun t => G.expectedStagePayoff σ s₀ t who
  have hstep : ∀ t, r t + V (t + 1) ≤ Z t + V t + e t := by
    intro t
    calc
      r t + V (t + 1) = expect (G.histDist σ s₀ t) (fun h =>
          G.stageEUAt σ h who +
            expect (G.stageActionDist σ h) (fun a =>
              expect (G.transition h.2 a) (v (t + 1)))) := by
        rw [expect_add, ← G.expectedStateValue_succ]
        rfl
      _ ≤ expect (G.histDist σ s₀ t) (fun h =>
          z t h.2 + v t h.2 + e t) :=
        expect_mono _ _ _ (hbellman t)
      _ = Z t + V t + e t := by
        rw [expect_add, expect_add, expect_const]
        rfl
  change (∑ t ∈ Finset.range T, r t) + V T ≤
    (∑ t ∈ Finset.range T, Z t) + V 0 +
      ∑ t ∈ Finset.range T, e t
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      linarith [hstep T]

/-- Dual finite-average verification retaining the state-dependent target
average. -/
theorem finiteAveragePayoff_le_targetAverage_of_averageReward_bellman_ge
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State)
    (who : ι) (z v : ℕ → G.State → ℝ) (e : ℕ → ℝ) {T : ℕ}
    {C0 CT : ℝ} (hv0 : ∀ s, |v 0 s| ≤ C0)
    (hvT : ∀ s, |v T s| ≤ CT)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      G.stageEUAt σ h who +
          expect (G.stageActionDist σ h) (fun a =>
            expect (G.transition h.2 a) (v (t + 1))) ≤
        z t h.2 + v t h.2 + e t)
    (hT : 0 < T) :
    G.finiteAveragePayoff s₀ T σ who ≤
      (T : ℝ)⁻¹ *
          ∑ t ∈ Finset.range T, G.expectedStateValue σ s₀ t (z t) +
        (C0 + CT) / (T : ℝ) +
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t := by
  have htel := G.finitePayoff_telescope_of_averageReward_bellman_ge
    σ s₀ who z v e hbellman T
  have hV0 : G.expectedStateValue σ s₀ 0 (v 0) ≤ C0 := by
    have habs := abs_expect_le_of_abs_le
      (G.histDist σ s₀ 0) (fun h => v 0 h.2) fun h => hv0 h.2
    exact le_of_abs_le habs
  have hVT : -CT ≤ G.expectedStateValue σ s₀ T (v T) := by
    have habs := abs_expect_le_of_abs_le
      (G.histDist σ s₀ T) (fun h => v T h.2) fun h => hvT h.2
    exact neg_le_of_abs_le habs
  have hraw :
      (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who) ≤
        (∑ t ∈ Finset.range T, G.expectedStateValue σ s₀ t (z t)) +
          C0 + CT + ∑ t ∈ Finset.range T, e t := by
    linarith
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  calc
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          G.expectedStagePayoff σ s₀ t who =
        (∑ t ∈ Finset.range T,
          G.expectedStagePayoff σ s₀ t who) / (T : ℝ) := by
      rw [div_eq_inv_mul]
    _ ≤ ((∑ t ∈ Finset.range T,
            G.expectedStateValue σ s₀ t (z t)) + C0 + CT +
          ∑ t ∈ Finset.range T, e t) / (T : ℝ) :=
      (div_le_div_iff_of_pos_right hTreal).2 hraw
    _ = (T : ℝ)⁻¹ *
            ∑ t ∈ Finset.range T, G.expectedStateValue σ s₀ t (z t) +
          (C0 + CT) / (T : ℝ) +
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t := by
      field_simp [ne_of_gt hTreal]
      ring

/-- Dual finite-average verification with separate initial and terminal bias
bounds. -/
theorem finiteAveragePayoff_le_of_averageReward_bellman_ge_endpoints
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State)
    (who : ι) (z v : ℕ → G.State → ℝ) (e : ℕ → ℝ) {T : ℕ}
    {c C0 CT : ℝ} (hz : ∀ t s, z t s ≤ c)
    (hv0 : ∀ s, |v 0 s| ≤ C0) (hvT : ∀ s, |v T s| ≤ CT)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      G.stageEUAt σ h who +
          expect (G.stageActionDist σ h) (fun a =>
            expect (G.transition h.2 a) (v (t + 1))) ≤
        z t h.2 + v t h.2 + e t)
    (hT : 0 < T) :
    G.finiteAveragePayoff s₀ T σ who ≤
      c + (C0 + CT) / (T : ℝ) +
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t := by
  have htel := G.finitePayoff_telescope_of_averageReward_bellman_ge
    σ s₀ who z v e hbellman T
  have hZ : ∀ t, G.expectedStateValue σ s₀ t (z t) ≤ c := by
    intro t
    calc
      expect (G.histDist σ s₀ t) (fun h => z t h.2) ≤
          expect (G.histDist σ s₀ t) (fun _ => c) :=
        expect_mono _ _ _ fun h => hz t h.2
      _ = c := expect_const _ _
  have hsumZ : (∑ t ∈ Finset.range T,
      G.expectedStateValue σ s₀ t (z t)) ≤ (T : ℝ) * c := by
    calc
      (∑ t ∈ Finset.range T, G.expectedStateValue σ s₀ t (z t)) ≤
          ∑ _t ∈ Finset.range T, c :=
        Finset.sum_le_sum fun t _ => hZ t
      _ = (T : ℝ) * c := by simp
  have hV0 : G.expectedStateValue σ s₀ 0 (v 0) ≤ C0 := by
    have habs := abs_expect_le_of_abs_le
      (G.histDist σ s₀ 0) (fun h => v 0 h.2) fun h => hv0 h.2
    exact le_of_abs_le habs
  have hVT : -CT ≤ G.expectedStateValue σ s₀ T (v T) := by
    have habs := abs_expect_le_of_abs_le
      (G.histDist σ s₀ T) (fun h => v T h.2) fun h => hvT h.2
    exact neg_le_of_abs_le habs
  have hraw : (∑ t ∈ Finset.range T,
      G.expectedStagePayoff σ s₀ t who) ≤
        (T : ℝ) * c + C0 + CT + ∑ t ∈ Finset.range T, e t := by
    linarith
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hsumPayoff :
      (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who) =
        (T : ℝ) * G.finiteAveragePayoff s₀ T σ who := by
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    field_simp
  rw [hsumPayoff] at hraw
  rw [show c + (C0 + CT) / (T : ℝ) +
      (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, e t) =
      ((T : ℝ) * c + C0 + CT + (∑ t ∈ Finset.range T, e t)) /
        (T : ℝ) by
    field_simp
    ring]
  exact (le_div_iff₀ hTreal).2 (by simpa [mul_comm] using hraw)

/-- Quantitative upper payoff bound from a uniformly upper-bounded target and
bounded time-varying bias. -/
theorem finiteAveragePayoff_le_of_averageReward_bellman_ge
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State)
    (who : ι) (z v : ℕ → G.State → ℝ) (e : ℕ → ℝ)
    {c C : ℝ} (hz : ∀ t s, z t s ≤ c) (hv : ∀ t s, |v t s| ≤ C)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      G.stageEUAt σ h who +
          expect (G.stageActionDist σ h) (fun a =>
            expect (G.transition h.2 a) (v (t + 1))) ≤
        z t h.2 + v t h.2 + e t)
    {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff s₀ T σ who ≤
      c + 2 * C / (T : ℝ) +
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t := by
  have htel := G.finitePayoff_telescope_of_averageReward_bellman_ge
    σ s₀ who z v e hbellman T
  have hZ : ∀ t, G.expectedStateValue σ s₀ t (z t) ≤ c := by
    intro t
    calc
      expect (G.histDist σ s₀ t) (fun h => z t h.2) ≤
          expect (G.histDist σ s₀ t) (fun _ => c) :=
        expect_mono _ _ _ fun h => hz t h.2
      _ = c := expect_const _ _
  have hsumZ : (∑ t ∈ Finset.range T,
      G.expectedStateValue σ s₀ t (z t)) ≤ (T : ℝ) * c := by
    calc
      (∑ t ∈ Finset.range T, G.expectedStateValue σ s₀ t (z t)) ≤
          ∑ _t ∈ Finset.range T, c :=
        Finset.sum_le_sum fun t _ => hZ t
      _ = (T : ℝ) * c := by simp
  have hV0 : G.expectedStateValue σ s₀ 0 (v 0) ≤ C := by
    have habs := abs_expect_le_of_abs_le
      (G.histDist σ s₀ 0) (fun h => v 0 h.2) fun h => hv 0 h.2
    exact le_of_abs_le habs
  have hVT : -C ≤ G.expectedStateValue σ s₀ T (v T) := by
    have habs := abs_expect_le_of_abs_le
      (G.histDist σ s₀ T) (fun h => v T h.2) fun h => hv T h.2
    exact neg_le_of_abs_le habs
  have hraw : (∑ t ∈ Finset.range T,
      G.expectedStagePayoff σ s₀ t who) ≤
        (T : ℝ) * c + 2 * C + ∑ t ∈ Finset.range T, e t := by
    linarith
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hsumPayoff :
      (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who) =
        (T : ℝ) * G.finiteAveragePayoff s₀ T σ who := by
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    field_simp
  rw [hsumPayoff] at hraw
  rw [show c + 2 * C / (T : ℝ) +
      (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, e t) =
      ((T : ℝ) * c + 2 * C + (∑ t ∈ Finset.range T, e t)) /
        (T : ℝ) by
    field_simp]
  exact (le_div_iff₀ hTreal).2 (by simpa [mul_comm] using hraw)

/-- A discounted Bellman lower certificate yields an explicit finite-horizon
average-payoff guarantee.  The boundary loss is controlled by the scaled bias
`β/(1-β) · v`; a discounted residual `δ` costs `δ/(1-β)` per stage. -/
theorem finiteAveragePayoff_ge_of_discounted_bellman_le
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State)
    (who : ι) (v : G.State → ℝ) {β δ c C : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hz : ∀ s, c ≤ v s)
    (hv : ∀ s, |v s| ≤ C)
    (hdisc : ∀ (t : ℕ) (h : G.Hist t),
      v h.2 ≤ (1 - β) * G.stageEUAt σ h who +
        β * expect (G.stageActionDist σ h) (fun a =>
          expect (G.transition h.2 a) v) + δ)
    {T : ℕ} (hT : 0 < T) :
    c - 2 * ((β / (1 - β)) * C) / (T : ℝ) - δ / (1 - β) ≤
      G.finiteAveragePayoff s₀ T σ who := by
  have hden : 0 < 1 - β := by linarith
  have hq : 0 ≤ β / (1 - β) := div_nonneg hβ0 hden.le
  have hbias : ∀ (t : ℕ) (s : G.State),
      |(β / (1 - β)) * v s| ≤ (β / (1 - β)) * C := by
    intro _ s
    rw [abs_mul, abs_of_nonneg hq]
    exact mul_le_mul_of_nonneg_left (hv s) hq
  have havg := G.finiteAveragePayoff_ge_of_averageReward_bellman_le
    σ s₀ who (fun _ => v)
      (fun _ s => (β / (1 - β)) * v s)
      (fun _ => δ / (1 - β))
      (fun _ s => hz s) hbias
      (G.averageReward_bellman_le_of_discounted_bellman_le
        σ who v hβ1 hdisc) hT
  have hTreal : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have herr : (T : ℝ)⁻¹ *
      (∑ t ∈ Finset.range T, δ / (1 - β)) = δ / (1 - β) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rwa [herr] at havg

/-- Dual finite-horizon upper bound from a discounted Bellman upper
certificate. -/
theorem finiteAveragePayoff_le_of_discounted_bellman_ge
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State)
    (who : ι) (v : G.State → ℝ) {β δ c C : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hz : ∀ s, v s ≤ c)
    (hv : ∀ s, |v s| ≤ C)
    (hdisc : ∀ (t : ℕ) (h : G.Hist t),
      (1 - β) * G.stageEUAt σ h who +
          β * expect (G.stageActionDist σ h) (fun a =>
            expect (G.transition h.2 a) v) ≤ v h.2 + δ)
    {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff s₀ T σ who ≤
      c + 2 * ((β / (1 - β)) * C) / (T : ℝ) + δ / (1 - β) := by
  have hden : 0 < 1 - β := by linarith
  have hq : 0 ≤ β / (1 - β) := div_nonneg hβ0 hden.le
  have hbias : ∀ (t : ℕ) (s : G.State),
      |(β / (1 - β)) * v s| ≤ (β / (1 - β)) * C := by
    intro _ s
    rw [abs_mul, abs_of_nonneg hq]
    exact mul_le_mul_of_nonneg_left (hv s) hq
  have havg := G.finiteAveragePayoff_le_of_averageReward_bellman_ge
    σ s₀ who (fun _ => v)
      (fun _ s => (β / (1 - β)) * v s)
      (fun _ => δ / (1 - β))
      (fun _ s => hz s) hbias
      (G.averageReward_bellman_ge_of_discounted_bellman_ge
        σ who v hβ1 hdisc) hT
  have hTreal : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have herr : (T : ℝ)⁻¹ *
      (∑ t ∈ Finset.range T, δ / (1 - β)) = δ / (1 - β) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rwa [herr] at havg

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
