/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Congestion.Basic
import GameTheory.Concepts.Welfare.Smoothness

/-!
# Affine congestion games: smoothness and the 5/2 price-of-anarchy bound

Christodoulou–Koutsoupias / Awerbuch–Azar–Epstein (2005): in atomic
congestion games with affine delays, the social cost of any pure Nash
equilibrium is at most `5/2` times the optimal social cost. The proof is a
smoothness argument: affine congestion games are `(5/3, -1/3)`-smooth in the
utility form of `Concepts/Welfare/Smoothness` (equivalently `(5/3, 1/3)`-cost
smooth), driven by the integer inequality `y(z+1) ≤ (5/3)y² + (1/3)z²`.

## Main results

* `CongestionGame.ck_inequality` — the Christodoulou–Koutsoupias pairing bound
* `CongestionGame.sum_deviation_cost_le` — cost-form `(5/3, 1/3)`-smoothness
* `CongestionGame.isSmooth_of_isAffine` — the `KernelGame.IsSmooth` instance
* `CongestionGame.socialCost_nash_le` — pure price of anarchy `≤ 5/2`
* `CongestionGame.correlated_socialCost_le` — robust price of anarchy: the
  same constant for every coarse correlated equilibrium
-/

open scoped BigOperators

namespace GameTheory

namespace CongestionGame

variable {ι : Type} [Fintype ι]

/-- A congestion game is affine when every delay is a nonnegative affine
function of the load: `delay r n = a r * n + b r` with `a r, b r ≥ 0`. -/
structure IsAffine (C : CongestionGame ι) (a b : C.Resource → ℝ) : Prop where
  delay_eq : ∀ r n, C.delay r n = a r * n + b r
  a_nonneg : ∀ r, 0 ≤ a r
  b_nonneg : ∀ r, 0 ≤ b r

/-- Affine delays are monotone in the load. -/
theorem IsAffine.delay_mono {C : CongestionGame ι} {a b : C.Resource → ℝ}
    (h : C.IsAffine a b) (r : C.Resource) {m n : ℕ} (hmn : m ≤ n) :
    C.delay r m ≤ C.delay r n := by
  rw [h.delay_eq, h.delay_eq]
  have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  nlinarith [h.a_nonneg r]

/-- The Christodoulou–Koutsoupias pairing inequality: for natural numbers
`y`, `z`, `y (z + 1) ≤ (5/3) y² + (1/3) z²`. Integrality is essential: the
inequality fails for real `y` (e.g. `y = 1/2`, `z = 1`). -/
theorem ck_inequality (y z : ℕ) :
    (y : ℝ) * (z + 1) ≤ 5 / 3 * (y : ℝ) ^ 2 + 1 / 3 * (z : ℝ) ^ 2 := by
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  rcases Nat.lt_or_ge y 1 with h1 | h1
  · obtain rfl : y = 0 := by omega
    push_cast
    nlinarith
  rcases Nat.lt_or_ge y 2 with h2 | h2
  · obtain rfl : y = 1 := by omega
    rcases Nat.lt_or_ge z 2 with hz2 | hz2
    · interval_cases z <;> norm_num
    · have hz2' : (2 : ℝ) ≤ z := by exact_mod_cast hz2
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (z:ℝ) - 2)
        (by linarith : (0:ℝ) ≤ (z:ℝ) - 1)]
  · have h2' : (2 : ℝ) ≤ y := by exact_mod_cast h2
    nlinarith [sq_nonneg (2 * (z : ℝ) - 3 * (y : ℝ))]

/-- Cost-form smoothness of affine congestion games: the total cost of
one-shot deviations from `σ` into any target profile `τ` is at most
`(5/3) C(τ) + (1/3) C(σ)`. -/
theorem sum_deviation_cost_le [DecidableEq ι] (C : CongestionGame ι) {a b : C.Resource → ℝ}
    (h : C.IsAffine a b) (σ τ : C.Profile) :
    ∑ i, C.playerCost (Function.update σ i (τ i)) i
      ≤ 5 / 3 * C.socialCost τ + 1 / 3 * C.socialCost σ := by
  have hstep : ∀ i, C.playerCost (Function.update σ i (τ i)) i
      ≤ ∑ r ∈ C.resources i (τ i), C.delay r (C.congestion σ r + 1) := by
    intro i
    rw [playerCost, Function.update_self]
    refine Finset.sum_le_sum fun r hr => ?_
    rw [C.congestion_update σ i (τ i) r, if_pos hr]
    exact h.delay_mono r
      (Nat.add_le_add_right (C.congestionWithout_le_congestion σ i r) 1)
  calc ∑ i, C.playerCost (Function.update σ i (τ i)) i
      ≤ ∑ i, ∑ r ∈ C.resources i (τ i), C.delay r (C.congestion σ r + 1) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = ∑ r : C.Resource,
          (C.congestion τ r : ℝ) * C.delay r (C.congestion σ r + 1) :=
        C.sum_players_sum_resources τ _
    _ ≤ 5 / 3 * C.socialCost τ + 1 / 3 * C.socialCost σ := by
        rw [C.socialCost_eq_sum_load_delay τ, C.socialCost_eq_sum_load_delay σ,
          Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun r _ => ?_
        rw [h.delay_eq, h.delay_eq, h.delay_eq]
        have hck := ck_inequality (C.congestion τ r) (C.congestion σ r)
        have ha := h.a_nonneg r
        have hb := h.b_nonneg r
        have hy : (0 : ℝ) ≤ C.congestion τ r := Nat.cast_nonneg _
        have hz : (0 : ℝ) ≤ C.congestion σ r := Nat.cast_nonneg _
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hck ha, mul_nonneg hb hy,
          mul_nonneg hb hz]

/-- Social welfare of the induced strategic game is the negated social cost. -/
theorem socialWelfare_toKernelGame (C : CongestionGame ι) (σ : C.Profile) :
    C.toKernelGame.socialWelfare σ = -C.socialCost σ := by
  rw [KernelGame.socialWelfare, socialCost]
  simp only [eu_toKernelGame]
  rw [← Finset.sum_neg_distrib]

/-- Affine congestion games are `(5/3, -1/3)`-smooth in the utility
(negated-cost) form; equivalently, `(5/3, 1/3)`-smooth as cost games. -/
theorem isSmooth_of_isAffine [DecidableEq ι] (C : CongestionGame ι)
    {a b : C.Resource → ℝ} (h : C.IsAffine a b) :
    C.toKernelGame.IsSmooth (5 / 3) (-(1 / 3)) := by
  intro s t
  rw [socialWelfare_toKernelGame, socialWelfare_toKernelGame]
  have hdev := C.sum_deviation_cost_le h s t
  calc 5 / 3 * -C.socialCost t - -(1 / 3) * -C.socialCost s
      = -(5 / 3 * C.socialCost t + 1 / 3 * C.socialCost s) := by ring
    _ ≤ -∑ i, C.playerCost (Function.update s i (t i)) i := by linarith
    _ = ∑ i, C.toKernelGame.eu (Function.update s i (t i)) i := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => (eu_toKernelGame C _ i).symm

/-- **Price of anarchy of affine congestion games**
(Christodoulou–Koutsoupias, Awerbuch–Azar–Epstein): at any pure Nash
equilibrium the social cost is at most `5/2` times the social cost of any
profile — in particular of the optimum. -/
theorem socialCost_nash_le [DecidableEq ι] (C : CongestionGame ι)
    {a b : C.Resource → ℝ} (h : C.IsAffine a b) {σ : C.Profile}
    (hσ : C.toKernelGame.IsNash σ) (τ : C.Profile) :
    C.socialCost σ ≤ 5 / 2 * C.socialCost τ := by
  have hb := KernelGame.IsSmooth.nash_bound C.toKernelGame
    (C.isSmooth_of_isAffine h) hσ τ
  rw [socialWelfare_toKernelGame, socialWelfare_toKernelGame] at hb
  linarith

/-- **Robust price of anarchy** (Roughgarden): the affine `5/2` bound extends
beyond pure Nash equilibria to every coarse correlated equilibrium — the
expected total cost `-(∑ i, correlatedEu ν i)` is at most `5/2` times the
social cost of any profile. In particular no-regret learning dynamics inherit
the bound in the limit. -/
theorem correlated_socialCost_le [DecidableEq ι] (C : CongestionGame ι)
    {a b : C.Resource → ℝ} (h : C.IsAffine a b)
    {ν : PMF (KernelGame.Profile C.toKernelGame)}
    (hν : C.toKernelGame.IsCoarseCorrelatedEq ν) (τ : C.Profile) :
    -(∑ i, C.toKernelGame.correlatedEu ν i) ≤ 5 / 2 * C.socialCost τ := by
  haveI (i : ι) : Fintype (C.toKernelGame.Strategy i) := C.instFintypeStrategy i
  haveI : Finite (KernelGame.Profile C.toKernelGame) := Pi.finite
  haveI : Finite C.toKernelGame.Outcome :=
    (Pi.finite : Finite (∀ i, C.StrategySet i))
  have hb := KernelGame.IsSmooth.coarseCorrelated_bound C.toKernelGame
    (C.isSmooth_of_isAffine h) hν τ
  rw [socialWelfare_toKernelGame] at hb
  linarith

end CongestionGame

end GameTheory
