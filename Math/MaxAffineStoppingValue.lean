/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The max-affine stopping operator and its anchored value

Fix a stopping payoff `A`, a stage reward `T` and a survival probability
`P ∈ [0, 1]`, and consider the **max-affine stopping operator**

    Φ(w) = max {A, T + P * w}.

`Φ` is the one-step Bellman operator of a scalar optimal-stopping problem:
stop now for `A`, or take the stage reward `T` and survive with probability
`P` into a continuation valued at `w`.  When `P < 1` this is a genuine metric
contraction and has a unique fixed point.  When `P = 1` the map is only
`1`-Lipschitz and, at `T = 0`, its fixed set is the whole ray `{w ≥ A}` -- not
a point -- so *which* fixed point is the right one depends on where the
iteration starts.

The **anchored value** at a boundary payoff `b` (the value of never acting)
is the least fixed point of `Φ` dominating `b`, computed as the limit of the
`Φ`-iterates started at `b`.  This is well posed whenever some fixed point of
`Φ` is comparable to `b` -- always true once `Φ` has any fixed point at all,
since `ℝ` is linearly ordered -- and it is exactly what an actual supremum
over strategies computes, the never-act option included.

## Why this object

The naive closed form for the value of the affine branch alone, `T / (1 -
P)`, is correct only when `P < 1` **and** it already dominates `A`; at `P = 1`
it divides by zero, and Lean's `x / 0 = 0` convention silently returns *a*
fixed point of the degenerate ray, generally the wrong one.  This file gives
the object that is correct in both regimes and fences the naive formula's
failure at `P = 1` (`naiveClosedForm_eq_anchoredValue_iff_of_P_eq_one`).

## Main definitions

* `Math.MaxAffineStopping.System` -- the bundle `(A, T, P)` with `P ∈ [0,1]`.
* `Math.MaxAffineStopping.System.Φ` -- the max-affine operator.
* `Math.MaxAffineStopping.System.anchoredValue` -- the least fixed point of
  `Φ` dominating a given anchor `b`.

## Main results

* `System.le_Φ_of_le_isFixedPt` / `System.Φ_le_of_isFixedPt_le` -- an anchor
  below (resp. above) some fixed point is itself a subsolution (resp.
  supersolution) of `Φ`, which is what starts the monotone iteration.
* `System.tendsto_iterate_anchoredValue_of_le_isFixedPt` /
  `..._of_isFixedPt_le` -- the anchored value is the limit of the
  `Φ`-iterates from `b`; existence is a monotone bounded sequence argument.
* `System.isFixedPt_anchoredValue_of_le_isFixedPt` / `..._of_isFixedPt_le` --
  the anchored value is itself a fixed point of `Φ`.
* `System.existsUnique_isFixedPt_of_P_lt_one` and
  `System.anchoredValue_eq_of_P_lt_one` -- **regime dichotomy, `P < 1`**: the
  fixed point is unique, and the anchored value equals it for every anchor.
* `System.isFixedPt_iff_of_P_eq_one_of_T_eq_zero` and
  `System.anchoredValue_eq_max_of_P_eq_one_of_T_eq_zero` -- **regime
  dichotomy, `P = 1`, `T = 0`**: the fixed set is exactly `{w ≥ A}`, and the
  anchored value is `max A b`.
* `System.naiveClosedForm_eq_anchoredValue_iff_of_P_eq_one_of_T_eq_zero` --
  **the fence**: the naive `T / (1 - P)` closed form agrees with the anchored
  value at `P = 1` only in the accident `max A b = 0`.
-/

set_option autoImplicit false

noncomputable section

namespace Math.MaxAffineStopping

/-- A max-affine stopping system: the payoff `A` for stopping immediately,
the stage reward `T` earned before continuing, and the survival probability
`P ∈ [0, 1]` carried into the continuation value. -/
structure System where
  /-- The payoff for stopping (acting) immediately. -/
  A : ℝ
  /-- The stage reward earned before continuing. -/
  T : ℝ
  /-- The survival probability applied to the continuation value. -/
  P : ℝ
  /-- Survival is nonnegative. -/
  P_nonneg : 0 ≤ P
  /-- Survival is at most one. -/
  P_le_one : P ≤ 1

namespace System

variable (s : System)

/-! ## The operator -/

/-- The **max-affine stopping operator** `Φ(w) = max {A, T + P * w}`: stop now
for `A`, or take the stage reward `T` and survive with probability `P` into
the continuation `w`. -/
def Φ (w : ℝ) : ℝ := max s.A (s.T + s.P * w)

/-- `Φ` never falls below the stop payoff: acting is always available. -/
theorem A_le_Φ (w : ℝ) : s.A ≤ s.Φ w := le_max_left _ _

/-- `Φ` is monotone: a better continuation is never worse to hold. -/
theorem monotone_Φ : Monotone s.Φ := by
  intro x y hxy
  refine max_le_max le_rfl ?_
  nlinarith [s.P_nonneg]

/-- `Φ` is continuous, being a `max` of a constant and an affine function. -/
theorem continuous_Φ : Continuous s.Φ :=
  continuous_const.max (continuous_const.add (continuous_const.mul continuous_id))

/-- `Φ` is `P`-Lipschitz for every `P ∈ [0, 1]`, not only `P < 1`: the stop
branch is constant and the continuation branch scales by `P`. -/
theorem abs_Φ_sub_Φ_le (w₁ w₂ : ℝ) : |s.Φ w₁ - s.Φ w₂| ≤ s.P * |w₁ - w₂| := by
  have hmax : |max s.A (s.T + s.P * w₁) - max s.A (s.T + s.P * w₂)| ≤
      |(s.T + s.P * w₁) - (s.T + s.P * w₂)| := by
    rw [max_comm s.A (s.T + s.P * w₁), max_comm s.A (s.T + s.P * w₂)]
    exact abs_max_sub_max_le_abs _ _ _
  refine hmax.trans_eq ?_
  rw [show s.T + s.P * w₁ - (s.T + s.P * w₂) = s.P * (w₁ - w₂) by ring, abs_mul,
    abs_of_nonneg s.P_nonneg]

/-! ## Manufacturing subsolutions and supersolutions from a fixed point

`ℝ` is linearly ordered, so an anchor `b` and any fixed point `y` are always
comparable.  Whichever side `b` falls on, it inherits the corresponding
one-sided monotonicity property, which is exactly what starts the monotone
iteration below. -/

/-- An anchor dominated by some fixed point of `Φ` is itself a subsolution:
`Φ` does not decrease it.  This is the algebraic core of the anchored-value
construction. -/
theorem le_Φ_of_le_isFixedPt {b y : ℝ} (hy : Function.IsFixedPt s.Φ y) (hby : b ≤ y) :
    b ≤ s.Φ b := by
  have hy' : max s.A (s.T + s.P * y) = y := hy
  rcases le_total s.A (s.T + s.P * y) with hcase | hcase
  · have haff : s.T + s.P * y = y := (max_eq_right hcase).symm.trans hy'
    have hprod : (0 : ℝ) ≤ (1 - s.P) * (y - b) :=
      mul_nonneg (sub_nonneg.mpr s.P_le_one) (sub_nonneg.mpr hby)
    calc b ≤ s.T + s.P * b := by nlinarith [hprod]
      _ ≤ s.Φ b := le_max_right _ _
  · have hya : s.A = y := (max_eq_left hcase).symm.trans hy'
    calc b ≤ y := hby
      _ = s.A := hya.symm
      _ ≤ s.Φ b := s.A_le_Φ b

/-- An anchor dominating some fixed point of `Φ` is itself a supersolution:
`Φ` does not increase it.  The dual of `le_Φ_of_le_isFixedPt`. -/
theorem Φ_le_of_isFixedPt_le {b y : ℝ} (hy : Function.IsFixedPt s.Φ y) (hyb : y ≤ b) :
    s.Φ b ≤ b := by
  have hy' : max s.A (s.T + s.P * y) = y := hy
  rcases le_total s.A (s.T + s.P * y) with hcase | hcase
  · have haff : s.T + s.P * y = y := (max_eq_right hcase).symm.trans hy'
    have hprod : (0 : ℝ) ≤ (1 - s.P) * (b - y) :=
      mul_nonneg (sub_nonneg.mpr s.P_le_one) (sub_nonneg.mpr hyb)
    refine max_le ?_ (by nlinarith [hprod])
    calc s.A ≤ s.T + s.P * y := hcase
      _ = y := haff
      _ ≤ b := hyb
  · have hya : s.A = y := (max_eq_left hcase).symm.trans hy'
    have haff : s.T + s.P * y ≤ y := by rw [hya] at hcase; linarith
    have hprod : (0 : ℝ) ≤ (1 - s.P) * (b - y) :=
      mul_nonneg (sub_nonneg.mpr s.P_le_one) (sub_nonneg.mpr hyb)
    refine max_le (by rw [hya]; exact hyb) ?_
    nlinarith [hprod]

/-! ## The anchored value -/

/-- The **anchored value** at anchor `b`: the least fixed point of `Φ`
dominating `b`, computed as the limit of the `Φ`-iterates started at `b`.
Since `Φ` is monotone and `ℝ` is linearly ordered, `b` is always either a
subsolution or a supersolution of `Φ`; the two branches below pick out the
matching one-sided limit.  Both formulas compute the genuine iterate limit
whenever some fixed point of `Φ` is comparable to `b`
(`tendsto_iterate_anchoredValue_of_le_isFixedPt` and its dual). -/
def anchoredValue (b : ℝ) : ℝ :=
  if b ≤ s.Φ b then ⨆ n : ℕ, s.Φ^[n] b else ⨅ n : ℕ, s.Φ^[n] b

/-- **Existence of the anchored value, subsolution case.**  If `b` is
dominated by some fixed point `y`, the `Φ`-iterates from `b` increase
monotonically -- bounded above by `y` -- so they converge, to the anchored
value by definition. -/
theorem tendsto_iterate_anchoredValue_of_le_isFixedPt {b y : ℝ}
    (hy : Function.IsFixedPt s.Φ y) (hby : b ≤ y) :
    Filter.Tendsto (fun n : ℕ => s.Φ^[n] b) Filter.atTop (nhds (s.anchoredValue b)) := by
  have hsub : b ≤ s.Φ b := s.le_Φ_of_le_isFixedPt hy hby
  have hmono : Monotone (fun n : ℕ => s.Φ^[n] b) := s.monotone_Φ.monotone_iterate_of_le_map hsub
  have hbdd : BddAbove (Set.range (fun n : ℕ => s.Φ^[n] b)) := by
    refine ⟨y, ?_⟩
    rintro _ ⟨n, rfl⟩
    calc s.Φ^[n] b ≤ s.Φ^[n] y := s.monotone_Φ.iterate n hby
      _ = y := Function.iterate_fixed hy n
  have hval : s.anchoredValue b = ⨆ n : ℕ, s.Φ^[n] b := if_pos hsub
  rw [hval]
  exact tendsto_atTop_ciSup hmono hbdd

/-- **The anchored value is a fixed point, subsolution case.**  The limit of
a convergent orbit of a continuous map is itself a fixed point. -/
theorem isFixedPt_anchoredValue_of_le_isFixedPt {b y : ℝ}
    (hy : Function.IsFixedPt s.Φ y) (hby : b ≤ y) :
    Function.IsFixedPt s.Φ (s.anchoredValue b) := by
  have htendsto := s.tendsto_iterate_anchoredValue_of_le_isFixedPt hy hby
  have hcont : Filter.Tendsto (fun n : ℕ => s.Φ (s.Φ^[n] b)) Filter.atTop
      (nhds (s.Φ (s.anchoredValue b))) :=
    (s.continuous_Φ.tendsto (s.anchoredValue b)).comp htendsto
  have heq : (fun n : ℕ => s.Φ (s.Φ^[n] b)) = fun n : ℕ => s.Φ^[n + 1] b := by
    funext n; rw [Function.iterate_succ_apply']
  rw [heq] at hcont
  have hshift : Filter.Tendsto (fun n : ℕ => s.Φ^[n + 1] b) Filter.atTop
      (nhds (s.anchoredValue b)) := htendsto.comp (Filter.tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hcont hshift

/-- The anchored value dominates its anchor, subsolution case. -/
theorem le_anchoredValue_of_le_isFixedPt {b y : ℝ}
    (hy : Function.IsFixedPt s.Φ y) (hby : b ≤ y) : b ≤ s.anchoredValue b := by
  have hval : s.anchoredValue b = ⨆ n : ℕ, s.Φ^[n] b :=
    if_pos (s.le_Φ_of_le_isFixedPt hy hby)
  rw [hval]
  have hbdd : BddAbove (Set.range (fun n : ℕ => s.Φ^[n] b)) := by
    refine ⟨y, ?_⟩
    rintro _ ⟨n, rfl⟩
    calc s.Φ^[n] b ≤ s.Φ^[n] y := s.monotone_Φ.iterate n hby
      _ = y := Function.iterate_fixed hy n
  simpa using le_ciSup hbdd 0

/-- **Least-ness, subsolution case.**  The anchored value is `≤` every fixed
point dominating the anchor, independently of which such fixed point was
used to prove convergence. -/
theorem anchoredValue_le_of_le_isFixedPt {b y : ℝ}
    (hy : Function.IsFixedPt s.Φ y) (hby : b ≤ y) : s.anchoredValue b ≤ y := by
  have hval : s.anchoredValue b = ⨆ n : ℕ, s.Φ^[n] b :=
    if_pos (s.le_Φ_of_le_isFixedPt hy hby)
  rw [hval]
  refine ciSup_le fun n => ?_
  calc s.Φ^[n] b ≤ s.Φ^[n] y := s.monotone_Φ.iterate n hby
    _ = y := Function.iterate_fixed hy n

/-- **Existence of the anchored value, supersolution case.**  Dual to
`tendsto_iterate_anchoredValue_of_le_isFixedPt`: if `b` dominates some fixed
point, the `Φ`-iterates from `b` decrease monotonically to the anchored
value. -/
theorem tendsto_iterate_anchoredValue_of_isFixedPt_le {b y : ℝ}
    (hy : Function.IsFixedPt s.Φ y) (hyb : y ≤ b) :
    Filter.Tendsto (fun n : ℕ => s.Φ^[n] b) Filter.atTop (nhds (s.anchoredValue b)) := by
  have hsuper : s.Φ b ≤ b := s.Φ_le_of_isFixedPt_le hy hyb
  by_cases hle : b ≤ s.Φ b
  · -- `b` is itself already a fixed point: both branches agree, trivially.
    have hbfix : Function.IsFixedPt s.Φ b := le_antisymm hsuper hle
    have hconst : ∀ n : ℕ, s.Φ^[n] b = b := fun n => Function.iterate_fixed hbfix n
    have hfun : (fun n : ℕ => s.Φ^[n] b) = fun _ : ℕ => b := funext hconst
    have hval : s.anchoredValue b = b := by
      unfold anchoredValue
      rw [if_pos hle, hfun]
      exact ciSup_const
    rw [hval, hfun]
    exact tendsto_const_nhds
  · have hanti : Antitone (fun n : ℕ => s.Φ^[n] b) :=
      s.monotone_Φ.antitone_iterate_of_map_le hsuper
    have hbdd : BddBelow (Set.range (fun n : ℕ => s.Φ^[n] b)) := by
      refine ⟨y, ?_⟩
      rintro _ ⟨n, rfl⟩
      calc y = s.Φ^[n] y := (Function.iterate_fixed hy n).symm
        _ ≤ s.Φ^[n] b := s.monotone_Φ.iterate n hyb
    have hval : s.anchoredValue b = ⨅ n : ℕ, s.Φ^[n] b := if_neg hle
    rw [hval]
    exact tendsto_atTop_ciInf hanti hbdd

/-- **The anchored value is a fixed point, supersolution case.**  Dual to
`isFixedPt_anchoredValue_of_le_isFixedPt`. -/
theorem isFixedPt_anchoredValue_of_isFixedPt_le {b y : ℝ}
    (hy : Function.IsFixedPt s.Φ y) (hyb : y ≤ b) :
    Function.IsFixedPt s.Φ (s.anchoredValue b) := by
  have htendsto := s.tendsto_iterate_anchoredValue_of_isFixedPt_le hy hyb
  have hcont : Filter.Tendsto (fun n : ℕ => s.Φ (s.Φ^[n] b)) Filter.atTop
      (nhds (s.Φ (s.anchoredValue b))) :=
    (s.continuous_Φ.tendsto (s.anchoredValue b)).comp htendsto
  have heq : (fun n : ℕ => s.Φ (s.Φ^[n] b)) = fun n : ℕ => s.Φ^[n + 1] b := by
    funext n; rw [Function.iterate_succ_apply']
  rw [heq] at hcont
  have hshift : Filter.Tendsto (fun n : ℕ => s.Φ^[n + 1] b) Filter.atTop
      (nhds (s.anchoredValue b)) := htendsto.comp (Filter.tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hcont hshift
