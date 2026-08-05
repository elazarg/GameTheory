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
failure at `P = 1` (`naiveClosedForm_eq_anchoredValue_iff_of_P_eq_one_of_T_eq_zero`).

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

## Relation to `CyclicMaxAffineBound`

`Math.CyclicMaxAffine.CyclicSolution` solves a *genuinely cyclic* system,
composing `L` **different** phase maps `w ↦ max {1 - p k, q k * w + p k}`
around a wraparound; the single-phase system here is one such map applied
repeatedly, and only its `L = 1` instance is a `System.Φ` fixed-point
equation, with the extra normalization `A + T = 1` that `CyclicSolution`
imposes and the nonnegativity `p k ≥ 0` in place of the signed data this file
allows.  So this file does not cheaply subsume `CyclicMaxAffineBound`'s
multi-phase composite: the shapes genuinely differ, and no attempt is made
to reformulate one in terms of the other.
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

/-! ## Regime dichotomy: `P < 1`

Here `Φ` is a genuine metric contraction (Lipschitz constant `P < 1`), so it
has a *unique* fixed point, and the anchored value equals it regardless of
where the anchor sits relative to that point. -/

/-- At `P < 1`, `Φ` has a fixed point: the affine solution `T / (1 - P)` of
the continuation-only recursion `w = T + P * w`, capped at the stop payoff
`A`.  This closed form is *correct* here -- contrast the fence theorem below,
which shows it becomes meaningless once `P = 1`. -/
theorem isFixedPt_max_div_of_P_lt_one (hP : s.P < 1) :
    Function.IsFixedPt s.Φ (max s.A (s.T / (1 - s.P))) := by
  change max s.A (s.T + s.P * max s.A (s.T / (1 - s.P))) = max s.A (s.T / (1 - s.P))
  rcases le_total s.A (s.T / (1 - s.P)) with hcase | hcase
  · have heq : s.T + s.P * (s.T / (1 - s.P)) = s.T / (1 - s.P) := by
      have hne : (1 : ℝ) - s.P ≠ 0 := by linarith
      field_simp
      ring
    rw [max_eq_right hcase, heq]
    exact max_eq_right hcase
  · have h2 : s.T ≤ s.A * (1 - s.P) := by
      rwa [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - s.P)] at hcase
    have h3 : s.T + s.P * s.A ≤ s.A := by nlinarith [h2]
    rw [max_eq_left hcase, max_eq_left h3]

/-- At `P < 1`, `Φ` has **at most one** fixed point: any two are within
factor `P` of each other, forcing them to coincide. -/
theorem eq_of_isFixedPt_of_P_lt_one (hP : s.P < 1) {x y : ℝ}
    (hx : Function.IsFixedPt s.Φ x) (hy : Function.IsFixedPt s.Φ y) : x = y := by
  have hlip := s.abs_Φ_sub_Φ_le x y
  rw [hx, hy] at hlip
  have hz : |x - y| = 0 := by nlinarith [abs_nonneg (x - y)]
  have hxy := abs_eq_zero.mp hz
  linarith

/-- **Regime dichotomy, `P < 1`, existence and uniqueness.**  The fixed point
is unique. -/
theorem existsUnique_isFixedPt_of_P_lt_one (hP : s.P < 1) :
    ∃! w, Function.IsFixedPt s.Φ w :=
  ⟨max s.A (s.T / (1 - s.P)), s.isFixedPt_max_div_of_P_lt_one hP,
    fun _ hw => s.eq_of_isFixedPt_of_P_lt_one hP hw (s.isFixedPt_max_div_of_P_lt_one hP)⟩

/-- **Regime dichotomy, `P < 1`, the anchored value.**  The anchored value
equals the unique fixed point *for every anchor* `b`: whichever side of the
fixed point `b` falls on, the anchored value is a fixed point on that same
side, and uniqueness forces it to be the one fixed point there is. -/
theorem anchoredValue_eq_of_P_lt_one (hP : s.P < 1) (b : ℝ) :
    s.anchoredValue b = max s.A (s.T / (1 - s.P)) := by
  have hw : Function.IsFixedPt s.Φ (max s.A (s.T / (1 - s.P))) :=
    s.isFixedPt_max_div_of_P_lt_one hP
  rcases le_total b (max s.A (s.T / (1 - s.P))) with hbw | hbw
  · exact s.eq_of_isFixedPt_of_P_lt_one hP
      (s.isFixedPt_anchoredValue_of_le_isFixedPt hw hbw) hw
  · exact s.eq_of_isFixedPt_of_P_lt_one hP
      (s.isFixedPt_anchoredValue_of_isFixedPt_le hw hbw) hw

/-! ## Regime dichotomy: `P = 1`, `T = 0`

Here `Φ(w) = max {A, w}` is only `1`-Lipschitz, and its fixed set is the
whole ray `{w ≥ A}`, not a point: which fixed point is reached depends on the
anchor, not just on `Φ`. -/

/-- At `P = 1`, `T = 0`, the fixed set of `Φ` is exactly `{w | A ≤ w}`. -/
theorem isFixedPt_iff_of_P_eq_one_of_T_eq_zero (hP : s.P = 1) (hT : s.T = 0) (w : ℝ) :
    Function.IsFixedPt s.Φ w ↔ s.A ≤ w := by
  change max s.A (s.T + s.P * w) = w ↔ s.A ≤ w
  rw [hT, hP, zero_add, one_mul]
  exact ⟨fun h => h ▸ le_max_left _ _, max_eq_right⟩

/-- **Regime dichotomy, `P = 1`, `T = 0`, the anchored value.**  The anchored
value is `max {A, b}`: every anchor is automatically a subsolution here
(`Φ b = max A b ≥ b` always), so the least fixed point dominating it is
exactly the least point of the ray `{w ≥ A}` that also dominates `b`. -/
theorem anchoredValue_eq_max_of_P_eq_one_of_T_eq_zero (hP : s.P = 1) (hT : s.T = 0) (b : ℝ) :
    s.anchoredValue b = max s.A b := by
  have hy : Function.IsFixedPt s.Φ (max s.A b) :=
    (s.isFixedPt_iff_of_P_eq_one_of_T_eq_zero hP hT (max s.A b)).mpr (le_max_left _ _)
  have hby : b ≤ max s.A b := le_max_right _ _
  have hfix := s.isFixedPt_anchoredValue_of_le_isFixedPt hy hby
  have hle := s.anchoredValue_le_of_le_isFixedPt hy hby
  have hge := s.le_anchoredValue_of_le_isFixedPt hy hby
  have hA_le : s.A ≤ s.anchoredValue b :=
    (s.isFixedPt_iff_of_P_eq_one_of_T_eq_zero hP hT _).mp hfix
  exact le_antisymm hle (max_le hA_le hge)

/-! ## The fence: the naive closed form at `P = 1`

The naive closed form `T / (1 - P)` for the affine-only fixed point is
correct at `P < 1` (`isFixedPt_max_div_of_P_lt_one`).  At `P = 1` the
denominator vanishes; Lean's `x / 0 = 0` convention turns the whole
expression into the *constant* `0`, independent of `A`, `T`, or the anchor
`b`.  This is exactly the shape of the bug in
`GameTheory.quittingRelaxedCycleGain`'s own `P_who = 1` extension
(`QuittingRelaxedCycleGainIsolatedCoordinate.lean`): dividing by the vanished
survival gap silently discards a term that should have taken part in a
`max`, landing on a fixed point of the ray that need not be the anchored
one. -/

/-- **The fence.**  At `P = 1`, `T = 0`, the naive closed form `T / (1 - P)`
(always `0`, by the division convention) agrees with the anchored value only
in the accident `max A b = 0`.  So reaching for `T / (1 - P)` at `P = 1` is
visibly wrong for every other anchor. -/
theorem naiveClosedForm_eq_anchoredValue_iff_of_P_eq_one_of_T_eq_zero
    (hP : s.P = 1) (hT : s.T = 0) (b : ℝ) :
    s.T / (1 - s.P) = s.anchoredValue b ↔ max s.A b = 0 := by
  rw [hT, hP, sub_self, div_zero, s.anchoredValue_eq_max_of_P_eq_one_of_T_eq_zero hP hT b, eq_comm]

/-- **The fence, concretely.**  At `A = 1`, `T = 0`, `P = 1`, `b = 0` the
naive closed form is `0`, but the anchored value is `1`: quitting is worth
acting on, and `x / 0 = 0` silently throws that away. -/
example : ∃ sys : System, sys.T / (1 - sys.P) ≠ sys.anchoredValue 0 := by
  refine ⟨⟨1, 0, 1, by norm_num, le_refl 1⟩, ?_⟩
  rw [anchoredValue_eq_max_of_P_eq_one_of_T_eq_zero _ rfl rfl 0]
  norm_num

end System

end Math.MaxAffineStopping
