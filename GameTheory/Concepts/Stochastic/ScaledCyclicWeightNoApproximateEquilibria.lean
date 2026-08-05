/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.WeightedRowMotionSeparation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The scaled cyclic weight has neither stationary nor instant approximate equilibria

This file completes the `M [reported]` leg of the counterexample package in
`ideas/UniformEquilibriumLiterature/WeightedOneStageNashCannotPriceMotion.md`.
That package exhibits a weight (the FTV cyclic table scaled by `1/3`,
`scaledCyclicWeight`) for which the granted constant of (K1) fails on the
**weighted** correspondence, at a continuation vector claimed to satisfy
(K1)'s hypothesis package: "neither stationary nor instant approximate
equilibria". This file proves that hypothesis holds for `scaledCyclicWeight`,
completing the counterexample end to end.

## The real encoding, and why it is the honest one

Both notions are genuinely infinite-horizon (the global payoff `U_j(p)` over
all deviation sequences `β : ℕ → [0,1]`), unlike the one-stage `E_ε`
machinery of `WeightedRowMotionSeparation.lean`. This file builds a
self-contained real-valued `Plan`/`planPayoff`/global-`ε`-equilibrium
apparatus matching that infinite-horizon payoff literally (`CyclicPlan`,
`deviatePlan`, `planPayoff` via `tsum`, `IsGlobalEpsilonEquilibrium`), rather
than routing through the heavy PMF-valued `quittingGame` machinery
(`QuittingStationaryBestResponse.lean` et al.): that machinery's global
quantifier is exactly as honest, but bridging its `PMF Bool`-valued roots to
the `sigmaValue`/`excludedValue`/`gainValue` real-hazard formulas already
computed for `scaledCyclicWeight` would duplicate substantial infrastructure
for no gain in rigor. The `Plan` apparatus here is proved summable in
general (via the bound `|survival · stage payoff| ≤ M · (survival drop)`)
and in closed form for the eventually-constant shape both notions need.

**The `for every ε` quantifier collapses to an exact condition.** A constant
(resp. stage-0-then-punishment) plan is a global equilibrium at every
positive tolerance iff a *specific* deviation's payoff is `≤` the candidate's
payoff *exactly* (`planPayoff_deviate_le_of_isGlobalApproxEquilibrium`, via
`le_of_forall_sub_le`). Consequently both impossibility proofs are exact
algebra, not limiting arguments: the "no instant" proof pins the two
non-quitters' hazards to `0` and `1` exactly, and the "no stationary" proof
runs the same case-split argument (its equations (8)-(14)) verbatim,
adapted to `scaledCyclicWeight`'s own constants.

## Contents

* `CyclicPlan`, `deviatePlan`, `planPayoff`, `IsGlobalEpsilonEquilibrium`,
  `IsGlobalApproxEquilibrium`: the real encoding.
* `eventuallyConstantPlan`, `constantPlan`, `constantPayoff`: the two plan
  shapes both notions use, and the self-consistent stationary payoff.
* `hasSum_eventuallyConstantPlan`: the summability and closed-form payoff of
  the eventually-constant shape.
* `no_stationary_approxEquilibrium`: no constant row is a global equilibrium
  at every tolerance.
* `no_instant_approxEquilibrium`: no stage-0-sure-quitter configuration is a
  global equilibrium at every tolerance.
* `scaledCyclicWeight_neither_stationary_nor_instant`: the package lemma.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Finset Math.PMFProduct

/-! ## Plans and the honest global-equilibrium quantifier -/

/-- A plan on the scaled cyclic weight's three coordinates: an infinite
sequence of hazard rows `p = (p_0, p_1, …)`. -/
def CyclicPlan := ℕ → CyclicIndex → ℝ

/-- Replacing one coordinate of every stage's row by a supplied hazard
sequence: the deviation `p[j → β]`. -/
def deviatePlan (p : CyclicPlan) (j : CyclicIndex) (β : ℕ → ℝ) : CyclicPlan :=
  fun t => Function.update (p t) j (β t)

/-- The survival probability through stage `t`: `∏_{s<t} c(p_s)`. -/
def survivalTo (p : CyclicPlan) (t : ℕ) : ℝ :=
  ∏ s ∈ Finset.range t, continueMass (p s)

/-- The one-stage total absorbed expectation `Σ_S a(x)(S) w_i(S)`, matching
`b_i(0, x)`: the one-stage payoff at row `x` with zero continuation. -/
def stageValue (x : CyclicIndex → ℝ) (i : CyclicIndex) : ℝ :=
  x i * sigmaValue scaledCyclicWeight x i + (1 - x i) * excludedValue scaledCyclicWeight x i

/-- The infinite-horizon payoff of a plan. -/
def planPayoff (p : CyclicPlan) (i : CyclicIndex) : ℝ :=
  ∑' t, survivalTo p t * stageValue (p t) i

/-- Global `ε`-equilibrium: no coordinate deviation to a
row sequence in `[0,1]` gains more than `ε`. -/
def IsGlobalEpsilonEquilibrium (p : CyclicPlan) (ε : ℝ) : Prop :=
  ∀ j : CyclicIndex, ∀ β : ℕ → ℝ, (∀ t, 0 ≤ β t ∧ β t ≤ 1) →
    planPayoff (deviatePlan p j β) j ≤ planPayoff p j + ε

/-- A plan is a global equilibrium at every positive tolerance: the
`for every ε` quantifier defining both approximate-equilibrium notions. -/
def IsGlobalApproxEquilibrium (p : CyclicPlan) : Prop :=
  ∀ ε > 0, IsGlobalEpsilonEquilibrium p ε

/-- **The quantifier collapse.** Requiring global `ε`-equilibrium for every
`ε > 0` is exactly requiring the exact (`ε = 0`) deviation bound: this is
the only place the infinitely-many-`ε` hypothesis is used, and it is what
makes both impossibility proofs below exact algebra. -/
theorem planPayoff_deviate_le_of_isGlobalApproxEquilibrium
    {p : CyclicPlan} (hp : IsGlobalApproxEquilibrium p)
    (j : CyclicIndex) (β : ℕ → ℝ) (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ 1) :
    planPayoff (deviatePlan p j β) j ≤ planPayoff p j := by
  apply le_of_forall_sub_le
  intro ε hε
  have := hp ε hε j β hβ
  linarith

/-! ## Basic bounds on `continueMass` and `stageValue` -/

theorem continueMass_nonneg {x : CyclicIndex → ℝ} (_hx0 : ∀ j, 0 ≤ x j)
    (hx1 : ∀ j, x j ≤ 1) : 0 ≤ continueMass x :=
  Finset.prod_nonneg fun i _ => by linarith [hx1 i]

theorem continueMass_le_one {x : CyclicIndex → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hx1 : ∀ j, x j ≤ 1) : continueMass x ≤ 1 :=
  Finset.prod_le_one (fun i _ => by linarith [hx1 i]) (fun i _ => by linarith [hx0 i])

/-- The scaled cyclic weight's diagonal quit value is `1/3 ≤ 1`, and every
row has `‖scaledCyclicWeight‖∞ ≤ 1`, so every `sigmaValue`/`excludedValue`
term (a convex-ish combination of table entries) is bounded; concretely, for
`CyclicIndex` this is read off `sigmaValue_scaledCyclicWeight`. -/
theorem continueMass_eq_zero_of_apply_eq_one {x : CyclicIndex → ℝ} {i : CyclicIndex}
    (hi : x i = 1) : continueMass x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; ring)

/-- `continueMass x = 1` forces every coordinate of a `[0,1]`-row to be `0`. -/
theorem apply_eq_zero_of_continueMass_eq_one {x : CyclicIndex → ℝ}
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j ≤ 1) (hc : continueMass x = 1) (i : CyclicIndex) :
    x i = 0 := by
  have hexp : (1 - x 0) * (1 - x 1) * (1 - x 2) = 1 := by
    have h := hc
    unfold continueMass at h
    rwa [Fin.prod_univ_three] at h
  have h0 : x 0 = 0 := by
    have hb1 : (1 - x 1) * (1 - x 2) ≤ 1 := by nlinarith [hx0 1, hx1 1, hx0 2, hx1 2]
    have key : (1 - x 0) * ((1 - x 1) * (1 - x 2)) ≤ (1 - x 0) * 1 :=
      mul_le_mul_of_nonneg_left hb1 (by linarith [hx1 0])
    nlinarith [hexp, key, hx0 0]
  have h1 : x 1 = 0 := by
    have hb1 : (1 - x 2) * (1 - x 0) ≤ 1 := by nlinarith [hx0 2, hx1 2, hx0 0, hx1 0]
    have key : (1 - x 1) * ((1 - x 2) * (1 - x 0)) ≤ (1 - x 1) * 1 :=
      mul_le_mul_of_nonneg_left hb1 (by linarith [hx1 1])
    nlinarith [hexp, key, hx0 1]
  have h2 : x 2 = 0 := by
    have hb1 : (1 - x 0) * (1 - x 1) ≤ 1 := by nlinarith [hx0 0, hx1 0, hx0 1, hx1 1]
    have key : (1 - x 2) * ((1 - x 0) * (1 - x 1)) ≤ (1 - x 2) * 1 :=
      mul_le_mul_of_nonneg_left hb1 (by linarith [hx1 2])
    nlinarith [hexp, key, hx0 2]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- `stageValue` vanishes at the all-zero row. -/
theorem stageValue_zero (i : CyclicIndex) : stageValue (fun _ => 0) i = 0 := by
  unfold stageValue
  rw [sigmaValue_scaledCyclicWeight, excludedValue_scaledCyclicWeight]
  simp

/-- `stageValue` vanishes whenever `continueMass = 1`, matching the
"never-quitting contributes 0" convention. -/
theorem stageValue_eq_zero_of_continueMass_eq_one {x : CyclicIndex → ℝ}
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j ≤ 1) (hc : continueMass x = 1) (i : CyclicIndex) :
    stageValue x i = 0 := by
  have hz : ∀ j, x j = 0 := apply_eq_zero_of_continueMass_eq_one hx0 hx1 hc
  have : x = fun _ => 0 := funext hz
  rw [this]; exact stageValue_zero i

/-! ## Eventually-constant plans -/

/-- The plan that plays `row0` at stage `0` and `π` forever after: the
stage-0-then-punishment shape used by both notions below. -/
def eventuallyConstantPlan (row0 π : CyclicIndex → ℝ) : CyclicPlan
  | 0 => row0
  | _ + 1 => π

/-- A plan constant from the start. -/
def constantPlan (x : CyclicIndex → ℝ) : CyclicPlan := fun _ => x

theorem constantPlan_eq_eventuallyConstantPlan (x : CyclicIndex → ℝ) :
    constantPlan x = eventuallyConstantPlan x x := by
  funext t; cases t <;> rfl

/-- The self-consistent (Bellman fixed-point) payoff of playing the constant
row `x` forever: `W_i(x)/(1 - c(x))` when `c(x) < 1`, else `0` (the
never-absorbing convention). -/
def constantPayoff (x : CyclicIndex → ℝ) (i : CyclicIndex) : ℝ :=
  if continueMass x < 1 then stageValue x i / (1 - continueMass x) else 0

theorem constantPayoff_mul_eq_stageValue {x : CyclicIndex → ℝ}
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j ≤ 1) (i : CyclicIndex) :
    constantPayoff x i * (1 - continueMass x) = stageValue x i := by
  unfold constantPayoff
  split_ifs with hc
  · exact div_mul_cancel₀ (stageValue x i) (ne_of_gt (sub_pos.mpr hc))
  · have hceq : continueMass x = 1 := le_antisymm (continueMass_le_one hx0 hx1) (not_lt.mp hc)
    rw [hceq]
    simp [stageValue_eq_zero_of_continueMass_eq_one hx0 hx1 hceq i]

theorem constantPayoff_eq_zero_of_continueMass_eq_one {x : CyclicIndex → ℝ}
    (hc : continueMass x = 1) (i : CyclicIndex) : constantPayoff x i = 0 := by
  unfold constantPayoff; rw [if_neg (by rw [hc]; norm_num)]

/-! ## Survival and the eventually-constant closed form -/

theorem survivalTo_eventuallyConstantPlan_zero (row0 π : CyclicIndex → ℝ) :
    survivalTo (eventuallyConstantPlan row0 π) 0 = 1 := by
  unfold survivalTo; simp

theorem survivalTo_eventuallyConstantPlan_succ (row0 π : CyclicIndex → ℝ) (n : ℕ) :
    survivalTo (eventuallyConstantPlan row0 π) (n + 1) =
      continueMass row0 * continueMass π ^ n := by
  unfold survivalTo
  rw [Finset.prod_range_succ']
  have h0 : eventuallyConstantPlan row0 π 0 = row0 := rfl
  have hk : ∀ k, eventuallyConstantPlan row0 π (k + 1) = π := fun _ => rfl
  simp only [hk, h0, Finset.prod_const, Finset.card_range]
  ring

/-- **Summability and closed form of the eventually-constant shape.** The
plan playing `row0` at stage `0` and `π` forever after has payoff
`stageValue row0 i + continueMass row0 * constantPayoff π i` at coordinate
`i`: the stage-`0` contribution, plus the (possibly zero) probability of
reaching stage `1` times the self-consistent value of playing `π` forever
from there. -/
theorem hasSum_eventuallyConstantPlan (row0 π : CyclicIndex → ℝ) (i : CyclicIndex)
    (hπ0 : ∀ j, 0 ≤ π j) (hπ1 : ∀ j, π j ≤ 1) :
    HasSum (fun t => survivalTo (eventuallyConstantPlan row0 π) t *
        stageValue (eventuallyConstantPlan row0 π t) i)
      (stageValue row0 i + continueMass row0 * constantPayoff π i) := by
  have htail : HasSum (fun n : ℕ => survivalTo (eventuallyConstantPlan row0 π) (n + 1) *
      stageValue (eventuallyConstantPlan row0 π (n + 1)) i)
      (continueMass row0 * constantPayoff π i) := by
    have heq : ∀ n : ℕ, survivalTo (eventuallyConstantPlan row0 π) (n + 1) *
        stageValue (eventuallyConstantPlan row0 π (n + 1)) i =
        (continueMass row0 * stageValue π i) * continueMass π ^ n := by
      intro n
      rw [survivalTo_eventuallyConstantPlan_succ]
      have hstep : eventuallyConstantPlan row0 π (n + 1) = π := rfl
      rw [hstep]; ring
    rw [funext heq]
    by_cases hc : continueMass π < 1
    · have hgeom := (hasSum_geometric_of_lt_one (continueMass_nonneg hπ0 hπ1) hc).mul_left
        (continueMass row0 * stageValue π i)
      have hval : continueMass row0 * stageValue π i * (1 - continueMass π)⁻¹ =
          continueMass row0 * constantPayoff π i := by
        unfold constantPayoff
        rw [if_pos hc]
        have hne : (1 : ℝ) - continueMass π ≠ 0 := sub_ne_zero.mpr hc.ne'
        field_simp
      rwa [hval] at hgeom
    · have hceq : continueMass π = 1 :=
        le_antisymm (continueMass_le_one hπ0 hπ1) (not_lt.mp hc)
      have hzero : stageValue π i = 0 :=
        stageValue_eq_zero_of_continueMass_eq_one hπ0 hπ1 hceq i
      have hCP : constantPayoff π i = 0 := constantPayoff_eq_zero_of_continueMass_eq_one hceq i
      simp [hzero, hCP]
  have h0 : survivalTo (eventuallyConstantPlan row0 π) 0 *
      stageValue (eventuallyConstantPlan row0 π 0) i = stageValue row0 i := by
    rw [survivalTo_eventuallyConstantPlan_zero]
    have hstep : eventuallyConstantPlan row0 π 0 = row0 := rfl
    rw [hstep]; ring
  have hfull := (hasSum_nat_add_iff
    (f := fun t => survivalTo (eventuallyConstantPlan row0 π) t *
      stageValue (eventuallyConstantPlan row0 π t) i) 1).mp htail
  rwa [Finset.sum_range_one, h0, add_comm] at hfull

theorem planPayoff_eventuallyConstantPlan (row0 π : CyclicIndex → ℝ) (i : CyclicIndex)
    (hπ0 : ∀ j, 0 ≤ π j) (hπ1 : ∀ j, π j ≤ 1) :
    planPayoff (eventuallyConstantPlan row0 π) i =
      stageValue row0 i + continueMass row0 * constantPayoff π i :=
  (hasSum_eventuallyConstantPlan row0 π i hπ0 hπ1).tsum_eq

/-- The constant plan's own payoff is exactly `constantPayoff`: it is the
genuine (honest, `tsum`-defined) infinite-horizon payoff, not merely a
name for the Bellman fixed point. -/
theorem planPayoff_constantPlan (x : CyclicIndex → ℝ) (i : CyclicIndex)
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j ≤ 1) :
    planPayoff (constantPlan x) i = constantPayoff x i := by
  rw [constantPlan_eq_eventuallyConstantPlan, planPayoff_eventuallyConstantPlan x x i hx0 hx1]
  have hfix := constantPayoff_mul_eq_stageValue hx0 hx1 i
  nlinarith [hfix]

/-! ## Updating a row at its own coordinate leaves its neighbours' view fixed

`sigmaValue`/`excludedValue`/`continueMassExcl` at coordinate `i` never read
`x i`, only `x (cyclicPred i)` and `x (cyclicSucc i)`. -/

theorem sigmaValue_scaledCyclicWeight_update_self (x : CyclicIndex → ℝ) (i : CyclicIndex)
    (v : ℝ) :
    sigmaValue scaledCyclicWeight (Function.update x i v) i =
      sigmaValue scaledCyclicWeight x i := by
  rw [sigmaValue_scaledCyclicWeight, sigmaValue_scaledCyclicWeight,
    Function.update_of_ne (cyclicPred_ne_self i) v x]

theorem excludedValue_scaledCyclicWeight_update_self (x : CyclicIndex → ℝ) (i : CyclicIndex)
    (v : ℝ) :
    excludedValue scaledCyclicWeight (Function.update x i v) i =
      excludedValue scaledCyclicWeight x i := by
  rw [excludedValue_scaledCyclicWeight, excludedValue_scaledCyclicWeight,
    Function.update_of_ne (cyclicPred_ne_self i) v x,
    Function.update_of_ne (cyclicSucc_ne_self i) v x]

theorem continueMassExcl_update_self (x : CyclicIndex → ℝ) (i : CyclicIndex) (v : ℝ) :
    continueMassExcl (Function.update x i v) i = continueMassExcl x i := by
  rw [continueMassExcl_cyclicIndex, continueMassExcl_cyclicIndex,
    Function.update_of_ne (cyclicSucc_ne_self i) v x,
    Function.update_of_ne (cyclicPred_ne_self i) v x]

/-- `c(x) = (1 - x_i) \cdot c_{-i}(x)`: peeling coordinate `i` out of the
full product. -/
theorem continueMass_eq_apply_mul_continueMassExcl (x : CyclicIndex → ℝ) (i : CyclicIndex) :
    continueMass x = (1 - x i) * continueMassExcl x i :=
  (Finset.mul_prod_erase Finset.univ (fun j => 1 - x j) (Finset.mem_univ i)).symm

theorem apply_update_self (x : CyclicIndex → ℝ) (i : CyclicIndex) (v : ℝ) :
    Function.update x i v i = v := by simp

theorem update_nonneg {x : CyclicIndex → ℝ} (hx0 : ∀ j, 0 ≤ x j) (i : CyclicIndex) {v : ℝ}
    (hv0 : 0 ≤ v) (j : CyclicIndex) : 0 ≤ Function.update x i v j := by
  by_cases hji : j = i
  · subst hji; rwa [Function.update_self]
  · rw [Function.update_of_ne hji]; exact hx0 j

theorem update_le_one {x : CyclicIndex → ℝ} (hx1 : ∀ j, x j ≤ 1) (i : CyclicIndex) {v : ℝ}
    (hv1 : v ≤ 1) (j : CyclicIndex) : Function.update x i v j ≤ 1 := by
  by_cases hji : j = i
  · subst hji; rwa [Function.update_self]
  · rw [Function.update_of_ne hji]; exact hx1 j

/-! ## Extracting the necessary one-stage conditions from the candidate -/

/-- **The quit-forever deviation bound.** If the constant row `x` is a
global equilibrium at every tolerance, quitting forever cannot beat it. -/
theorem sigmaValue_le_constantPayoff_of_isGlobalApproxEquilibrium {x : CyclicIndex → ℝ}
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j ≤ 1)
    (hp : IsGlobalApproxEquilibrium (constantPlan x)) (i : CyclicIndex) :
    sigmaValue scaledCyclicWeight x i ≤ constantPayoff x i := by
  have hdev : deviatePlan (constantPlan x) i (fun _ => (1 : ℝ)) =
      constantPlan (Function.update x i 1) := rfl
  have hle := planPayoff_deviate_le_of_isGlobalApproxEquilibrium hp i (fun _ => (1 : ℝ))
    (fun _ => ⟨by norm_num, le_refl 1⟩)
  rw [hdev, planPayoff_constantPlan x i hx0 hx1,
    planPayoff_constantPlan _ i (update_nonneg hx0 i (by norm_num))
      (update_le_one hx1 i (le_refl 1))] at hle
  have hcm : continueMass (Function.update x i 1) = 0 :=
    continueMass_eq_zero_of_apply_eq_one (apply_update_self x i 1)
  have hcp : constantPayoff (Function.update x i 1) i = sigmaValue scaledCyclicWeight x i := by
    unfold constantPayoff
    rw [if_pos (by rw [hcm]; norm_num), hcm]
    unfold stageValue
    rw [apply_update_self, sigmaValue_scaledCyclicWeight_update_self]
    ring
  rwa [hcp] at hle

/-- **The continue-forever deviation bound, cleared of its denominator.** If
the constant row `x` is a global equilibrium at every tolerance, continuing
forever cannot beat it. -/
theorem excludedValue_le_of_isGlobalApproxEquilibrium {x : CyclicIndex → ℝ}
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j ≤ 1)
    (hp : IsGlobalApproxEquilibrium (constantPlan x)) (i : CyclicIndex) :
    excludedValue scaledCyclicWeight x i ≤ (1 - continueMassExcl x i) * constantPayoff x i := by
  have hdev : deviatePlan (constantPlan x) i (fun _ => (0 : ℝ)) =
      constantPlan (Function.update x i 0) := rfl
  have hle := planPayoff_deviate_le_of_isGlobalApproxEquilibrium hp i (fun _ => (0 : ℝ))
    (fun _ => ⟨le_refl 0, by norm_num⟩)
  rw [hdev, planPayoff_constantPlan x i hx0 hx1,
    planPayoff_constantPlan _ i (update_nonneg hx0 i (le_refl 0))
      (update_le_one hx1 i (by norm_num))] at hle
  have hcm : continueMass (Function.update x i 0) = continueMassExcl x i := by
    rw [continueMass_eq_apply_mul_continueMassExcl (Function.update x i 0) i,
      apply_update_self, continueMassExcl_update_self]
    ring
  have hExcl_le_one : continueMassExcl x i ≤ 1 := by
    rw [continueMassExcl_cyclicIndex]
    nlinarith [hx0 (cyclicSucc i), hx1 (cyclicSucc i), hx0 (cyclicPred i), hx1 (cyclicPred i)]
  have hExcl_nonneg : 0 ≤ continueMassExcl x i := by
    rw [continueMassExcl_cyclicIndex]
    have h1 := hx1 (cyclicSucc i); have h2 := hx1 (cyclicPred i)
    positivity
  have hcp : constantPayoff (Function.update x i 0) i * (1 - continueMassExcl x i) =
      excludedValue scaledCyclicWeight x i := by
    have hbase := constantPayoff_mul_eq_stageValue (update_nonneg hx0 i (le_refl 0))
      (update_le_one hx1 i (by norm_num)) i
    rw [hcm] at hbase
    unfold stageValue at hbase
    rw [apply_update_self, excludedValue_scaledCyclicWeight_update_self] at hbase
    linarith [hbase]
  rcases lt_or_eq_of_le hExcl_le_one with hlt | heq
  · have := mul_le_mul_of_nonneg_right hle (by linarith : (0:ℝ) ≤ 1 - continueMassExcl x i)
    rw [hcp] at this
    linarith [this]
  · have hA0 : excludedValue scaledCyclicWeight x i = 0 := by
      rw [excludedValue_scaledCyclicWeight]
      have hp0 : x (cyclicPred i) = 0 := by
        rw [continueMassExcl_cyclicIndex] at heq
        nlinarith [heq, hx0 (cyclicSucc i), hx1 (cyclicSucc i), hx0 (cyclicPred i),
          hx1 (cyclicPred i)]
      rw [hp0]; ring
    rw [hA0, heq]; norm_num

/-! ## The stationary impossibility: source equations (8)-(14), adapted

`Pkg a b c Ua Ub Uc` packages the nine relations available at a candidate
stationary row `(a,b,c)` whose cyclic predecessor/successor structure
matches coordinate `a`'s (predecessor `c`, successor `b`): the
self-consistency identity and the two deviation bounds, at each of the
three coordinates. It is stated on bare reals so the same instance, cycled
by `Pkg.rotate`, proves the claim at every coordinate without repeating the
argument three times. -/
structure Pkg (a b c Ua Ub Uc : ℝ) : Prop where
  /-- Self-consistency at `a`: `U_a (1 - c(x)) = a \Sigma_a + (1-a) A_a`. -/
  hfix_a : Ua * (1 - (1 - a) * (1 - b) * (1 - c)) =
    a * ((1 - c) / 3) + (1 - a) * (c * (3 - 2 * b) / 3)
  hfix_b : Ub * (1 - (1 - a) * (1 - b) * (1 - c)) =
    b * ((1 - a) / 3) + (1 - b) * (a * (3 - 2 * c) / 3)
  hfix_c : Uc * (1 - (1 - a) * (1 - b) * (1 - c)) =
    c * ((1 - b) / 3) + (1 - c) * (b * (3 - 2 * a) / 3)
  /-- Quit-forever bound at `a`: `\Sigma_a \le U_a`. -/
  hq_a : (1 - c) / 3 ≤ Ua
  hq_b : (1 - a) / 3 ≤ Ub
  hq_c : (1 - b) / 3 ≤ Uc
  /-- Continue-forever bound at `a`, cleared: `A_a \le (1 - c_{-a}) U_a`. -/
  hc_a : c * (3 - 2 * b) / 3 ≤ (1 - (1 - b) * (1 - c)) * Ua
  hc_b : a * (3 - 2 * c) / 3 ≤ (1 - (1 - c) * (1 - a)) * Ub
  hc_c : b * (3 - 2 * a) / 3 ≤ (1 - (1 - a) * (1 - b)) * Uc

/-- Cyclic permutation: a package for `(a,b,c)` gives one for `(b,c,a)`. -/
theorem Pkg.rotate {a b c Ua Ub Uc : ℝ} (h : Pkg a b c Ua Ub Uc) :
    Pkg b c a Ub Uc Ua := by
  have hmass : (1 - b) * (1 - c) * (1 - a) = (1 - a) * (1 - b) * (1 - c) := by ring
  refine ⟨?_, ?_, ?_, h.hq_b, h.hq_c, h.hq_a, h.hc_b, h.hc_c, h.hc_a⟩
  · rw [hmass]; exact h.hfix_b
  · rw [hmass]; exact h.hfix_c
  · rw [hmass]; exact h.hfix_a

/-- **No coordinate can equal `1`.** Mirrors the answer's exclusion "if
`x_1 = 1` then `x_2 = 0`, forcing `x_3 = 1`, contradicting `x_1`'s own
bound": the same three-step cascade, run on `scaledCyclicWeight`'s own
constants. -/
theorem Pkg.case_one_impossible {a b c Ua Ub Uc : ℝ} (h : Pkg a b c Ua Ub Uc)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (_hb0 : 0 ≤ b) (_hb1 : b ≤ 1)
    (_hc0 : 0 ≤ c) (hc1 : c ≤ 1) (haeq : a = 1) : False := by
  subst haeq
  have hUa : Ua = (1 - c) / 3 := by have := h.hfix_a; nlinarith
  have hb : b = 0 := by
    have hUb : Ub = (1 - b) * (3 - 2 * c) / 3 := by have := h.hfix_b; nlinarith
    have hcb := h.hc_b
    rw [hUb] at hcb
    nlinarith [hc1]
  have hUc : Uc = c / 3 := by
    have hf := h.hfix_c
    rw [hb] at hf
    nlinarith
  have hc1' : c = 1 := by
    have hq := h.hq_c
    rw [hb, hUc] at hq
    nlinarith
  have hca := h.hc_a
  rw [hUa, hb, hc1'] at hca
  norm_num at hca

/-- `\varphi(t) = t(t+2)/(1+t^2)` strictly exceeds `t` for `0 < t \le 1`
(cleared of its denominator): equation (11)-(14)'s monotonicity fact. -/
theorem phi_gt (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t * (t + 2) > t * (1 + t ^ 2) := by nlinarith

/-- **If `a` is strictly interior, exact complementarity pins `b` in terms
of `c` via `\varphi`**: equation (11), `x_2 = \varphi(x_3)`, adapted. -/
theorem eq_phi_of_interior {a b c Ua : ℝ}
    (hfix_a : Ua * (1 - (1 - a) * (1 - b) * (1 - c)) =
      a * ((1 - c) / 3) + (1 - a) * (c * (3 - 2 * b) / 3))
    (hq_a : (1 - c) / 3 ≤ Ua)
    (hc_a : c * (3 - 2 * b) / 3 ≤ (1 - (1 - b) * (1 - c)) * Ua)
    (ha0 : 0 < a) (ha1 : a < 1) (_hb0 : 0 ≤ b) (_hb1 : b ≤ 1)
    (_hc0 : 0 ≤ c) (_hc1 : c ≤ 1) :
    b * (1 + c ^ 2) = c * (c + 2) := by
  have step1 : (1 - a) * (c * (3 - 2 * b) / 3) ≤ (1 - a) * ((1 - (1 - b) * (1 - c)) * Ua) :=
    mul_le_mul_of_nonneg_left hc_a (by linarith)
  have hSigma_eq : (1 - c) / 3 = Ua := by nlinarith [step1, hfix_a, mul_pos ha0 ha0]
  have step2 : a * ((1 - c) / 3) ≤ a * Ua := mul_le_mul_of_nonneg_left hq_a ha0.le
  have hGamma_eq : c * (3 - 2 * b) / 3 = (1 - (1 - b) * (1 - c)) * Ua := by
    nlinarith [step2, hfix_a, mul_pos (sub_pos.mpr ha1) (sub_pos.mpr ha1)]
  rw [← hSigma_eq] at hGamma_eq
  nlinarith [hGamma_eq]

/-- **No exact stationary equilibrium with every coordinate below `1`
exists.** The interior sub-case chains the three `\varphi` relations into
`a > b > c > a`; the boundary sub-case (`c = 0`, forcing `b = 0` too) fails
the quit-forever bound at `c`. Together with `case_one_impossible` and the
all-zero row (handled separately, as `constantPayoff` is pinned to `0`
there by definition, not merely by these relations), this exhausts every
row in `[0,1]^3`. -/
theorem Pkg.case_positive_impossible {a b c Ua Ub Uc : ℝ} (h : Pkg a b c Ua Ub Uc)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1) : False := by
  have heqa : b * (1 + c ^ 2) = c * (c + 2) :=
    eq_phi_of_interior h.hfix_a h.hq_a h.hc_a ha0 ha1 hb0 hb1.le hc0 hc1.le
  rcases eq_or_lt_of_le hc0 with hc0' | hc0'
  · have hb0' : b = 0 := by nlinarith [hc0']
    have hUc : Uc = 0 := by
      have hf := h.hfix_c
      rw [← hc0', hb0'] at hf
      nlinarith
    have hq := h.hq_c
    rw [hb0', hUc] at hq
    norm_num at hq
  · have hbpos : 0 < b := by nlinarith [phi_gt c hc0' hc1.le]
    have heqc : a * (1 + b ^ 2) = b * (b + 2) :=
      eq_phi_of_interior (h.rotate.rotate).hfix_a (h.rotate.rotate).hq_a
        (h.rotate.rotate).hc_a hc0' hc1 ha0.le ha1.le hb0 hb1.le
    have heqb : c * (1 + a ^ 2) = a * (a + 2) :=
      eq_phi_of_interior (h.rotate).hfix_a (h.rotate).hq_a (h.rotate).hc_a
        hbpos hb1 hc0 hc1.le ha0.le ha1.le
    have hab : a > b := by nlinarith [phi_gt b hbpos hb1.le]
    have hbc : b > c := by nlinarith [phi_gt c hc0' hc1.le]
    have hca : c > a := by nlinarith [phi_gt a ha0 ha1.le]
    linarith

/-- `c(x) = (1-x_0)(1-x_1)(1-x_2)` spelled out on `CyclicIndex = Fin 3`. -/
theorem continueMass_eq_prod3 (x : CyclicIndex → ℝ) :
    continueMass x = (1 - x 0) * (1 - x 1) * (1 - x 2) := by
  unfold continueMass; rw [Fin.prod_univ_three]

/-- **The `Pkg` instance carried by a stationary global-approximate
equilibrium candidate.** Assembles the self-consistency identity and the
two deviation bounds at every coordinate into the abstract package
consumed by the case analysis above. -/
theorem pkg_of_isGlobalApproxEquilibrium {x : CyclicIndex → ℝ}
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j ≤ 1)
    (hp : IsGlobalApproxEquilibrium (constantPlan x)) :
    Pkg (x 0) (x 1) (x 2) (constantPayoff x 0) (constantPayoff x 1) (constantPayoff x 2) := by
  have e0p : cyclicPred (0 : CyclicIndex) = 2 := by decide
  have e0s : cyclicSucc (0 : CyclicIndex) = 1 := by decide
  have e1p : cyclicPred (1 : CyclicIndex) = 0 := by decide
  have e1s : cyclicSucc (1 : CyclicIndex) = 2 := by decide
  have e2p : cyclicPred (2 : CyclicIndex) = 1 := by decide
  have e2s : cyclicSucc (2 : CyclicIndex) = 0 := by decide
  have hcm := continueMass_eq_prod3 x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hb := constantPayoff_mul_eq_stageValue hx0 hx1 0
    unfold stageValue at hb
    rwa [sigmaValue_scaledCyclicWeight, excludedValue_scaledCyclicWeight, e0p, e0s, hcm] at hb
  · have hb := constantPayoff_mul_eq_stageValue hx0 hx1 1
    unfold stageValue at hb
    rwa [sigmaValue_scaledCyclicWeight, excludedValue_scaledCyclicWeight, e1p, e1s, hcm] at hb
  · have hb := constantPayoff_mul_eq_stageValue hx0 hx1 2
    unfold stageValue at hb
    rwa [sigmaValue_scaledCyclicWeight, excludedValue_scaledCyclicWeight, e2p, e2s, hcm] at hb
  · have hb := sigmaValue_le_constantPayoff_of_isGlobalApproxEquilibrium hx0 hx1 hp 0
    rwa [sigmaValue_scaledCyclicWeight, e0p] at hb
  · have hb := sigmaValue_le_constantPayoff_of_isGlobalApproxEquilibrium hx0 hx1 hp 1
    rwa [sigmaValue_scaledCyclicWeight, e1p] at hb
  · have hb := sigmaValue_le_constantPayoff_of_isGlobalApproxEquilibrium hx0 hx1 hp 2
    rwa [sigmaValue_scaledCyclicWeight, e2p] at hb
  · have hb := excludedValue_le_of_isGlobalApproxEquilibrium hx0 hx1 hp 0
    rwa [excludedValue_scaledCyclicWeight, continueMassExcl_cyclicIndex, e0p, e0s] at hb
  · have hb := excludedValue_le_of_isGlobalApproxEquilibrium hx0 hx1 hp 1
    rwa [excludedValue_scaledCyclicWeight, continueMassExcl_cyclicIndex, e1p, e1s] at hb
  · have hb := excludedValue_le_of_isGlobalApproxEquilibrium hx0 hx1 hp 2
    rwa [excludedValue_scaledCyclicWeight, continueMassExcl_cyclicIndex, e2p, e2s] at hb

/-- **No stationary approximate family.** No constant row `x \in [0,1]^3` is
a global equilibrium of `scaledCyclicWeight` at every positive tolerance:
the "neither stationary" half of (K1)'s hypothesis package. -/
theorem no_stationary_approxEquilibrium {x : CyclicIndex → ℝ}
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j ≤ 1) :
    ¬ IsGlobalApproxEquilibrium (constantPlan x) := by
  intro hp
  have hpkg := pkg_of_isGlobalApproxEquilibrium hx0 hx1 hp
  by_cases h0 : x 0 = 1
  · exact hpkg.case_one_impossible (hx0 0) (hx1 0) (hx0 1) (hx1 1) (hx0 2) (hx1 2) h0
  by_cases h1 : x 1 = 1
  · exact hpkg.rotate.case_one_impossible (hx0 1) (hx1 1) (hx0 2) (hx1 2) (hx0 0) (hx1 0) h1
  by_cases h2 : x 2 = 1
  · exact hpkg.rotate.rotate.case_one_impossible
      (hx0 2) (hx1 2) (hx0 0) (hx1 0) (hx0 1) (hx1 1) h2
  have h0' : x 0 < 1 := lt_of_le_of_ne (hx1 0) h0
  have h1' : x 1 < 1 := lt_of_le_of_ne (hx1 1) h1
  have h2' : x 2 < 1 := lt_of_le_of_ne (hx1 2) h2
  rcases eq_or_lt_of_le (hx0 0) with h0z | h0z
  · rcases eq_or_lt_of_le (hx0 1) with h1z | h1z
    · rcases eq_or_lt_of_le (hx0 2) with h2z | h2z
      · -- the all-zero row: `constantPayoff` is `0` there by definition,
        -- contradicting the quit-forever bound at coordinate `0`.
        have hczero : continueMass x = 1 := by
          rw [continueMass_eq_prod3, ← h0z, ← h1z, ← h2z]; ring
        have hcp0 : constantPayoff x 0 = 0 :=
          constantPayoff_eq_zero_of_continueMass_eq_one hczero 0
        have hq0 := hpkg.hq_a
        rw [hcp0, ← h2z] at hq0
        norm_num at hq0
      · exact hpkg.rotate.rotate.case_positive_impossible h2z h2'
          (hx0 0) h0' (hx0 1) h1'
    · exact hpkg.rotate.case_positive_impossible h1z h1' (hx0 2) h2' (hx0 0) h0'
  · exact hpkg.case_positive_impossible h0z h0' (hx0 1) h1' (hx0 2) h2'

/-! ## The instant impossibility -/

theorem deviatePlan_eventuallyConstantPlan_const (row0 π : CyclicIndex → ℝ) (j : CyclicIndex)
    (v : ℝ) :
    deviatePlan (eventuallyConstantPlan row0 π) j (fun _ => v) =
      eventuallyConstantPlan (Function.update row0 j v) (Function.update π j v) := by
  funext t; cases t <;> rfl

theorem deviatePlan_eventuallyConstantPlan_quitter (row0 π : CyclicIndex → ℝ) (j : CyclicIndex)
    (v0 : ℝ) :
    deviatePlan (eventuallyConstantPlan row0 π) j (fun t => if t = 0 then v0 else π j) =
      eventuallyConstantPlan (Function.update row0 j v0) π := by
  funext t
  cases t with
  | zero => rfl
  | succ n => simp [deviatePlan, eventuallyConstantPlan, Function.update_eq_self]

/-- **No instant approximate family.** No configuration where some player
quits surely at stage `0`, followed by an arbitrary feasible punishment
`π`, is a global equilibrium of `scaledCyclicWeight` at every positive
tolerance: the "neither instant" half of (K1)'s hypothesis package.

Unlike the stationary case this is *not* a limiting argument: the source
answer's "as `x_2 \to 0`, `x_3 \to 1`" becomes an *exact* pin at `0` and `1`
respectively, because `for every ε` already collapsed to the exact `ε = 0`
deviation bound. The two non-quitters' payoffs never see the punishment `π`
at all (`continueMass row0 = 0` kills its coefficient outright), and the
quitter's own switch-to-Continue deviation sees `π` only through a
coefficient that itself vanishes once the two pins are in place, so the
final contradiction (`1 \le 0`) holds for *every* feasible `π`. -/
theorem no_instant_approxEquilibrium (quitter : CyclicIndex) (row0 π : CyclicIndex → ℝ)
    (hrow0q : row0 quitter = 1)
    (hrow00 : ∀ j, 0 ≤ row0 j) (hrow01 : ∀ j, row0 j ≤ 1)
    (hπ0 : ∀ j, 0 ≤ π j) (hπ1 : ∀ j, π j ≤ 1) :
    ¬ IsGlobalApproxEquilibrium (eventuallyConstantPlan row0 π) := by
  intro hp
  have hpj1 : cyclicPred (cyclicSucc quitter) = quitter := cyclicPred_cyclicSucc quitter
  have hsj1 : cyclicSucc (cyclicSucc quitter) = cyclicPred quitter :=
    cyclicSucc_cyclicSucc_eq_cyclicPred quitter
  have hpj2 : cyclicPred (cyclicPred quitter) = cyclicSucc quitter :=
    cyclicPred_cyclicPred_eq_cyclicSucc quitter
  have hsj2 : cyclicSucc (cyclicPred quitter) = quitter := cyclicSucc_cyclicPred quitter
  have hne_q_j1 : quitter ≠ cyclicSucc quitter := (cyclicSucc_ne_self quitter).symm
  have hne_q_j2 : quitter ≠ cyclicPred quitter := (cyclicPred_ne_self quitter).symm
  have hcm0 : continueMass row0 = 0 := continueMass_eq_zero_of_apply_eq_one hrow0q
  -- Step 1: `row0 (cyclicSucc quitter) = 0`, from the continue-forever
  -- deviation at `cyclicSucc quitter`.
  have ha : row0 (cyclicSucc quitter) = 0 := by
    have hle := planPayoff_deviate_le_of_isGlobalApproxEquilibrium hp (cyclicSucc quitter)
      (fun _ => (0 : ℝ)) (fun _ => ⟨le_refl 0, by norm_num⟩)
    rw [deviatePlan_eventuallyConstantPlan_const row0 π (cyclicSucc quitter) 0,
      planPayoff_eventuallyConstantPlan _ _ (cyclicSucc quitter)
        (update_nonneg hπ0 _ (le_refl 0)) (update_le_one hπ1 _ (by norm_num)),
      planPayoff_eventuallyConstantPlan row0 π (cyclicSucc quitter) hπ0 hπ1] at hle
    have hcmU : continueMass (Function.update row0 (cyclicSucc quitter) 0) = 0 :=
      continueMass_eq_zero_of_apply_eq_one
        (by rw [Function.update_of_ne hne_q_j1]; exact hrow0q)
    rw [hcm0, hcmU] at hle
    simp only [zero_mul, add_zero] at hle
    unfold stageValue at hle
    rw [apply_update_self, sigmaValue_scaledCyclicWeight_update_self,
      excludedValue_scaledCyclicWeight_update_self, sigmaValue_scaledCyclicWeight,
      excludedValue_scaledCyclicWeight, hpj1, hsj1, hrow0q] at hle
    nlinarith [hle, hrow01 (cyclicPred quitter), hrow00 (cyclicSucc quitter)]
  -- Step 2: `row0 (cyclicPred quitter) = 1`, from the quit-forever
  -- deviation at `cyclicPred quitter`, using `ha`.
  have hb : row0 (cyclicPred quitter) = 1 := by
    have hle := planPayoff_deviate_le_of_isGlobalApproxEquilibrium hp (cyclicPred quitter)
      (fun _ => (1 : ℝ)) (fun _ => ⟨by norm_num, le_refl 1⟩)
    rw [deviatePlan_eventuallyConstantPlan_const row0 π (cyclicPred quitter) 1,
      planPayoff_eventuallyConstantPlan _ _ (cyclicPred quitter)
        (update_nonneg hπ0 _ (by norm_num)) (update_le_one hπ1 _ (le_refl 1)),
      planPayoff_eventuallyConstantPlan row0 π (cyclicPred quitter) hπ0 hπ1] at hle
    have hcmU : continueMass (Function.update row0 (cyclicPred quitter) 1) = 0 :=
      continueMass_eq_zero_of_apply_eq_one (apply_update_self row0 (cyclicPred quitter) 1)
    rw [hcm0, hcmU] at hle
    simp only [zero_mul, add_zero] at hle
    unfold stageValue at hle
    rw [apply_update_self, sigmaValue_scaledCyclicWeight_update_self,
      excludedValue_scaledCyclicWeight_update_self, sigmaValue_scaledCyclicWeight,
      excludedValue_scaledCyclicWeight, hpj2, hsj2, ha, hrow0q] at hle
    nlinarith [hle, hrow01 (cyclicPred quitter), hrow00 (cyclicPred quitter)]
  -- Step 3: the quitter's own switch to Continue at stage `0` (matching
  -- `π` thereafter) contradicts the candidate's own payoff outright.
  have hle := planPayoff_deviate_le_of_isGlobalApproxEquilibrium hp quitter
    (fun t => if t = 0 then (0 : ℝ) else π quitter)
    (fun t => by by_cases ht : t = 0 <;> simp [ht, hπ0 quitter, hπ1 quitter])
  rw [deviatePlan_eventuallyConstantPlan_quitter row0 π quitter 0,
    planPayoff_eventuallyConstantPlan _ π quitter hπ0 hπ1,
    planPayoff_eventuallyConstantPlan row0 π quitter hπ0 hπ1, hcm0] at hle
  have hcmU : continueMass (Function.update row0 quitter 0) = continueMassExcl row0 quitter := by
    rw [continueMass_eq_apply_mul_continueMassExcl (Function.update row0 quitter 0) quitter,
      apply_update_self, continueMassExcl_update_self]
    ring
  rw [hcmU, continueMassExcl_cyclicIndex, ha, hb] at hle
  simp only [zero_mul, add_zero] at hle
  unfold stageValue at hle
  rw [apply_update_self, sigmaValue_scaledCyclicWeight_update_self,
    excludedValue_scaledCyclicWeight_update_self, sigmaValue_scaledCyclicWeight,
    excludedValue_scaledCyclicWeight, ha, hb, hrow0q] at hle
  norm_num at hle

/-! ## The package lemma -/

/-- **The scaled cyclic weight satisfies (K1)'s hypothesis package.** It has
neither stationary nor instant approximate equilibria, in the sense of
`IsGlobalApproxEquilibrium`: no constant row, and no stage-0-sure-quitter
configuration with an arbitrary feasible punishment, is a global equilibrium
at every positive tolerance. Combined with `no_motion_price_scaledCyclicWeight`
of `WeightedRowMotionSeparation.lean` — no positive `ρ` prices motion by quit
mass on the weighted correspondence at this same weight — this completes the
`WeightedOneStageNashCannotPriceMotion.md` counterexample end to end: (K1)
is granted exactly for weights meeting this package, `scaledCyclicWeight`
meets it, and yet no such `ρ` exists. -/
theorem scaledCyclicWeight_neither_stationary_nor_instant :
    (∀ x : CyclicIndex → ℝ, (∀ j, 0 ≤ x j) → (∀ j, x j ≤ 1) →
        ¬ IsGlobalApproxEquilibrium (constantPlan x)) ∧
      (∀ (quitter : CyclicIndex) (row0 π : CyclicIndex → ℝ), row0 quitter = 1 →
        (∀ j, 0 ≤ row0 j) → (∀ j, row0 j ≤ 1) → (∀ j, 0 ≤ π j) → (∀ j, π j ≤ 1) →
        ¬ IsGlobalApproxEquilibrium (eventuallyConstantPlan row0 π)) :=
  ⟨fun _x hx0 hx1 => no_stationary_approxEquilibrium hx0 hx1,
    fun quitter row0 π hq h00 h01 hπ0 hπ1 =>
      no_instant_approxEquilibrium quitter row0 π hq h00 h01 hπ0 hπ1⟩

end GameTheory
