/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PerturbedCyclicWeightCycleExistenceHoleOccupied
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding
import UniformEquilibrium.Quitting.Cycles.ScaledCyclicWeightNoApproximateEquilibria
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Weighted near-Nash rows keep continue mass, when no instant family exists

A quitting weight `w` has **no instant approximate equilibria** when no
configuration in which some player quits surely at stage `0`, followed by an
arbitrary feasible stationary punishment, is a global equilibrium at every
positive tolerance.  This file proves the per-stage bound that such a weight
grants: there is a `ρ > 0` such that every hazard row `x` that is weighted
`ρ`-near-Nash against a `ρ`-rational continuation vector has joint continue
mass at least `ρ`.

## The argument

The proof is the contrapositive, by compactness and separation from the face
`{c = 0}`.  If no `ρ` works, take `ρ_k → 0` with witnesses `(r_k, x_k)`,
extract a convergent subsequence `x_k → x*`, `r_k → r*`, and read off in the
limit that

* `c(x*) = 0`, so some coordinate `q` quits surely (`x* q = 1`);
* `r*` is `0`-rational: `reservation ≤ r*`;
* the weighted conditions hold at tolerance `0`.

The limit row, played at stage `0` and followed by a punishment of `q`, is
then an instant approximate equilibrium, contradicting the hypothesis.

Two points of the assembly deserve naming.

**Which coordinate sees the punishment.**  The continuation of the assembled
plan is invisible to every player *except* the sure quitter: for `j ≠ q` the
row `x*` already has `c_{-j}(x*) = 0`, because the product defining it
carries the factor `1 - x* q = 0`.  So only `q`'s own tail has to be
controlled, and only by a punishment that `q` cannot escape.  Requiring the
punishment row to satisfy `c_{-π}(q) = 0` — the opponents of `q` absorb the
game in one stage — makes every payoff in the assembly a *finite* sum
(survival vanishes from stage `2` on), so no summability theory is needed
anywhere in this file.

**The continuation vectors must be bounded.**  Rationality is a lower bound
only, and the theorem is not available from it alone: at a coordinate `j`
with `x*_j = 0` and `c_{-j}(x*) = 0` the products `c_{-j}(x_k) · r_{k,j}` can
diverge while every hypothesis stays satisfied, so the limiting one-stage
condition at `j` is lost.  A uniform bound on the continuation vectors is
therefore part of the hypothesis package, and is stated explicitly rather
than smuggled in.  It costs nothing in the intended application: the
continuation vectors that arise there are values of plays under a bounded
reward, hence bounded by the reward bound.

## Contents

* `weightStageValue`, `planDeviate`, `weightPlanPayoff`,
  `IsWeightGlobalEpsilonEquilibrium`, `IsWeightGlobalApproxEquilibrium`,
  `instantConfigurationPlan`: the infinite-horizon plan apparatus at an
  arbitrary weight, generalizing the three-coordinate instance of
  `ScaledCyclicWeightNoApproximateEquilibria.lean` (which is recovered
  definitionally by `weightPlanPayoff_scaledCyclicWeight` and friends).
* `HasNoInstantApproxEquilibria`: the hypothesis, at a general weight.
* `IsStationaryPunishment`: the punishment side of the hypothesis package.
* `isWeightGlobalApproxEquilibrium_instantConfigurationPlan`: the assembly.
* `exists_pos_le_continueMass`: the theorem.
* `hasNoInstantApproxEquilibria_scaledCyclicWeight`,
  `isStationaryPunishment_scaledCyclicWeight`,
  `exists_pos_le_continueMass_scaledCyclicWeight`: the sanity instance.
* `isεQuittingRootEndpointNash_iff_isWeightedRow`,
  `IsQuittingBoundedGrantedContinueMassBound`,
  `exists_pos_isQuittingBoundedGrantedContinueMassBound`: the consumer form,
  on the `PMF Bool` side.
-/

noncomputable section

namespace GameTheory

open Finset Filter Topology Math.PMFProduct

/-! ## The plan apparatus at an arbitrary weight -/

section GeneralWeight

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The one-stage total absorbed expectation `Σ_S a(x)(S) w_i(S)` at a
general weight: the one-stage payoff at row `x` with zero continuation. -/
def weightStageValue (w : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  x i * sigmaValue w x i + (1 - x i) * excludedValue w x i

/-- Replacing one coordinate of every stage's row by a supplied hazard
sequence: the deviation `p[j → β]`. -/
def planDeviate (p : ℕ → ι → ℝ) (j : ι) (β : ℕ → ℝ) : ℕ → ι → ℝ :=
  fun t => Function.update (p t) j (β t)

/-- The infinite-horizon payoff of a plan at a general weight. -/
def weightPlanPayoff (w : Finset ι → ι → ℝ) (p : ℕ → ι → ℝ) (i : ι) : ℝ :=
  ∑' t, survivalMass p t * weightStageValue w (p t) i

/-- Global `ε`-equilibrium: no coordinate deviation to a row sequence in
`[0,1]` gains more than `ε`. -/
def IsWeightGlobalEpsilonEquilibrium (w : Finset ι → ι → ℝ) (p : ℕ → ι → ℝ) (ε : ℝ) : Prop :=
  ∀ j : ι, ∀ β : ℕ → ℝ, (∀ t, 0 ≤ β t ∧ β t ≤ 1) →
    weightPlanPayoff w (planDeviate p j β) j ≤ weightPlanPayoff w p j + ε

/-- A plan is a global equilibrium at every positive tolerance. -/
def IsWeightGlobalApproxEquilibrium (w : Finset ι → ι → ℝ) (p : ℕ → ι → ℝ) : Prop :=
  ∀ ε > 0, IsWeightGlobalEpsilonEquilibrium w p ε

/-- The plan that plays `row0` at stage `0` and `π` forever after: the
instant-configuration shape. -/
def instantConfigurationPlan (row0 π : ι → ℝ) : ℕ → ι → ℝ
  | 0 => row0
  | _ + 1 => π

/-- **No instant approximate equilibria**, at a general weight: no
configuration in which some player quits surely at stage `0`, followed by an
arbitrary feasible punishment, is a global equilibrium at every positive
tolerance. -/
def HasNoInstantApproxEquilibria (w : Finset ι → ι → ℝ) : Prop :=
  ∀ (quitter : ι) (row0 π : ι → ℝ), row0 quitter = 1 →
    (∀ j, 0 ≤ row0 j) → (∀ j, row0 j ≤ 1) → (∀ j, 0 ≤ π j) → (∀ j, π j ≤ 1) →
      ¬ IsWeightGlobalApproxEquilibrium w (instantConfigurationPlan row0 π)

/-- **The punishment side of the hypothesis package.**  Every player `q` can
be held to its reservation level by a feasible stationary row whose other
coordinates absorb the game in a single stage (`c_{-q}(π) = 0`), whatever
`q` itself then does. -/
def IsStationaryPunishment (w : Finset ι → ι → ℝ) (reservation : ι → ℝ) : Prop :=
  ∀ q : ι, ∃ π : ι → ℝ, (∀ j, 0 ≤ π j) ∧ (∀ j, π j ≤ 1) ∧ continueMassExcl π q = 0 ∧
    ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      b * sigmaValue w π q + (1 - b) * excludedValue w π q ≤ reservation q

/-! ## Row algebra: the coordinates a value never reads -/

/-- `Σ_i` never reads coordinate `i` of the row. -/
theorem sigmaValue_update_self (w : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) (v : ℝ) :
    sigmaValue w (Function.update x i v) i = sigmaValue w x i := by
  unfold sigmaValue
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hsub : J ⊆ Finset.univ.erase i := Finset.mem_powerset.mp hJ
  have h1 : ∏ j ∈ J, Function.update x i v j = ∏ j ∈ J, x j :=
    Finset.prod_congr rfl fun j hj =>
      Function.update_of_ne (Finset.ne_of_mem_erase (hsub hj)) v x
  have h2 : ∏ j ∈ Finset.univ.erase i \ J, (1 - Function.update x i v j) =
      ∏ j ∈ Finset.univ.erase i \ J, (1 - x j) :=
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne
        (Finset.ne_of_mem_erase (Finset.mem_sdiff.mp hj).1) v x]
  rw [h1, h2]

/-- `A_i` never reads coordinate `i` of the row. -/
theorem excludedValue_update_self (w : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) (v : ℝ) :
    excludedValue w (Function.update x i v) i = excludedValue w x i := by
  unfold excludedValue
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hsub : J ⊆ Finset.univ.erase i :=
    Finset.mem_powerset.mp (Finset.mem_of_mem_erase hJ)
  have h1 : ∏ j ∈ J, Function.update x i v j = ∏ j ∈ J, x j :=
    Finset.prod_congr rfl fun j hj =>
      Function.update_of_ne (Finset.ne_of_mem_erase (hsub hj)) v x
  have h2 : ∏ j ∈ Finset.univ.erase i \ J, (1 - Function.update x i v j) =
      ∏ j ∈ Finset.univ.erase i \ J, (1 - x j) :=
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne
        (Finset.ne_of_mem_erase (Finset.mem_sdiff.mp hj).1) v x]
  rw [h1, h2]

/-- `c_{-i}` never reads coordinate `i` of the row. -/
theorem continueMassExcl_update_self' (x : ι → ℝ) (i : ι) (v : ℝ) :
    continueMassExcl (Function.update x i v) i = continueMassExcl x i := by
  unfold continueMassExcl
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj) v x]

/-- `c(x) = (1 - x_i) · c_{-i}(x)`: peeling coordinate `i` out of the full
product. -/
theorem continueMass_eq_sub_mul_continueMassExcl (x : ι → ℝ) (i : ι) :
    continueMass x = (1 - x i) * continueMassExcl x i := by
  unfold continueMass continueMassExcl
  exact (Finset.mul_prod_erase Finset.univ (fun j => 1 - x j) (Finset.mem_univ i)).symm

omit [DecidableEq ι] in
/-- A coordinate that quits surely kills the joint continue mass. -/
theorem continueMass_eq_zero_of_eq_one {x : ι → ℝ} {q : ι} (hq : x q = 1) :
    continueMass x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ q) (by rw [hq]; ring)

/-- A coordinate that quits surely kills every *other* coordinate's excluded
continue mass. -/
theorem continueMassExcl_eq_zero_of_ne (x : ι → ℝ) {j q : ι} (hne : q ≠ j)
    (hq : x q = 1) : continueMassExcl x j = 0 :=
  Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ q⟩) (by rw [hq]; ring)

omit [DecidableEq ι] in
/-- Vanishing joint continue mass exhibits a sure quitter. -/
theorem exists_eq_one_of_continueMass_eq_zero {x : ι → ℝ} (h : continueMass x = 0) :
    ∃ q, x q = 1 := by
  unfold continueMass at h
  obtain ⟨q, _, hq⟩ := Finset.prod_eq_zero_iff.mp h
  exact ⟨q, by linarith⟩

/-- The excluded continue mass of a `[0,1]`-row is nonnegative. -/
theorem continueMassExcl_nonneg {x : ι → ℝ} (hx1 : ∀ j, x j ≤ 1) (i : ι) :
    0 ≤ continueMassExcl x i := by
  unfold continueMassExcl
  exact Finset.prod_nonneg fun j _ => by linarith [hx1 j]

/-- `g_i` in the form used throughout: the stop-minus-continue difference is
the zero-continuation difference less the continuation's weight. -/
theorem gainValue_eq_sub_sub (w : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) (next : ℝ) :
    gainValue w x i next =
      sigmaValue w x i - excludedValue w x i - continueMassExcl x i * next := by
  unfold gainValue gammaValue
  ring

/-! ## Payoffs of plans whose survival dies out -/

omit [DecidableEq ι] in
/-- A stage whose row absorbs surely kills every later survival weight. -/
theorem survivalMass_eq_zero_of_lt {p : ℕ → ι → ℝ} {n t : ℕ} (hnt : n < t)
    (h : continueMass (p n) = 0) : survivalMass p t = 0 := by
  unfold survivalMass
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hnt) h

/-- **A plan whose survival dies out has a finite payoff sum.**  No
summability theory is needed: the family is supported on `range n`. -/
theorem weightPlanPayoff_eq_sum_range (w : Finset ι → ι → ℝ) (p : ℕ → ι → ℝ) (i : ι)
    (n : ℕ) (h : ∀ t, n ≤ t → survivalMass p t = 0) :
    weightPlanPayoff w p i =
      ∑ t ∈ Finset.range n, survivalMass p t * weightStageValue w (p t) i := by
  unfold weightPlanPayoff
  refine tsum_eq_sum fun t ht => ?_
  rw [h t (by simpa using ht)]
  ring

/-! ## The assembly: an instant approximate equilibrium out of limit data -/

/-- **The assembly.**  A `[0,1]`-row `x` with a sure quitter `q`, satisfying
the two exact one-stage endpoint conditions against a punishment level, is
the stage-`0` row of an instant approximate equilibrium whose punishment is
any feasible row absorbing `q`'s opponents in one stage.

Every payoff appearing in the proof is a sum of at most two terms: for
`j ≠ q` the row `x` already absorbs surely, and for `j = q` the punishment
does so one stage later. -/
theorem isWeightGlobalApproxEquilibrium_instantConfigurationPlan
    {w : Finset ι → ι → ℝ} {x π : ι → ℝ} {q : ι} {punish : ℝ}
    (hx1 : ∀ j, x j ≤ 1) (hq : x q = 1) (hπExcl : continueMassExcl π q = 0)
    (hquit : ∀ j, (1 - x j) * (sigmaValue w x j - excludedValue w x j) ≤ 0)
    (hcont : ∀ j, continueMassExcl x j * punish ≤
      x j * (sigmaValue w x j - excludedValue w x j))
    (hπpunish : ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      b * sigmaValue w π q + (1 - b) * excludedValue w π q ≤ punish) :
    IsWeightGlobalApproxEquilibrium w (instantConfigurationPlan x π) := by
  have hcm0 : continueMass x = 0 := continueMass_eq_zero_of_eq_one hq
  have hcand : ∀ j, weightPlanPayoff w (instantConfigurationPlan x π) j =
      weightStageValue w x j := by
    intro j
    rw [weightPlanPayoff_eq_sum_range w _ j 1 fun t ht =>
      survivalMass_eq_zero_of_lt (n := 0) (by omega) hcm0]
    rw [Finset.sum_range_one, survivalMass_zero]
    have h0 : instantConfigurationPlan x π 0 = x := rfl
    rw [h0, one_mul]
  intro ε hε j β hβ
  have hdev0 : planDeviate (instantConfigurationPlan x π) j β 0 =
      Function.update x j (β 0) := rfl
  have hdev1 : planDeviate (instantConfigurationPlan x π) j β 1 =
      Function.update π j (β 1) := rfl
  have hcmdev0 : continueMass (planDeviate (instantConfigurationPlan x π) j β 0) =
      (1 - β 0) * continueMassExcl x j := by
    rw [continueMass_eq_sub_mul_continueMassExcl _ j, hdev0, Function.update_self,
      continueMassExcl_update_self']
  have hvanish : ∀ t, 2 ≤ t →
      survivalMass (planDeviate (instantConfigurationPlan x π) j β) t = 0 := by
    intro t ht
    by_cases hjq : j = q
    · refine survivalMass_eq_zero_of_lt (n := 1) (by omega) ?_
      rw [continueMass_eq_sub_mul_continueMassExcl _ j, hdev1, Function.update_self,
        continueMassExcl_update_self', hjq, hπExcl, mul_zero]
    · refine survivalMass_eq_zero_of_lt (n := 0) (by omega) ?_
      rw [hcmdev0, continueMassExcl_eq_zero_of_ne x (Ne.symm hjq) hq, mul_zero]
  have hdevpay : weightPlanPayoff w (planDeviate (instantConfigurationPlan x π) j β) j =
      weightStageValue w (Function.update x j (β 0)) j +
        (1 - β 0) * continueMassExcl x j *
          weightStageValue w (planDeviate (instantConfigurationPlan x π) j β 1) j := by
    rw [weightPlanPayoff_eq_sum_range w _ j 2 hvanish, Finset.sum_range_succ,
      Finset.sum_range_one, survivalMass_zero, survivalMass_succ, survivalMass_zero,
      hcmdev0, hdev0]
    ring
  have hsv0 : weightStageValue w (Function.update x j (β 0)) j =
      β 0 * sigmaValue w x j + (1 - β 0) * excludedValue w x j := by
    unfold weightStageValue
    rw [Function.update_self, sigmaValue_update_self, excludedValue_update_self]
  have hExclNonneg : 0 ≤ continueMassExcl x j := continueMassExcl_nonneg hx1 j
  have hkey : continueMassExcl x j *
      weightStageValue w (planDeviate (instantConfigurationPlan x π) j β 1) j ≤
      x j * (sigmaValue w x j - excludedValue w x j) := by
    by_cases hjq : j = q
    · subst hjq
      have hsv1 : weightStageValue w
          (planDeviate (instantConfigurationPlan x π) j β 1) j =
          β 1 * sigmaValue w π j + (1 - β 1) * excludedValue w π j := by
        rw [hdev1]
        unfold weightStageValue
        rw [Function.update_self, sigmaValue_update_self, excludedValue_update_self]
      rw [hsv1]
      exact le_trans
        (mul_le_mul_of_nonneg_left (hπpunish (β 1) (hβ 1).1 (hβ 1).2) hExclNonneg) (hcont j)
    · have h0 : continueMassExcl x j = 0 :=
        continueMassExcl_eq_zero_of_ne x (Ne.symm hjq) hq
      have hc := hcont j
      rw [h0, zero_mul] at hc ⊢
      exact hc
  rw [hdevpay, hcand j, hsv0]
  have hsvx : weightStageValue w x j =
      x j * sigmaValue w x j + (1 - x j) * excludedValue w x j := rfl
  rw [hsvx]
  have ht1 : β 0 * ((1 - x j) * (sigmaValue w x j - excludedValue w x j)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hβ 0).1 (hquit j)
  have ht2 : (1 - β 0) * (continueMassExcl x j *
      weightStageValue w (planDeviate (instantConfigurationPlan x π) j β 1) j -
      x j * (sigmaValue w x j - excludedValue w x j)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [(hβ 0).2]) (by linarith [hkey])
  nlinarith [ht1, ht2, hε]

/-! ## Continuity of the row values, and the limit transfers

The limits below are stated as transfers along a sequence of rows rather
than as continuity on the product space `(ι → ℝ) × (ι → ℝ)`.  Composing
continuity on the product with a sequence of pairs forces the elaborator to
reduce `Function.comp` against a projection under the row values' `Finset`
sums, which is where the defeq cost lies; transferring one factor at a time
keeps every step first order. -/

omit [DecidableEq ι] in
theorem continuous_continueMass : Continuous fun x : ι → ℝ => continueMass x := by
  unfold continueMass
  exact continuous_finsetProd _ fun i _ => continuous_const.sub (continuous_apply i)

theorem continuous_continueMassExcl (i : ι) :
    Continuous fun x : ι → ℝ => continueMassExcl x i := by
  unfold continueMassExcl
  exact continuous_finsetProd _ fun j _ => continuous_const.sub (continuous_apply j)

theorem continuous_sigmaValue (w : Finset ι → ι → ℝ) (i : ι) :
    Continuous fun x : ι → ℝ => sigmaValue w x i := by
  unfold sigmaValue
  refine continuous_finsetSum _ fun J _ => ?_
  exact (((continuous_finsetProd _ fun j _ => continuous_apply j).mul
    (continuous_finsetProd _ fun j _ =>
      continuous_const.sub (continuous_apply j))).mul continuous_const)

theorem continuous_excludedValue (w : Finset ι → ι → ℝ) (i : ι) :
    Continuous fun x : ι → ℝ => excludedValue w x i := by
  unfold excludedValue
  refine continuous_finsetSum _ fun J _ => ?_
  exact (((continuous_finsetProd _ fun j _ => continuous_apply j).mul
    (continuous_finsetProd _ fun j _ =>
      continuous_const.sub (continuous_apply j))).mul continuous_const)

omit [Fintype ι] [DecidableEq ι] in
/-- A convergent sequence of rows converges coordinatewise. -/
theorem tendsto_apply_of_tendsto {rows : ℕ → ι → ℝ} {limit : ι → ℝ}
    (hrows : Tendsto rows atTop (𝓝 limit)) (i : ι) :
    Tendsto (fun k => rows k i) atTop (𝓝 (limit i)) :=
  tendsto_pi_nhds.mp hrows i

omit [DecidableEq ι] in
/-- The joint continue mass passes to the limit. -/
theorem tendsto_continueMass {rows : ℕ → ι → ℝ} {limit : ι → ℝ}
    (hrows : Tendsto rows atTop (𝓝 limit)) :
    Tendsto (fun k => continueMass (rows k)) atTop (𝓝 (continueMass limit)) :=
  (continuous_continueMass.tendsto limit).comp hrows

/-- The stop-minus-continue difference passes to the limit, jointly in the
row and in the continuation vector. -/
theorem tendsto_gainValue (w : Finset ι → ι → ℝ) {rows rests : ℕ → ι → ℝ}
    {rowLimit restLimit : ι → ℝ} (hrows : Tendsto rows atTop (𝓝 rowLimit))
    (hrests : Tendsto rests atTop (𝓝 restLimit)) (i : ι) :
    Tendsto (fun k => gainValue w (rows k) i (rests k i)) atTop
      (𝓝 (gainValue w rowLimit i (restLimit i))) := by
  simp only [gainValue_eq_sub_sub]
  exact ((((continuous_sigmaValue w i).tendsto rowLimit).comp hrows).sub
    (((continuous_excludedValue w i).tendsto rowLimit).comp hrows)).sub
    ((((continuous_continueMassExcl i).tendsto rowLimit).comp hrows).mul
      (tendsto_apply_of_tendsto hrests i))

/-! ## The theorem -/

/-- **The weighted continue-mass bound.**  For a quitting weight with no
instant approximate equilibria, whose players can each be punished to their
reservation level by a one-stage-absorbing stationary row, there is a
`ρ > 0` such that every `[0,1]`-row that is weighted `ρ`-near-Nash against a
`ρ`-rational, `bound`-bounded continuation vector has joint continue mass at
least `ρ`.

The bound on the continuation vector is a genuine hypothesis, not an
artefact: rationality constrains the continuation from below only, and the
limiting one-stage condition is lost at coordinates where the continuation
diverges while its weight `c_{-j}` vanishes. -/
theorem exists_pos_le_continueMass {w : Finset ι → ι → ℝ} {reservation : ι → ℝ}
    (bound : ℝ) (hnoInstant : HasNoInstantApproxEquilibria w)
    (hpunish : IsStationaryPunishment w reservation) :
    ∃ ρ > 0, ∀ rest x : ι → ℝ, (∀ i, |rest i| ≤ bound) →
      (∀ i, reservation i - ρ ≤ rest i) → (∀ i, 0 ≤ x i) → (∀ i, x i ≤ 1) →
        IsWeightedRow w x rest ρ → ρ ≤ continueMass x := by
  by_contra hcon
  push Not at hcon
  choose rest row hbnd hrat hrow0 hrow1 hweighted hmass using
    fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  -- The witnesses live in a compact set.
  set K : Set ((ι → ℝ) × (ι → ℝ)) :=
    (Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) ×ˢ
      (Set.univ.pi fun _ : ι => Set.Icc (-bound) bound) with hK
  have hKcompact : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hmem : ∀ k : ℕ, (row k, rest k) ∈ K := by
    intro k
    refine ⟨fun i _ => ⟨hrow0 k i, hrow1 k i⟩, fun i _ => ?_⟩
    exact ⟨neg_le_of_abs_le (hbnd k i), le_of_abs_le (hbnd k i)⟩
  obtain ⟨z, hzK, φ, hφ, hlim⟩ := hKcompact.tendsto_subseq hmem
  -- Pointwise limits.
  have hfst : Tendsto (fun k => row (φ k)) atTop (𝓝 z.1) :=
    (continuous_fst.tendsto z).comp hlim
  have hsnd : Tendsto (fun k => rest (φ k)) atTop (𝓝 z.2) :=
    (continuous_snd.tendsto z).comp hlim
  have hrho : Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  -- The limit row is feasible, and absorbs surely.
  have hz0 : ∀ i, 0 ≤ z.1 i := fun i => (hzK.1 i (Set.mem_univ i)).1
  have hz1 : ∀ i, z.1 i ≤ 1 := fun i => (hzK.1 i (Set.mem_univ i)).2
  have hcmle : continueMass z.1 ≤ 0 :=
    le_of_tendsto_of_tendsto' (tendsto_continueMass hfst) hrho fun k => (hmass (φ k)).le
  have hcmnonneg : 0 ≤ continueMass z.1 :=
    Finset.prod_nonneg fun i _ => by linarith [hz1 i]
  have hcmzero : continueMass z.1 = 0 := le_antisymm hcmle hcmnonneg
  obtain ⟨q, hq⟩ := exists_eq_one_of_continueMass_eq_zero hcmzero
  -- The limit continuation is rational, and the limit row is weighted-`0`.
  have hres : ∀ i, reservation i ≤ z.2 i := by
    intro i
    have hleft : Tendsto (fun k : ℕ => reservation i - 1 / ((φ k : ℝ) + 1)) atTop
        (𝓝 (reservation i)) := by
      simpa using (tendsto_const_nhds (x := reservation i) (f := atTop (α := ℕ))).sub hrho
    exact le_of_tendsto_of_tendsto' hleft (tendsto_apply_of_tendsto hsnd i)
      fun k => hrat (φ k) i
  have hgainlim : ∀ i, Tendsto (fun k => gainValue w (row (φ k)) i (rest (φ k) i)) atTop
      (𝓝 (gainValue w z.1 i (z.2 i))) := fun i => tendsto_gainValue w hfst hsnd i
  have hstop : ∀ i, (1 - z.1 i) * gainValue w z.1 i (z.2 i) ≤ 0 := by
    intro i
    have hone : Tendsto (fun k => 1 - row (φ k) i) atTop (𝓝 (1 - z.1 i)) :=
      tendsto_const_nhds.sub (tendsto_apply_of_tendsto hfst i)
    exact le_of_tendsto_of_tendsto' (hone.mul (hgainlim i)) hrho
      fun k => (hweighted (φ k) i).1
  have hgo : ∀ i, -(z.1 i) * gainValue w z.1 i (z.2 i) ≤ 0 := by
    intro i
    exact le_of_tendsto_of_tendsto' ((tendsto_apply_of_tendsto hfst i).neg.mul (hgainlim i))
      hrho fun k => (hweighted (φ k) i).2
  -- Assemble the instant approximate equilibrium.
  obtain ⟨π, hπ0, hπ1, hπExcl, hπpunish⟩ := hpunish q
  refine hnoInstant q z.1 π hq hz0 hz1 hπ0 hπ1
    (isWeightGlobalApproxEquilibrium_instantConfigurationPlan (punish := reservation q)
      hz1 hq hπExcl (fun j => ?_) (fun j => ?_) hπpunish)
  · by_cases hjq : j = q
    · rw [hjq, hq, sub_self, zero_mul]
    · have hexcl : continueMassExcl z.1 j = 0 :=
        continueMassExcl_eq_zero_of_ne z.1 (Ne.symm hjq) hq
      have := hstop j
      rw [gainValue_eq_sub_sub, hexcl, zero_mul, sub_zero] at this
      exact this
  · by_cases hjq : j = q
    · subst hjq
      have hgoj := hgo j
      rw [gainValue_eq_sub_sub, hq] at hgoj
      have hExclNonneg : 0 ≤ continueMassExcl z.1 j := continueMassExcl_nonneg hz1 j
      have hmono : continueMassExcl z.1 j * reservation j ≤ continueMassExcl z.1 j * z.2 j :=
        mul_le_mul_of_nonneg_left (hres j) hExclNonneg
      rw [hq]
      nlinarith [hgoj, hmono]
    · have hexcl : continueMassExcl z.1 j = 0 :=
        continueMassExcl_eq_zero_of_ne z.1 (Ne.symm hjq) hq
      have hgoj := hgo j
      rw [gainValue_eq_sub_sub, hexcl, zero_mul, sub_zero] at hgoj
      rw [hexcl, zero_mul]
      linarith [hgoj]

end GeneralWeight

/-! ## The three-coordinate instance

The general apparatus is definitionally the one of
`ScaledCyclicWeightNoApproximateEquilibria.lean` at the scaled cyclic
weight, so its instant impossibility theorem is exactly the general
hypothesis at that weight. -/

theorem weightStageValue_scaledCyclicWeight (x : CyclicIndex → ℝ) (i : CyclicIndex) :
    weightStageValue scaledCyclicWeight x i = stageValue x i := rfl

theorem weightPlanPayoff_scaledCyclicWeight (p : CyclicPlan) (i : CyclicIndex) :
    weightPlanPayoff scaledCyclicWeight p i = planPayoff p i := rfl

theorem instantConfigurationPlan_eq_eventuallyConstantPlan (row0 π : CyclicIndex → ℝ) :
    instantConfigurationPlan row0 π = eventuallyConstantPlan row0 π := by
  funext t; cases t <;> rfl

/-- **The scaled cyclic weight has no instant approximate equilibria**, in
the general sense of this file: the notion is definitionally the specialized
one, so the imported impossibility theorem transports verbatim. -/
theorem hasNoInstantApproxEquilibria_scaledCyclicWeight :
    HasNoInstantApproxEquilibria scaledCyclicWeight := by
  intro quitter row0 π hq h00 h01 hπ0 hπ1 hequilibrium
  refine no_instant_approxEquilibrium quitter row0 π hq h00 h01 hπ0 hπ1 fun ε hε j β hβ => ?_
  have h := hequilibrium ε hε j β hβ
  rw [instantConfigurationPlan_eq_eventuallyConstantPlan] at h
  exact h

/-- **The scaled cyclic weight punishes every player to `1/3`.**  Making the
successor of `q` quit surely absorbs the game in one stage and leaves `q`
with at most its own solo value `1/3`, whatever `q` does. -/
theorem isStationaryPunishment_scaledCyclicWeight :
    IsStationaryPunishment scaledCyclicWeight (fun _ => 1 / 3) := by
  intro q
  refine ⟨fun j => if j = cyclicSucc q then 1 else 0, fun j => ?_, fun j => ?_, ?_, ?_⟩
  · by_cases h : j = cyclicSucc q <;> simp [h]
  · by_cases h : j = cyclicSucc q <;> simp [h]
  · rw [continueMassExcl_cyclicIndex]
    simp
  · intro b _ hb1
    have hsucc : (if cyclicSucc q = cyclicSucc q then (1 : ℝ) else 0) = 1 := by simp
    have hpred : (if cyclicPred q = cyclicSucc q then (1 : ℝ) else 0) = 0 := by
      rw [if_neg (cyclicPred_ne_cyclicSucc q)]
    rw [sigmaValue_scaledCyclicWeight, excludedValue_scaledCyclicWeight, hpred, hsucc]
    linarith

/-- **The bound, at the scaled cyclic weight.**  The hypothesis package is
met there, so the theorem delivers an explicit positive `ρ`. -/
theorem exists_pos_le_continueMass_scaledCyclicWeight (bound : ℝ) :
    ∃ ρ > 0, ∀ rest x : CyclicIndex → ℝ, (∀ i, |rest i| ≤ bound) →
      (∀ i, (1 : ℝ) / 3 - ρ ≤ rest i) → (∀ i, 0 ≤ x i) → (∀ i, x i ≤ 1) →
        IsWeightedRow scaledCyclicWeight x rest ρ → ρ ≤ continueMass x :=
  exists_pos_le_continueMass bound hasNoInstantApproxEquilibria_scaledCyclicWeight
    isStationaryPunishment_scaledCyclicWeight

/-! ## The consumer form, on the `PMF Bool` side -/

section Consumer

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The endpoint condition is the weighted condition.**  The two clauses of
`IsεQuittingRootEndpointNash` are literally the two clauses of
`IsWeightedRow` at the translated row and weight: the Bool-side continue and
quit probabilities are `1 - x i` and `x i`, and the endpoint difference is
`gainValue`. -/
theorem isεQuittingRootEndpointNash_iff_isWeightedRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι) (ε : ℝ)
    (root : ι → PMF Bool) :
    IsεQuittingRootEndpointNash reward tail ε root ↔
      IsWeightedRow (weightOfReward reward) (hazardOfRoot root) tail ε := by
  constructor
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    rw [quittingRootEndpointDifference_eq_gainValue] at h1 h2
    have hx : (root i true).toReal = hazardOfRoot root i := rfl
    have hsum := quittingRoot_continueProbability_add_quitProbability root i
    rw [hx] at hsum h2
    have hy : (root i false).toReal = 1 - hazardOfRoot root i := by linarith
    rw [hy] at h1
    exact ⟨h1, by linarith⟩
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    rw [quittingRootEndpointDifference_eq_gainValue]
    have hx : (root i true).toReal = hazardOfRoot root i := rfl
    have hsum := quittingRoot_continueProbability_add_quitProbability root i
    rw [hx] at hsum
    have hy : (root i false).toReal = 1 - hazardOfRoot root i := by linarith
    rw [hx, hy]
    exact ⟨h1, by linarith⟩

/-- **The granted per-stage bound, with bounded continuations.**  This is
`IsQuittingGrantedContinueMassBound` of the survival-window landing chain
with the single extra clause that the continuation vector is bounded — the
clause the compactness argument genuinely needs, and one that every
continuation value of a bounded reward satisfies. -/
def IsQuittingBoundedGrantedContinueMassBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (reservation : Payoff ι) (bound ratio : ℝ) : Prop :=
  ∀ (continuation : Payoff ι) (root : ι → PMF Bool),
    (∀ player, |continuation player| ≤ bound) →
    (∀ player, reservation player - ratio ≤ continuation player) →
    IsεQuittingRootEndpointNash reward continuation ratio root →
      ratio ≤ quittingStationaryContinueMass root

/-- The bounded form is weaker than the landing chain's own hypothesis, so
nothing about the two is conflated: what is proved below is the bounded form
only. -/
theorem isQuittingBoundedGrantedContinueMassBound_of_isQuittingGrantedContinueMassBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (reservation : Payoff ι) (bound ratio : ℝ)
    (h : IsQuittingGrantedContinueMassBound reward reservation ratio) :
    IsQuittingBoundedGrantedContinueMassBound reward reservation bound ratio :=
  fun continuation root _ hrational hnash => h continuation root hrational hnash

/-- **The consumer form.**  A reward with no instant approximate equilibria
and a stationary punishment at every player grants the bounded per-stage
continue-mass bound at some positive ratio. -/
theorem exists_pos_isQuittingBoundedGrantedContinueMassBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (reservation : Payoff ι) (bound : ℝ)
    (hnoInstant : HasNoInstantApproxEquilibria (weightOfReward reward))
    (hpunish : IsStationaryPunishment (weightOfReward reward) reservation) :
    ∃ ratio > 0, IsQuittingBoundedGrantedContinueMassBound reward reservation bound ratio := by
  obtain ⟨ρ, hρ, hbound⟩ := exists_pos_le_continueMass (w := weightOfReward reward)
    (reservation := reservation) bound hnoInstant hpunish
  refine ⟨ρ, hρ, fun continuation root hcont hrational hnash => ?_⟩
  rw [← continueMass_hazardOfRoot]
  exact hbound continuation (hazardOfRoot root) hcont hrational
    (hazardOfRoot_nonneg root) (hazardOfRoot_le_one root)
    ((isεQuittingRootEndpointNash_iff_isWeightedRow reward continuation ρ root).mp hnash)

end Consumer

end GameTheory
