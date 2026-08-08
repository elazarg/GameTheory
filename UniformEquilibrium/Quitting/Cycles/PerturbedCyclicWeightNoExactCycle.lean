/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.CyclicWeightRowDichotomy
import Math.PMFProduct.CoalitionMass
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic

/-!
# An `ε`-perturbed cyclic weight with a positive diagonal and no exact cycle

This file builds, over the generic `sigmaValue`/`gammaValue`/`gainValue`
machinery of `QuittingCyclicWeightRowDichotomy.lean`, the notion of a
*periodic exactly complementary system* -- an "exact cycle" -- and proves
that the `ε`-perturbed three-coordinate cyclic weight admits none, at any
finite period, for every `ε` with `0 < ε ≤ 2`.

The weight, unnormalized, is

```
  J        r_0(J)   r_1(J)   r_2(J)
  {0}         1        3        0
  {1}         0        1        3
  {2}         3        0        1
  {0,1}     1+ε        0        1
  {1,2}       1      1+ε        0
  {0,2}       0        1      1+ε
  {0,1,2}     0        0        0
```

Its diagonal is `r_i({i}) = 1 > 0` at every coordinate. The normalization
used here is the unnormalized table; `normalizedPerturbedWeight` is the
same table divided by `3`, which satisfies `‖r‖∞ ≤ 1` for `0 ≤ ε ≤ 2`
(`abs_normalizedPerturbedWeight_le_one`), and `no_normalized_exactCycle`
transports the theorem to it through `ExactCycle.constMul`.

## Contents

* `ExactCycle`: a period-`m` exactly complementary system with period
  survival product below `1`, phases indexed by `ZMod m`.
* `ExactCycle.sigmaValue_le_value`, `ExactCycle.gammaValue_le_value`,
  `ExactCycle.value_eq_sigmaValue_of_pos`,
  `ExactCycle.value_eq_gammaValue_of_zero`: the Bellman identity
  `V_i(t) = max{Σ_i(t), Γ_i(t)}` in its four usable pieces.
* `perturbedWeight`, `sigmaValue_perturbedWeight`,
  `excludedValue_perturbedWeight`, `gammaValue_perturbedWeight`,
  `gainValue_perturbedWeight`: the table and its local identities.
* `one_le_value_perturbedWeight`: **stage 1**, the phase-value floor
  `V_i(t) ≥ 1`, valid for every `ε ≥ 0`.
* `perturbedWeight_atMostOnePositive`: **stage 2**, the row dichotomy for
  `0 ≤ ε ≤ 2`.
* `value_active_eq_one`, `value_next_active_eq_one`,
  `one_add_mul_le_value_pred`, `one_add_two_mul_le_value_succ`,
  `value_eq_of_zero_row`: **stage 3**, the label-lock inequalities.
* `no_exactCycle`: the theorem, for `0 < ε ≤ 2` and every period.
* `rotationExactCycle`: the `ε = 0` period-three phase rotation, built in
  this same encoding as the correctness test for all of the above.

## Where `ε = 0` breaks the argument

`one_add_mul_le_value_pred` degrades to `1 ≤ V_{k-1}(t)` at `ε = 0`, which
is exactly the floor and carries no information. The only consumers of its
strict form are the `cyclicPred` branch of `hsupp` inside `no_exactCycle`
and the matching branch of the label-propagation step, both of which
multiply `ε` by a positive rate. At `ε = 0` the value `1` may be passed
from one active label to the next, and indeed the period-three phase
rotation is an exact cycle there.
-/

noncomputable section

namespace GameTheory

open Finset Math.PMFProduct

/-! ## Reaching every phase by adding a natural number -/

/-- Every phase of `ZMod m` is reachable from every other by adding a
natural number. This is the only cyclicity fact the period-uniform
argument needs. -/
theorem exists_nat_add_eq {m : ℕ} [NeZero m] (t t' : ZMod m) :
    ∃ n : ℕ, t' = t + (n : ZMod m) := by
  obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (t' - t)
  exact ⟨n, by rw [hn]; ring⟩

/-! ## Periodic exactly complementary systems -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An **exact cycle of period `m`** for a weight `r`: a row of rates and a
value vector at each phase of `ZMod m`, tied by the one-stage value
recursion `V_i(t) = x_{t,i} Σ_i(t) + (1 - x_{t,i}) Γ_i(t)` -- which is the
coordinate-`i` split of the defining value series, the `i`-active mass
paying `Σ_i` and the rest paying `Γ_i` -- exactly complementary at every
phase, with period survival product strictly below `1`. -/
structure ExactCycle (r : Finset ι → ι → ℝ) (m : ℕ) [NeZero m] where
  /-- The per-coordinate rates at each phase. -/
  row : ZMod m → ι → ℝ
  /-- The value vector at each phase. -/
  value : ZMod m → ι → ℝ
  /-- Rates are nonnegative. -/
  row_nonneg : ∀ t i, 0 ≤ row t i
  /-- Rates are at most one. -/
  row_le_one : ∀ t i, row t i ≤ 1
  /-- The one-stage value recursion. -/
  bellman : ∀ t i, value t i =
    row t i * sigmaValue r (row t) i +
      (1 - row t i) * gammaValue r (row t) i (value (t + 1) i)
  /-- Exact complementarity at every phase. -/
  exact_row : ∀ t, IsExactRowComplementary (row t)
    (fun i => gainValue r (row t) i (value (t + 1) i))
  /-- The period survival product is strictly below one. -/
  survival : ∏ t : ZMod m, continueMass (row t) < 1

namespace ExactCycle

variable {r : Finset ι → ι → ℝ} {m : ℕ} [NeZero m] (C : ExactCycle r m)

/-- `Σ_i(t)` never exceeds the phase value: half of the Bellman identity
`V_i(t) = max{Σ_i(t), Γ_i(t)}`. -/
theorem sigmaValue_le_value (t : ZMod m) (i : ι) :
    sigmaValue r (C.row t) i ≤ C.value t i := by
  have hb := C.bellman t i
  have hgain : gainValue r (C.row t) i (C.value (t + 1) i) =
      sigmaValue r (C.row t) i - gammaValue r (C.row t) i (C.value (t + 1) i) := rfl
  rcases eq_or_lt_of_le (C.row_le_one t i) with heq | hlt
  · rw [heq] at hb; linarith
  · have h := (C.exact_row t i).2 hlt
    dsimp only at h
    rw [hgain] at h
    have h1 : (0 : ℝ) ≤ 1 - C.row t i := by linarith [C.row_le_one t i]
    have h2 : (0 : ℝ) ≤ gammaValue r (C.row t) i (C.value (t + 1) i) -
        sigmaValue r (C.row t) i := by linarith
    nlinarith [mul_nonneg h1 h2]

/-- `Γ_i(t)` never exceeds the phase value: the other half of the Bellman
identity. -/
theorem gammaValue_le_value (t : ZMod m) (i : ι) :
    gammaValue r (C.row t) i (C.value (t + 1) i) ≤ C.value t i := by
  have hb := C.bellman t i
  have hgain : gainValue r (C.row t) i (C.value (t + 1) i) =
      sigmaValue r (C.row t) i - gammaValue r (C.row t) i (C.value (t + 1) i) := rfl
  rcases eq_or_lt_of_le (C.row_nonneg t i) with heq | hpos
  · rw [← heq] at hb; linarith
  · have h := (C.exact_row t i).1 hpos
    dsimp only at h
    rw [hgain] at h
    nlinarith [mul_nonneg (le_of_lt hpos) h]

/-- At a coordinate acting at a positive rate the phase value is exactly
`Σ_i(t)`. -/
theorem value_eq_sigmaValue_of_pos (t : ZMod m) (i : ι) (hpos : 0 < C.row t i) :
    C.value t i = sigmaValue r (C.row t) i := by
  have hb := C.bellman t i
  have hgain : gainValue r (C.row t) i (C.value (t + 1) i) =
      sigmaValue r (C.row t) i - gammaValue r (C.row t) i (C.value (t + 1) i) := rfl
  have h := (C.exact_row t i).1 hpos
  dsimp only at h
  rw [hgain] at h
  have h1 : (0 : ℝ) ≤ 1 - C.row t i := by linarith [C.row_le_one t i]
  have hle : C.value t i ≤ sigmaValue r (C.row t) i := by
    nlinarith [mul_nonneg h1 h]
  exact le_antisymm hle (C.sigmaValue_le_value t i)

/-- At a silent coordinate the phase value is exactly `Γ_i(t)`. -/
theorem value_eq_gammaValue_of_zero (t : ZMod m) (i : ι) (hz : C.row t i = 0) :
    C.value t i = gammaValue r (C.row t) i (C.value (t + 1) i) := by
  have hb := C.bellman t i
  rw [hz] at hb
  linarith

end ExactCycle

/-! ## Positive coordinatewise scaling preserves exact cycles -/

/-- Scaling a weight by a constant scales `Σ_i`. -/
theorem sigmaValue_const_mul (c : ℝ) (r : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) :
    sigmaValue (fun S j => c * r S j) x i = c * sigmaValue r x i := by
  unfold sigmaValue
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun J _ => by ring

/-- Scaling a weight by a constant scales `A_i`. -/
theorem excludedValue_const_mul (c : ℝ) (r : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) :
    excludedValue (fun S j => c * r S j) x i = c * excludedValue r x i := by
  unfold excludedValue
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun J _ => by ring

/-- Scaling a weight and the continuation value by the same constant scales
`Γ_i`. -/
theorem gammaValue_const_mul (c : ℝ) (r : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) (next : ℝ) :
    gammaValue (fun S j => c * r S j) x i (c * next) = c * gammaValue r x i next := by
  unfold gammaValue
  rw [excludedValue_const_mul]
  ring

/-- Scaling a weight and the continuation value by the same constant scales
the gain. This is the affine invariance that makes the choice of
normalization immaterial. -/
theorem gainValue_const_mul (c : ℝ) (r : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) (next : ℝ) :
    gainValue (fun S j => c * r S j) x i (c * next) = c * gainValue r x i next := by
  unfold gainValue
  rw [sigmaValue_const_mul, gammaValue_const_mul]
  ring

/-- An exact cycle for `r` is an exact cycle for `c • r`, at the same rows
and the scaled value vector, for every `c > 0`. -/
def ExactCycle.constMul {r : Finset ι → ι → ℝ} {m : ℕ} [NeZero m] (C : ExactCycle r m)
    (c : ℝ) (hc : 0 < c) : ExactCycle (fun S j => c * r S j) m where
  row := C.row
  value := fun t i => c * C.value t i
  row_nonneg := C.row_nonneg
  row_le_one := C.row_le_one
  bellman := by
    intro t i
    rw [sigmaValue_const_mul, gammaValue_const_mul, C.bellman t i]
    ring
  exact_row := by
    intro t i
    obtain ⟨h1, h2⟩ := C.exact_row t i
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · change 0 ≤ gainValue (fun S j => c * r S j) (C.row t) i (c * C.value (t + 1) i)
      rw [gainValue_const_mul]
      exact mul_nonneg hc.le (h1 hp)
    · change gainValue (fun S j => c * r S j) (C.row t) i (c * C.value (t + 1) i) ≤ 0
      rw [gainValue_const_mul]
      nlinarith [h2 hp]
  survival := C.survival

/-! ## Cyclic index arithmetic -/

/-- The predecessor of a coordinate is never the coordinate itself. -/
theorem cyclicPred_ne_self (i : CyclicIndex) : cyclicPred i ≠ i := by
  fin_cases i <;> decide

/-- The successor of a coordinate is never the coordinate itself. -/
theorem cyclicSucc_ne_self (i : CyclicIndex) : cyclicSucc i ≠ i := by
  fin_cases i <;> decide

/-- `σ` really is the inverse of `π` on the three-cycle. -/
theorem cyclicPred_cyclicSucc (i : CyclicIndex) : cyclicPred (cyclicSucc i) = i := by
  fin_cases i <;> decide

/-- Two successor steps land on the predecessor. -/
theorem cyclicSucc_cyclicSucc_eq_cyclicPred (i : CyclicIndex) :
    cyclicSucc (cyclicSucc i) = cyclicPred i := by
  fin_cases i <;> decide

/-- The three coordinates are exhausted by a coordinate, its successor and
its predecessor. -/
theorem eq_or_eq_cyclicSucc_or_eq_cyclicPred (i j : CyclicIndex) :
    j = i ∨ j = cyclicSucc i ∨ j = cyclicPred i := by
  fin_cases i <;> fin_cases j <;> decide

/-! ## The `ε`-perturbed cyclic weight -/

/-- The `ε`-perturbed three-coordinate cyclic weight. Its diagonal is
`r_i({i}) = 1 > 0` at every coordinate; the value at the empty coalition and
at the full coalition is `0`, and the empty one is never read. -/
def perturbedWeight (ε : ℝ) (S : Finset CyclicIndex) (i : CyclicIndex) : ℝ :=
  if S = {0} then (if i = 0 then 1 else if i = 1 then 3 else 0)
  else if S = {1} then (if i = 0 then 0 else if i = 1 then 1 else 3)
  else if S = {2} then (if i = 0 then 3 else if i = 1 then 0 else 1)
  else if S = {0, 1} then (if i = 0 then 1 + ε else if i = 1 then 0 else 1)
  else if S = {1, 2} then (if i = 0 then 1 else if i = 1 then 1 + ε else 0)
  else if S = {0, 2} then (if i = 0 then 0 else if i = 1 then 1 else 1 + ε)
  else 0

/-- The diagonal of `perturbedWeight` is `1` at every coordinate, so the
weight is a positive-diagonal weight. -/
theorem perturbedWeight_diagonal (ε : ℝ) (i : CyclicIndex) :
    perturbedWeight ε {i} i = 1 := by
  fin_cases i <;> simp +decide [perturbedWeight]

/-- **`Σ_i(t)` for the perturbed weight**: `Σ_i = (1 - p)(1 + ε s)`, with
`p` the predecessor's rate and `s` the successor's. -/
theorem sigmaValue_perturbedWeight (ε : ℝ) (x : CyclicIndex → ℝ) (i : CyclicIndex) :
    sigmaValue (perturbedWeight ε) x i =
      (1 - x (cyclicPred i)) * (1 + ε * x (cyclicSucc i)) := by
  unfold sigmaValue
  rw [univ_erase_eq_pair i,
    sum_powerset_pair (cyclicSucc i) (cyclicPred i) (cyclicPred_ne_cyclicSucc i).symm]
  fin_cases i <;>
    simp +decide [cyclicSucc, cyclicPred, perturbedWeight,
      show ({1, 2} : Finset CyclicIndex) \ {1} = {2} from by decide,
      show ({2, 0} : Finset CyclicIndex) \ {2} = {0} from by decide,
      show ({0, 1} : Finset CyclicIndex) \ {0} = {1} from by decide] <;>
    ring

/-- **`A_i(t)` for the perturbed weight**: `A_i = p (3 - 2 s)`. -/
theorem excludedValue_perturbedWeight (ε : ℝ) (x : CyclicIndex → ℝ) (i : CyclicIndex) :
    excludedValue (perturbedWeight ε) x i =
      x (cyclicPred i) * (3 - 2 * x (cyclicSucc i)) := by
  unfold excludedValue
  rw [univ_erase_eq_pair i,
    sum_powerset_erase_empty_pair (cyclicSucc i) (cyclicPred i)
      (cyclicPred_ne_cyclicSucc i).symm]
  fin_cases i <;>
    simp +decide [cyclicSucc, cyclicPred, perturbedWeight,
      show ({1, 2} : Finset CyclicIndex) \ {1} = {2} from by decide,
      show ({2, 0} : Finset CyclicIndex) \ {2} = {0} from by decide,
      show ({0, 1} : Finset CyclicIndex) \ {0} = {1} from by decide] <;>
    ring

/-- **`Γ_i(t)` for the perturbed weight**:
`Γ_i = p (3 - 2 s) + (1 - p)(1 - s) W`. -/
theorem gammaValue_perturbedWeight (ε : ℝ) (x : CyclicIndex → ℝ) (i : CyclicIndex) (next : ℝ) :
    gammaValue (perturbedWeight ε) x i next =
      x (cyclicPred i) * (3 - 2 * x (cyclicSucc i)) +
        (1 - x (cyclicPred i)) * (1 - x (cyclicSucc i)) * next := by
  unfold gammaValue
  rw [excludedValue_perturbedWeight, continueMassExcl_cyclicIndex]
  ring

/-- **`g_i(t)` for the perturbed weight**, the local gain identity. Every
later step reads off this one line. -/
theorem gainValue_perturbedWeight (ε : ℝ) (x : CyclicIndex → ℝ) (i : CyclicIndex) (next : ℝ) :
    gainValue (perturbedWeight ε) x i next =
      (1 - x (cyclicPred i)) * (1 + ε * x (cyclicSucc i)) -
        (x (cyclicPred i) * (3 - 2 * x (cyclicSucc i)) +
          (1 - x (cyclicPred i)) * (1 - x (cyclicSucc i)) * next) := by
  unfold gainValue
  rw [sigmaValue_perturbedWeight, gammaValue_perturbedWeight]

/-! ## Stage 1: the phase-value floor -/

/-- **Rates at a minimizing phase.** If the phase value `V` at a coordinate
is a global minimum and is below `1`, then the predecessor's rate `p` is
positive and strictly below the successor's rate `s`. The `Γ` branch drives
this: pushing the global minimum through the survival factor forces
`2p < s(1+p)`. -/
theorem minimizing_rates (ε p s V W : ℝ) (hε : 0 ≤ ε)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hV : V < 1) (hVW : V ≤ W)
    (hsig : (1 - p) * (1 + ε * s) ≤ V)
    (hgam : p * (3 - 2 * s) + (1 - p) * (1 - s) * W ≤ V) :
    0 < p ∧ p < s := by
  have hq : (0 : ℝ) ≤ (1 - p) * (1 - s) := mul_nonneg (by linarith) (by linarith)
  have hpp : 0 < p := by
    rcases eq_or_lt_of_le hp0 with hz | hz
    · exfalso
      rw [← hz] at hsig
      linarith [mul_nonneg hε hs0]
    · exact hz
  refine ⟨hpp, ?_⟩
  have h1 : p * (3 - 2 * s) + (1 - p) * (1 - s) * V ≤ V := by
    nlinarith [mul_le_mul_of_nonneg_left hVW hq]
  have hpos2 : (0 : ℝ) < p + s - p * s := by
    nlinarith [mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 1 - p)]
  have h3 : V * (p + s - p * s) < p + s - p * s := by nlinarith
  have h4 : 2 * p < s * (1 + p) := by nlinarith
  nlinarith [mul_nonneg hp0 (by linarith : (0 : ℝ) ≤ 1 - p)]

/-- **The minimizing coordinate cannot be silent.** If the minimizing
coordinate's own rate is `0`, its predecessor is active, so the
predecessor's own value is its quit branch `1 - s`; the minimizing value is
at least `1 - p`, and `p < s` makes that impossible. -/
theorem minimizing_zero_rate (ε p s V Vp : ℝ) (hε : 0 ≤ ε)
    (hp1 : p ≤ 1) (hs0 : 0 ≤ s) (hps : p < s)
    (hsig : (1 - p) * (1 + ε * s) ≤ V) (hmin : V ≤ Vp) (hVp : Vp = 1 - s) : False := by
  have h := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - p) (mul_nonneg hε hs0)
  nlinarith

/-- **The minimizing coordinate cannot be active either.** With all three
rates positive every coordinate's value is its own quit branch. Minimality
against the predecessor forces `a > s`, minimality against the successor
forces `a < p`, and `p < s` closes the loop. This is the step that would
already close at `ε = 0`, where the predecessor comparison degenerates to
`s ≤ p`. -/
theorem minimizing_all_positive (ε p s a : ℝ) (hε : 0 ≤ ε)
    (hp0 : 0 ≤ p) (hs1 : s ≤ 1) (hps : p < s)
    (hA : (1 - p) * (1 + ε * s) ≤ (1 - s) * (1 + ε * a))
    (hB : (1 - p) * (1 + ε * s) ≤ (1 - a) * (1 + ε * p)) : False := by
  have hs0 : (0 : ℝ) < s := lt_of_le_of_lt hp0 hps
  have hp1 : p < 1 := lt_of_lt_of_le hps hs1
  have hkey : 0 < ε * (a * (1 - s) - s * (1 - p)) := by nlinarith
  have hεpos : 0 < ε := by
    rcases eq_or_lt_of_le hε with hz | hz
    · exfalso; rw [← hz] at hkey; simp at hkey
    · exact hz
  have hX : 0 < a * (1 - s) - s * (1 - p) := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hεpos.le (by linarith : (0 : ℝ) ≤ -(a * (1 - s) - s * (1 - p)))]
  have hslt : s < 1 := by
    by_contra hc
    push Not at hc
    have hse : s = 1 := le_antisymm hs1 hc
    rw [hse] at hX
    linarith
  have hsa : s < a := by nlinarith [mul_pos hs0 (sub_pos.mpr hps)]
  have hap : a < p := by
    by_contra hc
    push Not at hc
    have hfac : (0 : ℝ) ≤ 1 + ε * p := by nlinarith [mul_nonneg hε hp0]
    have e1 : (1 - a) * (1 + ε * p) ≤ (1 - p) * (1 + ε * p) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) hfac]
    have e2 : (1 - p) * (1 + ε * p) < (1 - p) * (1 + ε * s) :=
      mul_lt_mul_of_pos_left (by nlinarith [mul_lt_mul_of_pos_left hps hεpos])
        (by linarith)
    linarith
  linarith

/-- **Stage 1, the phase-value floor.** Every phase value of an exact cycle
for the perturbed weight is at least `1`. Only `ε ≥ 0` is needed; the
statement and its proof are equally valid at `ε = 0`, where the period-three
phase rotation attains the floor with equality at its active coordinate. -/
theorem one_le_value_perturbedWeight (ε : ℝ) (hε : 0 ≤ ε) {m : ℕ} [NeZero m]
    (C : ExactCycle (perturbedWeight ε) m) (t : ZMod m) (i : CyclicIndex) :
    1 ≤ C.value t i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨u, i0⟩, -, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (ZMod m × CyclicIndex)) (fun q => C.value q.1 q.2)
    ⟨(t, i), Finset.mem_univ _⟩
  have hmin' : ∀ (v : ZMod m) (j : CyclicIndex), C.value u i0 ≤ C.value v j :=
    fun v j => hmin (v, j) (Finset.mem_univ _)
  have hV : C.value u i0 < 1 := lt_of_le_of_lt (hmin' t i) hcon
  have hsig := C.sigmaValue_le_value u i0
  rw [sigmaValue_perturbedWeight] at hsig
  have hgam := C.gammaValue_le_value u i0
  rw [gammaValue_perturbedWeight] at hgam
  obtain ⟨hpp, hps⟩ := minimizing_rates ε (C.row u (cyclicPred i0)) (C.row u (cyclicSucc i0))
    (C.value u i0) (C.value (u + 1) i0) hε (C.row_nonneg u _) (C.row_le_one u _)
    (C.row_nonneg u _) (C.row_le_one u _) hV (hmin' (u + 1) i0) hsig hgam
  rcases eq_or_lt_of_le (C.row_nonneg u i0) with hz | hpos
  · have hval := C.value_eq_sigmaValue_of_pos u (cyclicPred i0) hpp
    rw [sigmaValue_perturbedWeight, cyclicPred_cyclicPred_eq_cyclicSucc,
      cyclicSucc_cyclicPred, ← hz] at hval
    refine minimizing_zero_rate ε (C.row u (cyclicPred i0)) (C.row u (cyclicSucc i0))
      (C.value u i0) (C.value u (cyclicPred i0)) hε (C.row_le_one u _) (C.row_nonneg u _)
      hps hsig (hmin' u (cyclicPred i0)) ?_
    rw [hval]; ring
  · have hspos : 0 < C.row u (cyclicSucc i0) := lt_trans hpp hps
    have hVi := C.value_eq_sigmaValue_of_pos u i0 hpos
    have hVp := C.value_eq_sigmaValue_of_pos u (cyclicPred i0) hpp
    have hVs := C.value_eq_sigmaValue_of_pos u (cyclicSucc i0) hspos
    rw [sigmaValue_perturbedWeight] at hVi
    rw [sigmaValue_perturbedWeight, cyclicPred_cyclicPred_eq_cyclicSucc,
      cyclicSucc_cyclicPred] at hVp
    rw [sigmaValue_perturbedWeight, cyclicPred_cyclicSucc,
      cyclicSucc_cyclicSucc_eq_cyclicPred] at hVs
    have hA := hmin' u (cyclicPred i0)
    have hB := hmin' u (cyclicSucc i0)
    rw [hVi, hVp] at hA
    rw [hVi, hVs] at hB
    exact minimizing_all_positive ε (C.row u (cyclicPred i0)) (C.row u (cyclicSucc i0))
      (C.row u i0) hε (C.row_nonneg u _) (C.row_le_one u _) hps hA hB

/-! ## Stage 2: the row dichotomy -/

/-- The bracket `(1 + ε) + (1 - ε) y` appearing on the right of the active
coordinate's rate inequality. -/
def perturbationFactor (ε y : ℝ) : ℝ := (1 + ε) + (1 - ε) * y

/-- The bracket is positive: it equals `(1 + ε)(1 - y) + 2 y`. -/
theorem perturbationFactor_pos (ε y : ℝ) (hε : 0 ≤ ε) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    0 < perturbationFactor ε y := by
  unfold perturbationFactor
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) (by linarith : (0 : ℝ) ≤ 1 - y)]

/-- The bracket is strictly below `3` for `0 ≤ ε ≤ 2` and `0 < y ≤ 1`:
`3 - ((1+ε) + (1-ε) y) = (2 - ε)(1 - y) + y`. This is the only place the
upper bound `ε ≤ 2` is used. -/
theorem perturbationFactor_lt_three (ε y : ℝ) (hε2 : ε ≤ 2) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    perturbationFactor ε y < 3 := by
  unfold perturbationFactor
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - ε) (by linarith : (0 : ℝ) ≤ 1 - y)]

/-- **The active coordinate's rate inequality.** If the gain at a coordinate
is nonnegative and the continuation value is at least `1`, then
`3 p ≤ s ((1+ε) + (1-ε) p)`. Obtained from the gain identity by discarding
the nonnegative slack `(1-p)(1-s)(W-1)`. -/
theorem rate_bound_of_gain (ε p s W : ℝ) (hp1 : p ≤ 1) (hs1 : s ≤ 1) (hW : 1 ≤ W)
    (hg : 0 ≤ (1 - p) * (1 + ε * s) -
      (p * (3 - 2 * s) + (1 - p) * (1 - s) * W)) :
    3 * p ≤ s * perturbationFactor ε p := by
  unfold perturbationFactor
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - p)
    (by linarith : (0 : ℝ) ≤ 1 - s)) (by linarith : (0 : ℝ) ≤ W - 1)]

/-- **Three simultaneously positive rates are impossible.** Multiplying the
three rate inequalities around the cycle and cancelling the common factor
`x_0 x_1 x_2 > 0` gives `27 ≤ ∏ ((1+ε) + (1-ε) x_j)`, while every bracket
lies strictly between `0` and `3`. -/
theorem not_all_three_rate_bounds (ε x0 x1 x2 : ℝ) (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (h0 : 0 < x0) (h1 : 0 < x1) (h2 : 0 < x2)
    (u0 : x0 ≤ 1) (u1 : x1 ≤ 1) (u2 : x2 ≤ 1)
    (b0 : 3 * x2 ≤ x1 * perturbationFactor ε x2)
    (b1 : 3 * x0 ≤ x2 * perturbationFactor ε x0)
    (b2 : 3 * x1 ≤ x0 * perturbationFactor ε x1) : False := by
  have f0 := perturbationFactor_pos ε x0 hε h0 u0
  have f1 := perturbationFactor_pos ε x1 hε h1 u1
  have f2 := perturbationFactor_pos ε x2 hε h2 u2
  have g0 := perturbationFactor_lt_three ε x0 hε2 h0 u0
  have g1 := perturbationFactor_lt_three ε x1 hε2 h1 u1
  have g2 := perturbationFactor_lt_three ε x2 hε2 h2 u2
  have step1 : (3 * x2) * (3 * x0) ≤ (x1 * perturbationFactor ε x2) *
      (x2 * perturbationFactor ε x0) :=
    mul_le_mul b0 b1 (by linarith) (by positivity)
  have step2 : ((3 * x2) * (3 * x0)) * (3 * x1) ≤
      ((x1 * perturbationFactor ε x2) * (x2 * perturbationFactor ε x0)) *
        (x0 * perturbationFactor ε x1) :=
    mul_le_mul step1 b2 (by linarith) (by positivity)
  have hprod : (0 : ℝ) < x0 * x1 * x2 := by positivity
  have hF : perturbationFactor ε x0 * perturbationFactor ε x1 * perturbationFactor ε x2 < 27 := by
    nlinarith
  nlinarith [mul_pos hprod (by linarith : (0 : ℝ) < 27 -
    perturbationFactor ε x0 * perturbationFactor ε x1 * perturbationFactor ε x2)]

/-- The rate inequality at a coordinate of an exactly complementary row of
the perturbed weight, with the floor supplying the continuation bound. -/
theorem perturbedWeight_rate_bound (ε : ℝ) (x next : CyclicIndex → ℝ)
    (hx1 : ∀ j, x j ≤ 1) (hnext : ∀ j, 1 ≤ next j) (i : CyclicIndex)
    (hgain : 0 ≤ gainValue (perturbedWeight ε) x i (next i)) :
    3 * x (cyclicPred i) ≤ x (cyclicSucc i) * perturbationFactor ε (x (cyclicPred i)) := by
  rw [gainValue_perturbedWeight] at hgain
  exact rate_bound_of_gain ε _ _ _ (hx1 _) (hx1 _) (hnext i) hgain

/-- **Two positive rates are impossible.** With coordinate `k` silent and
both its neighbours active, the rate inequality at `k`'s predecessor -- whose
own successor is the silent `k` -- reads `3 x_{σk} ≤ 0`. -/
theorem perturbedWeight_not_two_pos (ε : ℝ) (x next : CyclicIndex → ℝ)
    (hx1 : ∀ j, x j ≤ 1) (hnext : ∀ j, 1 ≤ next j)
    (hgain : ∀ i, 0 < x i → 0 ≤ gainValue (perturbedWeight ε) x i (next i))
    (k : CyclicIndex) (hk : x k = 0) (hA : 0 < x (cyclicPred k))
    (hB : 0 < x (cyclicSucc k)) : False := by
  have hb := perturbedWeight_rate_bound ε x next hx1 hnext (cyclicPred k)
    (hgain (cyclicPred k) hA)
  rw [cyclicSucc_cyclicPred, cyclicPred_cyclicPred_eq_cyclicSucc, hk, zero_mul] at hb
  linarith

/-- **All three rates positive is impossible** for `0 ≤ ε ≤ 2`. -/
theorem perturbedWeight_not_all_pos (ε : ℝ) (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (x next : CyclicIndex → ℝ) (hx1 : ∀ j, x j ≤ 1) (hnext : ∀ j, 1 ≤ next j)
    (hgain : ∀ i, 0 < x i → 0 ≤ gainValue (perturbedWeight ε) x i (next i))
    (h0 : 0 < x 0) (h1 : 0 < x 1) (h2 : 0 < x 2) : False := by
  have b0 := perturbedWeight_rate_bound ε x next hx1 hnext 0 (hgain 0 h0)
  have b1 := perturbedWeight_rate_bound ε x next hx1 hnext 1 (hgain 1 h1)
  have b2 := perturbedWeight_rate_bound ε x next hx1 hnext 2 (hgain 2 h2)
  have e0s : cyclicSucc (0 : CyclicIndex) = 1 := by decide
  have e0p : cyclicPred (0 : CyclicIndex) = 2 := by decide
  have e1s : cyclicSucc (1 : CyclicIndex) = 2 := by decide
  have e1p : cyclicPred (1 : CyclicIndex) = 0 := by decide
  have e2s : cyclicSucc (2 : CyclicIndex) = 0 := by decide
  have e2p : cyclicPred (2 : CyclicIndex) = 1 := by decide
  rw [e0s, e0p] at b0
  rw [e1s, e1p] at b1
  rw [e2s, e2p] at b2
  exact not_all_three_rate_bounds ε (x 0) (x 1) (x 2) hε hε2 h0 h1 h2
    (hx1 0) (hx1 1) (hx1 2) b0 b1 b2

/-- **Stage 2, the row dichotomy.** For `0 ≤ ε ≤ 2`, an exactly
complementary row of the perturbed weight whose continuation values are all
at least `1` has at most one positive coordinate. -/
theorem perturbedWeight_atMostOnePositive (ε : ℝ) (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (x next : CyclicIndex → ℝ) (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j ≤ 1)
    (hnext : ∀ j, 1 ≤ next j)
    (hgain : ∀ i, 0 < x i → 0 ≤ gainValue (perturbedWeight ε) x i (next i))
    (i j : CyclicIndex) (hi : 0 < x i) (hj : 0 < x j) : i = j := by
  have e0s : cyclicSucc (0 : CyclicIndex) = 1 := by decide
  have e0p : cyclicPred (0 : CyclicIndex) = 2 := by decide
  have e1s : cyclicSucc (1 : CyclicIndex) = 2 := by decide
  have e1p : cyclicPred (1 : CyclicIndex) = 0 := by decide
  have e2s : cyclicSucc (2 : CyclicIndex) = 0 := by decide
  have e2p : cyclicPred (2 : CyclicIndex) = 1 := by decide
  have pair : ¬ (0 < x 0 ∧ 0 < x 1) ∧ ¬ (0 < x 1 ∧ 0 < x 2) ∧ ¬ (0 < x 0 ∧ 0 < x 2) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨p0, p1⟩
      rcases eq_or_lt_of_le (hx0 2) with hk | hk
      · exact perturbedWeight_not_two_pos ε x next hx1 hnext hgain 2 hk.symm
          (by rw [e2p]; exact p1) (by rw [e2s]; exact p0)
      · exact perturbedWeight_not_all_pos ε hε hε2 x next hx1 hnext hgain p0 p1 hk
    · rintro ⟨p1, p2⟩
      rcases eq_or_lt_of_le (hx0 0) with hk | hk
      · exact perturbedWeight_not_two_pos ε x next hx1 hnext hgain 0 hk.symm
          (by rw [e0p]; exact p2) (by rw [e0s]; exact p1)
      · exact perturbedWeight_not_all_pos ε hε hε2 x next hx1 hnext hgain hk p1 p2
    · rintro ⟨p0, p2⟩
      rcases eq_or_lt_of_le (hx0 1) with hk | hk
      · exact perturbedWeight_not_two_pos ε x next hx1 hnext hgain 1 hk.symm
          (by rw [e1p]; exact p0) (by rw [e1s]; exact p2)
      · exact perturbedWeight_not_all_pos ε hε hε2 x next hx1 hnext hgain p0 hk p2
  by_contra hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact (pair.1 ⟨hi, hj⟩).elim
      | exact (pair.1 ⟨hj, hi⟩).elim
      | exact (pair.2.1 ⟨hi, hj⟩).elim
      | exact (pair.2.1 ⟨hj, hi⟩).elim
      | exact (pair.2.2 ⟨hi, hj⟩).elim
      | exact (pair.2.2 ⟨hj, hi⟩).elim

/-! ## Stage 3: the label lock -/

/-- **Zero rows do not move the value vector.** At an all-silent phase every
coordinate's value is its own continuation value. -/
theorem value_eq_of_zero_row (ε : ℝ) {m : ℕ} [NeZero m]
    (C : ExactCycle (perturbedWeight ε) m) (t : ZMod m)
    (hz : ∀ j, C.row t j = 0) (i : CyclicIndex) :
    C.value t i = C.value (t + 1) i := by
  have hval := C.value_eq_gammaValue_of_zero t i (hz i)
  rw [gammaValue_perturbedWeight, hz (cyclicPred i), hz (cyclicSucc i)] at hval
  rw [hval]; ring

/-- **The active coordinate's value is pinned to `1`.** At a singleton row
`h e_k` both opponents of `k` are silent, so `Σ_k = 1`, and `k` is active. -/
theorem value_active_eq_one (ε : ℝ) {m : ℕ} [NeZero m]
    (C : ExactCycle (perturbedWeight ε) m) (t : ZMod m) (k : CyclicIndex)
    (hk : 0 < C.row t k) (hz : ∀ j, j ≠ k → C.row t j = 0) :
    C.value t k = 1 := by
  have hval := C.value_eq_sigmaValue_of_pos t k hk
  rw [sigmaValue_perturbedWeight, hz _ (cyclicPred_ne_self k),
    hz _ (cyclicSucc_ne_self k)] at hval
  rw [hval]; ring

/-- **The active coordinate carries the value `1` forward.** At a singleton
row `h e_k`, `Γ_k` is exactly the continuation value, so the floor and the
pin above squeeze `V_k(t+1)` to `1`. -/
theorem value_next_active_eq_one (ε : ℝ) (hε : 0 ≤ ε) {m : ℕ} [NeZero m]
    (C : ExactCycle (perturbedWeight ε) m) (t : ZMod m) (k : CyclicIndex)
    (hk : 0 < C.row t k) (hz : ∀ j, j ≠ k → C.row t j = 0) :
    C.value (t + 1) k = 1 := by
  have hg := C.gammaValue_le_value t k
  rw [gammaValue_perturbedWeight, hz _ (cyclicPred_ne_self k),
    hz _ (cyclicSucc_ne_self k)] at hg
  rw [value_active_eq_one ε C t k hk hz] at hg
  have hfl := one_le_value_perturbedWeight ε hε C (t + 1) k
  linarith

/-- **The silent predecessor is strictly above `1`.** At a singleton row
`h e_k` the coordinate `k-1` sees `k` as its successor, so its quit branch
is `1 + ε h`. **This is the sole point where `ε > 0` enters**: at `ε = 0`
the bound degrades to the floor `1` and says nothing. -/
theorem one_add_mul_le_value_pred (ε : ℝ) {m : ℕ} [NeZero m]
    (C : ExactCycle (perturbedWeight ε) m) (t : ZMod m) (k : CyclicIndex)
    (hz : ∀ j, j ≠ k → C.row t j = 0) :
    1 + ε * C.row t k ≤ C.value t (cyclicPred k) := by
  have hs := C.sigmaValue_le_value t (cyclicPred k)
  rw [sigmaValue_perturbedWeight, cyclicPred_cyclicPred_eq_cyclicSucc,
    cyclicSucc_cyclicPred, hz _ (cyclicSucc_ne_self k)] at hs
  linarith

/-- **The silent successor is strictly above `1`.** At a singleton row
`h e_k` the coordinate `k+1` sees `k` as its predecessor and earns `3` from
it, so its continue branch is `3h + (1-h) V_{k+1}(t+1) ≥ 1 + 2h`. -/
theorem one_add_two_mul_le_value_succ (ε : ℝ) (hε : 0 ≤ ε) {m : ℕ} [NeZero m]
    (C : ExactCycle (perturbedWeight ε) m) (t : ZMod m) (k : CyclicIndex)
    (hz : ∀ j, j ≠ k → C.row t j = 0) :
    1 + 2 * C.row t k ≤ C.value t (cyclicSucc k) := by
  have hg := C.gammaValue_le_value t (cyclicSucc k)
  rw [gammaValue_perturbedWeight, cyclicPred_cyclicSucc,
    cyclicSucc_cyclicSucc_eq_cyclicPred, hz _ (cyclicPred_ne_self k)] at hg
  have hfl := one_le_value_perturbedWeight ε hε C (t + 1) (cyclicSucc k)
  nlinarith [mul_nonneg (by linarith [C.row_le_one t k] : (0 : ℝ) ≤ 1 - C.row t k)
    (by linarith : (0 : ℝ) ≤ C.value (t + 1) (cyclicSucc k) - 1)]

/-! ## The theorem -/

/-- **The perturbed weight admits no exact cycle of any finite period**, for
every `ε` with `0 < ε ≤ 2`. The argument is uniform in the period: it never
inducts on `m`, using finiteness only to take a global minimum of the phase
values and to traverse `ZMod m` by repeated `+1`.

The three stages: the floor `V ≥ 1`; the row dichotomy, so every nonzero row
is a singleton `h e_k`; and the label lock, where "value `= 1`" identifies
the active coordinate, propagates forward through zero rows, and pins the
active label for the whole period -- after which `k-1` earns `0` at every
phase, its value contracts around the cycle to `0`, and the floor is
violated. -/
theorem no_exactCycle (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2) {m : ℕ} [NeZero m]
    (C : ExactCycle (perturbedWeight ε) m) : False := by
  have hfl := one_le_value_perturbedWeight ε hε.le C
  -- Stage 2, phase by phase.
  have hdich : ∀ (t : ZMod m) (i j : CyclicIndex), 0 < C.row t i → 0 < C.row t j → i = j :=
    fun t i j hi hj => perturbedWeight_atMostOnePositive ε hε.le hε2 (C.row t)
      (fun l => C.value (t + 1) l) (C.row_nonneg t) (C.row_le_one t)
      (fun l => hfl (t + 1) l) (fun l hl => (C.exact_row t l).1 hl) i j hi hj
  -- Every row is either all silent or a singleton.
  have hrow : ∀ t : ZMod m, (∀ j, C.row t j = 0) ∨
      ∃ k, 0 < C.row t k ∧ ∀ j, j ≠ k → C.row t j = 0 := by
    intro t
    by_cases hall : ∀ j, C.row t j = 0
    · exact Or.inl hall
    · push Not at hall
      obtain ⟨k, hk⟩ := hall
      have hkpos : 0 < C.row t k := lt_of_le_of_ne (C.row_nonneg t k) (Ne.symm hk)
      refine Or.inr ⟨k, hkpos, fun j hj => ?_⟩
      by_contra hne
      exact hj (hdich t j k (lt_of_le_of_ne (C.row_nonneg t j) (Ne.symm hne)) hkpos)
  -- Some phase is nonzero, since the period survival product is below one.
  have hnonzero : ∃ (t : ZMod m) (k : CyclicIndex), 0 < C.row t k := by
    by_contra hcon
    push Not at hcon
    have hone : ∀ t : ZMod m, continueMass (C.row t) = 1 := by
      intro t
      have hz : ∀ k, C.row t k = 0 := fun k => le_antisymm (hcon t k) (C.row_nonneg t k)
      simp [continueMass, hz]
    have hsurv := C.survival
    rw [Finset.prod_congr rfl fun t _ => hone t] at hsurv
    simp at hsurv
  obtain ⟨t0, k0, hk0⟩ := hnonzero
  -- The value `1` moves forward one phase at a time and never changes label.
  have hstep : ∀ t : ZMod m, C.value t k0 = 1 → C.value (t + 1) k0 = 1 := by
    intro t h1
    rcases hrow t with hall | ⟨k, hk, hkz⟩
    · rw [← value_eq_of_zero_row ε C t hall k0]; exact h1
    · rcases eq_or_eq_cyclicSucc_or_eq_cyclicPred k k0 with he | he | he
      · rw [he]
        exact value_next_active_eq_one ε hε.le C t k hk hkz
      · exact absurd h1 (by
          have hv := one_add_two_mul_le_value_succ ε hε.le C t k hkz
          rw [← he] at hv
          exact ne_of_gt (by linarith))
      · exact absurd h1 (by
          have hv := one_add_mul_le_value_pred ε C t k hkz
          rw [← he] at hv
          exact ne_of_gt (by nlinarith [mul_pos hε hk]))
  have hseed : C.value t0 k0 = 1 := by
    refine value_active_eq_one ε C t0 k0 hk0 fun j hj => ?_
    by_contra hne
    exact hj (hdich t0 j k0 (lt_of_le_of_ne (C.row_nonneg t0 j) (Ne.symm hne)) hk0)
  have hiter : ∀ n : ℕ, C.value (t0 + (n : ZMod m)) k0 = 1 := by
    intro n
    induction n with
    | zero => simpa using hseed
    | succ n ih =>
        have hcast : ((n + 1 : ℕ) : ZMod m) = (n : ZMod m) + 1 := by push_cast; ring
        rw [hcast, ← add_assoc]
        exact hstep _ ih
  have hone : ∀ t : ZMod m, C.value t k0 = 1 := by
    intro t
    obtain ⟨n, hn⟩ := exists_nat_add_eq t0 t
    rw [hn]; exact hiter n
  -- Hence every nonzero row is supported on `k0`.
  have hsupp : ∀ (t : ZMod m) (j : CyclicIndex), 0 < C.row t j → j = k0 := by
    intro t j hj
    have hjz : ∀ l, l ≠ j → C.row t l = 0 := by
      intro l hl
      by_contra hne
      exact hl (hdich t l j (lt_of_le_of_ne (C.row_nonneg t l) (Ne.symm hne)) hj)
    rcases eq_or_eq_cyclicSucc_or_eq_cyclicPred j k0 with he | he | he
    · exact he.symm
    · exfalso
      have hv := one_add_two_mul_le_value_succ ε hε.le C t j hjz
      rw [← he, hone t] at hv
      linarith
    · exfalso
      have hv := one_add_mul_le_value_pred ε C t j hjz
      rw [← he, hone t] at hv
      nlinarith [mul_pos hε hj]
  -- Coordinate `k0 - 1` earns nothing at any phase.
  have hrec : ∀ t : ZMod m,
      C.value t (cyclicPred k0) = (1 - C.row t k0) * C.value (t + 1) (cyclicPred k0) := by
    intro t
    have hz : ∀ l, l ≠ k0 → C.row t l = 0 := by
      intro l hl
      by_contra hne
      exact hl (hsupp t l (lt_of_le_of_ne (C.row_nonneg t l) (Ne.symm hne)))
    have hval := C.value_eq_gammaValue_of_zero t (cyclicPred k0)
      (hz _ (cyclicPred_ne_self k0))
    rw [gammaValue_perturbedWeight, cyclicPred_cyclicPred_eq_cyclicSucc,
      cyclicSucc_cyclicPred, hz _ (cyclicSucc_ne_self k0)] at hval
    rw [hval]; ring
  have hmono : ∀ t : ZMod m,
      C.value t (cyclicPred k0) ≤ C.value (t + 1) (cyclicPred k0) := by
    intro t
    have h1 := hrec t
    have h2 := hfl (t + 1) (cyclicPred k0)
    nlinarith [mul_nonneg (C.row_nonneg t k0) (by linarith : (0 : ℝ) ≤
      C.value (t + 1) (cyclicPred k0))]
  have hchain : ∀ (n : ℕ) (t : ZMod m),
      C.value t (cyclicPred k0) ≤ C.value (t + (n : ZMod m)) (cyclicPred k0) := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
        intro t
        have hcast : ((n + 1 : ℕ) : ZMod m) = (n : ZMod m) + 1 := by push_cast; ring
        rw [hcast, ← add_assoc]
        exact le_trans (ih t) (hmono _)
  have hle : ∀ t t' : ZMod m, C.value t (cyclicPred k0) ≤ C.value t' (cyclicPred k0) := by
    intro t t'
    obtain ⟨n, hn⟩ := exists_nat_add_eq t t'
    rw [hn]; exact hchain n t
  have hzero : ∀ t : ZMod m, C.row t k0 = 0 := by
    intro t
    have hconst : C.value t (cyclicPred k0) = C.value (t + 1) (cyclicPred k0) :=
      le_antisymm (hle t (t + 1)) (hle (t + 1) t)
    have h1 := hrec t
    have h2 := hfl (t + 1) (cyclicPred k0)
    have h4 : C.row t k0 * C.value (t + 1) (cyclicPred k0) = 0 := by linarith
    exact (mul_eq_zero.mp h4).resolve_right (by linarith)
  have := hzero t0
  linarith

/-! ## The normalized weight -/

/-- The same weight divided by `3`, so that `‖r‖∞ ≤ 1` for `0 ≤ ε ≤ 2`. -/
def normalizedPerturbedWeight (ε : ℝ) (S : Finset CyclicIndex) (i : CyclicIndex) : ℝ :=
  perturbedWeight ε S i / 3

/-- Every entry of the normalized weight lies in `[-1, 1]` for
`0 ≤ ε ≤ 2`, so it meets the setting's `‖r‖∞ ≤ 1` requirement. -/
theorem abs_normalizedPerturbedWeight_le_one (ε : ℝ) (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (S : Finset CyclicIndex) (i : CyclicIndex) :
    |normalizedPerturbedWeight ε S i| ≤ 1 := by
  unfold normalizedPerturbedWeight perturbedWeight
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- The diagonal of the normalized weight is `1/3 > 0`. -/
theorem normalizedPerturbedWeight_diagonal (ε : ℝ) (i : CyclicIndex) :
    normalizedPerturbedWeight ε {i} i = 1 / 3 := by
  unfold normalizedPerturbedWeight
  rw [perturbedWeight_diagonal]

/-- **The normalized weight admits no exact cycle of any finite period**,
for `0 < ε ≤ 2`. Transported from `no_exactCycle` by the positive scaling
`ExactCycle.constMul`, which is where affine invariance is used. -/
theorem no_normalized_exactCycle (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2) {m : ℕ} [NeZero m]
    (C : ExactCycle (normalizedPerturbedWeight ε) m) : False := by
  have hfun : (fun S j => (3 : ℝ) * normalizedPerturbedWeight ε S j) = perturbedWeight ε := by
    funext S j
    unfold normalizedPerturbedWeight
    ring
  exact no_exactCycle ε hε hε2 (hfun ▸ C.constMul 3 (by norm_num))

/-! ## The `ε = 0` witness

At `ε = 0` the weight **does** admit an exact cycle, the period-three phase
rotation. Building it in this very encoding is the correctness test for
everything above: had the table been mistranscribed, or the predecessor and
successor been swapped, the construction below would fail to typecheck.
Its existence is consistent with `no_exactCycle` precisely because that
theorem requires `0 < ε`. -/

/-- The phase rotation: at phase `t` the coordinate `t` acts at rate
`1/2` and the other two are silent. -/
def rotationRow (t : ZMod 3) (i : CyclicIndex) : ℝ :=
  if t = 0 then (if i = 0 then 1 / 2 else 0)
  else if t = 1 then (if i = 1 then 1 / 2 else 0)
  else (if i = 2 then 1 / 2 else 0)

/-- The phase values of the rotation: `V(0) = (1,2,1)`, `V(1) = (1,1,2)`,
`V(2) = (2,1,1)`. The value `2 = 1 + 2·(1/2)` sits at the successor of the
active coordinate, meeting `one_add_two_mul_le_value_succ` with equality;
the value `1` sits at the active coordinate and at its predecessor, the
latter meeting `one_add_mul_le_value_pred` with equality exactly because
`ε = 0`. -/
def rotationValue (t : ZMod 3) (i : CyclicIndex) : ℝ :=
  if t = 0 then (if i = 1 then 2 else 1)
  else if t = 1 then (if i = 2 then 2 else 1)
  else (if i = 0 then 2 else 1)

/-- The three phases of `ZMod 3`. -/
theorem zmod_three_cases (t : ZMod 3) : t = 0 ∨ t = 1 ∨ t = 2 := by
  revert t; decide

/-- **The correctness test.** At `ε = 0` the period-three phase rotation is
an exact cycle for the weight. Combined with `no_exactCycle`, which needs
`0 < ε`, this pins `ε = 0` as the exact boundary of the family. -/
def rotationExactCycle : ExactCycle (perturbedWeight 0) 3 where
  row := rotationRow
  value := rotationValue
  row_nonneg := by
    intro t i
    unfold rotationRow
    split_ifs <;> norm_num
  row_le_one := by
    intro t i
    unfold rotationRow
    split_ifs <;> norm_num
  bellman := by
    intro t i
    rw [sigmaValue_perturbedWeight, gammaValue_perturbedWeight]
    rcases zmod_three_cases t with rfl | rfl | rfl <;> fin_cases i <;>
      simp +decide [rotationRow, rotationValue] <;> norm_num
  exact_row := by
    intro t i
    dsimp only
    rw [gainValue_perturbedWeight]
    rcases zmod_three_cases t with rfl | rfl | rfl <;> fin_cases i <;>
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
        simp +decide [rotationRow, rotationValue] at h ⊢ <;> norm_num
  survival := by
    have h : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
    rw [h, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton]
    simp +decide [continueMass, rotationRow, Fin.prod_univ_three]
    norm_num

end GameTheory
