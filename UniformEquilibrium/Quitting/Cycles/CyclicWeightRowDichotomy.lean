/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# A row-local dichotomy for a rational three-coordinate cyclic weight

This file works entirely with a single row of the general finite-`I`
setting: an index set `ι`, a weight `r : Finset ι → ι → ℝ` giving the
reward to a player from each nonempty coalition, and a row `x : ι → ℝ` of
per-coordinate hazards. It defines `Σ_i`, `Γ_i`, `g_i` exactly as the
sums they are, and the "exactly complementary" sign condition on a single
row, then specializes to the explicit rational weight on three cyclically
ordered coordinates and proves the row dichotomy: an exactly complementary
row of this weight, together with a nonnegative next-phase centered value,
has at most one positive coordinate.

This isolates the purely algebraic core consumed by the surrounding
periodic argument (not built here): once every nonzero row is a scaled
standard basis vector, exact complementarity cannot close into a cycle
of any finite period, while relaxed (`ε`-)complementary cycles of growing
period exist at every tolerance. So exact complementarity is not
recoverable as a limit of relaxed complementarity for this weight, even
though the cycles realizing every tolerance keep a constant absorbed mass
of `7/8` per period -- the obstruction is not a mass-poor block.

## Contents

* `sigmaValue`, `excludedValue`, `gammaValue`, `gainValue`: `Σ_i`, `A_i`,
  `Γ_i`, `g_i`, for a general finite `ι`.
* `IsExactRowComplementary`: the single-row sign condition.
* `sum_powerset_pair`, `sum_powerset_erase_empty_pair`: the finite-arithmetic
  engine that expands a sum over the powerset of a two-element finset.
* `cyclicWeight`: the explicit rational weight, equation (9).
* `sigmaValue_cyclicWeight`, `gammaValue_cyclicWeight`, `gainValue_cyclicWeight`:
  equations (13), (14), (15), reproduced from the definitions above.
* `atMostOnePositive_of_isExactRowComplementary`: the row dichotomy.
-/

noncomputable section

namespace GameTheory

open Finset

/-! ## The finite-arithmetic engine: powerset of a two-element finset -/

/-- Expanding a sum over the powerset of a two-element finset `{a, b}`
(`a ≠ b`) into its four terms. Proved by two applications of
`Finset.sum_powerset_insert`, so it holds for any index type with decidable
equality -- no finiteness of `ι` itself is needed. -/
theorem sum_powerset_pair {ι : Type*} [DecidableEq ι] (a b : ι) (hab : a ≠ b)
    (f : Finset ι → ℝ) :
    ∑ J ∈ ({a, b} : Finset ι).powerset, f J =
      f ∅ + f {b} + f {a} + f {a, b} := by
  have h1 : ({a, b} : Finset ι) = insert a {b} := rfl
  have h2 : ({b} : Finset ι) = insert b ∅ := by simp
  rw [h1, Finset.sum_powerset_insert (by simpa using hab)]
  simp only [h2, Finset.sum_powerset_insert (Finset.notMem_empty b)]
  simp
  ring

/-- The same expansion with the empty coalition dropped: the three nonempty
terms. -/
theorem sum_powerset_erase_empty_pair {ι : Type*} [DecidableEq ι] (a b : ι)
    (hab : a ≠ b) (f : Finset ι → ℝ) :
    ∑ J ∈ ({a, b} : Finset ι).powerset.erase ∅, f J =
      f {b} + f {a} + f {a, b} := by
  have hmem : (∅ : Finset ι) ∈ ({a, b} : Finset ι).powerset :=
    Finset.empty_mem_powerset _
  have hsplit := Finset.add_sum_erase _ f hmem
  rw [sum_powerset_pair a b hab f] at hsplit
  linarith [hsplit]

/-! ## `Σ_i`, `Γ_i`, `g_i`, and single-row exact complementarity -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `c_{-i}(y)`, equation (1): the probability that every coordinate other
than `i` stays put. -/
def continueMassExcl (x : ι → ℝ) (i : ι) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (1 - x j)

/-- `Σ_i(t)`, equation (3): summed over subsets `J` of the coordinates other
than `i`, the reward to `i` from the outcome `J ∪ {i}`, weighted by the
coalition mass of `J` relative to the other coordinates. -/
def sigmaValue (r : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  ∑ J ∈ (Finset.univ.erase i).powerset,
    (∏ j ∈ J, x j) * (∏ j ∈ Finset.univ.erase i \ J, (1 - x j)) * r (insert i J) i

/-- `A_i(t)`, the nonempty-coalition part of `Γ_i`, equation (4). -/
def excludedValue (r : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  ∑ J ∈ (Finset.univ.erase i).powerset.erase ∅,
    (∏ j ∈ J, x j) * (∏ j ∈ Finset.univ.erase i \ J, (1 - x j)) * r J i

/-- `Γ_i(t)`, equation (4): the nonempty-coalition value plus the
continuation value, the latter reached exactly when everyone but `i` stays
put. -/
def gammaValue (r : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) (next : ℝ) : ℝ :=
  excludedValue r x i + continueMassExcl x i * next

/-- `g_i = Σ_i - Γ_i`, the local exactness gain. -/
def gainValue (r : Finset ι → ι → ℝ) (x : ι → ℝ) (i : ι) (next : ℝ) : ℝ :=
  sigmaValue r x i - gammaValue r x i next

/-- Exact complementarity of a single row `x` against gains `g`, from the
"Setting" section: `x i > 0 → g i ≥ 0` and `x i < 1 → g i ≤ 0`, at every
coordinate. -/
def IsExactRowComplementary (x g : ι → ℝ) : Prop :=
  ∀ i, (0 < x i → 0 ≤ g i) ∧ (x i < 1 → g i ≤ 0)

/-! ## The explicit rational weight on three cyclic coordinates -/

/-- The three cyclically ordered coordinates. -/
abbrev CyclicIndex := Fin 3

/-- The cyclic successor `σ`, equation (9)'s `σ(1)=2, σ(2)=3, σ(3)=1` in the
zero-indexed labelling used here. -/
def cyclicSucc (i : CyclicIndex) : CyclicIndex := i + 1

/-- The cyclic predecessor `π = σ⁻¹`. -/
def cyclicPred (i : CyclicIndex) : CyclicIndex := i + 2

/-- `π` really is the inverse of `σ` on the three-cycle. -/
theorem cyclicSucc_cyclicPred (i : CyclicIndex) : cyclicSucc (cyclicPred i) = i := by
  fin_cases i <;> decide

/-- The predecessor and successor of a coordinate are always distinct. -/
theorem cyclicPred_ne_cyclicSucc (i : CyclicIndex) : cyclicPred i ≠ cyclicSucc i := by
  fin_cases i <;> decide

/-- The coordinates other than `i` are exactly its successor and
predecessor. -/
theorem univ_erase_eq_pair (i : CyclicIndex) :
    (Finset.univ.erase i : Finset CyclicIndex) = {cyclicSucc i, cyclicPred i} := by
  fin_cases i <;> decide

/-- The explicit rational weight, equation (9). The value at the empty
coalition is never read by `sigmaValue` or `excludedValue`. -/
def cyclicWeight (S : Finset CyclicIndex) (i : CyclicIndex) : ℝ :=
  if S = {0} then (if i = 0 then -1 / 2 else if i = 1 then 1 / 2 else -1)
  else if S = {1} then (if i = 0 then -1 else if i = 1 then -1 / 2 else 1 / 2)
  else if S = {2} then (if i = 0 then 1 / 2 else if i = 1 then -1 else -1 / 2)
  else if S = {0, 1} then (if i = 0 then -1 / 4 else if i = 1 then -1 / 2 else 1 / 2)
  else if S = {1, 2} then (if i = 0 then 1 / 2 else if i = 1 then -1 / 4 else -1 / 2)
  else if S = {0, 2} then (if i = 0 then -1 / 2 else if i = 1 then 1 / 2 else -1 / 4)
  else if S = {0, 1, 2} then -1 / 2
  else 0

/-- **Equation (13), reproduced.** `Σ_i(t) + 1/2 = (1/4) s (1-p)`, with
`s` the successor's hazard and `p` the predecessor's, computed directly
from `sigmaValue` and the weight table `cyclicWeight`. -/
theorem sigmaValue_cyclicWeight (x : CyclicIndex → ℝ) (i : CyclicIndex) :
    sigmaValue cyclicWeight x i + 1 / 2 =
      (1 / 4) * x (cyclicSucc i) * (1 - x (cyclicPred i)) := by
  unfold sigmaValue
  rw [univ_erase_eq_pair i,
    sum_powerset_pair (cyclicSucc i) (cyclicPred i) (cyclicPred_ne_cyclicSucc i).symm]
  fin_cases i <;>
    simp +decide [cyclicSucc, cyclicPred, cyclicWeight,
      show ({1, 2} : Finset CyclicIndex) \ {1} = {2} from by decide,
      show ({2, 0} : Finset CyclicIndex) \ {2} = {0} from by decide,
      show ({0, 1} : Finset CyclicIndex) \ {0} = {1} from by decide] <;>
    ring

/-- `A_i(t)`, the nonempty-coalition half of equation (14), computed
directly from `excludedValue` and the weight table `cyclicWeight`. -/
theorem excludedValue_cyclicWeight (x : CyclicIndex → ℝ) (i : CyclicIndex) :
    excludedValue cyclicWeight x i =
      (1 / 2) * x (cyclicPred i) - x (cyclicSucc i) +
        x (cyclicSucc i) * x (cyclicPred i) := by
  unfold excludedValue
  rw [univ_erase_eq_pair i,
    sum_powerset_erase_empty_pair (cyclicSucc i) (cyclicPred i)
      (cyclicPred_ne_cyclicSucc i).symm]
  fin_cases i <;>
    simp +decide [cyclicSucc, cyclicPred, cyclicWeight,
      show ({1, 2} : Finset CyclicIndex) \ {1} = {2} from by decide,
      show ({2, 0} : Finset CyclicIndex) \ {2} = {0} from by decide,
      show ({0, 1} : Finset CyclicIndex) \ {0} = {1} from by decide] <;>
    ring

/-- `c_{-i}` for `cyclicWeight`'s three coordinates: the product of the
successor's and the predecessor's survival, since those are exactly the
two coordinates other than `i`. -/
theorem continueMassExcl_cyclicIndex (x : CyclicIndex → ℝ) (i : CyclicIndex) :
    continueMassExcl x i =
      (1 - x (cyclicSucc i)) * (1 - x (cyclicPred i)) := by
  unfold continueMassExcl
  rw [univ_erase_eq_pair i, Finset.prod_pair (cyclicPred_ne_cyclicSucc i).symm]

/-- **Equation (14), reproduced.** `Γ_i(t) + 1/2 = (1-p)(1-s) z + p -
(1/2) s (1-p)`, with `z = next + 1/2` the centered next-phase value. -/
theorem gammaValue_cyclicWeight (x : CyclicIndex → ℝ) (i : CyclicIndex) (next : ℝ) :
    gammaValue cyclicWeight x i next + 1 / 2 =
      (1 - x (cyclicPred i)) * (1 - x (cyclicSucc i)) * (next + 1 / 2) +
        x (cyclicPred i) - (1 / 2) * x (cyclicSucc i) * (1 - x (cyclicPred i)) := by
  unfold gammaValue
  rw [excludedValue_cyclicWeight, continueMassExcl_cyclicIndex]
  ring

/-- **Equation (15), reproduced.** `g_i(t) = (3/4) s (1-p) - p -
(1-p)(1-s) z`, with `z = next + 1/2` the centered next-phase value `V_i(t+1)
+ 1/2`. This is the central algebraic identity: everything downstream in
the hand proof (the row dichotomy, and ultimately the nonexistence of an
exact cycle) is read off from this one line. -/
theorem gainValue_cyclicWeight (x : CyclicIndex → ℝ) (i : CyclicIndex) (next : ℝ) :
    gainValue cyclicWeight x i next =
      (3 / 4) * x (cyclicSucc i) * (1 - x (cyclicPred i)) - x (cyclicPred i) -
        (1 - x (cyclicPred i)) * (1 - x (cyclicSucc i)) * (next + 1 / 2) := by
  have hsigma := sigmaValue_cyclicWeight x i
  have hgamma := gammaValue_cyclicWeight x i next
  unfold gainValue
  linarith [hsigma, hgamma]

/-! ## The row dichotomy -/

/-- **Equation (16), reproduced.** If `i` is active (`x i > 0`) in an
exactly complementary row with a nonnegative centered next-phase value at
`i`, its predecessor's hazard is bounded by `(3/4)` times its successor's
hazard, discounted by the predecessor's own survival: `p ≤ (3/4) s (1-p)`.
Proved by dropping the nonnegative `(1-p)(1-s)z` term from equation (15). -/
theorem cyclicWeight_pred_le_of_pos (x z : CyclicIndex → ℝ) (i : CyclicIndex)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hz : 0 ≤ z i)
    (hgain : 0 ≤ gainValue cyclicWeight x i (z i - 1 / 2)) :
    x (cyclicPred i) ≤ (3 / 4) * x (cyclicSucc i) * (1 - x (cyclicPred i)) := by
  rw [gainValue_cyclicWeight] at hgain
  have hp := hx (cyclicPred i)
  have hs := hx (cyclicSucc i)
  have heq : z i - 1 / 2 + 1 / 2 = z i := by ring
  rw [heq] at hgain
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hs.2)) hz]

/-- Two predecessor steps land on the successor: `π(π(k)) = σ(k)` on the
three-cycle. Used to identify "the other active coordinate" when the third
coordinate `k` is inert. -/
theorem cyclicPred_cyclicPred_eq_cyclicSucc (k : CyclicIndex) :
    cyclicPred (cyclicPred k) = cyclicSucc k := by
  fin_cases k <;> decide

/-- **The two-active-coordinates case of the row dichotomy.** If coordinate
`k` is inert (`x k = 0`) while both its predecessor and successor are
active, equation (16) applied at the predecessor forces the successor's
hazard to be at most `0`, contradicting its positivity. This is the "choose
an active coordinate whose predecessor is active and successor is inactive"
step of the hand proof. -/
theorem cyclicWeight_false_of_zero_between_two_pos (x z : CyclicIndex → ℝ)
    (k : CyclicIndex) (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hz : ∀ j, 0 ≤ z j)
    (hcompl : ∀ i, 0 < x i → 0 ≤ gainValue cyclicWeight x i (z i - 1 / 2))
    (hk : x k = 0) (hA : 0 < x (cyclicPred k)) (hB : 0 < x (cyclicSucc k)) :
    False := by
  have hbound := cyclicWeight_pred_le_of_pos x z (cyclicPred k) hx (hz (cyclicPred k))
    (hcompl (cyclicPred k) hA)
  rw [cyclicSucc_cyclicPred, hk, cyclicPred_cyclicPred_eq_cyclicSucc] at hbound
  nlinarith [hbound, hB]

/-- **The all-three-active case of the row dichotomy.** If every coordinate
is active, multiplying equation (16) around the cycle gives
`1 ≤ (3/4)^3 ∏(1-x_i) < 1`, a contradiction: the predecessor and successor
hazards range over the same three values in some order, so the hazard
factors cancel from both sides. -/
theorem cyclicWeight_false_of_all_pos (x z : CyclicIndex → ℝ)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1)
    (hcompl : ∀ i, 0 < x i → 0 ≤ gainValue cyclicWeight x i (z i - 1 / 2))
    (hz : ∀ j, 0 ≤ z j) (h0 : 0 < x 0) (h1 : 0 < x 1) (h2 : 0 < x 2) : False := by
  have b0 := cyclicWeight_pred_le_of_pos x z 0 hx (hz 0) (hcompl 0 h0)
  have b1 := cyclicWeight_pred_le_of_pos x z 1 hx (hz 1) (hcompl 1 h1)
  have b2 := cyclicWeight_pred_le_of_pos x z 2 hx (hz 2) (hcompl 2 h2)
  have e0s : cyclicSucc (0 : CyclicIndex) = 1 := by decide
  have e0p : cyclicPred (0 : CyclicIndex) = 2 := by decide
  have e1s : cyclicSucc (1 : CyclicIndex) = 2 := by decide
  have e1p : cyclicPred (1 : CyclicIndex) = 0 := by decide
  have e2s : cyclicSucc (2 : CyclicIndex) = 0 := by decide
  have e2p : cyclicPred (2 : CyclicIndex) = 1 := by decide
  rw [e0s, e0p] at b0
  rw [e1s, e1p] at b1
  rw [e2s, e2p] at b2
  have hp0 := (hx 0).1
  have hp1 := (hx 1).1
  have hp2 := (hx 2).1
  have hle1 : 0 ≤ (3 / 4 : ℝ) * x 1 * (1 - x 2) := by nlinarith [(hx 1).1, (hx 2).2]
  have step1 : x 2 * x 0 ≤ ((3 / 4 : ℝ) * x 1 * (1 - x 2)) * ((3 / 4) * x 2 * (1 - x 0)) :=
    mul_le_mul b0 b1 hp0 hle1
  have hle2 : 0 ≤ ((3 / 4 : ℝ) * x 1 * (1 - x 2)) * ((3 / 4) * x 2 * (1 - x 0)) :=
    le_trans (mul_nonneg hp2 hp0) step1
  have step2 : (x 2 * x 0) * x 1 ≤
      (((3 / 4 : ℝ) * x 1 * (1 - x 2)) * ((3 / 4) * x 2 * (1 - x 0))) *
        ((3 / 4) * x 0 * (1 - x 1)) :=
    mul_le_mul step1 b2 hp1 hle2
  have hX : 0 < x 0 * x 1 * x 2 := by positivity
  nlinarith [step2, hX, (hx 0).2, (hx 1).2, (hx 2).2,
    mul_pos (mul_pos h0 h1) h2]

/-- Every unordered pair of coordinates fails to be simultaneously active:
the two building blocks above, one per pair, routed through whether the
third coordinate is inert or active. -/
theorem cyclicWeight_pairwise_not_both_pos (x z : CyclicIndex → ℝ)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hz : ∀ j, 0 ≤ z j)
    (hcompl : ∀ i, 0 < x i → 0 ≤ gainValue cyclicWeight x i (z i - 1 / 2)) :
    ¬ (0 < x 0 ∧ 0 < x 1) ∧ ¬ (0 < x 1 ∧ 0 < x 2) ∧ ¬ (0 < x 0 ∧ 0 < x 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h0, h1⟩
    rcases eq_or_lt_of_le (hx 2).1 with hk | hk
    · exact cyclicWeight_false_of_zero_between_two_pos x z 2 hx hz hcompl hk.symm h1 h0
    · exact cyclicWeight_false_of_all_pos x z hx hcompl hz h0 h1 hk
  · rintro ⟨h1, h2⟩
    rcases eq_or_lt_of_le (hx 0).1 with hk | hk
    · exact cyclicWeight_false_of_zero_between_two_pos x z 0 hx hz hcompl hk.symm h2 h1
    · exact cyclicWeight_false_of_all_pos x z hx hcompl hz hk h1 h2
  · rintro ⟨h0, h2⟩
    rcases eq_or_lt_of_le (hx 1).1 with hk | hk
    · exact cyclicWeight_false_of_zero_between_two_pos x z 1 hx hz hcompl hk.symm h0 h2
    · exact cyclicWeight_false_of_all_pos x z hx hcompl hz h0 hk h2

/-- **The row dichotomy (goal 2 of the question).** An exactly complementary
row of `cyclicWeight`, together with a nonnegative centered next-phase value
`z` at every coordinate, has at most one positive coordinate: any two active
coordinates coincide. This is the finite-dimensional algebraic core behind
equation (17)'s "every nonzero exact row has the form `h · e_i`", isolated
from the surrounding periodic argument that is not built in this file. -/
theorem atMostOnePositive_of_isExactRowComplementary
    (x z : CyclicIndex → ℝ) (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hz : ∀ j, 0 ≤ z j)
    (hcompl : IsExactRowComplementary x
      (fun i => gainValue cyclicWeight x i (z i - 1 / 2)))
    (i j : CyclicIndex) (hi : 0 < x i) (hj : 0 < x j) : i = j := by
  have hcompl' : ∀ k, 0 < x k → 0 ≤ gainValue cyclicWeight x k (z k - 1 / 2) :=
    fun k hk => (hcompl k).1 hk
  have H := cyclicWeight_pairwise_not_both_pos x z hx hz hcompl'
  by_contra hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact H.1 ⟨hi, hj⟩
      | exact H.1 ⟨hj, hi⟩
      | exact H.2.1 ⟨hi, hj⟩
      | exact H.2.1 ⟨hj, hi⟩
      | exact H.2.2 ⟨hi, hj⟩
      | exact H.2.2 ⟨hj, hi⟩

end GameTheory
