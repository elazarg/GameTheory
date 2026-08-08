/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Tactic

/-!
# Sharp exposure bounds on a finite permutation system

Let `next` be a permutation of a finite nonempty coordinate set and `prev`
its inverse. For a row `x : ι → ℝ`, define the directed exposure

`exposure x i = x (next i) * (1 - x (prev i))`.

When every coordinate of `x` lies in `[0,1]`, some exposure is at most
`1 / 4`. The bound is sharp, and the constant row `x = 1 / 2` is the unique
row for which every exposure is at least `1 / 4`.

The result is componentwise: no single-orbit hypothesis and no restriction on
the permutation's cycle lengths is needed.
-/

noncomputable section

namespace Math.CyclicExposure

/-- Mutually inverse successor and predecessor maps on a coordinate type. -/
structure Neighbours (ι : Type) where
  next : ι → ι
  prev : ι → ι
  prev_next : Function.LeftInverse prev next
  next_prev : Function.RightInverse prev next

namespace Neighbours

variable {ι : Type} (C : Neighbours ι)

/-- The successor map viewed as a permutation. -/
def nextEquiv : ι ≃ ι where
  toFun := C.next
  invFun := C.prev
  left_inv := C.prev_next
  right_inv := C.next_prev

/-- Directed exposure of coordinate `i`. -/
def exposure (x : ι → ℝ) (i : ι) : ℝ :=
  x (C.next i) * (1 - x (C.prev i))

/-- The elementary quadratic bound behind the sharp constant. -/
theorem selfExposure_le_quarter (z : ℝ) :
    z * (1 - z) ≤ (1 / 4 : ℝ) := by
  nlinarith [sq_nonneg (z - 1 / 2)]

/-- A maximum coordinate gives an exposure of at most one quarter one step
ahead. This is the local form of the finite theorem. -/
theorem exposure_successor_argmax_le_quarter
    (x : ι → ℝ) (hunit : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (k : ι) (hmax : ∀ j, x j ≤ x k) :
    C.exposure x (C.next k) ≤ (1 / 4 : ℝ) := by
  have hprev : C.prev (C.next k) = k := C.prev_next k
  have hnonneg : 0 ≤ 1 - x k := by linarith [(hunit k).2]
  calc
    C.exposure x (C.next k) =
        x (C.next (C.next k)) * (1 - x k) := by
          simp only [exposure, hprev]
    _ ≤ x k * (1 - x k) := by
          exact mul_le_mul_of_nonneg_right
            (hmax (C.next (C.next k))) hnonneg
    _ ≤ (1 / 4 : ℝ) := selfExposure_le_quarter (x k)

/-- **Sharp finite exposure bound.** Some directed exposure of every finite
probability row is at most one quarter. -/
theorem exists_exposure_le_quarter [Finite ι] [Nonempty ι]
    (x : ι → ℝ) (hunit : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ i, C.exposure x i ≤ (1 / 4 : ℝ) := by
  classical
  obtain ⟨k, hk⟩ := Finite.exists_max x
  exact ⟨C.next k,
    C.exposure_successor_argmax_le_quarter x hunit k hk⟩

/-- The fair row attains exposure one quarter at every coordinate. -/
@[simp] theorem exposure_fair (i : ι) :
    C.exposure (fun _ => (1 / 2 : ℝ)) i = (1 / 4 : ℝ) := by
  simp [exposure]
  norm_num

/-- If every exposure is at least one quarter, the row is fair.

The exposure inequalities make `x` nondecreasing under `next²`. Since
`next²` is a finite permutation, its nonnegative coordinate increments sum
to zero and therefore vanish. Every exposure then reduces to the sharp scalar
product `x i * (1 - x i)`. -/
theorem eq_fair_of_forall_quarter_le_exposure [Finite ι] [Nonempty ι]
    (x : ι → ℝ) (hunit : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hall : ∀ i, (1 / 4 : ℝ) ≤ C.exposure x i) :
    x = fun _ => (1 / 2 : ℝ) := by
  classical
  obtain ⟨k, hkmax⟩ := Finite.exists_max x
  have hnonneg : 0 ≤ 1 - x k := by linarith [(hunit k).2]
  have htop : C.exposure x (C.next k) ≤ x k * (1 - x k) := by
    calc
      C.exposure x (C.next k) =
          x (C.next (C.next k)) * (1 - x k) := by
            rw [exposure, C.prev_next k]
      _ ≤ x k * (1 - x k) := by
            exact mul_le_mul_of_nonneg_right
              (hkmax (C.next (C.next k))) hnonneg
  have hkquarter : (1 / 4 : ℝ) ≤ x k * (1 - x k) :=
    (hall (C.next k)).trans htop
  have hkquad : x k * (1 - x k) ≤ (1 / 4 : ℝ) :=
    selfExposure_le_quarter (x k)
  have hkhalf : x k = (1 / 2 : ℝ) := by
    nlinarith [sq_nonneg (x k - 1 / 2)]
  have hlehalf : ∀ i, x i ≤ (1 / 2 : ℝ) := by
    intro i
    linarith [hkmax i]
  have hstep : ∀ i, x i ≤ x (C.next (C.next i)) := by
    intro i
    by_contra hnot
    have hlt : x (C.next (C.next i)) < x i := lt_of_not_ge hnot
    have hpos : 0 < 1 - x i := by linarith [hlehalf i]
    have hstrict :
        x (C.next (C.next i)) * (1 - x i) < x i * (1 - x i) :=
      mul_lt_mul_of_pos_right hlt hpos
    have hquad : x i * (1 - x i) ≤ (1 / 4 : ℝ) :=
      selfExposure_le_quarter (x i)
    have hbound : (1 / 4 : ℝ) ≤
        x (C.next (C.next i)) * (1 - x i) := by
      have h := hall (C.next i)
      rw [exposure, C.prev_next i] at h
      exact h
    linarith
  letI : Fintype ι := Fintype.ofFinite ι
  have hsumperm : (∑ i, x (C.next (C.next i))) = ∑ i, x i := by
    simpa [nextEquiv] using (C.nextEquiv.trans C.nextEquiv).sum_comp x
  have hsumzero : ∑ i, (x (C.next (C.next i)) - x i) = 0 := by
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hsumperm
  have hstepEq : ∀ i, x i = x (C.next (C.next i)) := by
    intro i
    have hzeros : (fun j => x (C.next (C.next j)) - x j) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg
        (fun j => sub_nonneg.mpr (hstep j))).mp hsumzero
    have hzero : x (C.next (C.next i)) - x i = 0 :=
      congrFun hzeros i
    exact (sub_eq_zero.mp hzero).symm
  funext i
  have hbound : (1 / 4 : ℝ) ≤ x i * (1 - x i) := by
    have h := hall (C.next i)
    rw [exposure, C.prev_next i, ← hstepEq i] at h
    exact h
  have hquad : x i * (1 - x i) ≤ (1 / 4 : ℝ) :=
    selfExposure_le_quarter (x i)
  nlinarith [sq_nonneg (x i - 1 / 2)]

/-- **Unique optimizer.** Every exposure is at least one quarter exactly for
the fair row. Combined with `exists_exposure_le_quarter`, this says that the
fair row uniquely maximizes the minimum exposure, with value `1 / 4`. -/
theorem forall_quarter_le_exposure_iff_eq_fair [Finite ι] [Nonempty ι]
    (x : ι → ℝ) (hunit : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    (∀ i, (1 / 4 : ℝ) ≤ C.exposure x i) ↔
      x = fun _ => (1 / 2 : ℝ) := by
  constructor
  · exact C.eq_fair_of_forall_quarter_le_exposure x hunit
  · intro h
    subst x
    intro i
    rw [C.exposure_fair i]

end Neighbours

end Math.CyclicExposure
