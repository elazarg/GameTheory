import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Int.NatAbs
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-! Fixed-support best-response constraints as an integer linear system with
nonnegative variables. This is a linear view of weights and payoffs. -/

namespace GameTheory.Complexity.Backend

open scoped BigOperators

/-- Simplex, payoff, support tightness, forbidden weights, and threshold rows. -/
abbrev SupportRow (q : ℕ) := Unit ⊕ (Fin q ⊕ (Fin q ⊕ (Fin q ⊕ Unit)))

/-- Weights, payoff, pure-action slacks, and the payoff-one threshold slack. -/
abbrev SupportVariable (q : ℕ) := Fin q ⊕ (Unit ⊕ (Fin q ⊕ Unit))

/-- Integer coefficients of the fixed-support best-response system. -/
def supportMatrix {q : ℕ} (A : Fin q → Fin q → ℤ) (S T : Fin q → Bool) :
    SupportRow q → SupportVariable q → ℤ
  | .inl _, .inl _ => 1
  | .inr (.inl i), .inl j => A i j
  | .inr (.inl _), .inr (.inl _) => -1
  | .inr (.inl i), .inr (.inr (.inl j)) => if i = j then 1 else 0
  | .inr (.inr (.inl i)), .inr (.inr (.inl j)) =>
      if i = j ∧ S i = true then 1 else 0
  | .inr (.inr (.inr (.inl i))), .inl j =>
      if i = j ∧ T i = false then 1 else 0
  | .inr (.inr (.inr (.inr _))), .inr (.inl _) => 1
  | .inr (.inr (.inr (.inr _))), .inr (.inr (.inr _)) => -1
  | _, _ => 0

/-- The simplex and threshold rows have right-hand side one; all others zero. -/
def supportRhs {q : ℕ} : SupportRow q → ℤ
  | .inl _ => 1
  | .inr (.inr (.inr (.inr _))) => 1
  | _ => 0

/-- Feasible weights and a payoff satisfying the chosen tight and allowed sets. -/
def realSupportFeasible {q : ℕ} (A : Fin q → Fin q → ℤ) (S T : Fin q → Bool)
    (w : Fin q → ℝ) (u : ℝ) : Prop :=
  (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧ 1 ≤ u ∧
    (∀ i, (∑ j, (A i j : ℝ) * w j) ≤ u) ∧
    (∀ i, S i = true → (∑ j, (A i j : ℝ) * w j) = u) ∧
    (∀ j, T j = false → w j = 0)

/-- The feasible weights augmented with their pure-action and threshold slacks. -/
def supportVector {q : ℕ} (A : Fin q → Fin q → ℤ) (w : Fin q → ℝ)
    (u : ℝ) : SupportVariable q → ℝ
  | .inl j => w j
  | .inr (.inl _) => u
  | .inr (.inr (.inl i)) => u - ∑ j, (A i j : ℝ) * w j
  | .inr (.inr (.inr _)) => u - 1

theorem supportRow_card (q : ℕ) : Fintype.card (SupportRow q) = 3 * q + 2 := by
  simp [Fintype.card_sum]
  omega

theorem supportVariable_card (q : ℕ) : Fintype.card (SupportVariable q) = 2 * q + 2 := by
  simp [Fintype.card_sum]
  omega

theorem supportVector_nonneg {q : ℕ} (A : Fin q → Fin q → ℤ)
    (S T : Fin q → Bool) (w : Fin q → ℝ) (u : ℝ)
    (h : realSupportFeasible A S T w u) : ∀ j, 0 ≤ supportVector A w u j := by
  rcases h with ⟨hw, _, hu, hscore, _, _⟩
  rintro (j | _ | i | _)
  · exact hw j
  · exact le_trans (by norm_num) hu
  · exact sub_nonneg.mpr (hscore i)
  · exact sub_nonneg.mpr hu

theorem supportVector_solution {q : ℕ} (A : Fin q → Fin q → ℤ)
    (S T : Fin q → Bool) (w : Fin q → ℝ) (u : ℝ)
    (h : realSupportFeasible A S T w u) (r : SupportRow q) :
    (∑ j, (supportMatrix A S T r j : ℝ) * supportVector A w u j) =
      (supportRhs r : ℝ) := by
  rcases h with ⟨_, hw, _, _, htight, hzero⟩
  rcases r with _ | i | i | j | _
  · simpa [supportMatrix, supportVector, supportRhs, Fintype.sum_sum_type] using hw
  · simp [supportMatrix, supportVector, supportRhs, Fintype.sum_sum_type]
    ring
  · by_cases hi : S i = true
    · simp [supportMatrix, supportVector, supportRhs, Fintype.sum_sum_type, hi, htight i hi]
    · simp [supportMatrix, supportVector, supportRhs, Fintype.sum_sum_type, hi]
  · by_cases hj : T j = false
    · simp [supportMatrix, supportVector, supportRhs, Fintype.sum_sum_type, hj, hzero j hj]
    · simp [supportMatrix, supportVector, supportRhs, Fintype.sum_sum_type, hj]
  · simp [supportMatrix, supportVector, supportRhs, Fintype.sum_sum_type]

theorem supportMatrix_bound {q H : ℕ} (A : Fin q → Fin q → ℤ)
    (S T : Fin q → Bool) (hH : 1 ≤ H) (hA : ∀ i j, (A i j).natAbs ≤ H)
    (r : SupportRow q) (c : SupportVariable q) :
    (supportMatrix A S T r c).natAbs ≤ H := by
  rcases r with _ | i | i | i | _ <;> rcases c with j | _ | j | _ <;>
    simp only [supportMatrix] <;> (try split_ifs) <;> simp_all

theorem supportRhs_bound {q H : ℕ} (hH : 1 ≤ H) (r : SupportRow q) :
    (supportRhs r).natAbs ≤ H := by
  rcases r with _ | _ | _ | _ | _ <;> simp [supportRhs, hH]

/-- Clearing a positive denominator of a nonnegative solution recovers the
simplex, payoff threshold, and fixed-support integer best-response constraints. -/
theorem natural_solution_constraints {q : ℕ} (A : Fin q → Fin q → ℤ)
    (S T : Fin q → Bool) (N : SupportVariable q → ℕ) (D : ℕ)
    (h : ∀ r, ∑ j, supportMatrix A S T r j * (N j : ℤ) = (D : ℤ) * supportRhs r) :
    (∑ j, N (.inl j)) = D ∧ D ≤ N (.inr (.inl PUnit.unit)) ∧
      (∀ i, (∑ j, A i j * (N (.inl j) : ℤ)) ≤ (N (.inr (.inl PUnit.unit)) : ℤ)) ∧
      (∀ i, S i = true →
        (∑ j, A i j * (N (.inl j) : ℤ)) = (N (.inr (.inl PUnit.unit)) : ℤ)) ∧
      (∀ j, T j = false → N (.inl j) = 0) := by
  have hsum := h (.inl PUnit.unit)
  simp only [Fintype.sum_sum_type, supportMatrix, supportRhs, one_mul, zero_mul,
    Finset.sum_const_zero, add_zero, mul_one] at hsum
  have hthreshold := h (.inr (.inr (.inr (.inr PUnit.unit))))
  simp [supportMatrix, supportRhs, Fintype.sum_sum_type] at hthreshold
  have hpayoff (i : Fin q) := h (.inr (.inl i))
  have hpayoff' (i : Fin q) : (∑ j, A i j * (N (.inl j) : ℤ)) -
      N (.inr (.inl PUnit.unit)) + N (.inr (.inr (.inl i))) = 0 := by
    have hi := hpayoff i
    simpa [supportMatrix, supportRhs, Fintype.sum_sum_type, sub_eq_add_neg, add_assoc] using hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hsum
  · omega
  · intro i
    have hi := hpayoff' i
    have hn := Int.natCast_nonneg (N (.inr (.inr (.inl i))))
    omega
  · intro i hi
    have htight := h (.inr (.inr (.inl i)))
    simp [supportMatrix, supportRhs, Fintype.sum_sum_type, hi] at htight
    have hp := hpayoff' i
    omega
  · intro j hj
    have hzero := h (.inr (.inr (.inr (.inl j))))
    simpa [supportMatrix, supportRhs, Fintype.sum_sum_type, hj] using hzero

end GameTheory.Complexity.Backend
