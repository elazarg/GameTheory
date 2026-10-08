import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Int.NatAbs
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

/-! Fixed-support best-response constraints for a rectangular signed payoff
table. Splitting the utility into its positive and negative parts expresses
the constraints as an integer linear system with nonnegative variables. -/

namespace GameTheory.BimatrixSupportSystem

open scoped BigOperators

/-- Simplex, payoff, support tightness, and forbidden-weight rows. -/
abbrev SupportRow (m n : ℕ) := Unit ⊕ (Fin m ⊕ (Fin m ⊕ Fin n))

/-- Weights, positive utility, negative utility, and pure-action slacks. -/
abbrev SupportVariable (m n : ℕ) := Fin n ⊕ (Unit ⊕ (Unit ⊕ Fin m))

/-- Integer coefficients of the fixed-support best-response system. -/
def supportMatrix {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (S : Fin m → Bool) (T : Fin n → Bool) :
    SupportRow m n → SupportVariable m n → ℤ
  | .inl _, .inl _ => 1
  | .inr (.inl i), .inl j => A i j
  | .inr (.inl _), .inr (.inl _) => -1
  | .inr (.inl _), .inr (.inr (.inl _)) => 1
  | .inr (.inl i), .inr (.inr (.inr j)) => if i = j then 1 else 0
  | .inr (.inr (.inl i)), .inr (.inr (.inr j)) =>
      if i = j ∧ S i = true then 1 else 0
  | .inr (.inr (.inr i)), .inl j => if i = j ∧ T i = false then 1 else 0
  | _, _ => 0

/-- Only the simplex row has a nonzero right-hand side. -/
def supportRhs {m n : ℕ} : SupportRow m n → ℤ
  | .inl _ => 1
  | _ => 0

/-- Feasible weights and a signed utility satisfying the chosen tight and
allowed sets. No sign or threshold restriction is imposed on utility. -/
def realSupportFeasible {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (S : Fin m → Bool) (T : Fin n → Bool) (w : Fin n → ℝ) (u : ℝ) : Prop :=
  (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
    (∀ i, (∑ j, (A i j : ℝ) * w j) ≤ u) ∧
    (∀ i, S i = true → (∑ j, (A i j : ℝ) * w j) = u) ∧
    (∀ j, T j = false → w j = 0)

/-- A feasible vector augmented by signed-utility parts and payoff slacks. -/
noncomputable def supportVector {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (w : Fin n → ℝ) (u : ℝ) : SupportVariable m n → ℝ
  | .inl j => w j
  | .inr (.inl _) => max u 0
  | .inr (.inr (.inl _)) => max (-u) 0
  | .inr (.inr (.inr i)) => u - ∑ j, (A i j : ℝ) * w j

/-- Recover signed utility from its two nonnegative numerator coordinates. -/
def utilityNumerator {m n : ℕ} (N : SupportVariable m n → ℕ) : ℤ :=
  (N (.inr (.inl PUnit.unit)) : ℤ) - N (.inr (.inr (.inl PUnit.unit)))

theorem supportRow_card (m n : ℕ) : Fintype.card (SupportRow m n) = 1 + 2 * m + n := by
  simp [Fintype.card_sum]
  omega

theorem supportVariable_card (m n : ℕ) :
    Fintype.card (SupportVariable m n) = n + 2 + m := by
  simp [Fintype.card_sum]
  omega

theorem utility_parts (u : ℝ) : max u 0 - max (-u) 0 = u := by
  by_cases hu : 0 ≤ u
  · rw [max_eq_left hu, max_eq_right (neg_nonpos.mpr hu)]
    ring
  · have hu' : u ≤ 0 := le_of_not_ge hu
    rw [max_eq_right hu', max_eq_left (neg_nonneg.mpr hu')]
    ring

theorem supportVector_nonneg {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (S : Fin m → Bool) (T : Fin n → Bool) (w : Fin n → ℝ) (u : ℝ)
    (h : realSupportFeasible A S T w u) : ∀ j, 0 ≤ supportVector A w u j := by
  rcases h with ⟨hw, _, hscore, _, _⟩
  rintro (j | _ | _ | i)
  · exact hw j
  · exact le_max_right _ _
  · exact le_max_right _ _
  · exact sub_nonneg.mpr (hscore i)

theorem supportVector_solution {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (S : Fin m → Bool) (T : Fin n → Bool) (w : Fin n → ℝ) (u : ℝ)
    (h : realSupportFeasible A S T w u) (r : SupportRow m n) :
    (∑ j, (supportMatrix A S T r j : ℝ) * supportVector A w u j) =
      (supportRhs r : ℝ) := by
  rcases h with ⟨_, hw, _, htight, hzero⟩
  rcases r with _ | i | i | j
  · simpa [supportMatrix, supportVector, supportRhs, Fintype.sum_sum_type] using hw
  · simp [supportMatrix, supportVector, supportRhs, Fintype.sum_sum_type]
    have hu := utility_parts u
    linarith
  · by_cases hi : S i = true
    · simp [supportMatrix, supportVector, supportRhs, Fintype.sum_sum_type, hi, htight i hi]
    · simp [supportMatrix, supportVector, supportRhs, Fintype.sum_sum_type, hi]
  · by_cases hj : T j = false
    · simp [supportMatrix, supportVector, supportRhs, Fintype.sum_sum_type, hj, hzero j hj]
    · simp [supportMatrix, supportVector, supportRhs, Fintype.sum_sum_type, hj]

theorem supportMatrix_bound {m n H : ℕ} (A : Fin m → Fin n → ℤ)
    (S : Fin m → Bool) (T : Fin n → Bool) (hH : 1 ≤ H)
    (hA : ∀ i j, (A i j).natAbs ≤ H) (r : SupportRow m n)
    (c : SupportVariable m n) : (supportMatrix A S T r c).natAbs ≤ H := by
  rcases r with _ | i | i | i <;> rcases c with j | _ | _ | j <;>
    simp only [supportMatrix] <;> (try split_ifs) <;> simp_all

theorem supportRhs_bound {m n H : ℕ} (hH : 1 ≤ H) (r : SupportRow m n) :
    (supportRhs r).natAbs ≤ H := by
  rcases r with _ | _ | _ | _ <;> simp [supportRhs, hH]

/-- Clearing a denominator recovers the simplex and signed fixed-support
best-response constraints. The signed utility is a difference of naturals. -/
theorem natural_solution_constraints {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (S : Fin m → Bool) (T : Fin n → Bool) (N : SupportVariable m n → ℕ) (D : ℕ)
    (h : ∀ r, ∑ j, supportMatrix A S T r j * (N j : ℤ) =
      (D : ℤ) * supportRhs r) :
    (∑ j, N (.inl j)) = D ∧
      (∀ i, (∑ j, A i j * (N (.inl j) : ℤ)) ≤ utilityNumerator N) ∧
      (∀ i, S i = true →
        (∑ j, A i j * (N (.inl j) : ℤ)) = utilityNumerator N) ∧
      (∀ j, T j = false → N (.inl j) = 0) := by
  have hsum := h (.inl PUnit.unit)
  simp only [Fintype.sum_sum_type, supportMatrix, supportRhs, one_mul, zero_mul,
    Finset.sum_const_zero, add_zero, mul_one] at hsum
  have hpayoff (i : Fin m) : (∑ j, A i j * (N (.inl j) : ℤ)) -
      utilityNumerator N + N (.inr (.inr (.inr i))) = 0 := by
    have hi := h (.inr (.inl i))
    simp [supportMatrix, supportRhs, Fintype.sum_sum_type] at hi
    dsimp [utilityNumerator]
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast hsum
  · intro i
    have hi := hpayoff i
    have hn := Int.natCast_nonneg (N (.inr (.inr (.inr i))))
    omega
  · intro i hi
    have htight := h (.inr (.inr (.inl i)))
    simp [supportMatrix, supportRhs, Fintype.sum_sum_type, hi] at htight
    have hp := hpayoff i
    omega
  · intro j hj
    have hzero := h (.inr (.inr (.inr j)))
    simpa [supportMatrix, supportRhs, Fintype.sum_sum_type, hj] using hzero

end GameTheory.BimatrixSupportSystem
