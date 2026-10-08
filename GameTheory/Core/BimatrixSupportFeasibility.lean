import GameTheory.Core.BimatrixSupport
import GameTheory.Core.BimatrixSupportSystem
import GameTheory.Math.Probability.Support

/-! A bimatrix Nash equilibrium supplies feasible fixed-support linear systems
for the two independent payoff tables. The support masks are supplied by the
caller rather than built into the representation. -/
-- This representation bridge owns the extraction of native real atom weights;
-- the linear systems and certificate operations consume ordinary real vectors.

namespace GameTheory.BimatrixSupportSystem

open GameTheory.Math.Probability
open scoped BigOperators

private theorem atomWeights_sum {n : ℕ} (p : PMF (Fin n)) :
    (∑ i, (p i).toReal) = 1 := by
  simpa only [expect_eq_sum, mul_one] using expect_constant p 1

private theorem atomWeight_zero {n : ℕ} (p : PMF (Fin n))
    (S : Fin n → Bool) (hS : ∀ i, S i = true ↔ i ∈ p.support)
    (i : Fin n) (hi : S i = false) : (p i).toReal = 0 := by
  have hn : i ∉ p.support := by
    intro hs
    have ht := (hS i).mpr hs
    simp [hi] at ht
  rw [PMF.mem_support_iff, not_not] at hn
  simp [hn]

private theorem weightedScore_eq_expect {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (p : PMF (Fin n)) (i : Fin m) :
    (∑ j, (A i j : ℝ) * (p j).toReal) = expect p (fun j => (A i j : ℝ)) := by
  rw [expect_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- A general rectangular integer-payoff Nash equilibrium gives both feasible
support systems with the original atom weights and signed expected utilities. -/
theorem nash_realSupportFeasible {m n : ℕ} (A B : Fin m → Fin n → ℤ)
    (p : PMF (Fin m)) (q : PMF (Fin n)) (S : Fin m → Bool) (T : Fin n → Bool)
    (hS : ∀ i, S i = true ↔ i ∈ p.support)
    (hT : ∀ j, T j = true ↔ j ∈ q.support)
    (hnash : IsNash (MatrixGame.form (Fin m) (Fin n)).mixed
      (euPreference (MatrixGame.bimatrixUtility (fun i j => (A i j : ℝ))
        (fun i j => (B i j : ℝ)))) (MatrixGame.mixedProfile p q)) :
    realSupportFeasible A S T (fun j => (q j).toReal)
      (expect (bindPairLaw p (fun _ => q)) (fun x => (A x.1 x.2 : ℝ))) ∧
    realSupportFeasible (fun j i => B i j) T S (fun i => (p i).toReal)
      (expect (bindPairLaw p (fun _ => q)) (fun x => (B x.1 x.2 : ℝ))) := by
  have hdev := (MatrixGame.isNash_bimatrix_iff
    (fun i j => (A i j : ℝ)) (fun i j => (B i j : ℝ)) p q).mp hnash
  constructor
  · refine ⟨fun _ => ENNReal.toReal_nonneg, atomWeights_sum q,
      ?_, ?_, atomWeight_zero q T hT⟩
    · intro i
      rw [weightedScore_eq_expect]
      exact hdev.1 i
    · intro i hi
      rw [weightedScore_eq_expect]
      exact MatrixGame.row_payoff_eq_of_mem_support _ _ p q hnash i ((hS i).mp hi)
  · refine ⟨fun _ => ENNReal.toReal_nonneg, atomWeights_sum p,
      ?_, ?_, atomWeight_zero p S hS⟩
    · intro j
      rw [weightedScore_eq_expect (fun j i => B i j) p j]
      exact hdev.2 j
    · intro j hj
      rw [weightedScore_eq_expect (fun j i => B i j) p j]
      exact MatrixGame.col_payoff_eq_of_mem_support _ _ p q hnash j ((hT j).mp hj)

end GameTheory.BimatrixSupportSystem
