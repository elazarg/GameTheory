import GameTheory.Core.BimatrixSupport
import GameTheory.Core.ConstrainedNash
import GameTheory.Math.Probability.Support
import GameTheoryComplexity.Backend.NashSupportSystem

/-! A canonical mixed Nash equilibrium supplies the two feasible fixed-support
linear systems used to obtain bounded rational witnesses. -/

noncomputable section

namespace GameTheory.Complexity.Backend

open GameTheory.Math.Probability
open scoped BigOperators

/-- The support indicator of an ordinary probability mass function. -/
def nashSupport {q : ℕ} (p : PMF (Fin q)) : Fin q → Bool := by
  classical
  exact fun i => decide (i ∈ p.support)

private theorem atomWeights_sum {q : ℕ} (p : PMF (Fin q)) :
    (∑ i, (p i).toReal) = 1 := by
  simpa only [expect_eq_sum, mul_one] using expect_constant p 1

private theorem atomWeight_zero {q : ℕ} (p : PMF (Fin q)) (i : Fin q)
    (hi : nashSupport p i = false) : (p i).toReal = 0 := by
  classical
  have hn : i ∉ p.support := by simpa [nashSupport] using hi
  rw [PMF.mem_support_iff, not_not] at hn
  simp [hn]

/-- Equilibrium inequalities and support equalities give both nonnegative
linear systems, with the original real atom weights and expected payoffs. -/
theorem nash_realSupportFeasible {q : ℕ} (A : Fin q → Fin q → ℤ)
    (p r : PMF (Fin q))
    (hnash : IsNash (MatrixGame.form (Fin q) (Fin q)).mixed
      (euPreference (MatrixGame.bimatrixUtility (fun i j => (A i j : ℝ))
        (fun i j => (A j i : ℝ)))) (MatrixGame.mixedProfile p r))
    (hrow : 1 ≤ expect (bindPairLaw p (fun _ => r)) (fun x => (A x.1 x.2 : ℝ)))
    (hcol : 1 ≤ expect (bindPairLaw p (fun _ => r)) (fun x => (A x.2 x.1 : ℝ))) :
    realSupportFeasible A (nashSupport p) (nashSupport r) (fun j => (r j).toReal)
      (expect (bindPairLaw p (fun _ => r)) (fun x => (A x.1 x.2 : ℝ))) ∧
    realSupportFeasible A (nashSupport r) (nashSupport p) (fun j => (p j).toReal)
      (expect (bindPairLaw p (fun _ => r)) (fun x => (A x.2 x.1 : ℝ))) := by
  classical
  have hdev := (MatrixGame.isNash_bimatrix_iff
    (fun i j => (A i j : ℝ)) (fun i j => (A j i : ℝ)) p r).mp hnash
  have hscore (s : PMF (Fin q)) (i : Fin q) :
      (∑ j, (A i j : ℝ) * (s j).toReal) = expect s (fun j => (A i j : ℝ)) := by
    rw [expect_eq_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  constructor
  · refine ⟨fun _ => ENNReal.toReal_nonneg, atomWeights_sum r, hrow,
      ?_, ?_, atomWeight_zero r⟩
    · intro i
      rw [hscore]
      exact hdev.1 i
    · intro i hi
      rw [hscore]
      exact MatrixGame.row_payoff_eq_of_mem_support _ _ p r hnash i
        (by simpa [nashSupport] using hi)
  · refine ⟨fun _ => ENNReal.toReal_nonneg, atomWeights_sum p, hcol,
      ?_, ?_, atomWeight_zero p⟩
    · intro i
      rw [hscore]
      exact hdev.2 i
    · intro i hi
      rw [hscore]
      exact MatrixGame.col_payoff_eq_of_mem_support _ _ p r hnash i
        (by simpa [nashSupport] using hi)

end GameTheory.Complexity.Backend
