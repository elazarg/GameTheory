import GameTheory.Core.BimatrixSupportFeasibility
import GameTheory.Finite.BimatrixCertificateCorrectness
import GameTheory.Math.BoundedLinearCertificate
import Mathlib.Data.Int.NatAbs

/-! Every real Nash equilibrium of a finite integer bimatrix game admits an
exact rational certificate with polynomial binary width. The support systems
are independent, and signed payoffs require no normalization or thresholds. -/

namespace GameTheory

open scoped BigOperators
open GameTheory.Finite BimatrixSupportSystem

/-- Uniform field width for rectangular bimatrix certificates. -/
def bimatrixCertificateWidth (m n h : ℕ) : ℕ :=
  (m + n + 2) * (3 * (m + n) + 2 * h + 6) + 1

private theorem supportWidth_le (m n h : ℕ) :
    Math.linearCertificateWidth (n + 2 + m) (1 + 2 * m + n) h ≤
      bimatrixCertificateWidth m n h := by
  dsimp [Math.linearCertificateWidth, bimatrixCertificateWidth]
  have hk : n + 2 + m = m + n + 2 := by omega
  rw [hk]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _

private theorem utilityNumerator_bound {m n W : ℕ} (N : SupportVariable m n → ℕ)
    (hN : ∀ j, N j < 2 ^ W) : (utilityNumerator N).natAbs < 2 ^ W := by
  unfold utilityNumerator
  by_cases h : N (.inr (.inr (.inl PUnit.unit))) ≤ N (.inr (.inl PUnit.unit))
  · rw [Int.natAbs_natCast_sub_natCast_of_ge h]
    exact (Nat.sub_le _ _).trans_lt (hN _)
  · rw [Int.natAbs_natCast_sub_natCast_of_le (by omega)]
    exact (Nat.sub_le _ _).trans_lt (hN _)

/-- A real equilibrium supplies an exact certificate of polynomial binary width. -/
theorem exists_bounded_bimatrixCertificate {m n : ℕ}
    (A B : Fin m → Fin n → ℤ) (h : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h)
    (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h)
    (p : PMF (Fin m)) (q : PMF (Fin n))
    (hnash : IsNash (MatrixGame.form (Fin m) (Fin n)).mixed
      (euPreference (MatrixGame.bimatrixUtility (fun i j => (A i j : ℝ))
        (fun i j => (B i j : ℝ)))) (MatrixGame.mixedProfile p q)) :
    ∃ c : BimatrixCertificate m n, c.Valid A B ∧
      c.FitsWidth (bimatrixCertificateWidth m n h) := by
  classical
  let S : Fin m → Bool := fun i => decide (i ∈ p.support)
  let T : Fin n → Bool := fun j => decide (j ∈ q.support)
  obtain ⟨hfrow, hfcol⟩ := nash_realSupportFeasible A B p q S T
    (fun _ => by simp [S]) (fun _ => by simp [T]) hnash
  have hpos : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by decide)
  obtain ⟨Dq, Nq, hDq, hbDq, hbNq, heqQ⟩ :=
    Math.exists_bounded_nonnegative_linear_solution
      (supportMatrix A S T) supportRhs h
      (supportMatrix_bound A S T hpos hA) (supportRhs_bound hpos)
      (supportVector A _ _) (supportVector_nonneg A S T _ _ hfrow)
      (supportVector_solution A S T _ _ hfrow)
  obtain ⟨Dp, Np, hDp, hbDp, hbNp, heqP⟩ :=
    Math.exists_bounded_nonnegative_linear_solution
      (supportMatrix (fun j i => B i j) T S) supportRhs h
      (supportMatrix_bound _ T S hpos (fun j i => hB i j)) (supportRhs_bound hpos)
      (supportVector _ _ _) (supportVector_nonneg _ T S _ _ hfcol)
      (supportVector_solution _ T S _ _ hfcol)
  have hWq : Math.linearCertificateWidth
      (Fintype.card (SupportVariable m n)) (Fintype.card (SupportRow m n)) h ≤
      bimatrixCertificateWidth m n h := by
    rw [supportVariable_card, supportRow_card]
    exact supportWidth_le m n h
  have hWp : Math.linearCertificateWidth
      (Fintype.card (SupportVariable n m)) (Fintype.card (SupportRow n m)) h ≤
      bimatrixCertificateWidth m n h := by
    rw [supportVariable_card, supportRow_card]
    simpa [bimatrixCertificateWidth, Nat.add_comm] using supportWidth_le n m h
  have hpowq := pow_le_pow_right' (by decide : 1 ≤ 2) hWq
  have hpowp := pow_le_pow_right' (by decide : 1 ≤ 2) hWp
  have hNq : ∀ j, Nq j < 2 ^ bimatrixCertificateWidth m n h :=
    fun j => (hbNq j).trans_le hpowq
  have hNp : ∀ j, Np j < 2 ^ bimatrixCertificateWidth m n h :=
    fun j => (hbNp j).trans_le hpowp
  obtain ⟨hsQ, hiQ, heQ, hzQ⟩ := natural_solution_constraints A S T Nq Dq heqQ
  obtain ⟨hsP, hiP, heP, hzP⟩ := natural_solution_constraints
    (fun j i => B i j) T S Np Dp heqP
  let c : BimatrixCertificate m n :=
    ⟨fun i => Np (.inl i), fun j => Nq (.inl j), Dp, Dq,
      utilityNumerator Nq, utilityNumerator Np⟩
  refine ⟨c, ?_, hbDp.trans_le hpowp, hbDq.trans_le hpowq,
    fun i => hNp (.inl i), fun j => hNq (.inl j),
    utilityNumerator_bound Nq hNq, utilityNumerator_bound Np hNp⟩
  refine ⟨hDp, hDq, hsP, hsQ, ?_, ?_⟩
  · intro i
    refine ⟨hiQ i, ?_⟩
    intro hi
    apply heQ i
    by_cases hs : S i = true
    · exact hs
    · have hz := hzP i (Bool.eq_false_iff.mpr hs)
      exact False.elim ((Nat.ne_of_gt hi) hz)
  · intro j
    refine ⟨hiP j, ?_⟩
    intro hj
    apply heP j
    by_cases ht : T j = true
    · exact ht
    · have hz := hzQ j (Bool.eq_false_iff.mpr ht)
      exact False.elim ((Nat.ne_of_gt hj) hz)

/-- Real equilibrium existence is equivalent to a bounded exact rational certificate. -/
theorem bimatrix_nash_exists_iff_bounded_certificate {m n : ℕ}
    (A B : Fin m → Fin n → ℤ) (h : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h)
    (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h) :
    (∃ (p : PMF (Fin m)) (q : PMF (Fin n)),
      IsNash (MatrixGame.form (Fin m) (Fin n)).mixed
        (euPreference (MatrixGame.bimatrixUtility (fun i j => (A i j : ℝ))
          (fun i j => (B i j : ℝ)))) (MatrixGame.mixedProfile p q)) ↔
      ∃ c : BimatrixCertificate m n, c.Valid A B ∧
        c.FitsWidth (bimatrixCertificateWidth m n h) := by
  constructor
  · rintro ⟨p, q, hnash⟩
    exact exists_bounded_bimatrixCertificate A B h hA hB p q hnash
  · rintro ⟨c, hc, _⟩
    exact c.hasNash_of_valid A B hc

end GameTheory
