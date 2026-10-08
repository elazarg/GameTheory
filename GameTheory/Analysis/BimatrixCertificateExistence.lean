import GameTheory.Analysis.Nash
import GameTheory.Finite.BimatrixCertificateCompleteness

/-! Every nonempty finite integer bimatrix game has an exact rational Nash
certificate of polynomial binary width. Analytic Nash existence supplies a
real equilibrium; finite integer linear algebra supplies the bounded certificate. -/

namespace GameTheory

open GameTheory.Finite

/-- Nonempty rectangular integer games admit bounded exact equilibrium certificates. -/
theorem exists_bounded_bimatrixCertificate_of_nonempty {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    (A B : Fin m → Fin n → ℤ) (h : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h)
    (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h) :
    ∃ c : BimatrixCertificate m n, c.Valid A B ∧
      c.FitsWidth (bimatrixCertificateWidth m n h) := by
  let _ : ∀ i, Fintype ((MatrixGame.form (Fin m) (Fin n)).sig.Strategy i) :=
    fun i => Fin.cases (show Fintype (Fin m) from inferInstance)
      (fun j => Fin.cases (show Fintype (Fin n) from inferInstance)
        (fun k => k.elim0) j) i
  let _ : ∀ i, Nonempty ((MatrixGame.form (Fin m) (Fin n)).sig.Strategy i) := by
    intro i
    fin_cases i <;> infer_instance
  let u := MatrixGame.bimatrixUtility
    (fun i j => (A i j : ℝ)) (fun i j => (B i j : ℝ))
  obtain ⟨μ, hμ⟩ := exists_isNash_mixed (F := MatrixGame.form (Fin m) (Fin n)) u
    ((MatrixGame.form (Fin m) (Fin n)).hasIntegrableUtility_of_finiteOutcome u)
  have hη : MatrixGame.mixedProfile (μ 0) (μ 1) = μ := by
    funext i
    fin_cases i <;> rfl
  exact exists_bounded_bimatrixCertificate A B h hA hB (μ 0) (μ 1)
    (by rw [hη]; exact hμ)

end GameTheory
