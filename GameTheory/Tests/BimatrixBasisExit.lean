import GameTheory.Finite.BimatrixBasisExit
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! Fully tied positive games admit exits for both slack and payoff variables. -/

namespace GameTheory.Tests.BimatrixBasisExit

open GameTheory.Finite GameTheory.Math GameTheory.Math.CanonicalDictionary

private def tied : Fin 1 → Fin 2 → ℤ := fun _ _ => 1

example (v : BimatrixVariable 1 2) : ∃ i, 0 < bimatrixBasisColumns tied tied i v :=
  bimatrixBasisColumns_positive tied tied (by decide) (by decide)
    (by intro _ _; norm_num [tied]) (by intro _ _; norm_num [tied]) v

-- Exit existence applies to every feasible basis, beyond the artificial source.
example (basis : BimatrixBasis tied tied) (v : BimatrixVariable 1 2) :
    ∃! l, IsLeavingRow (PerturbedDictionary.dictionaryCoefficients
      (basisMatrix (bimatrixBasisColumns tied tied) basis.basic basis.cardinality) (fun _ => 1))
      ((basisMatrix (bimatrixBasisColumns tied tied) basis.basic basis.cardinality)⁻¹.mulVec
        (fun i => bimatrixBasisColumns tied tied i v)) l :=
  basis.exists_unique_leavingRow (by decide) (by decide)
    (by intro _ _; norm_num [tied]) (by intro _ _; norm_num [tied]) v

-- A zero-payoff variable has no positive coordinate; positivity is substantive.
example : ¬ ∃ i, 0 < bimatrixBasisColumns (fun _ : Fin 1 => fun _ : Fin 1 => 0)
    (fun _ _ => 0) i (toLex ((0 : Fin 2), true)) := by
  rintro ⟨i, hi⟩
  simp only [bimatrixBasisColumns, ofLex_toLex, ↓reduceIte, bimatrixEnteringColumn] at hi
  unfold bimatrixComplementaryMatrix at hi
  cases hi' : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm i <;>
    cases hzero : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 0 <;>
    simp [hi', hzero] at hi

end GameTheory.Tests.BimatrixBasisExit
