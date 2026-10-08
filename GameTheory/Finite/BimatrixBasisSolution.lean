import GameTheory.Finite.BimatrixBasis
import GameTheory.Math.BasisCoordinates
import Mathlib.Tactic.Linarith

/-! Rational complementary solutions decoded from feasible bimatrix bases.
Nonbasic variables are zero, while symbolic feasibility ensures nonnegative
constant coordinates. A complementary basis therefore solves the original
complementarity problem; the zero payoff point identifies the all-slack source.
-/

namespace GameTheory.Finite.BimatrixBasis

open scoped BigOperators
open GameTheory.Math GameTheory.Math.CanonicalDictionary
open GameTheory.Math.LinearComplementarity

variable {m n : ℕ} {A B : Fin m → Fin n → ℤ}

/-- Constant coordinates of every variable, extended by zero outside the basis. -/
noncomputable def coordinates (basis : BimatrixBasis A B) : BimatrixVariable m n → ℚ :=
  BasisCoordinates.inverseCoordinates (bimatrixBasisColumns A B) (fun _ => 1)
    basis.basic basis.cardinality

/-- The payoff block of the original rational solution. -/
noncomputable def payoffPoint (basis : BimatrixBasis A B) : Fin m ⊕ Fin n → ℚ :=
  fun i => basis.coordinates (toLex (finSumFinEquiv i, true))

theorem coordinates_nonneg (basis : BimatrixBasis A B) (v : BimatrixVariable m n) :
    0 ≤ basis.coordinates v :=
  BasisCoordinates.inverseCoordinates_nonneg_of_feasible _ _ _ _ basis.feasible v

theorem coordinates_outside (basis : BimatrixBasis A B) (v : BimatrixVariable m n)
    (hv : v ∉ basis.basic) : basis.coordinates v = 0 :=
  BasisCoordinates.inverseCoordinates_outside _ _ _ _ _ hv

/-- Full coordinates satisfy the ambient equation, without a complementary-label premise. -/
theorem coordinates_equation (basis : BimatrixBasis A B) (i : Fin (m + n)) :
    ∑ v, bimatrixBasisColumns A B i v * basis.coordinates v = 1 :=
  BasisCoordinates.inverseCoordinates_equation _ _ _ _ basis.feasible.1 i

/-- The affine complementarity slack is precisely the slack-variable coordinate. -/
theorem slack_eq_coordinate (basis : BimatrixBasis A B) (i : Fin m ⊕ Fin n) :
    slack (fun _ => 1) (bimatrixComplementaryMatrix A B) basis.payoffPoint i =
      basis.coordinates (toLex (finSumFinEquiv i, false)) := by
  have he := basis.coordinates_equation (finSumFinEquiv i)
  rw [← toLex.sum_comp] at he
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, bimatrixBasisColumns,
    ofLex_toLex, Bool.false_eq_true, ↓reduceIte, bimatrixEnteringColumn, Equiv.symm_apply_apply,
    Pi.single_apply] at he
  simp only [Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib] at he
  have hsingle : (∑ j : Fin (m + n), (if finSumFinEquiv i = j then (1 : ℚ) else 0) *
      basis.coordinates (toLex (j, false))) =
      basis.coordinates (toLex (finSumFinEquiv i, false)) := by simp
  rw [hsingle] at he
  have hsum : (∑ j : Fin (m + n), bimatrixComplementaryMatrix A B i
      (finSumFinEquiv.symm j) * basis.coordinates (toLex (j, true))) =
      ∑ j : Fin m ⊕ Fin n, bimatrixComplementaryMatrix A B i j * basis.payoffPoint j := by
    simpa only [payoffPoint, Equiv.symm_apply_apply] using
      (finSumFinEquiv.sum_comp (fun j : Fin (m + n) => bimatrixComplementaryMatrix A B i
        (finSumFinEquiv.symm j) * basis.coordinates (toLex (j, true)))).symm
  rw [hsum] at he
  unfold slack
  linarith

/-- Complementary nonbasic labels give a solution of the original rational problem. -/
theorem payoffPoint_isSolution (basis : BimatrixBasis A B)
    (hc : ComplementaryLabels.IsComplementary basis.nonbasic) :
    IsSolution (fun _ => 1) (bimatrixComplementaryMatrix A B) basis.payoffPoint := by
  rw [isSolution_iff]
  refine ⟨fun i => basis.coordinates_nonneg _, ?_, ?_⟩
  · intro i
    rw [basis.slack_eq_coordinate]
    exact basis.coordinates_nonneg _
  · intro i
    by_cases ht : (finSumFinEquiv i, true) ∈ basis.nonbasic
    · left
      exact basis.coordinates_outside _ ((basis.mem_nonbasic _).mp ht)
    · right
      rw [basis.slack_eq_coordinate]
      exact basis.coordinates_outside _
        ((basis.mem_nonbasic _).mp ((hc (finSumFinEquiv i)).mpr ht))

@[simp] theorem source_payoffPoint (A B : Fin m → Fin n → ℤ) :
    (bimatrixSourceBasis A B).payoffPoint = 0 := by
  funext i
  exact (bimatrixSourceBasis A B).coordinates_outside _
    (((bimatrixSourceBasis A B).mem_nonbasic _).mp
      ((bimatrixSource_nonbasic_mem A B (finSumFinEquiv i, true)).mpr rfl))

/-- No other feasible basis represents the artificial zero payoff point. -/
theorem payoffPoint_eq_zero_iff (basis : BimatrixBasis A B) :
    basis.payoffPoint = 0 ↔ basis = bimatrixSourceBasis A B := by
  constructor
  · intro hz
    have hs : bimatrixSlackVariables m n ⊆ basis.basic := by
      intro v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      by_contra hi
      have hzero := basis.coordinates_outside (toLex (i, false)) hi
      have hone : basis.coordinates (toLex (i, false)) = 1 := by
        have hh := basis.slack_eq_coordinate (finSumFinEquiv.symm i)
        rw [hz] at hh
        simpa [slack] using hh.symm
      exact zero_ne_one (hzero.symm.trans hone)
    apply BimatrixBasis.ext
    exact (Finset.eq_of_subset_of_card_le hs
      (by rw [basis.cardinality, bimatrixSlackVariables_card])).symm
  · rintro rfl
    exact source_payoffPoint A B

/-- Every complementary non-source basis supplies a nonzero rational solution. -/
theorem nonzero_payoffPoint_isSolution (basis : BimatrixBasis A B)
    (hc : ComplementaryLabels.IsComplementary basis.nonbasic)
    (hsource : basis ≠ bimatrixSourceBasis A B) :
    basis.payoffPoint ≠ 0 ∧
      IsSolution (fun _ => 1) (bimatrixComplementaryMatrix A B) basis.payoffPoint :=
  ⟨fun h => hsource (basis.payoffPoint_eq_zero_iff.mp h), basis.payoffPoint_isSolution hc⟩

end GameTheory.Finite.BimatrixBasis
