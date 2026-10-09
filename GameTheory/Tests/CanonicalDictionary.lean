import GameTheory.Math.CanonicalDictionary
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Sorting after an actual feasible pivot changes the leaving-column slot. -/

namespace GameTheory.Tests.CanonicalDictionary

open GameTheory.Math GameTheory.Math.PerturbedDictionary
open GameTheory.Math.FiniteBasisExchange GameTheory.Math.CanonicalDictionary

private def columns : Matrix (Fin 2) (Fin 3) ℚ := !![1, 0, 1; 0, 1, 1]
private def basis : Finset (Fin 3) := {0, 1}
private theorem basis_card : basis.card = 2 := by decide
private def rhs : Fin 2 → ℚ := ![1, 2]
private theorem entering_new : (2 : Fin 3) ∉ basis := by decide

private theorem enumeration : (fun j => basis.orderEmbOfFin basis_card j) =
    (![0, 1] : Fin 2 → Fin 3) := by
  exact (canonical_unique basis_card (f := ![0, 1]) (by decide) (by decide)).symm

private theorem initial_matrix : basisMatrix columns basis basis_card = 1 := by
  ext i j
  simp only [basisMatrix, enumeration]
  fin_cases i <;> fin_cases j <;> norm_num [columns]

private theorem feasible : IsFeasible columns rhs basis basis_card := by
  refine ⟨by rw [initial_matrix]; simp, ?_⟩
  intro i
  rw [initial_matrix]
  refine ⟨0, fun j hj => (Fin.not_lt_zero j hj).elim, ?_⟩
  change (0 : ℚ) < dictionaryCoefficients 1 rhs i 0
  fin_cases i <;> norm_num [rhs]

private theorem leaving : IsLeavingRow (dictionaryCoefficients
    (basisMatrix columns basis basis_card) rhs)
    ((basisMatrix columns basis basis_card)⁻¹.mulVec (fun i => columns i 2)) 0 := by
  rw [initial_matrix]
  refine ⟨by norm_num [columns], ?_⟩
  intro i _
  fin_cases i
  · exact le_rfl
  · apply le_of_lt
    refine ⟨0, fun j hj => (Fin.not_lt_zero j hj).elim, ?_⟩
    norm_num [rhs, columns]

example : exchange basis (basis.orderEmbOfFin basis_card 0) 2 = {1, 2} := by
  change exchange basis ((fun j => basis.orderEmbOfFin basis_card j) 0) 2 = {1, 2}
  rw [enumeration]
  decide

example : IsFeasible columns rhs (exchange basis (basis.orderEmbOfFin basis_card 0) 2)
    ((card_exchange (Finset.orderEmbOfFin_mem basis basis_card 0) entering_new).trans
      basis_card) :=
  exchange_feasible columns rhs basis basis_card feasible 0 2 entering_new leaving

private theorem reverse_slot :
    (exchangePermutation basis basis_card 0 2 entering_new).symm 0 = 1 := by
  apply (exchangePermutation basis basis_card 0 2 entering_new).injective
  simp only [Equiv.apply_symm_apply]
  have h := exchangePermutation_apply basis basis_card 0 2 entering_new 1
  have hsorted : (exchange basis (basis.orderEmbOfFin basis_card 0) 2).orderEmbOfFin
      ((card_exchange (Finset.orderEmbOfFin_mem basis basis_card 0) entering_new).trans
        basis_card) 1 = 2 := by
    have hs0 : basis.orderEmbOfFin basis_card 0 = 0 := congrFun enumeration 0
    have hen := canonical_unique
      ((card_exchange (Finset.orderEmbOfFin_mem basis basis_card 0) entering_new).trans basis_card)
      (f := (![1, 2] : Fin 2 → Fin 3)) (by rw [hs0]; decide) (by decide)
    exact (congrFun hen 1).symm
  rw [hsorted] at h
  generalize hi : (exchangePermutation basis basis_card 0 2 entering_new) 1 = a at h ⊢
  fin_cases a
  · rfl
  · change (2 : Fin 3) = if (1 : Fin 2) = 0 then 2 else basis.orderEmbOfFin basis_card 1 at h
    have hs1 : basis.orderEmbOfFin basis_card 1 = 1 := congrFun enumeration 1
    norm_num [hs1] at h

example : IsLeavingRow (dictionaryCoefficients (basisMatrix columns
    (exchange basis (basis.orderEmbOfFin basis_card 0) 2)
    ((card_exchange (Finset.orderEmbOfFin_mem basis basis_card 0) entering_new).trans
      basis_card)) rhs)
    ((basisMatrix columns (exchange basis (basis.orderEmbOfFin basis_card 0) 2)
    ((card_exchange (Finset.orderEmbOfFin_mem basis basis_card 0) entering_new).trans
      basis_card))⁻¹.mulVec
      (fun i => columns i (basis.orderEmbOfFin basis_card 0))) 1 := by
  have h := exchange_reverse_leavingRow columns rhs basis basis_card feasible 0 2
    entering_new leaving
  rw [reverse_slot] at h
  exact h

example : exchange (exchange basis (basis.orderEmbOfFin basis_card 0) 2) 2
    (basis.orderEmbOfFin basis_card 0) = basis :=
  reverse_exchange (Finset.orderEmbOfFin_mem basis basis_card 0) entering_new

end GameTheory.Tests.CanonicalDictionary
