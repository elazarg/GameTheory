import GameTheory.Math.FiniteBasisExchange
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! Canonical basis labels survive exchanges that reorder the columns. -/

namespace GameTheory.Tests.FiniteBasisExchange

open GameTheory.Math.FiniteBasisExchange

private def basis : Finset ℕ := {1, 3, 5}
private theorem basis_card : basis.card = 3 := by decide

example : exchange basis 3 0 = {0, 1, 5} := by decide

example : (exchange basis 3 0).card = 3 :=
  (card_exchange (by decide : 3 ∈ basis) (by decide : 0 ∉ basis)).trans basis_card

example : exchange (exchange basis 3 0) 0 3 = basis :=
  reverse_exchange (by decide : 3 ∈ basis) (by decide : 0 ∉ basis)

example : 3 ∉ exchange basis 3 0 :=
  leaving_not_mem (by decide : 3 ∈ basis) (by decide : 0 ∉ basis)

example : 0 ∈ exchange basis 3 0 := entering_mem _ _ _

-- Column insertion order cannot change the canonical enumeration.
example : ({5, 1, 3} : Finset ℕ).orderEmbOfFin (by decide :
    ({5, 1, 3} : Finset ℕ).card = 3) = basis.orderEmbOfFin basis_card :=
  (canonical_eq_iff _ _).mpr (by decide)

example : exchange basis 3 0 ≠ exchange basis 3 2 := by
  intro h
  have := (exchange_eq_iff (by decide : 0 ∉ basis) (by decide : 2 ∉ basis)).mp h
  exact (by decide : (0 : ℕ) ≠ 2) this

-- Sorting the replacement of the middle column is an actual permutation.
example (i : Fin 3) :
    (exchange basis (basis.orderEmbOfFin basis_card 1) 0).orderEmbOfFin
      ((card_exchange (Finset.orderEmbOfFin_mem basis basis_card 1)
        (by decide : 0 ∉ basis)).trans basis_card) i =
    exchangeEnumeration basis basis_card 1 0
      (exchangePermutation basis basis_card 1 0 (by decide) i) :=
  exchangePermutation_apply basis basis_card 1 0 (by decide) i

-- A singleton exchange and its reverse have the same cardinality.
example : exchange ({4} : Finset ℕ) 4 1 = {1} := by decide

example : exchange (exchange ({4} : Finset ℕ) 4 1) 1 4 = {4} :=
  reverse_exchange (by simp) (by simp)

-- Nonbasic labels exchange in the opposite direction.
example : (exchange ({0, 2} : Finset (Fin 4)) 0 1)ᶜ =
    exchange ({0, 2} : Finset (Fin 4))ᶜ 1 0 :=
  compl_exchange (by decide) (by decide)

-- Embedding labels in a larger finite universe preserves the exchange.
example : (exchange ({0, 2} : Finset (Fin 3)) 0 1).map
    (Fin.castLEEmb (by decide : 3 ≤ 4)) =
    exchange (({0, 2} : Finset (Fin 3)).map (Fin.castLEEmb (by decide : 3 ≤ 4)))
      (0 : Fin 4) (1 : Fin 4) :=
  map_exchange (Fin.castLEEmb (by decide : 3 ≤ 4)) _ _ _

end GameTheory.Tests.FiniteBasisExchange
