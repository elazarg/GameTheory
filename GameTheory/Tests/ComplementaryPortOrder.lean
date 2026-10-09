import GameTheory.Math.ComplementaryPortOrder
import Mathlib.Algebra.Order.Ring.Int

/-! Twin ports have the same sorted coordinate and opposite payoff parity,
including ports inserted between existing labels and at either boundary.
-/

namespace GameTheory.Tests.ComplementaryPortOrder

open GameTheory.Math.ComplementaryPortOrder

private def middle : Finset (Fin 3 ×ₗ Bool) := {toLex (0, true), toLex (2, false)}
private theorem middle_card : middle.card = 2 := by decide
private theorem middle_false_missing : toLex ((1 : Fin 3), false) ∉ middle := by decide
private theorem middle_true_missing : toLex ((1 : Fin 3), true) ∉ middle := by decide

example : ((insert (toLex ((1 : Fin 3), false)) middle).orderIsoOfFin
      ((Finset.card_insert_of_notMem middle_false_missing).trans
        (congrArg (· + 1) middle_card))).symm
        ⟨toLex ((1 : Fin 3), false), Finset.mem_insert_self _ _⟩ =
    ((insert (toLex ((1 : Fin 3), true)) middle).orderIsoOfFin
      ((Finset.card_insert_of_notMem middle_true_missing).trans
        (congrArg (· + 1) middle_card))).symm
        ⟨toLex ((1 : Fin 3), true), Finset.mem_insert_self _ _⟩ :=
  twin_index middle middle_card 1 middle_false_missing middle_true_missing

example : payoffParity (R := ℤ) (insert (toLex ((1 : Fin 3), true)) middle) 2 =
    -payoffParity (R := ℤ) (insert (toLex ((1 : Fin 3), false)) middle) 2 :=
  twin_payoffParity middle 1 2 middle_true_missing (by decide)

example : payoffParity (R := ℤ) (insert (toLex ((1 : Fin 3), false)) middle) 2 = -1 ∧
    payoffParity (R := ℤ) (insert (toLex ((1 : Fin 3), true)) middle) 2 = 1 := by
  unfold payoffParity
  decide

-- A designated-label port is excluded from the count and therefore does not change parity.
example : payoffParity (R := ℤ) (insert (toLex ((1 : Fin 3), true)) middle) 1 =
    payoffParity (R := ℤ) (insert (toLex ((1 : Fin 3), false)) middle) 1 := by
  unfold payoffParity
  decide

-- At an empty basis both ports have the sole canonical coordinate.
example : ((insert (toLex ((0 : Fin 1), false)) (∅ : Finset (Fin 1 ×ₗ Bool))).orderIsoOfFin
      (by decide : (insert (toLex ((0 : Fin 1), false))
        (∅ : Finset (Fin 1 ×ₗ Bool))).card = 1)).symm
        ⟨toLex ((0 : Fin 1), false), Finset.mem_insert_self _ _⟩ =
    ((insert (toLex ((0 : Fin 1), true)) (∅ : Finset (Fin 1 ×ₗ Bool))).orderIsoOfFin
      (by decide : (insert (toLex ((0 : Fin 1), true)) (∅ : Finset (Fin 1 ×ₗ Bool))).card = 1)).symm
        ⟨toLex ((0 : Fin 1), true), Finset.mem_insert_self _ _⟩ :=
  twin_index ∅ rfl 0 (by simp) (by simp)

end GameTheory.Tests.ComplementaryPortOrder
