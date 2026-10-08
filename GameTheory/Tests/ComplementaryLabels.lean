import GameTheory.Math.ComplementaryLabels

/-! Finite paired-label controls exercise the complementary boundary, a missing
label with a distinct unique duplicate, and failure of the size/coverage guards. -/

namespace GameTheory.Tests.ComplementaryLabels

open GameTheory.Math.ComplementaryLabels
open GameTheory.Math.FiniteBasisExchange

private def complete : Finset (Fin 2 × Bool) := {(0, false), (1, true)}
private def duplicated : Finset (Fin 2 × Bool) := {(1, false), (1, true)}

example : IsComplementary complete := by unfold IsComplementary; decide

example : CoversExcept duplicated 0 := by unfold CoversExcept; decide

example : ∃! i : Fin 2, (i, false) ∈ duplicated ∧ (i, true) ∈ duplicated := by
  exact exists_unique_duplicate_of_missing duplicated 0 (by decide)
    (by unfold CoversExcept; decide) (by decide)

example : ¬IsComplementary duplicated := by unfold IsComplementary; decide

-- Exchanging either member of the duplicate for the missing label closes the boundary.
example : IsComplementary (exchange duplicated (1, false) (0, false)) := by
  unfold IsComplementary; decide

example : CoversExcept (exchange duplicated (1, false) (0, false)) 0 := by
  exact CoversExcept.exchange_duplicate (by unfold CoversExcept; decide : CoversExcept duplicated 0)
    (by decide) false (0, false)

-- Removing a designated label preserves the coverage certificate for all other labels.
example : CoversExcept (exchange complete (0, false) (1, false)) 0 := by
  exact CoversExcept.exchange_dropped
    (by unfold CoversExcept; decide : CoversExcept complete 0) false (1, false)

-- Two missing labels fail coverage even if the set has the required cardinality.
private def twoMissing : Finset (Fin 4 × Bool) :=
  {(2, false), (2, true), (3, false), (3, true)}

example : twoMissing.card = Fintype.card (Fin 4) := by decide
example : ¬CoversExcept twoMissing 0 := by unfold CoversExcept; decide

-- Coverage alone cannot compensate for the wrong number of variables.
private def tooLarge : Finset (Fin 2 × Bool) := {(0, false), (1, false), (1, true)}

example : CoversExcept tooLarge 0 := by unfold CoversExcept; decide
example : tooLarge.card ≠ Fintype.card (Fin 2) := by decide
example : ¬IsComplementary tooLarge := by unfold IsComplementary; decide

end GameTheory.Tests.ComplementaryLabels
