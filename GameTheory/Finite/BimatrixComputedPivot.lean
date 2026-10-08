import GameTheory.Finite.BimatrixPivot
import GameTheory.Finite.BimatrixBasisBounds
import GameTheory.Math.IntegerDictionaryComputation

/-! # Executable symbolic bimatrix pivots

Materialized integer Cramer data and cross-product comparisons select a leaving
row without rational inverse evaluation. The computed exchange agrees with the
canonical symbolic pivot for nonempty positive-payoff games.
-/

namespace GameTheory.Finite.BimatrixPivotPort
open GameTheory.Math GameTheory.Math.CanonicalDictionary
variable {m n : ℕ} {A B : Fin m → Fin n → ℤ}

/-- Scan the computed integer dictionary for an eligible minimum ratio. -/
def computedLeavingRow (port : BimatrixPivotPort A B) : Option (Fin (m + n)) :=
  IntegerDictionaryComputation.select port.basis.integerMatrix (fun _ => 1)
    (fun i => bimatrixIntegerColumns A B i port.entering)

theorem computedLeavingRow_spec (port : BimatrixPivotPort A B) (l : Fin (m + n))
    (h : port.computedLeavingRow = some l) : port.basis.IsLeaving port.entering l := by
  have hh := IntegerDictionaryComputation.select_some_spec port.basis.integerMatrix
    (fun _ => 1) (fun i => bimatrixIntegerColumns A B i port.entering)
    port.basis.integerMatrix_det_ne_zero l h
  simpa only [port.basis.integerMatrix_map, Int.cast_one, bimatrixIntegerColumns_cast] using hh

/-- Absence of a selected row means every exact direction coordinate is nonpositive. -/
theorem computedLeavingRow_none (port : BimatrixPivotPort A B) :
    port.computedLeavingRow = none ↔ ∀ i,
      (basisMatrix (bimatrixBasisColumns A B) port.basis.basic port.basis.cardinality)⁻¹.mulVec
        (fun j => bimatrixBasisColumns A B j port.entering) i ≤ 0 := by
  have hh := IntegerDictionaryComputation.select_none port.basis.integerMatrix
    (fun _ => 1) (fun i => bimatrixIntegerColumns A B i port.entering)
    port.basis.integerMatrix_det_ne_zero
  simpa only [computedLeavingRow, port.basis.integerMatrix_map, bimatrixIntegerColumns_cast]
    using hh

/-- Positive bimatrix games select precisely the canonical symbolic leaving row. -/
theorem computedLeavingRow_eq_some (port : BimatrixPivotPort A B)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    port.computedLeavingRow = some (port.leavingRow hm hn hA hB) := by
  cases he : port.computedLeavingRow with
  | none =>
    obtain ⟨i, hi⟩ := port.basis.exists_positive_direction hm hn hA hB port.entering
    exact (not_le_of_gt hi ((port.computedLeavingRow_none.mp he) i)).elim
  | some l =>
    have hl := port.computedLeavingRow_spec l he
    have hle : l = port.leavingRow hm hn hA hB :=
      (port.basis.exists_unique_leavingRow hm hn hA hB port.entering).choose_spec.2 l hl
    exact congrArg some hle

/-- Exchange at the computed row; `none` represents a dictionary without an eligible row. -/
def computedPivot (port : BimatrixPivotPort A B) : Option (BimatrixPivotPort A B) :=
  match h : port.computedLeavingRow with
  | none => none
  | some l => some (port.exchange l (port.computedLeavingRow_spec l h))

/-- Computed exchange agrees with the canonical mathematical pivot. -/
theorem computedPivot_eq_some (port : BimatrixPivotPort A B)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    port.computedPivot = some (port.pivot hm hn hA hB) := by
  unfold computedPivot
  split
  · rename_i hh
    have he := port.computedLeavingRow_eq_some hm hn hA hB
    rw [hh] at he
    cases he
  · rename_i l hh
    have he : l = port.leavingRow hm hn hA hB :=
      Option.some.inj (hh.symm.trans (port.computedLeavingRow_eq_some hm hn hA hB))
    subst l
    rfl

end GameTheory.Finite.BimatrixPivotPort
