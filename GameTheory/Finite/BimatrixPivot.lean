import GameTheory.Finite.BimatrixBasisExit

/-! Reversible pivots between canonical bimatrix bases.
A port records a nonbasic entering variable. Nonempty positive-payoff games have a
unique symbolic pivot at every port. The opposite port enters the old leaving
variable; pivoting there restores both the basis and the original entering
variable. This is an unoriented edge operation, before path orientation.
-/
namespace GameTheory.Finite
open GameTheory.Math GameTheory.Math.CanonicalDictionary
variable {m n : ℕ} {A B : Fin m → Fin n → ℤ}

/-- The symbolic leaving-row predicate specialized to a bimatrix basis. -/
abbrev BimatrixBasis.IsLeaving (basis : BimatrixBasis A B)
    (entering : BimatrixVariable m n) (l : Fin (m + n)) : Prop :=
  IsLeavingRow (PerturbedDictionary.dictionaryCoefficients
    (basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality) (fun _ => 1))
    ((basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality)⁻¹.mulVec
      (fun i => bimatrixBasisColumns A B i entering)) l

/-- A canonical feasible basis with one nonbasic variable designated to enter. -/
structure BimatrixPivotPort (A B : Fin m → Fin n → ℤ) where
  /-- The invertible, strictly feasible basis at this port. -/
  basis : BimatrixBasis A B
  /-- The system variable whose column enters at this port. -/
  entering : BimatrixVariable m n
  nonbasic : entering ∉ basis.basic

namespace BimatrixPivotPort

@[ext] theorem ext {port other : BimatrixPivotPort A B}
    (hb : port.basis = other.basis) (he : port.entering = other.entering) : port = other := by
  cases port
  cases other
  cases hb
  cases he
  rfl

/-- The variable occupying the selected leaving row. -/
def leavingVariable (port : BimatrixPivotPort A B) (l : Fin (m + n)) : BimatrixVariable m n :=
  port.basis.basic.orderEmbOfFin port.basis.cardinality l

/-- The corresponding row of the exchanged basis after canonical sorting. -/
noncomputable def reverseRow (port : BimatrixPivotPort A B) (l : Fin (m + n)) : Fin (m + n) :=
  (FiniteBasisExchange.exchangePermutation port.basis.basic port.basis.cardinality
    l port.entering port.nonbasic).symm l

/-- The opposite port of a certified pivot enters the old leaving variable. -/
def exchange (port : BimatrixPivotPort A B) (l : Fin (m + n))
    (hl : port.basis.IsLeaving port.entering l) : BimatrixPivotPort A B where
  basis := port.basis.exchange l port.entering port.nonbasic hl
  entering := port.leavingVariable l
  nonbasic := FiniteBasisExchange.leaving_not_mem
    (Finset.orderEmbOfFin_mem port.basis.basic port.basis.cardinality l) port.nonbasic

/-- The reverse ratio test selects the row occupied by the entering variable. -/
theorem exchange_isLeaving (port : BimatrixPivotPort A B) (l : Fin (m + n))
    (hl : port.basis.IsLeaving port.entering l) :
    (port.exchange l hl).basis.IsLeaving (port.exchange l hl).entering (port.reverseRow l) :=
  exchange_reverse_leavingRow _ _ _ _ port.basis.feasible l port.entering port.nonbasic hl

/-- Certified reverse exchange restores the full port, including its entering variable. -/
theorem exchange_reverse (port : BimatrixPivotPort A B) (l : Fin (m + n))
    (hl : port.basis.IsLeaving port.entering l) :
    (port.exchange l hl).exchange (port.reverseRow l) (port.exchange_isLeaving l hl) = port := by
  apply ext
  · apply BimatrixBasis.ext
    exact exchange_reverse_set port.basis.basic port.basis.cardinality l port.entering port.nonbasic
  · exact exchanged_reverse_row port.basis.basic port.basis.cardinality l port.entering
      port.nonbasic

/-- Equality of leaving rows identifies their exchanged ports independently of certificates. -/
theorem exchange_congr (port : BimatrixPivotPort A B) {l r : Fin (m + n)}
    (hl : port.basis.IsLeaving port.entering l) (hr : port.basis.IsLeaving port.entering r)
    (h : l = r) : port.exchange l hl = port.exchange r hr := by
  cases h
  rfl

/-- The unique symbolic leaving row at a port of a positive-payoff game. -/
noncomputable def leavingRow (port : BimatrixPivotPort A B)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    Fin (m + n) :=
  (port.basis.exists_unique_leavingRow hm hn hA hB port.entering).choose

theorem leavingRow_spec (port : BimatrixPivotPort A B)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    port.basis.IsLeaving port.entering (port.leavingRow hm hn hA hB) :=
  (port.basis.exists_unique_leavingRow hm hn hA hB port.entering).choose_spec.1

/-- Deterministic symbolic pivoting at every nonbasic port of a positive-payoff game. -/
noncomputable def pivot (port : BimatrixPivotPort A B)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    BimatrixPivotPort A B :=
  port.exchange (port.leavingRow hm hn hA hB) (port.leavingRow_spec hm hn hA hB)

/-- The deterministic pivot chooses the certified reverse row at the opposite port. -/
theorem pivot_leavingRow (port : BimatrixPivotPort A B)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    (port.pivot hm hn hA hB).leavingRow hm hn hA hB =
      port.reverseRow (port.leavingRow hm hn hA hB) := by
  exact ((port.pivot hm hn hA hB).basis.exists_unique_leavingRow
    hm hn hA hB (port.pivot hm hn hA hB).entering |>.choose_spec.2 _
      (port.exchange_isLeaving _ (port.leavingRow_spec hm hn hA hB))).symm

/-- Pivoting twice restores the basis and the entering variable. -/
theorem pivot_pivot (port : BimatrixPivotPort A B)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    (port.pivot hm hn hA hB).pivot hm hn hA hB = port := by
  calc
    (port.pivot hm hn hA hB).pivot hm hn hA hB =
        (port.pivot hm hn hA hB).exchange
          (port.reverseRow (port.leavingRow hm hn hA hB))
          (port.exchange_isLeaving _ (port.leavingRow_spec hm hn hA hB)) :=
      exchange_congr _ _ _ (port.pivot_leavingRow hm hn hA hB)
    _ = port := port.exchange_reverse _ (port.leavingRow_spec hm hn hA hB)

/-- A pivot always changes the port, since a basic variable replaces a nonbasic one. -/
theorem pivot_ne_self (port : BimatrixPivotPort A B)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    port.pivot hm hn hA hB ≠ port := by
  intro h
  have he := congrArg BimatrixPivotPort.entering h
  change port.leavingVariable (port.leavingRow hm hn hA hB) = port.entering at he
  apply port.nonbasic
  rw [← he]
  exact Finset.orderEmbOfFin_mem _ _ _

end BimatrixPivotPort
end GameTheory.Finite
