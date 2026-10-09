import GameTheory.Finite.BimatrixComputedPivot
import GameTheory.Finite.BimatrixPathOrientation
import GameTheory.Math.FiniteSetRank

/-! Integer computation of determinant-oriented complementary path colors.
Counting preceding columns and payoff kinds replaces augmented rational minors;
the resulting color agrees with the canonical source-calibrated orientation. -/
namespace GameTheory.Finite.BimatrixPathPort
open GameTheory.Math GameTheory.Math.CanonicalDictionary
variable {m n : ℕ} {A B : Fin m → Fin n → ℤ} {d : Fin (m + n)}

/-- Signed basis determinant adjusted by its insertion rank and payoff parity. -/
def computedOrientationScore (port : BimatrixPathPort A B d) : ℤ :=
  (-1 : ℤ) ^ ((insert port.entering port.node.basis.basic).filter
    (fun v => v < port.entering)).card *
    IntegerCramerComputation.determinant port.node.basis.integerMatrix *
    ComplementaryPortOrder.payoffParity (insert port.entering port.node.basis.basic) d

theorem computedOrientationScore_cast (port : BimatrixPathPort A B d) :
    (port.computedOrientationScore : ℚ) = port.orientationScore := by
  have hcard := (Finset.card_insert_of_notMem port.toPivotPort.nonbasic).trans
    (congrArg (· + 1) port.node.basis.cardinality)
  have hrank := FiniteSetRank.rank_eq_index (insert port.entering port.node.basis.basic) hcard
    port.entering (Finset.mem_insert_self _ _)
  change _ = FacetOrientation.canonicalOrientation (bimatrixBasisColumns A B)
    (insert port.entering port.node.basis.basic) hcard port.entering
      (Finset.mem_insert_self _ _) *
        ComplementaryPortOrder.payoffParity (insert port.entering port.node.basis.basic) d
  rw [FacetOrientation.canonicalOrientation_insert (bimatrixBasisColumns A B)
    port.node.basis.basic port.node.basis.cardinality port.entering port.toPivotPort.nonbasic]
  unfold computedOrientationScore ComplementaryPortOrder.payoffParity
  rw [hrank]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    IntegerCramerComputation.determinant_eq]
  rw [Int.cast_det, port.node.basis.integerMatrix_map]
  rfl

/-- Evaluate the color using integer signs and the source's integer score. -/
def computedColor (port : BimatrixPathPort A B d) : Bool :=
  decide (0 < port.computedOrientationScore *
    (bimatrixSourcePort A B d).computedOrientationScore)

/-- The executable integer color is the mathematical path color. -/
theorem computedColor_eq (port : BimatrixPathPort A B d) : port.computedColor = port.color := by
  unfold computedColor color
  have hcast := Int.cast_pos (R := ℚ)
    (n := port.computedOrientationScore * (bimatrixSourcePort A B d).computedOrientationScore)
  have hiff : 0 < port.computedOrientationScore *
      (bimatrixSourcePort A B d).computedOrientationScore ↔
      0 < port.orientationScore * (bimatrixSourcePort A B d).orientationScore := by
    simpa only [Int.cast_mul, computedOrientationScore_cast] using hcast.symm
  exact decide_eq_decide.mpr hiff

end GameTheory.Finite.BimatrixPathPort
