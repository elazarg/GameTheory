import GameTheory.Finite.BimatrixBasisBounds
import GameTheory.Finite.BimatrixPivot

/-! Binary bounds hold for signed source columns and a degenerate rectangular pivot. -/
namespace GameTheory.Tests.BimatrixBasisBounds
open GameTheory.Finite GameTheory.Math GameTheory.Math.CanonicalDictionary

private def A (_ : Fin 1) (_ : Fin 2) : ℤ := 8
private def B (_ : Fin 1) (_ : Fin 2) : ℤ := -8

example (i : Fin 3) (v : BimatrixVariable 1 2) :
    (bimatrixIntegerColumns A B i v).natAbs ≤ 2 ^ 3 :=
  bimatrixIntegerColumns_bound A B 3 (by decide) (by decide) i v

example (i : Fin 3) (k : Fin 4) :
    (PerturbedDictionary.dictionaryCoefficients
      (basisMatrix (bimatrixBasisColumns A B) (bimatrixSourceBasis A B).basic
        (bimatrixSourceBasis A B).cardinality) (fun _ => 1) i k).den <
      2 ^ IntegerBasisBounds.width 3 3 :=
  ((bimatrixSourceBasis A B).dictionaryCoefficients_bounds 3 (by decide) (by decide) i k).2

example (i : Fin 3) :
    ((basisMatrix (bimatrixBasisColumns A B) (bimatrixSourceBasis A B).basic
        (bimatrixSourceBasis A B).cardinality)⁻¹.mulVec
      (fun j => bimatrixBasisColumns A B j (toLex (0, true))) i).num.natAbs <
      2 ^ IntegerBasisBounds.width 3 3 :=
  ((bimatrixSourceBasis A B).direction_bounds 3 (by decide) (by decide) _ i).1

private def positive (_ : Fin 1) (_ : Fin 2) : ℤ := 8
private def sourcePort : BimatrixPivotPort positive positive where
  basis := bimatrixSourceBasis positive positive
  entering := toLex (0, true)
  nonbasic := by simp [bimatrixSourceBasis, bimatrixSlackVariables]

private noncomputable def successor : BimatrixBasis positive positive :=
  (sourcePort.pivot (by decide) (by decide) (by decide) (by decide)).basis

example (i : Fin 1 ⊕ Fin 2) : (successor.payoffPoint i).den <
    2 ^ IntegerBasisBounds.width 3 3 :=
  (successor.payoffPoint_bounds 3 (by decide) (by decide) i).2

example : (bimatrixEndpointCertificate successor.payoffPoint 9 9).FitsWidth
    (bimatrixEndpointWidth 1 2 (IntegerBasisBounds.width 3 3) 4) :=
  successor.endpointCertificate_fitsWidth 9 9 3 4 (by decide) (by decide)
    (by decide) (by decide)

end GameTheory.Tests.BimatrixBasisBounds
