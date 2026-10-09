import GameTheoryComplexity.Backend.GeneralBimatrixEndpointCapacity

/-! Signed rectangular controller emission requires no client arithmetic bounds. -/
namespace GameTheory.Complexity.Tests.GeneralBimatrixEndpointCapacity
open Backend GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec GameTheory.Math
open _root_.Complexity _root_.Complexity.Cobham

private def input : List Bool := encodeGeneralInstance 1 2 2
  (fun _ j => if j = 0 then -1 else 2)
  (fun _ j => if j = 0 then 2 else -2)

private theorem input_valid : GeneralInstanceValid input := by decide +kernel

example : decodeGeneralPayoff false input 0 0 = -1 := by decide +kernel
example : decodeGeneralPayoff true input 0 1 = -2 := by decide +kernel

-- The controller supplies determinant, coefficients and sufficient width itself.
example (basis : GeneralBimatrixShiftedBasis input) (entering : List Bool) :
    generalBimatrixDictionaryEndpointWord ![input, membershipWord basis.basic, entering] =
      generalBimatrixEndpointWord input basis :=
  generalBimatrixDictionaryEndpointWord_eq_endpoint input input_valid basis entering

example (basis : GeneralBimatrixShiftedBasis input) (entering : List Bool)
    (hc : ComplementaryLabels.IsComplementary basis.nonbasic)
    (hs : basis ≠ bimatrixSourceBasis _ _) :
    generalBimatrixRelation input
      (generalBimatrixDictionaryEndpointWord ![input, membershipWord basis.basic, entering]) :=
  generalBimatrixDictionaryEndpointWord_accept input input_valid basis entering hc hs

-- Empty or malformed input remains computable, while acceptance requires valid dimensions.
example : ¬GeneralInstanceValid [] := by decide +kernel
example : FPn generalBimatrixDictionaryEndpointWord := generalBimatrixDictionaryEndpointWord_mem_FPn

end GameTheory.Complexity.Tests.GeneralBimatrixEndpointCapacity
