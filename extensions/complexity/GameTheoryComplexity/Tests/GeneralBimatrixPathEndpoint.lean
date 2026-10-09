import GameTheoryComplexity.Backend.GeneralBimatrixPathEndpoint

/-! Raw path witnesses produce accepted answers for signed rectangular games. -/
namespace GameTheory.Complexity.Tests.GeneralBimatrixPathEndpoint
open Backend GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec GameTheory.Math

private def input : List Bool := encodeGeneralInstance 1 2 2
  (fun _ j => if j = 0 then -1 else 2) (fun _ j => if j = 0 then 2 else -2)
private theorem hi : GeneralInstanceValid input := by decide +kernel
private abbrev A (i : Fin (generalRowCount input)) (j : Fin (generalColCount input)) : ℤ :=
  decodeGeneralPayoff false input i.val j.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)
private abbrev B (i : Fin (generalRowCount input)) (j : Fin (generalColCount input)) : ℤ :=
  decodeGeneralPayoff true input i.val j.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)
private def dropped : Fin (generalRowCount input + generalColCount input) := ⟨0, by decide +kernel⟩
private theorem hA : ∀ i j, 0 < A i j := fun i j =>
  payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le
private theorem hB : ∀ i j, 0 < B i j := fun i j =>
  payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le

-- Source consistency excludes the outgoing branch even though RawWitness permits it syntactically.
example : ¬EndOfLine.RawWitness (BimatrixPathPort.predecessor hi.1 hi.2.1 hA hB)
    (BimatrixPathPort.successor hi.1 hi.2.1 hA hB)
    (bimatrixSourcePort A B dropped) (bimatrixSourcePort A B dropped) := by
  intro hw
  have ht := (BimatrixPathPort.rawWitness_iff hi.1 hi.2.1 hA hB
    (bimatrixSourcePort A B dropped)).mp hw
  exact ht.2 rfl

-- Complementarity and non-source hypotheses follow from the pointer witness.
example (port : BimatrixPathPort A B dropped) (entering : List Bool)
    (hw : EndOfLine.RawWitness (BimatrixPathPort.predecessor hi.1 hi.2.1 hA hB)
      (BimatrixPathPort.successor hi.1 hi.2.1 hA hB) (bimatrixSourcePort A B dropped) port) :
    generalBimatrixRelation input
      (generalBimatrixDictionaryEndpointWord ![input, membershipWord port.node.basis.basic, entering]) :=
  generalBimatrixPathEndpoint_accept input hi dropped port entering hw

end GameTheory.Complexity.Tests.GeneralBimatrixPathEndpoint
