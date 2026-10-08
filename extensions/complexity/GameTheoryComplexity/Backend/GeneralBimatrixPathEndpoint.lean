import GameTheoryComplexity.Backend.GeneralBimatrixEndpointCapacity
import GameTheory.Finite.BimatrixPathWitness

/-! Accepted certificate emission from canonical bimatrix path witnesses.
Raw pointer inconsistency identifies a complementary non-source basis; its
computed dictionary emits an answer for the original independently signed game. -/
namespace GameTheory.Complexity.Backend
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec GameTheory.Math

/-- A raw witness on the canonical decoded path emits an accepted Nash certificate. -/
theorem generalBimatrixPathEndpoint_accept (input : List Bool) (hi : GeneralInstanceValid input)
    (d : Fin (generalRowCount input + generalColCount input))
    (port : BimatrixPathPort
      (fun i : Fin (generalRowCount input) => fun j : Fin (generalColCount input) =>
        decodeGeneralPayoff false input i.val j.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
      (fun i : Fin (generalRowCount input) => fun j : Fin (generalColCount input) =>
        decodeGeneralPayoff true input i.val j.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)) d)
    (entering : List Bool)
    (hw : EndOfLine.RawWitness
      (BimatrixPathPort.predecessor hi.1 hi.2.1
        (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le)
        (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le))
      (BimatrixPathPort.successor hi.1 hi.2.1
        (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le)
        (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le))
      (bimatrixSourcePort _ _ d) port) :
    generalBimatrixRelation input
      (generalBimatrixDictionaryEndpointWord ![input, membershipWord port.node.basis.basic, entering]) := by
  obtain ⟨_, hc, hs⟩ := BimatrixPathPort.rawWitness_terminal hi.1 hi.2.1
    (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le)
    (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le) port hw
  exact generalBimatrixDictionaryEndpointWord_accept input hi port.node.basis entering hc hs

end GameTheory.Complexity.Backend
