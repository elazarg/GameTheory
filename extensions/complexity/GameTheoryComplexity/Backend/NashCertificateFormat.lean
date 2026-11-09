module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import GameTheory.Finite.BimatrixNashCertificate

@[expose] public section

/-! Fixed-width little-endian fields for the ordinary integer numerator
certificate. The machine verifier and encoding proofs share this total parser. -/

namespace GameTheory.Complexity.Backend
open Turing.MultiTapeTM

/-- Read one fixed-width field; missing bits are absent from the returned word. -/
def nashCertificateField (W k : ℕ) (certificate : List Bool) : List Bool :=
  (certificate.drop (k * W)).take W

/-- Parse denominators, utility numerators, row weights, then column weights.
All fields use the same little-endian width. Parsing is total on malformed words. -/
def decodeNashCertificate (q W : ℕ) (certificate : List Bool) :
    GameTheory.Finite.NumeratorCertificate q where
  rowDenominator := ofBits (nashCertificateField W 0 certificate)
  colDenominator := ofBits (nashCertificateField W 1 certificate)
  rowUtilityNumerator := ofBits (nashCertificateField W 2 certificate)
  colUtilityNumerator := ofBits (nashCertificateField W 3 certificate)
  rowWeights := fun i => ofBits (nashCertificateField W (4 + i) certificate)
  colWeights := fun i => ofBits (nashCertificateField W (4 + q + i) certificate)

end GameTheory.Complexity.Backend
