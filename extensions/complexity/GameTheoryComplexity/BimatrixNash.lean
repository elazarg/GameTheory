module

public import GameTheoryComplexity.Backend.GeneralBimatrixTotality
public import GameTheoryComplexity.Backend.GeneralBimatrixEndpoint
public import GameTheoryComplexity.Backend.GeneralBimatrixReduction
public import GameTheoryComplexity.PPAD
public import GameTheoryComplexity.Brouwer
public import GameTheoryComplexity.Backend.BrouwerNashHardness

@[expose] public section

/-! Optional machine certificates for exact mixed Nash search in signed
rectangular bimatrix games. Binary answers represent ordinary mixed equilibria;
certified complementary-path circuits establish PPAD membership, and the
Brouwer-to-game reduction establishes PPAD hardness on the same serialized relation. -/
namespace GameTheory.Complexity
open Turing.MultiTapeTM Cslib.Complexity Backend

/-- Independently signed rectangular bimatrix Nash certificates belong to FNP. -/
theorem bimatrixNashRelation_mem_FNP : generalBimatrixRelation ∈ FNP encBits :=
  generalBimatrixRelation_mem_FNP

/-- Serialized signed rectangular Nash search is total and polynomially verified. -/
theorem bimatrixNashRelation_mem_TFNP : generalBimatrixRelation ∈ TFNP encBits :=
  generalBimatrixRelation_mem_TFNP

/-- Exact Nash search for independently signed rectangular bimatrix games is in PPAD. -/
theorem bimatrixNashRelation_mem_PPAD : generalBimatrixRelation ∈ PPAD encBits :=
  exists_generalBimatrixToEndOfLineReduction.mem_PPAD generalBimatrixRelation_mem_FNP
    rawEndOfLineRelation_mem_PPAD

/-- Every PPAD search problem reduces to exact signed rectangular bimatrix Nash search. -/
theorem bimatrixNashRelation_PPADHard : SearchHard @PPAD encBits generalBimatrixRelation := by
  intro α enc R hR
  exact (brouwerRelation_PPADHard enc R hR).trans
    BrouwerNashHardness.exists_brouwerToBimatrixReduction

/-- Exact signed rectangular bimatrix Nash search is PPAD-complete. -/
theorem bimatrixNashRelation_PPADComplete : SearchComplete @PPAD encBits generalBimatrixRelation :=
  ⟨bimatrixNashRelation_mem_PPAD, bimatrixNashRelation_PPADHard⟩

/-- Every serialized input has an answer, including malformed-input fallback. -/
theorem exists_bimatrixNashCertificate (input : List Bool) :
    ∃ certificate, generalBimatrixRelation input certificate :=
  generalBimatrixRelation_total input

/-- The actual Boolean verifier charges both the entire instance and candidate. -/
theorem bimatrixNashVerifier_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => generalBimatrixAccepts p.1 p.2)
      (encPair encBits encBits) encBool :=
  generalBimatrixAccepts_polyTime (ComputableInPolyTime.fst encBits encBits)
    (ComputableInPolyTime.snd encBits encBits)

end GameTheory.Complexity
