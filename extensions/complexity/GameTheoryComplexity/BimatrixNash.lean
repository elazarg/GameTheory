import GameTheoryComplexity.Backend.GeneralBimatrixTotality
import GameTheoryComplexity.Backend.GeneralBimatrixEndpoint
import GameTheoryComplexity.Backend.GeneralBimatrixReduction
import GameTheoryComplexity.PPAD
import GameTheoryComplexity.Brouwer
import GameTheoryComplexity.Backend.BrouwerNashHardness

/-! Optional machine certificates for exact mixed Nash search in signed
rectangular bimatrix games. Binary answers represent ordinary mixed equilibria;
certified complementary-path circuits establish PPAD membership, and the
Brouwer-to-game reduction establishes PPAD hardness on the same serialized relation. -/
namespace GameTheory.Complexity
open _root_.Complexity Backend

/-- Independently signed rectangular bimatrix Nash certificates belong to FNP. -/
theorem bimatrixNashRelation_mem_FNP : generalBimatrixRelation ∈ FNP :=
  generalBimatrixRelation_mem_FNP

/-- Serialized signed rectangular Nash search is total and polynomially verified. -/
theorem bimatrixNashRelation_mem_TFNP : generalBimatrixRelation ∈ TFNP :=
  generalBimatrixRelation_mem_TFNP

/-- Exact Nash search for independently signed rectangular bimatrix games is in PPAD. -/
theorem bimatrixNashRelation_mem_PPAD : generalBimatrixRelation ∈ PPAD :=
  ⟨generalBimatrixRelation_mem_FNP, exists_generalBimatrixToEndOfLineReduction⟩

/-- Every PPAD search problem reduces to exact signed rectangular bimatrix Nash search. -/
theorem bimatrixNashRelation_PPADHard : PPADHard generalBimatrixRelation := by
  intro T hT
  obtain ⟨a⟩ := brouwerRelation_PPADHard T hT
  obtain ⟨b⟩ := BrouwerNashHardness.exists_brouwerToBimatrixReduction
  exact ⟨a.trans b⟩

/-- Exact signed rectangular bimatrix Nash search is PPAD-complete. -/
theorem bimatrixNashRelation_PPADComplete : PPADComplete generalBimatrixRelation :=
  ⟨bimatrixNashRelation_mem_PPAD, bimatrixNashRelation_PPADHard⟩

/-- Every serialized input has an answer, including malformed-input fallback. -/
theorem exists_bimatrixNashCertificate (input : List Bool) :
    ∃ certificate, generalBimatrixRelation input certificate :=
  generalBimatrixRelation_total input

/-- The complete serialized verifier has an actual polynomial-time machine. -/
theorem exists_bimatrixNashVerifier_machine :
    ∃ (k : ℕ) (machine : TM k) (bound : Polynomial ℕ),
      machine.ComputesInTime generalBimatrixPairedVerdict bound.eval :=
  exists_generalBimatrixPairedVerdict_machine

end GameTheory.Complexity
