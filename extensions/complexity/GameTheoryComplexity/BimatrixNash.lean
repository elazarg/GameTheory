import GameTheoryComplexity.Backend.GeneralBimatrixFNP

/-! Optional machine certificates for exact mixed Nash search in signed
rectangular bimatrix games. Binary answers represent ordinary mixed equilibria;
FNP verification does not by itself establish PPAD membership. -/
namespace GameTheory.Complexity
open _root_.Complexity Backend

/-- Independently signed rectangular bimatrix Nash certificates belong to FNP. -/
theorem bimatrixNashRelation_mem_FNP : generalBimatrixRelation ∈ FNP :=
  generalBimatrixRelation_mem_FNP

/-- The complete serialized verifier has an actual polynomial-time machine. -/
theorem exists_bimatrixNashVerifier_machine :
    ∃ (k : ℕ) (machine : TM k) (bound : Polynomial ℕ),
      machine.ComputesInTime generalBimatrixPairedVerdict bound.eval :=
  exists_generalBimatrixPairedVerdict_machine

end GameTheory.Complexity
