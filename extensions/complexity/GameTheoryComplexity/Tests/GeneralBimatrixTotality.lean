import GameTheoryComplexity.BimatrixNash

/-! Total search controls for honest signed games and malformed encodings. -/
namespace GameTheory.Complexity.Tests.GeneralBimatrixTotality
open _root_.Complexity Backend

-- Exercise the upstream class, rather than a library-local totality predicate.
example : generalBimatrixRelation ∈ TFNP := bimatrixNashRelation_mem_TFNP

-- Negative, independent rectangular payoffs require no analytic existence input.
private def input : List Bool :=
  encodeGeneralInstance 1 2 3 (fun _ j => if j = 0 then -3 else 2)
    (fun _ j => if j = 0 then 1 else -2)

example : GeneralInstanceValid input :=
  encodeGeneralInstance_valid 1 2 3 _ _ (by decide) (by decide) (by decide)

example : ∃ certificate, generalBimatrixRelation input certificate :=
  exists_bimatrixNashCertificate input

-- Empty and zero-dimension headers are included in totality.
example : ∃ certificate, generalBimatrixRelation [] certificate :=
  exists_bimatrixNashCertificate []

example : generalBimatrixRelation [] [] := Or.inr ⟨by decide, rfl⟩

example : ¬ generalBimatrixRelation [] [true] := by
  rw [generalBimatrixRelation_invalid_iff _ _ (by decide)]
  decide

example : generalBimatrixRelation [false, true, false, true, false] [] :=
  Or.inr ⟨by decide, rfl⟩

end GameTheory.Complexity.Tests.GeneralBimatrixTotality
