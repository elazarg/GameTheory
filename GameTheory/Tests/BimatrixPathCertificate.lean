import GameTheory.Finite.BimatrixPathCertificate

/-! Endpoint decoding preserves a degenerate equilibrium and restores signed payoffs. -/
namespace GameTheory.Tests.BimatrixPathCertificate

open GameTheory.Finite GameTheory.Math.LinearComplementarity

private def A (_ : Fin 1) (_ : Fin 2) : ℤ := -3
private def B (_ : Fin 1) (_ : Fin 2) : ℤ := -5
private def point : Fin 1 ⊕ Fin 2 → ℚ
  | .inl _ => 1
  | .inr j => if j = 0 then 1 / 3 else 2 / 3

example : IsSolution (fun _ => 1)
    (bimatrixComplementaryMatrix (fun i j => A i j + 4) (fun i j => B i j + 6))
    point := by
  unfold IsSolution
  decide +kernel

example : (bimatrixEndpointCertificate point 4 6).Valid A B := by
  apply bimatrixEndpointCertificate_valid A B 4 6 point
  · unfold IsSolution
    decide +kernel
  · intro hz
    have h := congrFun hz (.inl 0)
    norm_num [point] at h

example : (bimatrixEndpointCertificate point 4 6).colWeights 1 =
    2 * (bimatrixEndpointCertificate point 4 6).colWeights 0 := by decide +kernel

example : (bimatrixEndpointCertificate point 4 6).rowUtilityNumerator < 0 ∧
    (bimatrixEndpointCertificate point 4 6).colUtilityNumerator < 0 := by decide +kernel

example : ∃ c : BimatrixCertificate 1 2, c.Valid A B ∧
    c.FitsWidth (GameTheory.bimatrixCertificateWidth 1 2 3) :=
  exists_bounded_bimatrixCertificate_via_path A B 3 (by decide) (by decide)
    (by decide) (by decide)

end GameTheory.Tests.BimatrixPathCertificate
