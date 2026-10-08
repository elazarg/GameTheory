import GameTheory.Finite.BimatrixEndpointBounds

/-! Direct endpoint bounds cover tied signed games, zero coordinates and
truncated negative coordinates, without confusing width with validity. -/
namespace GameTheory.Tests.BimatrixEndpointBounds
open GameTheory.Finite

private def tiedEndpoint : Fin 1 ⊕ Fin 2 → ℚ
  | .inl _ => 1 / 2
  | .inr _ => 1 / 4

-- Both columns are tied; payoff shifts recover utilities zero and minus one.
example : (bimatrixEndpointCertificate tiedEndpoint 2 3).Valid
    (fun _ _ => 0) (fun _ _ => -1) := by decide +kernel

example : (bimatrixEndpointCertificate tiedEndpoint 2 3).FitsWidth
    (bimatrixEndpointWidth 1 2 2 2) :=
  bimatrixEndpointCertificate_fitsWidth tiedEndpoint 2 3 2 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def zeroCoordinate : Fin 1 ⊕ Fin 1 → ℚ
  | .inl _ => 0
  | .inr _ => 1 / 2

example : (bimatrixEndpointCertificate zeroCoordinate (-2) 1).FitsWidth
    (bimatrixEndpointWidth 1 1 1 1) :=
  bimatrixEndpointCertificate_fitsWidth zeroCoordinate (-2) 1 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def negativeCoordinate : Fin 1 ⊕ Fin 1 → ℚ
  | .inl _ => -1 / 2
  | .inr _ => 1 / 2

-- Truncation is bounded for negative coordinates, but supplies no valid strategy.
example : (bimatrixEndpointCertificate negativeCoordinate 0 0).FitsWidth
    (bimatrixEndpointWidth 1 1 1 0) :=
  bimatrixEndpointCertificate_fitsWidth negativeCoordinate 0 0 1 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : ¬ (bimatrixEndpointCertificate negativeCoordinate 0 0).Valid
    (fun _ _ => 1) (fun _ _ => 1) := by decide +kernel

end GameTheory.Tests.BimatrixEndpointBounds
